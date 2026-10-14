/* -*- Source -*-
 * Public conversion API, extracted from the former somt-convert entry point.
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/translation/convert.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/translation/translate.h"
#include "somtparser/translation/module.h"

#include <fstream>
#include <iostream>
#include <new>
#include <sstream>
#include <vector>

namespace SOMTParser {
namespace {

std::string joined(const std::vector<std::string>& items) {
    std::string out;
    for (const auto& i : items) {
        if (!out.empty()) { out += ", "; }
        out += i;
    }
    return out;
}

bool parseDialect(const std::string& s, Lower::OmtDialect& out) {
    if (s == "gomt" || s == "smtlib-omt-2025") { out = Lower::OmtDialect::Gomt; return true; }
    if (s == "z3")              { out = Lower::OmtDialect::Z3;          return true; }
    if (s == "optimathsat")     { out = Lower::OmtDialect::OptiMathSAT; return true; }
    if (s == "none")            { out = Lower::OmtDialect::None;        return true; }
    return false;
}

const char* severityName(Uir::Severity s) {
    switch (s) {
    case Uir::Severity::NOTE:    return "note";
    case Uir::Severity::WARNING: return "warning";
    case Uir::Severity::ERROR:   return "error";
    }
    return "error";
}

} // namespace

int convert(const Lang::SourceUnit& source, const ConvertOptions& options,
            std::istream& input, std::ostream& output, std::ostream& diagnostics) {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());
    Lang::SourceUnit unit = source;
    TranslateOptions opts;
    opts.language_id = options.language;
    opts.profile_id = options.profile.value_or("default");
    opts.parse = options.parse;
    const std::string& report_path = options.report;
    const bool module_mode = options.module;
    if (options.dialect && !parseDialect(*options.dialect, opts.omt_dialect)) {
        diagnostics << "unknown dialect '" << *options.dialect << "'\n";
        return 2;
    }
    if (unit.main_path.empty() && unit.inline_source.empty()) {
        diagnostics << "an input path or source is required\n";
        return 2;
    }
    if (unit.display_name == "<memory>" && !unit.main_path.empty()) {
        unit.display_name = unit.main_path;
    }

    // An id this build does not have is a mistake in the command line, so it
    // exits 2 like `--dialect bogus` already did. Letting it through to
    // translate() instead filed `--from nosuh` under E_UNSUPPORTED_CONSTRUCT --
    // the bucket that is supposed to measure how much of each *language* we
    // cover -- so a typo in a batch script inflated the very number the
    // evaluation reports.
    if (!opts.language_id.empty()
        && Lang::LanguageRegistry::instance().byId(opts.language_id) == nullptr) {
        std::vector<std::string> ids;
        for (const auto* l : Lang::LanguageRegistry::instance().all()) {
            ids.push_back(l->id());
        }
        diagnostics << "unknown language '" << opts.language_id << "'; known: "
                  << joined(ids) << '\n';
        return 2;
    }
    // Same reasoning for the profile, which exited 1 with E_PASS_PIPELINE --
    // the bucket for a pipeline that is genuinely misordered.
    if (!Uir::EncodingProfile::builtin(opts.profile_id)) {
        diagnostics << "unknown profile '" << opts.profile_id << "'; known: "
                  << joined(Uir::EncodingProfile::builtinIds()) << '\n';
        return 2;
    }

    if (unit.main_path == "-" && unit.inline_source.empty()) {
        // Detection is by file extension, and stdin has none.
        if (opts.language_id.empty()) {
            diagnostics << "reading from stdin needs --from: there is no file name to "
                         "detect the language from\n";
            return 2;
        }
        std::ostringstream in;
        char buffer[8192];
        // Read through istream so a failing caller-owned stream sets badbit.
        // Inserting its rdbuf into an ostream can report a read exception only
        // as failbit on the destination, indistinguishable from empty stdin.
        while (input.read(buffer, sizeof(buffer)) || input.gcount() != 0) {
            in.write(buffer, input.gcount());
        }
        if (input.bad() || (input.fail() && !input.eof()) || !in) {
            diagnostics << "error: cannot read stdin\n";
            return 3;
        }
        unit.inline_source = in.str();
        unit.display_name = "<stdin>";
        // An empty stdin must still reach the frontend, which reports it as the
        // empty model it is. inline_source is only consulted when non-empty, so
        // clearing main_path here would send the frontend to open the file "-".
        if (unit.inline_source.empty()) {
            diagnostics << "error: E_IO: stdin is empty\n";
            return 1;
        }
    }

    if (module_mode) {
        if (options.profile || options.dialect) {
            diagnostics << "--module cannot be combined with --profile or --dialect\n";
            return 2;
        }
        const auto imported = Lang::importModule(unit, opts.language_id, opts.parse);
        for (const auto& d : imported.diagnostics.all()) {
            diagnostics << severityName(d.severity) << ": " << Uir::errorCodeName(d.code)
                      << ": " << d.message << '\n';
        }
        if (!imported.ok()) { return 1; }
        const auto exported = Lang::exportModule(*imported.module);
        for (const auto& d : exported.diagnostics.all()) {
            diagnostics << severityName(d.severity) << ": " << Uir::errorCodeName(d.code)
                      << ": " << d.message << '\n';
        }
        if (!exported.ok()) { return 1; }
        if (!report_path.empty()) {
            std::ofstream report(report_path);
            report << exported.interface_json << '\n';
            report.close();
            if (!report) { diagnostics << "cannot write module interface\n"; return 3; }
        }
        output << exported.smt2;
        output.flush();
        if (!output) {
            diagnostics << "error: cannot write SMT-LIB output\n";
            return 3;
        }
        return 0;
    }

    const Translation t = translate(unit, opts);

    // Diagnostics go to stderr so stdout stays a clean SMT-LIB stream that can
    // be piped straight into a solver.
    for (const auto& d : t.diagnostics().all()) {
        diagnostics << severityName(d.severity) << ": ";
        if (!d.loc.file.empty()) {
            diagnostics << d.loc.file << ':' << d.loc.line << ':' << d.loc.column << ": ";
        }
        diagnostics << Uir::errorCodeName(d.code) << ": " << d.message << '\n';
    }

    if (!report_path.empty()) {
        std::ofstream out(report_path);
        if (!out) {
            // A failure here is the CLI's own environment (bad path, no
            // permission, disk full), not the input's translatability -- the
            // translation above may well have succeeded. Exit code 1 is
            // reserved for "this benchmark could not be translated" (data);
            // conflating this with it would fabricate a translation failure
            // for a benchmark that actually translated fine.
            diagnostics << "error: cannot write report to '" << report_path << "'\n";
            return 3;
        }
        out << t.report().toJson() << '\n';
        out.close();
        if (!out) {
            diagnostics << "error: cannot write report to '" << report_path << "'\n";
            return 3;
        }
    }

    // Includes E_IO diagnostics raised while reading the input itself (e.g.
    // an unopenable main_path): that failure happened inside translate(),
    // is recorded in t.diagnostics()/t.report() like any other translation
    // outcome, and answers "was this benchmark translatable" (no) rather
    // than "did the CLI's own I/O fail after translation already
    // succeeded" (exit 3, above) -- the two are not the same question, so
    // they keep different exit codes.
    if (!t.ok()) {
        return 1;
    }
    // Write directly to the consumer without a second, complete script in
    // memory. Distinguish output failure from an internal export invariant,
    // preserving the documented I/O (3) and translation (1) exit codes.
    try {
        t.writeSmt2(output, opts.omt_dialect);
        output.flush();
        if (!output) {
            diagnostics << "error: cannot write SMT-LIB output\n";
            return 3;
        }
    } catch (const std::bad_alloc&) {
        if (!output) {
            diagnostics << "error: cannot write SMT-LIB output\n";
            return 3;
        }
        diagnostics << "error: E_RESOURCE: memory allocation failed during SMT-LIB output\n";
        return 1;
    } catch (const std::exception& e) {
        if (!output) {
            diagnostics << "error: cannot write SMT-LIB output\n";
            return 3;
        }
        diagnostics << "error: E_INTERNAL: " << e.what() << '\n';
        return 1;
    }
    return 0;
}

ConvertResult convert(const Lang::SourceUnit& source, const ConvertOptions& options) {
    std::ostringstream output, diagnostics;
    ConvertResult result;
    result.exit_code = convert(source, options, std::cin, output, diagnostics);
    result.smt2 = output.str();
    result.diagnostics = diagnostics.str();
    return result;
}

} // namespace SOMTParser
