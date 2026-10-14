/* -*- Source -*-
 * somt-convert: any supported constraint language to SMT/OMT.
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/register_all.h"
#include "somtparser/uir/translate.h"
#include "somtparser/uir/module.h"

#include <fstream>
#include <iostream>
#include <new>
#include <sstream>
#include <string>
#include <vector>

using namespace SOMTParser;

namespace {

int usage(const char* argv0, int code) {
    std::ostream& o = (code == 0) ? std::cout : std::cerr;
    o << "Usage: " << argv0 << " [options] FILE\n"
      << "  FILE               input file, or - to read the model from stdin\n"
      << "  --from ID          input language id (default: detect; required for -)\n"
      << "  --profile ID       encoding profile (default: default)\n"
      << "  --dialect NAME     gomt (alias: smtlib-omt-2025) | z3 | optimathsat | none\n"
      << "  --data FILE        companion data file, repeatable\n"
      << "  --opt KEY=VALUE    frontend option, repeatable (e.g. bmc_depth=10)\n"
      << "  --report FILE      write the TranslationReport as JSON\n"
      << "  --module           export a library/open model without check-sat; --report writes its interface\n"
      << "  --list-languages   list registered languages and exit\n"
      << "  --list-profiles    list built-in profiles and exit\n"
      << "  --                 end of options; everything after is a file name\n"
      << "Exit codes: 0 success, 1 translation failed, 2 usage error,\n"
      << "            3 I/O fault (e.g. --report path could not be written)\n";
    return code;
}

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

int main(int argc, char** argv) {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    TranslateOptions opts;
    Lang::SourceUnit unit;
    std::string report_path;

    bool options_ended = false;      // set by "--"
    bool module_mode = false, query_options = false;

    for (int i = 1; i < argc; ++i) {
        const std::string a = argv[i];
        auto needValue = [&](std::string& dst) {
            if (i + 1 >= argc) { std::cerr << a << " needs a value\n"; return false; }
            const std::string v = argv[i + 1];
            // "--from --profile x.mzn" used to set language_id to "--profile"
            // and then translate x.mzn under a language nobody asked for,
            // reporting the resulting failure as thin language coverage. A
            // value that is itself an option is always a typo; a file really
            // named "-x" is still reachable as "./-x" or after "--".
            if (v.size() > 1 && v[0] == '-') {
                std::cerr << a << " needs a value, but the next argument is the option '"
                          << v << "'\n";
                return false;
            }
            dst = v;
            ++i;
            return true;
        };
        if (options_ended) {
            if (!unit.main_path.empty()) {
                std::cerr << "more than one input file given\n";
                return 2;
            }
            unit.main_path = a;
            continue;
        }
        if (a == "--") { options_ended = true; continue; }
        if (a == "--module") { module_mode = true; continue; }
        if (a == "-h" || a == "--help") {
            return usage(argv[0], 0);
        }
        if (a == "--list-languages") {
            for (const auto* l : Lang::LanguageRegistry::instance().all()) {
                std::cout << l->id() << '\t' << l->displayName() << '\t'
                          << l->version() << '\n';
            }
            return 0;
        }
        if (a == "--list-profiles") {
            for (const auto& id : Uir::EncodingProfile::builtinIds()) {
                std::cout << id << '\n';
            }
            return 0;
        }
        if (a == "--from")    { if (!needValue(opts.language_id)) return 2; continue; }
        if (a == "--profile") { query_options = true; if (!needValue(opts.profile_id))  return 2; continue; }
        if (a == "--report")  { if (!needValue(report_path))      return 2; continue; }
        if (a == "--opt") {
            // A frontend option, as ParseOptions::options carries them. The
            // field existed and nothing could set it, so a language that needs
            // one -- BTOR2's unrolling depth, which deliberately has no default
            // -- could not be driven from the command line at all.
            std::string kv;
            if (!needValue(kv)) { return 2; }
            const std::size_t eq = kv.find('=');
            if (eq == std::string::npos || eq == 0) {
                std::cerr << "--opt takes KEY=VALUE, got '" << kv << "'\n";
                return 2;
            }
            opts.parse.options[kv.substr(0, eq)] = kv.substr(eq + 1);
            continue;
        }
        if (a == "--data") {
            std::string d;
            if (!needValue(d)) { return 2; }
            unit.data_paths.push_back(d);
            continue;
        }
        if (a == "--dialect") {
            query_options = true;
            std::string d;
            if (!needValue(d)) { return 2; }
            if (!parseDialect(d, opts.omt_dialect)) {
                std::cerr << "unknown dialect '" << d << "'\n";
                return 2;
            }
            continue;
        }
        // A bare "-" is the input, not an option: language.h documents
        // main_path == "-" as stdin.
        if (a.size() > 1 && a[0] == '-') {
            std::cerr << "unknown option '" << a << "'\n";
            return usage(argv[0], 2);
        }
        if (!unit.main_path.empty()) {
            std::cerr << "more than one input file given\n";
            return 2;
        }
        unit.main_path = a;
    }

    if (unit.main_path.empty()) {
        return usage(argv[0], 2);
    }
    unit.display_name = unit.main_path;

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
        std::cerr << "unknown language '" << opts.language_id << "'; known: "
                  << joined(ids) << '\n';
        return 2;
    }
    // Same reasoning for the profile, which exited 1 with E_PASS_PIPELINE --
    // the bucket for a pipeline that is genuinely misordered.
    if (!Uir::EncodingProfile::builtin(opts.profile_id)) {
        std::cerr << "unknown profile '" << opts.profile_id << "'; known: "
                  << joined(Uir::EncodingProfile::builtinIds()) << '\n';
        return 2;
    }

    if (unit.main_path == "-") {
        // Detection is by file extension, and stdin has none.
        if (opts.language_id.empty()) {
            std::cerr << "reading from stdin needs --from: there is no file name to "
                         "detect the language from\n";
            return 2;
        }
        std::ostringstream in;
        in << std::cin.rdbuf();
        if (std::cin.bad()) {
            std::cerr << "error: cannot read stdin\n";
            return 3;
        }
        unit.inline_source = in.str();
        unit.display_name = "<stdin>";
        // An empty stdin must still reach the frontend, which reports it as the
        // empty model it is. inline_source is only consulted when non-empty, so
        // clearing main_path here would send the frontend to open the file "-".
        if (unit.inline_source.empty()) {
            std::cerr << "error: E_IO: stdin is empty\n";
            return 1;
        }
    }

    if (module_mode) {
        if (query_options) {
            std::cerr << "--module cannot be combined with --profile or --dialect\n";
            return 2;
        }
        const auto imported = Lang::importModule(unit, opts.language_id, opts.parse);
        for (const auto& d : imported.diagnostics.all()) {
            std::cerr << severityName(d.severity) << ": " << Uir::errorCodeName(d.code)
                      << ": " << d.message << '\n';
        }
        if (!imported.ok()) { return 1; }
        const auto exported = Lang::exportModule(*imported.module);
        for (const auto& d : exported.diagnostics.all()) {
            std::cerr << severityName(d.severity) << ": " << Uir::errorCodeName(d.code)
                      << ": " << d.message << '\n';
        }
        if (!exported.ok()) { return 1; }
        if (!report_path.empty()) {
            std::ofstream report(report_path);
            report << exported.interface_json << '\n';
            report.close();
            if (!report) { std::cerr << "cannot write module interface\n"; return 3; }
        }
        std::cout << exported.smt2;
        std::cout.flush();
        if (!std::cout) {
            std::cerr << "error: cannot write SMT-LIB output\n";
            return 3;
        }
        return 0;
    }

    const Translation t = translate(unit, opts);

    // Diagnostics go to stderr so stdout stays a clean SMT-LIB stream that can
    // be piped straight into a solver.
    for (const auto& d : t.diagnostics().all()) {
        std::cerr << severityName(d.severity) << ": ";
        if (!d.loc.file.empty()) {
            std::cerr << d.loc.file << ':' << d.loc.line << ':' << d.loc.column << ": ";
        }
        std::cerr << Uir::errorCodeName(d.code) << ": " << d.message << '\n';
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
            std::cerr << "error: cannot write report to '" << report_path << "'\n";
            return 3;
        }
        out << t.report().toJson() << '\n';
        out.close();
        if (!out) {
            std::cerr << "error: cannot write report to '" << report_path << "'\n";
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
        t.writeSmt2(std::cout, opts.omt_dialect);
        std::cout.flush();
        if (!std::cout) {
            std::cerr << "error: cannot write SMT-LIB output\n";
            return 3;
        }
    } catch (const std::bad_alloc&) {
        if (!std::cout) {
            std::cerr << "error: cannot write SMT-LIB output\n";
            return 3;
        }
        std::cerr << "error: E_RESOURCE: memory allocation failed during SMT-LIB output\n";
        return 1;
    } catch (const std::exception& e) {
        if (!std::cout) {
            std::cerr << "error: cannot write SMT-LIB output\n";
            return 3;
        }
        std::cerr << "error: E_INTERNAL: " << e.what() << '\n';
        return 1;
    }
    return 0;
}
