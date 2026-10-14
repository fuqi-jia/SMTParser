#include "somtparser/translation/convert.h"
#include "test_helpers.h"

#include <sstream>
#include <stdexcept>
#include <streambuf>

using namespace SOMTParser;

namespace {
struct FailedWrite : std::streambuf {
    int_type overflow(int_type) override { return traits_type::eof(); }
};
struct FailedRead : std::streambuf {
    int_type underflow() override { throw std::runtime_error("read failed"); }
};
}

int main() {
    Lang::SourceUnit unit;
    unit.inline_source = "(declare-const x Int)(assert (>= x 2))(minimize x)(check-sat)";
    ConvertOptions opts;
    opts.language = "smtlib2";
    opts.dialect = "z3";
    const auto captured = convert(unit, opts);
    VERIFY(captured.exit_code == 0);
    VERIFY(captured.diagnostics.empty());
    VERIFY(captured.smt2.find("(minimize x)") != std::string::npos);
    VERIFY(captured.smt2.find("(check-sat)") != std::string::npos);

    std::istringstream input;
    std::ostringstream output, diagnostics;
    VERIFY(convert(unit, opts, input, output, diagnostics) == 0);
    VERIFY(output.str() == captured.smt2);
    VERIFY(diagnostics.str().empty());
    VERIFY(convert(unit, opts).smt2 == captured.smt2);

    FailedWrite failed_write;
    std::ostream bad_output(&failed_write);
    VERIFY(convert(unit, opts, input, bad_output, diagnostics) == 3);
    VERIFY(diagnostics.str() == "error: cannot write SMT-LIB output\n");

    opts.dialect = "invalid";
    const auto invalid = convert(unit, opts);
    VERIFY(invalid.exit_code == 2);
    VERIFY(invalid.smt2.empty());
    VERIFY(invalid.diagnostics == "unknown dialect 'invalid'\n");

    opts.dialect = "z3";
    unit.inline_source.clear();
    unit.main_path = "-";
    std::istringstream model("(assert true)(check-sat)");
    std::ostringstream stdin_output, stdin_diagnostics;
    VERIFY(convert(unit, opts, model, stdin_output, stdin_diagnostics) == 0);
    VERIFY(stdin_diagnostics.str().empty());
    VERIFY(stdin_output.str().find("(check-sat)") != std::string::npos);

    std::istringstream empty;
    VERIFY(convert(unit, opts, empty, stdin_output, stdin_diagnostics) == 1);
    VERIFY(stdin_diagnostics.str() == "error: E_IO: stdin is empty\n");
    FailedRead failed_read;
    std::istream bad_input(&failed_read);
    std::ostringstream read_diagnostics;
    VERIFY(convert(unit, opts, bad_input, stdin_output, read_diagnostics) == 3);
    VERIFY(read_diagnostics.str() == "error: cannot read stdin\n");

    unit.main_path.clear();
    unit.inline_source = "aag 0 0 0 0 0\n";
    opts = {};
    opts.language = "aiger";
    opts.module = true;
    const auto module = convert(unit, opts);
    VERIFY(module.exit_code == 0);
    VERIFY(module.smt2.find("; SOMT module interface ") == 0);
    VERIFY(module.smt2.find("(check-sat)") == std::string::npos);
    opts.profile = "default";
    const auto conflict = convert(unit, opts);
    VERIFY(conflict.exit_code == 2);
    VERIFY(conflict.smt2.empty());
    VERIFY(conflict.diagnostics == "--module cannot be combined with --profile or --dialect\n");
}
