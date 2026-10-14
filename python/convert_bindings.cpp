#include "convert_bindings.h"
#include <pybind11/stl.h>

#include "somtparser/translation/convert.h"
#include "somtparser/lowering/omt_emitter.h"

#include <array>
#include <memory>
#include <sstream>
#include <streambuf>

namespace py = pybind11;

namespace {

// Per-call streams: never redirect process-wide cout/cerr or assemble a full
// script when the caller supplies an output sink. Decode incrementally because
// a UTF-8 character may cross a buffer boundary.
class PythonOutputBuffer : public std::streambuf {
public:
    explicit PythonOutputBuffer(const py::object& stream)
        : write_(stream.attr("write")), flush_(stream.attr("flush")),
          decoder_(py::module_::import("codecs").attr("getincrementaldecoder")("utf-8")()) {
        setp(buffer_.data(), buffer_.data() + buffer_.size());
    }

protected:
    int sync() override {
        if (failed_) { return -1; }
        try {
            const auto size = pptr() - pbase();
            const py::object text = decoder_.attr("decode")(py::bytes(pbase(), size));
            setp(buffer_.data(), buffer_.data() + buffer_.size());
            if (py::len(text)) {
                const py::object written = write_(text);
                if (!written.is_none() && written.cast<py::ssize_t>()
                        != static_cast<py::ssize_t>(py::len(text))) {
                    failed_ = true;
                    return -1;
                }
            }
            flush_();
            return 0;
        } catch (const py::error_already_set&) {
            failed_ = true;
            return -1;
        }
    }

    int_type overflow(int_type ch) override {
        if (sync() != 0) { return traits_type::eof(); }
        if (!traits_type::eq_int_type(ch, traits_type::eof())) {
            *pptr() = traits_type::to_char_type(ch);
            pbump(1);
        }
        return traits_type::not_eof(ch);
    }

private:
    std::array<char, 8192> buffer_;
    py::object write_, flush_, decoder_;
    bool failed_ = false;
};

class PythonInputBuffer : public std::streambuf {
public:
    explicit PythonInputBuffer(py::object stream) : stream_(std::move(stream)) {}

protected:
    int_type underflow() override {
        if (gptr() && gptr() < egptr()) { return traits_type::to_int_type(*gptr()); }
        buffer_ = stream_.attr("read")(8192).cast<std::string>();
        if (buffer_.empty()) { return traits_type::eof(); }
        setg(buffer_.data(), buffer_.data(), buffer_.data() + buffer_.size());
        return traits_type::to_int_type(*gptr());
    }

private:
    py::object stream_;
    std::string buffer_;
};

std::optional<std::string> dialectName(const py::object& dialect) {
    if (dialect.is_none()) { return std::nullopt; }
    if (py::isinstance<py::str>(dialect)) { return dialect.cast<std::string>(); }
    if (!py::isinstance<SOMTParser::Lower::OmtDialect>(dialect)) {
        throw py::type_error("dialect must be a string, OmtDialect, or None");
    }
    switch (dialect.cast<SOMTParser::Lower::OmtDialect>()) {
    case SOMTParser::Lower::OmtDialect::Gomt: return "gomt";
    case SOMTParser::Lower::OmtDialect::Z3: return "z3";
    case SOMTParser::Lower::OmtDialect::OptiMathSAT: return "optimathsat";
    case SOMTParser::Lower::OmtDialect::None: return "none";
    }
    throw py::value_error("unknown OmtDialect");
}

} // namespace

namespace SomtPythonConvert {

void bind(py::module_& m) {
    using namespace SOMTParser;
    py::class_<ConvertResult>(m, "ConvertResult")
        .def_readonly("exit_code", &ConvertResult::exit_code)
        .def_readonly("smt2", &ConvertResult::smt2)
        .def_readonly("diagnostics", &ConvertResult::diagnostics);

    m.def("convert", [](const std::string& path, const std::string& source,
                        const std::string& language, const std::optional<std::string>& profile,
                        const py::object& dialect, const std::vector<std::string>& data,
                        const Uir::ParamMap& options,
                        const std::string& report, bool module, py::object input,
                        const py::object& output, const py::object& diagnostics) {
        Lang::SourceUnit unit;
        unit.main_path = path;
        unit.inline_source = source;
        unit.data_paths = data;
        if (!path.empty()) { unit.display_name = path; }
        ConvertOptions opts;
        opts.language = language;
        opts.profile = profile;
        opts.dialect = dialectName(dialect);
        opts.parse.options = options;
        opts.report = report;
        opts.module = module;

        if (input.is_none()) { input = py::module_::import("sys").attr("stdin"); }
        PythonInputBuffer input_buffer(std::move(input));
        std::istream in(&input_buffer);
        std::ostringstream captured_output, captured_diagnostics;
        std::unique_ptr<PythonOutputBuffer> output_buffer, diagnostic_buffer;
        if (!output.is_none()) { output_buffer = std::make_unique<PythonOutputBuffer>(output); }
        if (!diagnostics.is_none()) {
            diagnostic_buffer = std::make_unique<PythonOutputBuffer>(diagnostics);
        }
        std::streambuf* out_buffer = captured_output.rdbuf();
        std::streambuf* err_buffer = captured_diagnostics.rdbuf();
        if (output_buffer) { out_buffer = output_buffer.get(); }
        if (diagnostic_buffer) { err_buffer = diagnostic_buffer.get(); }
        std::ostream out(out_buffer), err(err_buffer);
        ConvertResult result;
        result.exit_code = convert(unit, opts, in, out, err);
        err.flush();
        if (!err) { result.exit_code = 3; }
        result.smt2 = captured_output.str();
        result.diagnostics = captured_diagnostics.str();
        return result;
    }, py::arg("path") = "", py::kw_only(), py::arg("source") = "",
       py::arg("language") = "", py::arg("profile") = py::none(),
       py::arg("dialect") = py::none(), py::arg("data") = std::vector<std::string>{},
       py::arg("options") = Uir::ParamMap{},
       py::arg("report") = "", py::arg("module") = false,
       py::arg("stdin") = py::none(), py::arg("output") = py::none(),
       py::arg("diagnostics") = py::none(),
       "Convert a model; capture output by default or write to caller-owned text streams.");
}

} // namespace SomtPythonConvert
