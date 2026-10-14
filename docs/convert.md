# Conversion API

`somtparser.convert` converts a file or inline model, formats diagnostics,
optionally writes a JSON report, and emits SMT-LIB/OMT. The implementation lives
in the C++ language library; Python calls that implementation directly. No
converter executable is built or installed, and no converter console script
is registered by pip. `SOMTPARSER_BUILD_TOOLS` is not required.

```python
import somtparser as sp

result = sp.convert("model.mzn", language="minizinc", dialect="z3",
                    data=["instance.dzn"], report="report.json")
assert result.exit_code == 0, result.diagnostics
smt2 = result.smt2
```

The result is a `ConvertResult` with `exit_code: int`, `smt2: str`, and
`diagnostics: str`. Diagnostics retain their severity, source location when
available, error code and final newline. Conversion failures return a result;
the function does not terminate the calling process. Invalid Python argument
types still raise normal Python exceptions.

| Parameter | Meaning |
| --- | --- |
| `path` | Main input path; detected by extension unless `language` is set |
| `source` | Inline model text, taking precedence over file contents |
| `language` | Registered language ID; empty selects detection |
| `profile` | Encoding profile; `None` selects `default` |
| `dialect` | `gomt`, `smtlib-omt-2025`, `z3`, `optimathsat`, `none`, or an `OmtDialect`; `None` selects GOMT |
| `data` | Sequence of companion data paths |
| `options` | Mapping of frontend option names to string values |
| `report` | JSON destination path; empty disables report writing |
| `module` | Export a query-free library/open model; report becomes its interface |
| `stdin` | Input text stream for `path="-"`; defaults to `sys.stdin` |
| `output` | SMT output text stream; `None` captures `result.smt2` |
| `diagnostics` | Diagnostic text stream; `None` captures `result.diagnostics` |

Paths accept strings or `os.PathLike` objects. Streams are flushed and remain
owned by the caller. A streamed channel has an empty corresponding result
string, avoiding a second complete copy of a large SMT script. Capture is
silent: neither result channel is printed to process stdout/stderr.

```python
with open("model.smt2", "w", encoding="utf-8", newline="") as output:
    result = sp.convert("model.btor2", profile="bmc",
                        options={"bmc_depth": "10"}, dialect="z3",
                        output=output, report="report.json")
if result.exit_code:
    print(result.diagnostics)
```

For in-memory input, use `sp.convert(source=text, language="minizinc")`.
For stdin, use `sp.convert("-", language="minizinc", stdin=stream)`; an empty
stdin remains a translation failure. In module mode, leave `profile` and
`dialect` unset. Even an explicitly selected default profile/dialect is
incompatible with that mode.

## Status and experiment migration

| `exit_code` | Meaning |
| --- | --- |
| `0` | Conversion and requested output/report writing succeeded |
| `1` | Input could not be translated or exported, including input-file I/O diagnostics |
| `2` | Invalid conversion settings, such as unknown IDs or incompatible module settings |
| `3` | Input-stream, output-stream or report-destination I/O failure |

The former command-line settings map to named parameters:

| Former setting | API equivalent |
| --- | --- |
| Positional input file | `path` |
| `--from ID` | `language="ID"` |
| `--profile ID` | `profile="ID"` |
| `--dialect NAME` | `dialect="NAME"` |
| Repeated `--data FILE` | `data=[...]` |
| Repeated `--opt KEY=VALUE` | `options={"KEY": "VALUE"}`; the last value wins |
| `--report FILE` | `report="FILE"` |
| `--module` | `module=True` |
| `--list-languages`, `--list-profiles` | `sp.languages()`, `sp.profiles()` |

An experiment driver previously using `subprocess.run` should replace
`completed.returncode`, `completed.stdout` and `completed.stderr` with
`result.exit_code`, `result.smt2` and `result.diagnostics`. Corresponding
conversion settings retain the existing SMT bytes, diagnostic formatting,
report serialization and status classification. JSON reports still contain
measured timings, so timing values naturally differ between executions.
Legacy diagnostic strings that mention option spellings remain unchanged.
Command-line token errors and help text are replaced by the function's named
parameters and Python argument validation.

Conversion runs inside the caller's process. Drivers that require a separate
memory limit, a hard wall-clock timeout or per-instance process isolation
should call this function in their own worker process. Account for conversion
time separately from worker startup when comparing prior measurements.

Use `sp.translate` when the driver needs a `Translation`, structured
diagnostics, semantic metadata or re-emission into several dialects. `convert`
provides the completed conversion outcome and the former report/output policy;
it does not replace those inspection APIs.

## C++

```cpp
#include <somtparser/translation/convert.h>

SOMTParser::Lang::SourceUnit source;
source.main_path = "model.mzn";
SOMTParser::ConvertOptions options;
options.language = "minizinc";
options.dialect = "z3";
auto result = SOMTParser::convert(source, options);
// result.exit_code, result.smt2, result.diagnostics
```

Link `SOMTParser::languages`; built-in languages are registered by the function.
The overload `convert(source, options, input, output, diagnostics)` accepts
`std::istream`/`std::ostream` references and returns the integer status without
capturing a full script. The captured overload reads `std::cin` only when the
source requests stdin. Neither overload changes global output streams.
