"""SOMTParser: Python bindings for the SOMTParser SMT-LIB2 / OMT front-end library.

Parse SMT-LIB2 and OMT input into a typed DAG IR, build expressions
programmatically, convert formulas (NNF/CNF/DNF), parse solver models and
evaluate formulas under (partial) models.

Example:
    >>> import somtparser as sp
    >>> p = sp.parse("(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))")
    >>> len(p.assertions)
    1
    >>> m = p.parse_model("(model (define-fun x () Int 3))")
    >>> p.evaluate(p.assertions[0], m).value
    True
"""

import os
import sys

if sys.platform == "win32":
    _package_dir = os.path.dirname(os.path.abspath(__file__))
    _bin_dir = os.path.join(_package_dir, "bin")
    if os.path.isdir(_bin_dir):
        os.add_dll_directory(_bin_dir)
        os.environ["PATH"] = _bin_dir + os.pathsep + os.environ.get("PATH", "")

from ._somtparser import (
    __version__,
    CmdType,
    Command,
    MetaObjective,
    Model,
    Node,
    Objective,
    OptKind,
    ParseError,
    Parser,
    ResultType,
    Script,
    Sort,
    parse,
    parse_file,
)
from .construction_limits import ConstructionLimits, construction_limits, current_construction_limits

from ._somtparser import (
    AnnotationSemantics,
    ArithmeticSemantics,
    ArraySemantics,
    AssumptionProfile,
    Bound,
    CarrierEmptiness,
    CarrierSemantics,
    ConvertResult,
    DecisionKind,
    Diagnostic,
    DivisionSemantics,
    EncodingChoice,
    EqualitySemantics,
    ErrorCode,
    Fidelity,
    FunctionSemantics,
    Institution,
    OmtDialect,
    OverflowSemantics,
    PhaseSemantics,
    Provenance,
    QuantifierSemantics,
    Severity,
    SetSolverRequirements,
    SmtEmbeddingKind,
    SourceSemanticSpec,
    Stats,
    Translation,
    TranslationReport,
    ModuleImport,
    import_module,
    UndefinedSemantics,
    coverage,
    languages,
    profiles,
    source_semantics,
)
from ._somtparser import translate as _translate_raw
from ._somtparser import convert as _convert_raw


def convert(path="", *, source="", language="", profile=None, dialect=None,
            data=(), options=None, report="", module=False, stdin=None,
            output=None, diagnostics=None):
    """Convert a file or inline model to SMT/OMT and return a ConvertResult.

    The result contains exit_code (0 success, 1 translation failure, 2 invalid
    settings, 3 I/O failure), smt2 and formatted diagnostics. No process is
    spawned and conversion failures do not raise SystemExit.

    Pass caller-owned text streams as output/diagnostics to stream rather than
    capture that channel; its corresponding result string will then be empty.
    Streams are flushed, never closed. For byte-stable file output, open with
    encoding="utf-8", newline="". path="-" reads stdin (default sys.stdin) and
    requires language. source supplies an inline model without reading stdin.

    dialect accepts an OmtDialect or "gomt", "smtlib-omt-2025", "z3",
    "optimathsat", "none". Unset profile/dialect use "default"/"gomt".
    module=True exports a query-free module; explicitly selecting profile or
    dialect in that mode is an invalid setting. report writes the translation
    report, or the exported module's interface, as JSON with a final newline.
    """
    return _convert_raw(
        path=os.fspath(path), source=source, language=language, profile=profile,
        dialect=dialect, data=[os.fspath(p) for p in data],
        options=dict(options or {}), report=os.fspath(report), module=module,
        stdin=stdin, output=output, diagnostics=diagnostics,
    )


class TranslationError(RuntimeError):
    """Raised by translate(..., strict=True) when a translation fails.

    The C++ layer never throws across its API boundary, because one bad
    frontend must not end a batch of ten thousand benchmarks. Python callers
    expect exceptions though, so strict=True opts into them here.
    """

    def __init__(self, message, code, diagnostics):
        super().__init__(message)
        self.code = code
        self.diagnostics = diagnostics


def translate(path="", *, source="", data=(), language="", profile="default",
              dialect=OmtDialect.SmtLib2025, strict=False, options=None):
    """Translate any supported constraint language to SMT/OMT.

    `options` carries per-language parse options (a dict of strings), the same
    channel the CLI's `--opt` uses -- e.g. boogie's `chc=1` emits Horn clauses.
    """
    t = _translate_raw(path=path, source=source, data=list(data),
                       language=language, profile=profile, dialect=dialect,
                       options=dict(options or {}))
    if strict and not t.ok:
        diags = t.diagnostics
        # The first ERROR, not the first diagnostic. A frontend may emit notes
        # and warnings before the thing that actually stopped it -- Essence'
        # notes that it skipped a `branching` directive, then fails on a parse
        # gap several lines later -- and taking diags[0] reported the note's
        # code and text as the cause. That is not a cosmetic slip: it is the
        # code a corpus sweep buckets failures by, so it put genuine parse
        # gaps in the coverage column and made the failure-cause distribution
        # wrong for every file whose frontend says anything before it fails.
        errors = [d for d in diags if d.severity == Severity.ERROR]
        first = errors[0] if errors else (diags[0] if diags else None)
        message = first.message if first is not None else "translation failed"
        code = first.code if first is not None else ErrorCode.E_INTERNAL
        raise TranslationError(message, code, diags)
    return t


from .natural_language import CandidateSizeLimits


def propose_nl(source, *, provider=None, language="typed", context=None,
               required_outputs=None, size_limits=None):
    """Propose an interpretation in an explicit language configuration."""
    from .natural_language import propose_nl as propose
    return propose(source, provider=provider, language=language, context=context,
                   required_outputs=required_outputs, size_limits=size_limits)


def propose_nl_with_repair(source, *, provider, max_attempts=1, language="hir",
                           context=None, required_outputs=None, size_limits=None):
    """Retain each proposal and feed validation errors to an explicit provider."""
    from .natural_language import propose_nl_with_repair as propose
    return propose(source, provider=provider, max_attempts=max_attempts,
                   language=language, context=context,
                   required_outputs=required_outputs, size_limits=size_limits)


def compile_candidate(candidate, *, accept_digest="", profile="default", dialect=None):
    """Compile the exact selected candidate through the formal pipeline."""
    from .natural_language import compile_candidate as compile_selected
    return compile_selected(candidate, accept_digest=accept_digest, profile=profile, dialect=dialect)


def translate_nl(source, *, provider=None, accept_digest="", profile="default", dialect=None,
                 size_limits=None):
    """Translate controlled English/Chinese, or select a provider's candidate."""
    from .natural_language import translate_nl as translate_text
    return translate_text(source, provider=provider, accept_digest=accept_digest,
                          profile=profile, dialect=dialect, size_limits=size_limits)


from .hir import HirBuilder, hir_api, hir_schema

from ._backends import BackendNotFound, backend_path
from ._solving import FidelityError, Formula, Result
from ._solving import profile, seed


_UNSET = object()


def read(path="", *, source="", data=(), language="", profile=None,
         options=None, seed=_UNSET):
    """Translate a model and return a Formula.

    The PyTorch-shaped entry point. `sp.translate()` still exists and is
    unchanged; this wraps it so `.to(...).solve()` has something to hang on.

    Consults the scoped defaults set by `sp.profile(...)` when the caller
    does not name a profile explicitly, and carries the seed set by
    `sp.seed(...)` onto the returned `Formula`.

    `options` and `seed` override those scoped defaults rather than reading
    them. They exist because `sweep` must resolve the ambient scope once, at
    the call, and then apply that same resolution to every file it reads --
    see its docstring for why reading the scope per file would be wrong.
    `seed=None` is a real value (it clears the seed), which is why the default
    is a sentinel and not `None`.
    """
    from ._solving import _default
    chosen = profile if profile is not None else (_default("profile") or "default")
    t = translate(path, source=source, data=list(data), language=language,
                  profile=chosen,
                  options=_default("options", {}) if options is None else options,
                  strict=True)
    return Formula(t, language or "auto",
                   seed=_default("seed") if seed is _UNSET else seed)


def sweep(pattern, *, language="", profile=None):
    """A Formula per file matching @p pattern.

    A file that fails to translate is yielded with `.error` set rather than
    raised: a sweep over a corpus that stopped at the first refusal would
    measure nothing, and a refusal is a result.

    The scoped defaults and the glob are resolved HERE, when `sweep` is
    called, and not when the result is first iterated. That is the reason this
    is a plain function returning a generator rather than a generator function
    itself. Written the obvious way, the body would not run until iteration,
    so

        with sp.profile("bv32"):
            results = sp.sweep("corpus/*")     # nothing has run yet
        for f in results:                      # ...and it runs HERE

    would read every file under `default`, silently answering a different
    question from the one the block asks for. Nothing would be mislabelled --
    the provenance would honestly say `default` -- which is precisely why it
    would be hard to notice.
    """
    import glob
    from ._solving import _default

    # Resolved to a concrete string, not to `None`: `read` treats `None` as
    # "not given" and falls back to the thread-local, which would put the
    # lookup back at iteration time for exactly the mirror case -- a sweep
    # created OUTSIDE any block and iterated inside one. `options` and `seed`
    # are already concrete for the same reason.
    resolved_profile = (profile if profile is not None
                        else (_default("profile") or "default"))
    resolved_options = dict(_default("options", {}))
    resolved_seed = _default("seed")
    paths = sorted(glob.glob(pattern))
    return _sweep(paths, language, resolved_profile, resolved_options,
                  resolved_seed)


def _sweep(paths, language, profile, options, seed):
    for path in paths:
        try:
            yield read(path, language=language, profile=profile,
                       options=options, seed=seed)
        except TranslationError as error:
            yield Formula(None, language or "auto", seed=seed, error=error)


__all__ = [
    "AnnotationSemantics",
    "ArithmeticSemantics",
    "ArraySemantics",
    "AssumptionProfile",
    "BackendNotFound",
    "Bound",
    "CarrierEmptiness",
    "CarrierSemantics",
    "CmdType",
    "ConstructionLimits",
    "ConvertResult",
    "CandidateSizeLimits",
    "Command",
    "DecisionKind",
    "Diagnostic",
    "DivisionSemantics",
    "EncodingChoice",
    "EqualitySemantics",
    "ErrorCode",
    "Fidelity",
    "FidelityError",
    "Formula",
    "FunctionSemantics",
    "Institution",
    "MetaObjective",
    "Model",
    "ModuleImport",
    "import_module",
    "Node",
    "Objective",
    "OmtDialect",
    "OptKind",
    "OverflowSemantics",
    "ParseError",
    "Parser",
    "PhaseSemantics",
    "Provenance",
    "QuantifierSemantics",
    "Result",
    "ResultType",
    "Script",
    "Severity",
    "SmtEmbeddingKind",
    "Sort",
    "SourceSemanticSpec",
    "Stats",
    "SetSolverRequirements",
    "Translation",
    "TranslationError",
    "TranslationReport",
    "UndefinedSemantics",
    "backend_path",
    "coverage",
    "convert",
    "languages",
    "parse",
    "parse_file",
    "profile",
    "profiles",
    "read",
    "seed",
    "source_semantics",
    "sweep",
    "translate",
    "construction_limits",
    "current_construction_limits",
    "propose_nl",
    "propose_nl_with_repair",
    "compile_candidate",
    "translate_nl",
    "HirBuilder",
    "hir_api",
    "hir_schema",
    "__version__",
]
