/* -*- Header -*-
 *
 * translate() — the single entry point: any supported language to SMT/OMT.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_UIR_TRANSLATE_HEADER
#define SOMTPARSER_UIR_TRANSLATE_HEADER

#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/lowering/omt_emitter.h"
#include "somtparser/uir/language.h"
#include "somtparser/uir/pass.h"
#include "somtparser/uir/report.h"
#include "somtparser/uir/typecheck.h"

#include <cstdint>
#include <memory>
#include <iosfwd>
#include <stdexcept>
#include <string>

namespace SOMTParser {

struct TranslateOptions {
    std::string        language_id;                              // empty = auto-detect
    std::string        profile_id = "default";
    Lower::OmtDialect  omt_dialect = Lower::OmtDialect::SmtLib2025;
    std::uint32_t      timeout_ms = 0;                           // 0 = no limit
    /**
     * Passed through to Lang::Language::parse.
     *
     * It had no channel: ParseOptions::strict existed on the frontend interface
     * and translate() constructed a default one, so the option was declared and
     * unreachable from the public entry point -- the same shape as an operator
     * with no producer. `strict` is where a caller chooses to refuse a file
     * whose header disagrees with its content rather than trust the content and
     * warn (docs/languages/dimacs-cnf.md §4.2).
     */
    Lang::ParseOptions parse;
};

class Translation {
public:
    bool ok() const noexcept { return ok_; }
    /** Whether a materialized parser tree is available. Packed models
     *  are streamed directly to SMT-LIB to avoid per-symbol/per-clause expansion. */
    bool hasParser() const noexcept { return static_cast<bool>(parser_); }
    /** Materialized parser tree. Throws std::logic_error when a successful
     *  translation uses the packed streaming backend. Failed translations keep
     *  the existing null result; check ok() and hasParser() before requesting. */
    ParserPtr parser() const {
        if (packed_smt_) {
            throw std::logic_error("Translation uses packed SMT streaming and has no materialized Parser; use writeSmt2() or toSmt2()");
        }
        return parser_;
    }
    bool usesPackedSmtStream() const noexcept { return packed_smt_; }
    const Uir::TranslationReport& report() const noexcept { return report_; }
    const Uir::Diagnostics& diagnostics() const noexcept { return diagnostics_; }
    const Uir::Sem::TranslationPipeline& semantics() const noexcept {
        return semantics_;
    }
    Uir::Hir::SetSolverRequirements setSolverRequirements() const noexcept {
        return set_solver_requirements_;
    }

    /** SMT body plus objectives in the dialect chosen at translate() time. */
    std::string toSmt2() const;
    /** Re-emit in another dialect without re-translating. */
    std::string toSmt2(Lower::OmtDialect dialect) const;
    /** Replay into SOMTParser with native theories and minimize/maximize
     *  commands. This internal interchange format is not a Z3 export. */
    std::string toParserSmt2() const;
    /** Emit directly to a stream without assembling a complete script string. */
    void writeSmt2(std::ostream& out, Lower::OmtDialect dialect) const;
    /** Write a complete script to a file, reporting open/write failures. */
    void writeSmt2(const std::string& path,
                   Lower::OmtDialect dialect = Lower::OmtDialect::SmtLib2025) const;

    /** Number of effective objectives: distinct soft groups (including the
     *  unnamed packed-clause group), followed by explicit arithmetic objectives.
     *  The count survives consuming lowering and packed streaming. */
    std::size_t objectiveCount() const noexcept;

private:
    void validateForSmt2() const;
    std::string objectiveCommands(Lower::OmtDialect dialect,
                                  std::vector<std::string>* objective_names,
                                  std::string* preamble) const;
    void writeSmt2Body(std::ostream& out, const std::string& objectives,
                      Lower::OmtDialect dialect,
                      const std::vector<std::string>& objective_names,
                      const std::string& preamble) const;

    friend Translation translateImpl(const Lang::SourceUnit&, const TranslateOptions&,
                                     Uir::Hir::ConstraintModelPtr,
                                     const std::vector<Uir::Hir::LocatedExpr>&);

    bool                                 ok_ = false;
    ParserPtr                            parser_;
    Uir::Hir::ConstraintModelPtr                   model_;
    std::shared_ptr<Lower::HirToParser>  lowered_;
    Uir::TranslationReport               report_;
    Uir::Sem::TranslationPipeline        semantics_;
    Uir::Hir::SetSolverRequirements       set_solver_requirements_;
    Uir::Diagnostics                     diagnostics_;
    Lower::OmtDialect                    dialect_ = Lower::OmtDialect::SmtLib2025;
    bool packed_smt_ = false;
    // Preserve counts before consuming lowering releases constraint metadata.
    std::size_t soft_objective_count_ = 0;
    std::size_t objective_count_ = 0;
    std::vector<std::string> terminal_responses_;
    // Only the ordinary declaration/bound/objective part of a packed numeric
    // model is materialized. It must never be exposed as the complete parser.
    ParserPtr packed_base_parser_;
    std::vector<std::string> packed_linear_symbols_;
};

Translation translate(const Lang::SourceUnit& unit, const TranslateOptions& opts = {});

/** Translate a typed HIR snapshot through the same checked pass pipeline.
 *  Copies the mutable container; immutable expressions may safely be shared.
 *  The contract starts at HIR and makes no natural-language intent claim. */
Translation translateHir(const Uir::Hir::ConstraintModel& model,
                         const TranslateOptions& opts = {});

/** Additionally validate source terms erased during construction. These terms
 *  are checked in the initial model check, never asserted, passed through
 *  lowering, or added to the semantic signature. Each term must be closed over
 *  its lexical binders (ordinary model identifiers remain free). The caller
 *  retains immutable terms for this synchronous call only. */
Translation translateHir(const Uir::Hir::ConstraintModel& model,
                         const TranslateOptions& opts,
                         const std::vector<Uir::Hir::LocatedExpr>& source_terms);

} // namespace SOMTParser

#endif /* SOMTPARSER_UIR_TRANSLATE_HEADER */
