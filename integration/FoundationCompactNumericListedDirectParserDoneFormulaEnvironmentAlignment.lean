import integration.FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate

open LO FirstOrder LO.FirstOrder.Arithmetic
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler

namespace FoundationCompactNumericListedDirectParserDoneFormulaEnvironmentAlignment

theorem compactUnifiedParserDoneClosedFormula_environment_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates) :
    compactUnifiedParserDoneClosedFormula tokenTable width tokenCount current
        next witness =
      (Rew.subst (fun coordinate =>
        FoundationCompactPABinaryNumeralAddition.shortBinaryNumeralTerm
          (compactUnifiedParserDoneFormulaEnvironmentOf tokenTable width
            tokenCount current next witness coordinate))) ▹
        (Rewriting.emb (ξ := Nat)
          compactUnifiedParserDoneGraphRowsDef.val) := by
  unfold compactUnifiedParserDoneClosedFormula
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [compactUnifiedParserDoneFormulaEnvironmentOf,
      compactUnifiedParserDoneFormulaEnvironment]

theorem compactUnifiedParserDoneClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates) :
    (compactUnifiedParserDoneClosedFormula tokenTable width tokenCount current
      next witness).freeVariables = ∅ := by
  unfold compactUnifiedParserDoneClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

end FoundationCompactNumericListedDirectParserDoneFormulaEnvironmentAlignment
