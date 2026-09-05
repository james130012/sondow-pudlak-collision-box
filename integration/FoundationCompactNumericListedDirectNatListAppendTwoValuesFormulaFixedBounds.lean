import integration.FoundationCompactNumericListedDirectNatListAppendTwoValuesFormulaCodeFixedBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Closed formula for appending two exact values -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 60000

namespace FoundationCompactNumericListedDirectNatListAppendTwoValuesFormulaFixedBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListAppendTwoValues
open FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate

theorem
    compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula_closed
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount : Nat)
    (firstTerm secondTerm : ValuationTerm)
    (hfirstClosed : firstTerm.freeVariables = ∅)
    (hsecondClosed : secondTerm.freeVariables = ∅) :
    (compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
      tokenTable width tokenCount sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount firstTerm
      secondTerm).freeVariables = ∅ := by
  let terms := appendTwoAtValuationValuesTerms tokenTable width tokenCount
    sourceStart sourceFinish sourceCount targetStart targetFinish targetBoundary
    targetCount firstTerm secondTerm
  have hterms : forall coordinate, (terms coordinate).freeVariables = ∅ := by
    intro coordinate
    fin_cases coordinate
    · simpa [terms, appendTwoAtValuationValuesTerms] using
        shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
    · simpa [terms, appendTwoAtValuationValuesTerms] using
        shortBinaryNumeralTerm_freeVariables_eq_empty width
    · simpa [terms, appendTwoAtValuationValuesTerms] using
        shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
    · simpa [terms, appendTwoAtValuationValuesTerms] using
        shortBinaryNumeralTerm_freeVariables_eq_empty sourceStart
    · simpa [terms, appendTwoAtValuationValuesTerms] using
        shortBinaryNumeralTerm_freeVariables_eq_empty sourceFinish
    · simpa [terms, appendTwoAtValuationValuesTerms] using
        shortBinaryNumeralTerm_freeVariables_eq_empty sourceCount
    · simpa [terms, appendTwoAtValuationValuesTerms] using
        shortBinaryNumeralTerm_freeVariables_eq_empty targetStart
    · simpa [terms, appendTwoAtValuationValuesTerms] using
        shortBinaryNumeralTerm_freeVariables_eq_empty targetFinish
    · simpa [terms, appendTwoAtValuationValuesTerms] using
        shortBinaryNumeralTerm_freeVariables_eq_empty targetBoundary
    · simpa [terms, appendTwoAtValuationValuesTerms] using
        shortBinaryNumeralTerm_freeVariables_eq_empty targetCount
    · simpa [terms, appendTwoAtValuationValuesTerms] using hfirstClosed
    · simpa [terms, appendTwoAtValuationValuesTerms] using hsecondClosed
  unfold compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
  change
    ((Rewriting.emb (ξ := Nat)
      compactAdditiveNatListAppendTwoValuesDef.val) ⇜ terms).freeVariables = ∅
  exact embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
    _ terms hterms

#print axioms
  compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula_closed

end FoundationCompactNumericListedDirectNatListAppendTwoValuesFormulaFixedBounds
