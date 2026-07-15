import integration.FoundationCompactNumericListedDirectVerifierClosedLeafRuleRows

/-!
# Converse construction for the closed leaf rule

The formula-negation trace and its typed canonical rows determine the direct
closed-rule result.  No rule-check proposition or result bit is supplied as
an input to the constructor.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierClosedLeafRuleRowsCompleteness

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
open FoundationCompactNumericListedDirectClosedRuleCheck
open FoundationCompactNumericListedDirectVerifierClosedLeafRuleRows

theorem CompactNumericVerifierClosedLeafRuleRows.of_components
    {tokenTable width tokenCount gammaBoundary
      formulaStart formulaFinish formulaBoundary
      negatedStart negatedFinish negatedBoundary
      stateBoundary stateCount emptyStart emptyFinish emptyBoundary
      tableWidth valueBound : Nat}
    {Gamma : List (List Nat)} {formula negated : List Nat}
    (htransform : CompactFormulaTransformTotalExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount 3
      emptyStart emptyFinish 0
      formulaBoundary formula.length negatedBoundary negated.length
      emptyBoundary 0 tableWidth valueBound)
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hformula : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount formulaStart formulaFinish formula)
    (hformulaRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        formulaBoundary formula)
    (hnegated : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount negatedStart negatedFinish negated)
    (hnegatedRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        negatedBoundary negated)
    (hempty : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount emptyStart emptyFinish [])
    (hemptyRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptyBoundary [])
    (hparsed : ∃ parsed : LO.FirstOrder.ArithmeticSemiformula Nat 0,
      formula = FoundationCompactSyntaxTokenMachine.compactArithmeticFormulaTokens
        parsed) :
    CompactNumericVerifierClosedLeafRuleRows
      tokenTable width tokenCount 0 0
      gammaBoundary Gamma.length
      formulaStart formulaFinish formulaBoundary formula.length
      negatedStart negatedFinish negatedBoundary negated.length
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary
      tableWidth valueBound
      (compactAdditiveBoolTag (compactClosedRuleCheck (Gamma, formula))) := by
  refine ⟨rfl, rfl, ?_⟩
  exact (compactAdditiveClosedRuleCheck_iff
    htransform hGamma hformula hformulaRows hnegated hnegatedRows
    hempty hemptyRows hparsed).mpr rfl

theorem compactNumericVerifierClosedLeafRuleRows_iff_of_components
    {tokenTable width tokenCount proofTag certificateTag gammaBoundary
      formulaStart formulaFinish formulaBoundary
      negatedStart negatedFinish negatedBoundary
      stateBoundary stateCount emptyStart emptyFinish emptyBoundary
      tableWidth valueBound resultBool : Nat}
    {Gamma : List (List Nat)} {formula negated : List Nat}
    (htransform : CompactFormulaTransformTotalExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount 3
      emptyStart emptyFinish 0
      formulaBoundary formula.length negatedBoundary negated.length
      emptyBoundary 0 tableWidth valueBound)
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hformula : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount formulaStart formulaFinish formula)
    (hformulaRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        formulaBoundary formula)
    (hnegated : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount negatedStart negatedFinish negated)
    (hnegatedRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        negatedBoundary negated)
    (hempty : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount emptyStart emptyFinish [])
    (hemptyRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptyBoundary [])
    (hparsed : ∃ parsed : LO.FirstOrder.ArithmeticSemiformula Nat 0,
      formula = FoundationCompactSyntaxTokenMachine.compactArithmeticFormulaTokens
        parsed) :
    CompactNumericVerifierClosedLeafRuleRows
        tokenTable width tokenCount proofTag certificateTag
        gammaBoundary Gamma.length
        formulaStart formulaFinish formulaBoundary formula.length
        negatedStart negatedFinish negatedBoundary negated.length
        stateBoundary stateCount
        emptyStart emptyFinish emptyBoundary
        tableWidth valueBound resultBool ↔
      proofTag = 0 ∧ certificateTag = 0 ∧
        resultBool = compactAdditiveBoolTag
          (compactClosedRuleCheck (Gamma, formula)) := by
  constructor
  · rintro ⟨hproofTag, hcertificateTag, hcheck⟩
    exact ⟨hproofTag, hcertificateTag,
      (compactAdditiveClosedRuleCheck_iff
        htransform hGamma hformula hformulaRows hnegated hnegatedRows
        hempty hemptyRows hparsed).mp hcheck⟩
  · rintro ⟨hproofTag, hcertificateTag, hresult⟩
    exact ⟨hproofTag, hcertificateTag,
      (compactAdditiveClosedRuleCheck_iff
        htransform hGamma hformula hformulaRows hnegated hnegatedRows
        hempty hemptyRows hparsed).mpr hresult⟩

#print axioms CompactNumericVerifierClosedLeafRuleRows.of_components
#print axioms compactNumericVerifierClosedLeafRuleRows_iff_of_components

end FoundationCompactNumericListedDirectVerifierClosedLeafRuleRowsCompleteness
