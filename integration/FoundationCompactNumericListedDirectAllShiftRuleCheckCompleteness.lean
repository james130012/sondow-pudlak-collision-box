import integration.FoundationCompactNumericListedDirectAllShiftRuleCheck

/-!
# Converse constructors for universal and shift rule checks

The checked transform graphs and typed semantic outputs determine the public
Boolean result.  These constructors expose the reverse direction used by the
successful combine-row completeness proof.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectAllShiftRuleCheckCompleteness

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericFormulaConstructors
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectFormulaShiftExactListRows
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
open FoundationCompactNumericListedDirectFormulaConstructorMembership
open FoundationCompactNumericListedDirectFormulaSetEqCons
open FoundationCompactNumericListedDirectFormulaSetChecks
open FoundationCompactNumericListedDirectAllShiftRuleCheck

theorem CompactAdditiveAllRuleCheck.of_semantics
    {tokenTable width tokenCount gammaBoundary
      formulaStart formulaFinish formulaBoundary
      premiseBoundary premiseBoolValue
      freedStart freedFinish freedBoundary
      freeStateBoundary shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound : Nat}
    {Gamma premise : List (List Nat)} {formula : List Nat}
    {premiseValid : Bool}
    (hfree : CompactFormulaTransformTotalExactBoundedGraph
      tokenTable width tokenCount freeStateBoundary
        (compactSyntaxRunFuelBound formula + 1) 0
      emptyStart emptyFinish 0
      formulaBoundary formula.length
      freedBoundary ((compactFormulaFreeExact formula).getD []).length
      emptyBoundary 1 freeTableWidth freeValueBound)
    (hshift : CompactFormulaShiftExactListRows
      tokenTable width tokenCount
      gammaBoundary Gamma.length shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary ((compactFormulaShiftExactList Gamma).getD []).length
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound)
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hformula : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount formulaStart formulaFinish formula)
    (hpremise : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        premiseBoundary premise)
    (hfreed : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount freedStart freedFinish
        ((compactFormulaFreeExact formula).getD []))
    (hshifted : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        shiftedBoundary ((compactFormulaShiftExactList Gamma).getD []))
    (hpremiseBool : premiseBoolValue =
      compactAdditiveBoolTag premiseValid) :
    CompactAdditiveAllRuleCheck
      tokenTable width tokenCount
      gammaBoundary Gamma.length
      formulaStart formulaFinish formulaBoundary formula.length
      premiseBoundary premise.length premiseBoolValue
      freedStart freedFinish freedBoundary
        ((compactFormulaFreeExact formula).getD []).length
      freeStateBoundary (compactSyntaxRunFuelBound formula + 1)
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary ((compactFormulaShiftExactList Gamma).getD []).length
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      (compactAdditiveBoolTag
        (compactAllRuleCheck
          (Gamma, (formula, (premise, premiseValid))))) := by
  have hshiftedWellFormed : CompactAdditiveNatListListRowsWellFormed
      tokenTable width tokenCount shiftedBoundary
        ((compactFormulaShiftExactList Gamma).getD []).length :=
    CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
      hshifted
  refine ⟨hfree, hshift, hshiftedWellFormed, ?_, ?_⟩
  · cases hresult : compactAllRuleCheck
        (Gamma, (formula, (premise, premiseValid))) <;>
      simp [compactAdditiveBoolTag]
  · have hmember := compactAdditiveFormulaAllMemberRows_iff hGamma hformula
    have hsetEq := compactAdditiveFormulaSetEqConsRows_iff_tokenCheck
      hpremise hfreed hshifted
    rw [hmember, hsetEq, hpremiseBool]
    cases hmemberValue : tokenFormulaMem
        (tokenFormulaAll formula) Gamma <;>
      cases hsetEqValue : tokenFormulaSetEq premise
        ((compactFormulaFreeExact formula).getD [] ::
          (compactFormulaShiftExactList Gamma).getD []) <;>
      cases premiseValid <;>
      simp [compactAllRuleCheck, compactAdditiveBoolTag,
        hmemberValue, hsetEqValue]

theorem CompactAdditiveShiftRuleCheck.of_semantics
    {tokenTable width tokenCount gammaBoundary premiseBoundary
      premiseBoolValue shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound : Nat}
    {Gamma premise : List (List Nat)} {premiseValid : Bool}
    (hshift : CompactFormulaShiftExactListRows
      tokenTable width tokenCount
      premiseBoundary premise.length shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary ((compactFormulaShiftExactList premise).getD []).length
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound)
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hshifted : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        shiftedBoundary ((compactFormulaShiftExactList premise).getD []))
    (hpremiseBool : premiseBoolValue =
      compactAdditiveBoolTag premiseValid) :
    CompactAdditiveShiftRuleCheck
      tokenTable width tokenCount
      gammaBoundary Gamma.length
      premiseBoundary premise.length premiseBoolValue
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary ((compactFormulaShiftExactList premise).getD []).length
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound
      (compactAdditiveBoolTag
        (compactShiftRuleCheck (Gamma, (premise, premiseValid)))) := by
  have hshiftedWellFormed : CompactAdditiveNatListListRowsWellFormed
      tokenTable width tokenCount shiftedBoundary
        ((compactFormulaShiftExactList premise).getD []).length :=
    CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
      hshifted
  refine ⟨hshift, hshiftedWellFormed, ?_, ?_⟩
  · cases hresult : compactShiftRuleCheck
        (Gamma, (premise, premiseValid)) <;>
      simp [compactAdditiveBoolTag]
  · have hsetEq := compactAdditiveFormulaSetEqRows_iff_tokenCheck
      hGamma hshifted
    rw [hsetEq, hpremiseBool]
    cases hsetEqValue : tokenFormulaSetEq Gamma
        ((compactFormulaShiftExactList premise).getD []) <;>
      cases premiseValid <;>
      simp [compactShiftRuleCheck, compactAdditiveBoolTag,
        hsetEqValue]

#print axioms CompactAdditiveAllRuleCheck.of_semantics
#print axioms CompactAdditiveShiftRuleCheck.of_semantics

end FoundationCompactNumericListedDirectAllShiftRuleCheckCompleteness
