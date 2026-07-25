import integration.FoundationCompactNumericListedDirectTokenSliceBitContextualBranchesFullyFixedBounds
import integration.FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds

/-!
# Fully fixed shifted-bound equality for token-slice bits

The shifted short width term, its value, the offset valuation coordinate, and
its binary code are all charged to one explicit scalar scale.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceBitShiftedBoundFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSliceBitAtomFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitUniversalOuterVariables

def tokenSliceBitShiftedBoundFixedScalePolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound + 2 * binaryNumeralTermCodeEnvelope bitBound + 1

theorem tokenSliceAtValuationBitShiftedBoundResource_le_fullyFixed
    (valuation : Nat -> Nat)
    (tokenTable width sourceStart targetStart offset numericBound bitBound :
      Nat)
    (hwidth : width <= numericBound)
    (hoffset : offset <= numericBound)
    (hwidthSize : Nat.size width <= bitBound) :
    let tableTerm := shortBinaryNumeralTerm tokenTable
    let widthTerm := shortBinaryNumeralTerm width
    let sourceTerm := shortBinaryNumeralTerm sourceStart
    let targetTerm := shortBinaryNumeralTerm targetStart
    let branchValuation := extendValuation offset valuation
    let body := tokenSliceAtValuationBitBody tableTerm widthTerm sourceTerm
      targetTerm
    let boundTerm := Rew.shift widthTerm
    let outerFormula := ∀⁰ termBoundedUniversalBody
      (Rew.bShift boundTerm) body
    let outerVariables := outerFormula.freeVariables
    compileShiftedBoundEqualityPayloadResource branchValuation outerVariables
        boundTerm <=
      compileShiftedBoundEqualityFixedPayloadPolynomial
        (tokenSliceBitShiftedBoundFixedScalePolynomial numericBound
          bitBound) := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let sourceTerm := shortBinaryNumeralTerm sourceStart
  let targetTerm := shortBinaryNumeralTerm targetStart
  let branchValuation := extendValuation offset valuation
  let body := tokenSliceAtValuationBitBody tableTerm widthTerm sourceTerm
    targetTerm
  let boundTerm := Rew.shift widthTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let scale :=
    tokenSliceBitShiftedBoundFixedScalePolynomial numericBound bitBound
  have hwidthClosed : widthTerm.freeVariables = ∅ := by
    dsimp only [widthTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  have hboundClosed : boundTerm.freeVariables = ∅ := by
    dsimp only [boundTerm]
    exact shiftedTerm_freeVariables_eq_empty_of_closed widthTerm hwidthClosed
  have hsourceVars :
      (tokenSliceAtValuationBitAtom tableTerm sourceTerm
        widthTerm).freeVariables ⊆ {0, 1} := by
    simpa only [tableTerm, sourceTerm, widthTerm] using
      tokenSliceBitAtom_freeVariables_subset tokenTable width sourceStart
  have htargetVars :
      (tokenSliceAtValuationBitAtom tableTerm targetTerm
        widthTerm).freeVariables ⊆ {0, 1} := by
    simpa only [tableTerm, targetTerm, widthTerm] using
      tokenSliceBitAtom_freeVariables_subset tokenTable width targetStart
  have houter : outerVariables ⊆ {0} := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      tokenSliceAtValuationBitUniversalOuterVariables_subset_singleton_of_atoms
        tableTerm widthTerm sourceTerm targetTerm boundTerm
        (by rw [hboundClosed]; simp) hsourceVars htargetVars
  have hzero : branchValuation 0 <= scale := by
    dsimp only [branchValuation, scale]
    simp only [extendValuation_zero]
    unfold tokenSliceBitShiftedBoundFixedScalePolynomial
    omega
  have hvalue : termValue branchValuation boundTerm <= scale := by
    dsimp only [branchValuation, boundTerm, widthTerm, scale]
    simp only [termValue_shift, termValue_shortBinaryNumeralTerm]
    unfold tokenSliceBitShiftedBoundFixedScalePolynomial
    omega
  have hshortCode :
      (binaryTermCode widthTerm).length <=
        binaryNumeralTermCodeEnvelope bitBound := by
    dsimp only [widthTerm]
    exact binaryNumeralTerm_code_length_le_envelope width bitBound hwidthSize
  have hshiftCode := binaryTermCode_shift_length_le widthTerm
  have hcode : (binaryTermCode boundTerm).length <= scale := by
    dsimp only [boundTerm, scale]
    unfold tokenSliceBitShiftedBoundFixedScalePolynomial
    omega
  have hpublic :=
    compileShiftedBoundEqualityPayloadResource_le_publicPolynomial
      branchValuation outerVariables boundTerm hboundClosed
  have hfixed :=
    compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq
      branchValuation outerVariables boundTerm
      (compileShiftedBoundEqualityPayloadPublicPolynomial branchValuation
        outerVariables boundTerm)
      (compileShiftedBoundEqualityFixedPayloadPolynomial scale) scale rfl rfl
      hboundClosed houter hzero hvalue hcode
  exact hpublic.trans hfixed

#print axioms
  tokenSliceAtValuationBitShiftedBoundResource_le_fullyFixed

end FoundationCompactNumericListedDirectTokenSliceBitShiftedBoundFullyFixedBounds
