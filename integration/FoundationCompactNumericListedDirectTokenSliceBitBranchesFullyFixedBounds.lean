import integration.FoundationCompactNumericListedDirectTokenSliceBitBranchesFixedAssembly

/-!
# Concrete fully fixed inner token-slice branches

This layer discharges the four generic assembly premises for short binary
numerals and the actual token-slice bit certificates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 900000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceBitBranchesFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPAValuationContextShiftedCodeSumBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceBitAtomFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitUniversalFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitUniversalOuterVariables
open FoundationCompactNumericListedDirectTokenSliceBitBranchesFixedAssembly

theorem tokenSliceAtValuationBitBranchesTransparentEnvelope_le_fullyFixed
    (valuation : Nat -> Nat)
    (tokenTable width sourceStart targetStart offset numericBound bitBound :
      Nat)
    (hwidth : width <= numericBound)
    (hsourceStart : sourceStart <= numericBound)
    (htargetStart : targetStart <= numericBound)
    (hoffset : offset <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound) :
    tokenSliceAtValuationBitBranchesTransparentEnvelope valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm sourceStart)
        (shortBinaryNumeralTerm targetStart) offset <=
      tokenSliceBitBranchesFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let sourceTerm := shortBinaryNumeralTerm sourceStart
  let targetTerm := shortBinaryNumeralTerm targetStart
  let boundTerm := Rew.shift widthTerm
  have hbound :
      termValue (extendValuation offset valuation) boundTerm <= numericBound := by
    dsimp only [boundTerm, widthTerm]
    simp only [termValue_shift, termValue_shortBinaryNumeralTerm]
    exact hwidth
  have hleaf :
      tokenSliceAtValuationBitBranchPayloadResourceSum valuation tableTerm
          widthTerm sourceTerm targetTerm offset <=
        tokenSliceAtValuationBitBranchPayloadSumFixedPolynomial numericBound
          bitBound := by
    dsimp only [tableTerm, widthTerm, sourceTerm, targetTerm]
    exact tokenSliceAtValuationBitBranchPayloadResourceSum_le_fixed
      valuation tokenTable width sourceStart targetStart offset numericBound
      bitBound hwidth hsourceStart htargetStart hoffset htableSize hwidthSize
      hsourceStartSize htargetStartSize
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
  let body := tokenSliceAtValuationBitBody tableTerm widthTerm sourceTerm
    targetTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let branchValuation := extendValuation offset valuation
  have houterExplicit : outerVariables ⊆ {0} := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      tokenSliceAtValuationBitUniversalOuterVariables_subset_singleton_of_atoms
        tableTerm widthTerm sourceTerm targetTerm boundTerm
        (by rw [hboundClosed]; simp) hsourceVars htargetVars
  have houter :
      let body := tokenSliceAtValuationBitBody tableTerm widthTerm sourceTerm
        targetTerm
      let outerFormula := ∀⁰ termBoundedUniversalBody
        (Rew.bShift boundTerm) body
      outerFormula.freeVariables ⊆ {0} := by
    simpa only [body, outerFormula, outerVariables] using houterExplicit
  have houterCard : outerVariables.card <= 1 :=
    (Finset.card_le_card houterExplicit).trans (by simp)
  have houterValues : forall index, index ∈ outerVariables ->
      branchValuation index <= numericBound := by
    intro index hindex
    have hsmall := houterExplicit hindex
    simp only [Finset.mem_singleton] at hsmall
    subst index
    dsimp only [branchValuation]
    simp only [extendValuation_zero]
    exact hoffset
  have houterVariableCodes : forall index, index ∈ outerVariables ->
      (binaryTermCode (&index : ValuationTerm)).length <=
        tokenSliceBitBranchVariableCodeCeiling := by
    intro index hindex
    have hsmall := houterExplicit hindex
    simp only [Finset.mem_singleton] at hsmall
    subst index
    unfold tokenSliceBitBranchVariableCodeCeiling
    omega
  have hGammaCodeExplicit :
      contextualHybridUniversalFormulaCodeSum
          ((valuationContext outerVariables branchValuation).image
            Rewriting.shift) <=
        2 * valuationContextFormulaCodeSumEnvelope 1 numericBound
          tokenSliceBitBranchVariableCodeCeiling :=
    shiftedValuationContext_formulaCodeSum_le_uniform outerVariables
      branchValuation 1 numericBound tokenSliceBitBranchVariableCodeCeiling
      houterCard houterValues houterVariableCodes
  have hGammaCode :
      let body := tokenSliceAtValuationBitBody tableTerm widthTerm sourceTerm
        targetTerm
      let boundTerm := Rew.shift widthTerm
      let outerFormula := ∀⁰ termBoundedUniversalBody
        (Rew.bShift boundTerm) body
      let outerVariables := outerFormula.freeVariables
      let branchValuation := extendValuation offset valuation
      contextualHybridUniversalFormulaCodeSum
          ((valuationContext outerVariables branchValuation).image
            Rewriting.shift) <=
        2 * valuationContextFormulaCodeSumEnvelope 1 numericBound
          tokenSliceBitBranchVariableCodeCeiling := by
    simpa only [body, boundTerm, outerFormula, outerVariables,
      branchValuation] using hGammaCodeExplicit
  have hbody :
      (binaryFormulaCode
        (tokenSliceAtValuationBitBody tableTerm widthTerm sourceTerm
          targetTerm)).length <=
        tokenSliceBitUniversalBodyCodePolynomial bitBound := by
    dsimp only [tableTerm, widthTerm, sourceTerm, targetTerm]
    exact tokenSliceAtValuationBitBody_code_length_le_fixed tokenTable width
      sourceStart targetStart bitBound htableSize hwidthSize hsourceStartSize
      htargetStartSize
  exact tokenSliceBitBranchesTransparentEnvelope_le_fixed_of_components
    valuation tableTerm widthTerm sourceTerm targetTerm offset numericBound
    bitBound hbound hleaf houter hbody hGammaCode

#print axioms
  tokenSliceAtValuationBitBranchesTransparentEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectTokenSliceBitBranchesFullyFixedBounds
