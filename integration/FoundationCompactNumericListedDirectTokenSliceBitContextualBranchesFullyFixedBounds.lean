import integration.FoundationCompactNumericListedDirectTokenSliceBitBranchesFullyFixedBounds
import integration.FoundationCompactPAContextualBranchesFixedAssembly

/-!
# Fully fixed contextual bit-index branches for token slices

This layer pays for the nonempty offset valuation context and all finite
exhaustion assembly surrounding the already fixed bit branches.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceBitContextualBranchesFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPAValuationContextShiftedCodeSumBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceBitAtomFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitUniversalFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitUniversalOuterVariables
open FoundationCompactNumericListedDirectTokenSliceBitBranchesFixedAssembly
open FoundationCompactNumericListedDirectTokenSliceBitBranchesFullyFixedBounds
open FoundationCompactPAContextualBranchesFixedAssembly

def tokenSliceBitContextualBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  contextualBranchesFixedAssemblyEnvelope
    (tokenSliceBitUniversalSyntaxFixedPolynomial numericBound bitBound)
    (tokenSliceBitUniversalContextFormulaFixedPolynomial numericBound bitBound)
    (tokenSliceBitBranchesFullyFixedPayloadPolynomial numericBound bitBound)

theorem tokenSliceAtValuationBitContextualBranchesResource_le_fullyFixed
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
    let Gamma :=
      (valuationContext outerVariables branchValuation).image
        Rewriting.shift
    contextualBranchesUnderBoundPayloadEnvelope Gamma width
        (Rewriting.free body)
        (tokenSliceAtValuationBitBranchesTransparentEnvelope valuation
          tableTerm widthTerm sourceTerm targetTerm offset) <=
      tokenSliceBitContextualBranchesFullyFixedPayloadPolynomial numericBound
        bitBound := by
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
  let Gamma :=
    (valuationContext outerVariables branchValuation).image Rewriting.shift
  let targetFormula := Rewriting.free body
  let caseResource :=
    tokenSliceAtValuationBitBranchesTransparentEnvelope valuation tableTerm
      widthTerm sourceTerm targetTerm offset
  let syntaxCode :=
    tokenSliceBitUniversalSyntaxFixedPolynomial numericBound bitBound
  let formulaCode :=
    tokenSliceBitUniversalContextFormulaFixedPolynomial numericBound bitBound
  let caseBound :=
    tokenSliceBitBranchesFullyFixedPayloadPolynomial numericBound bitBound
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
  have houterCard : outerVariables.card <= 1 :=
    (Finset.card_le_card houter).trans (by simp)
  have houterValues : forall index, index ∈ outerVariables ->
      branchValuation index <= numericBound := by
    intro index hindex
    have hsmall := houter hindex
    simp only [Finset.mem_singleton] at hsmall
    subst index
    dsimp only [branchValuation]
    simp only [extendValuation_zero]
    exact hoffset
  have houterVariableCodes : forall index, index ∈ outerVariables ->
      (binaryTermCode (&index : ValuationTerm)).length <=
        tokenSliceBitBranchVariableCodeCeiling := by
    intro index hindex
    have hsmall := houter hindex
    simp only [Finset.mem_singleton] at hsmall
    subst index
    unfold tokenSliceBitBranchVariableCodeCeiling
    omega
  have hGammaCode :
      contextualHybridUniversalFormulaCodeSum Gamma <=
        2 * valuationContextFormulaCodeSumEnvelope 1 numericBound
          tokenSliceBitBranchVariableCodeCeiling := by
    dsimp only [Gamma]
    exact shiftedValuationContext_formulaCodeSum_le_uniform outerVariables
      branchValuation 1 numericBound tokenSliceBitBranchVariableCodeCeiling
      houterCard houterValues houterVariableCodes
  have hGammaCard : Gamma.card <= 1 := by
    dsimp only [Gamma]
    have hcontext :
        (valuationContext outerVariables branchValuation).card <=
          outerVariables.card := by
      unfold valuationContext
      exact Finset.card_image_le
    exact Finset.card_image_le.trans (hcontext.trans houterCard)
  have hGammaBound : FormulaCodeBound Gamma formulaCode := by
    intro formula hformula
    have hsingle :=
      formulaCode_le_contextualHybridUniversalFormulaCodeSum hformula
    exact hsingle.trans (hGammaCode.trans (by
      dsimp only [formulaCode]
      unfold tokenSliceBitUniversalContextFormulaFixedPolynomial
      omega))
  have hbody :
      (binaryFormulaCode body).length <=
        tokenSliceBitUniversalBodyCodePolynomial bitBound := by
    dsimp only [body, tableTerm, widthTerm, sourceTerm, targetTerm]
    exact tokenSliceAtValuationBitBody_code_length_le_fixed tokenTable width
      sourceStart targetStart bitBound htableSize hwidthSize hsourceStartSize
      htargetStartSize
  have hboundSyntax : width <= syntaxCode := by
    dsimp only [syntaxCode]
    unfold tokenSliceBitUniversalSyntaxFixedPolynomial
    omega
  have hclosedLe :
      boundedUniversalClosedFormulaEnvelope syntaxCode <= formulaCode := by
    dsimp only [syntaxCode, formulaCode]
    unfold tokenSliceBitUniversalContextFormulaFixedPolynomial
      tokenSliceBitUniversalFormulaFixedPolynomial
    omega
  have htargetCode :
      (binaryFormulaCode targetFormula).length <= formulaCode := by
    have hfree := binaryFormulaCode_free_length_le body
    dsimp only [targetFormula, formulaCode]
    unfold tokenSliceBitUniversalContextFormulaFixedPolynomial
      tokenSliceBitUniversalFormulaFixedPolynomial
    omega
  have hcase : caseResource <= caseBound := by
    dsimp only [caseResource, caseBound, tableTerm, widthTerm, sourceTerm,
      targetTerm]
    exact
      tokenSliceAtValuationBitBranchesTransparentEnvelope_le_fullyFixed
        valuation tokenTable width sourceStart targetStart offset numericBound
        bitBound hwidth hsourceStart htargetStart hoffset htableSize hwidthSize
        hsourceStartSize htargetStartSize
  have hassembled :=
    contextualBranchesUnderBoundPayloadEnvelope_le_fixedAssembly Gamma width
      syntaxCode formulaCode caseResource caseBound targetFormula
      hboundSyntax hclosedLe htargetCode hGammaCard hGammaBound hcase
  unfold tokenSliceBitContextualBranchesFullyFixedPayloadPolynomial
  simpa only [tableTerm, widthTerm, sourceTerm, targetTerm, branchValuation,
    body, boundTerm, outerFormula, outerVariables, Gamma, targetFormula,
    caseResource, syntaxCode, formulaCode, caseBound] using hassembled

#print axioms
  tokenSliceAtValuationBitContextualBranchesResource_le_fullyFixed

end FoundationCompactNumericListedDirectTokenSliceBitContextualBranchesFullyFixedBounds
