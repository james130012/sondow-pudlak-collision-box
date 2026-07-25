import integration.FoundationCompactNumericListedDirectTokenSliceBitShiftedBoundFullyFixedBounds
import integration.FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds

/-!
# Fully fixed bit-index universal certificate for token slices

The nonempty offset context, fixed bit branches, shifted-bound equality, and
the complete contextual universal shell are charged to two public scalars.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 900000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceBitUniversalFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPAValuationContextShiftedCodeSumBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceBitAtomFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitUniversalFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitUniversalOuterVariables
open FoundationCompactNumericListedDirectTokenSliceBitBranchesFixedAssembly
open FoundationCompactNumericListedDirectTokenSliceBitContextualBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitShiftedBoundFullyFixedBounds

def tokenSliceBitUniversalShellBodyCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  tokenSliceBitUniversalBodyCodePolynomial bitBound +
    valuationContextFormulaCodeSumEnvelope 1 numericBound
      tokenSliceBitBranchVariableCodeCeiling + 1

def tokenSliceBitUniversalFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  closedShortUniversalShellFixedPayloadPolynomial numericBound bitBound
    (tokenSliceBitUniversalSyntaxFixedPolynomial numericBound bitBound)
    (tokenSliceBitUniversalShellBodyCodePolynomial numericBound bitBound)
    (tokenSliceBitContextualBranchesFullyFixedPayloadPolynomial numericBound
      bitBound)
    (compileShiftedBoundEqualityFixedPayloadPolynomial
      (tokenSliceBitShiftedBoundFixedScalePolynomial numericBound bitBound))

theorem tokenSliceAtValuationBitUniversalPayloadEnvelope_le_fullyFixed
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
    tokenSliceAtValuationBitUniversalPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm sourceStart)
        (shortBinaryNumeralTerm targetStart) offset <=
      tokenSliceBitUniversalFullyFixedPayloadPolynomial numericBound
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
  let Gamma := valuationContext outerVariables branchValuation
  let boundResource := compileShiftedBoundEqualityPayloadResource
    branchValuation outerVariables boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) width (Rewriting.free body)
    (tokenSliceAtValuationBitBranchesTransparentEnvelope valuation tableTerm
      widthTerm sourceTerm targetTerm offset)
  let syntaxCode :=
    tokenSliceBitUniversalSyntaxFixedPolynomial numericBound bitBound
  let bodyCode :=
    tokenSliceBitUniversalShellBodyCodePolynomial numericBound bitBound
  let branchBound :=
    tokenSliceBitContextualBranchesFullyFixedPayloadPolynomial numericBound
      bitBound
  let boundEqualityBound :=
    compileShiftedBoundEqualityFixedPayloadPolynomial
      (tokenSliceBitShiftedBoundFixedScalePolynomial numericBound bitBound)
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
  have hGammaSum :
      formulaCodeSum Gamma <=
        valuationContextFormulaCodeSumEnvelope 1 numericBound
          tokenSliceBitBranchVariableCodeCeiling := by
    dsimp only [Gamma]
    exact valuationContext_formulaCodeSum_le_uniform outerVariables
      branchValuation 1 numericBound tokenSliceBitBranchVariableCodeCeiling
      houterCard houterValues houterVariableCodes
  have hGammaCard : Gamma.card <= 1 := by
    dsimp only [Gamma]
    exact Finset.card_image_le.trans houterCard
  have hshiftedGammaSum :
      contextualHybridUniversalFormulaCodeSum
          (Gamma.image Rewriting.shift) <=
        2 * valuationContextFormulaCodeSumEnvelope 1 numericBound
          tokenSliceBitBranchVariableCodeCeiling := by
    dsimp only [Gamma]
    exact shiftedValuationContext_formulaCodeSum_le_uniform outerVariables
      branchValuation 1 numericBound tokenSliceBitBranchVariableCodeCeiling
      houterCard houterValues houterVariableCodes
  have hbody :
      (binaryFormulaCode body).length <=
        tokenSliceBitUniversalBodyCodePolynomial bitBound := by
    dsimp only [body, tableTerm, widthTerm, sourceTerm, targetTerm]
    exact tokenSliceAtValuationBitBody_code_length_le_fixed tokenTable width
      sourceStart targetStart bitBound htableSize hwidthSize hsourceStartSize
      htargetStartSize
  have hbodyShell :
      (binaryFormulaCode body).length <= bodyCode := by
    dsimp only [bodyCode]
    unfold tokenSliceBitUniversalShellBodyCodePolynomial
    omega
  have hcontextSource :
      valuationContextFormulaCodeSumEnvelope 1 numericBound
          tokenSliceBitBranchVariableCodeCeiling <=
        closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
          syntaxCode bodyCode := by
    dsimp only [syntaxCode, bodyCode]
    unfold tokenSliceBitUniversalShellBodyCodePolynomial
      closedShortUniversalShellSourceFormulaPolynomial
      closedShortUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have hshiftedContextFormula :
      2 * valuationContextFormulaCodeSumEnvelope 1 numericBound
          tokenSliceBitBranchVariableCodeCeiling <=
        closedShortUniversalShellFormulaPolynomial numericBound bitBound
          syntaxCode bodyCode := by
    have hraw := hcontextSource
    dsimp only [syntaxCode, bodyCode] at hraw ⊢
    unfold tokenSliceBitUniversalShellBodyCodePolynomial
      closedShortUniversalShellSourceFormulaPolynomial
      closedShortUniversalShellRawFormulaPolynomial at hraw
    unfold tokenSliceBitUniversalShellBodyCodePolynomial
      closedShortUniversalShellFormulaPolynomial
      closedShortUniversalShellSourceFormulaPolynomial
      closedShortUniversalShellRawFormulaPolynomial
    dsimp only at hraw ⊢
    omega
  have hGammaSource : FormulaCodeBound Gamma
      (closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
        syntaxCode bodyCode) := by
    intro formula hformula
    have hmember :=
      FoundationCompactPAValuationTermCompilerPublicBounds.formulaCode_le_formulaCodeSum
        hformula
    exact hmember.trans (hGammaSum.trans hcontextSource)
  have hshiftedFormula : FormulaCodeBound (Gamma.image Rewriting.shift)
      (closedShortUniversalShellFormulaPolynomial numericBound bitBound
        syntaxCode bodyCode) := by
    intro formula hformula
    have hmember :=
      formulaCode_le_contextualHybridUniversalFormulaCodeSum hformula
    exact hmember.trans
      (hshiftedGammaSum.trans hshiftedContextFormula)
  have hboundResource : boundResource <= boundEqualityBound := by
    dsimp only [boundResource, boundEqualityBound, tableTerm, widthTerm,
      sourceTerm, targetTerm, branchValuation, body, boundTerm, outerFormula,
      outerVariables]
    exact tokenSliceAtValuationBitShiftedBoundResource_le_fullyFixed valuation
      tokenTable width sourceStart targetStart offset numericBound bitBound
      hwidth hoffset hwidthSize
  have hbranchResource : branchResource <= branchBound := by
    dsimp only [branchResource, branchBound, tableTerm, widthTerm, sourceTerm,
      targetTerm, branchValuation, body, boundTerm, outerFormula,
      outerVariables, Gamma]
    exact tokenSliceAtValuationBitContextualBranchesResource_le_fullyFixed
      valuation tokenTable width sourceStart targetStart offset numericBound
      bitBound hwidth hsourceStart htargetStart hoffset htableSize hwidthSize
      hsourceStartSize htargetStartSize
  have hshell :=
    compileContextualTermBoundedUniversalPayloadEnvelope_short_le_fixed_of_context
      body Gamma width numericBound bitBound syntaxCode bodyCode boundResource
      branchResource boundEqualityBound branchBound hwidth hwidthSize
      (by
        dsimp only [syntaxCode]
        unfold tokenSliceBitUniversalSyntaxFixedPolynomial
        omega)
      hbodyShell hboundResource hbranchResource hGammaCard hGammaSource
      hshiftedFormula
  have hshiftWidth : boundTerm = widthTerm := by
    dsimp only [boundTerm, widthTerm]
    simp
  unfold tokenSliceAtValuationBitUniversalPayloadEnvelope
  simp only [termValue_shift, termValue_shortBinaryNumeralTerm]
  rw [show Rew.shift (shortBinaryNumeralTerm width) =
      shortBinaryNumeralTerm width by simp]
  unfold tokenSliceBitUniversalFullyFixedPayloadPolynomial
  simpa only [tableTerm, widthTerm, sourceTerm, targetTerm, branchValuation,
    body, boundTerm, outerFormula, outerVariables, Gamma, boundResource,
    branchResource, syntaxCode, bodyCode, branchBound, boundEqualityBound,
    hshiftWidth] using hshell

#print axioms
  tokenSliceAtValuationBitUniversalPayloadEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectTokenSliceBitUniversalFullyFixedBounds
