import integration.FoundationCompactNumericListedDirectTokenSliceBitClosedTermUniversalFullyFixedBounds

/-!
# Short-width universal endpoint for closed token-slice starts

The term-code, branch, and contextual bounds are imported from the base
module.  This file pays only for the shifted width equality and the final
bounded-universal shell.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 900000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceBitClosedTermUniversalEndpointFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationContextShiftedCodeSumBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceBitAtomFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitAtomClosedTermFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitUniversalOuterVariables
open FoundationCompactNumericListedDirectTokenSliceBitClosedTermUniversalFullyFixedBounds

def tokenSliceClosedTermBitUniversalShellBodyCodePolynomial
    (numericBound termCode : Nat) : Nat :=
  tokenSliceClosedTermBitUniversalBodyCodePolynomial termCode +
    valuationContextFormulaCodeSumEnvelope 1 numericBound
      tokenSliceBitBranchVariableCodeCeiling + 1

def tokenSliceClosedTermBitShiftedBoundFixedScalePolynomial
    (numericBound termCode : Nat) : Nat :=
  numericBound + 4 * termCode + 1

def tokenSliceClosedTermBitUniversalFullyFixedPayloadPolynomial
    (numericBound termCode bitBound : Nat) : Nat :=
  closedShortUniversalShellFixedPayloadPolynomial numericBound bitBound
    (tokenSliceClosedTermBitUniversalSyntaxFixedPolynomial numericBound
      termCode)
    (tokenSliceClosedTermBitUniversalShellBodyCodePolynomial numericBound
      termCode)
    (tokenSliceClosedTermBitContextualBranchesFullyFixedPayloadPolynomial
      numericBound termCode bitBound)
    (compileShiftedBoundEqualityFixedPayloadPolynomial
      (tokenSliceClosedTermBitShiftedBoundFixedScalePolynomial numericBound
        termCode))

private theorem
    tokenSliceShortWidthContextualBranchesResource_le_closedFixed
    (valuation : Nat -> Nat)
    (tokenTable width offset numericBound termCode bitBound : Nat)
    (sourceStartTerm targetStartTerm : ValuationTerm)
    (hsourceClosed : sourceStartTerm.freeVariables = ∅)
    (htargetClosed : targetStartTerm.freeVariables = ∅)
    (htableCode :
      (binaryTermCode (shortBinaryNumeralTerm tokenTable)).length <= termCode)
    (hwidthCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= termCode)
    (hsourceCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (htargetCode : (binaryTermCode targetStartTerm).length <= termCode)
    (hwidth : width <= numericBound)
    (hsource : termValue valuation sourceStartTerm <= numericBound)
    (htarget : termValue valuation targetStartTerm <= numericBound)
    (hoffset : offset <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound) :
    let tableTerm := shortBinaryNumeralTerm tokenTable
    let widthTerm := shortBinaryNumeralTerm width
    let branchValuation := extendValuation offset valuation
    let body := tokenSliceAtValuationBitBody tableTerm widthTerm
      sourceStartTerm targetStartTerm
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
          tableTerm widthTerm sourceStartTerm targetStartTerm offset) <=
      tokenSliceClosedTermBitContextualBranchesFullyFixedPayloadPolynomial
        numericBound termCode bitBound := by
  have htableClosed :
      (shortBinaryNumeralTerm tokenTable).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  have hwidthClosed :
      (shortBinaryNumeralTerm width).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty width
  have hraw :=
    tokenSliceAtValuationBitContextualBranchesResource_le_closedFixed
      valuation (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width) sourceStartTerm targetStartTerm offset
      numericBound termCode bitBound htableClosed hwidthClosed hsourceClosed
      htargetClosed htableCode hwidthCode hsourceCode htargetCode
      (by simpa only [termValue_shortBinaryNumeralTerm] using hwidth)
      hsource htarget hoffset
      (by simpa only [termValue_shortBinaryNumeralTerm] using htableSize)
  simpa only [termValue_shortBinaryNumeralTerm] using hraw

noncomputable def tokenSliceClosedTermBitUniversalShortShellEnvelope
    (valuation : Nat -> Nat) (tokenTable width offset : Nat)
    (sourceStartTerm targetStartTerm : ValuationTerm) : Nat :=
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let branchValuation := extendValuation offset valuation
  let body := tokenSliceAtValuationBitBody tableTerm widthTerm sourceStartTerm
    targetStartTerm
  let boundTerm := Rew.shift widthTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables branchValuation
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) width (Rewriting.free body)
    (tokenSliceAtValuationBitBranchesTransparentEnvelope valuation tableTerm
      widthTerm sourceStartTerm targetStartTerm offset)
  compileContextualTermBoundedUniversalPayloadEnvelope Gamma width
    (Rew.bShift boundTerm) body
    (compileShiftedBoundEqualityPayloadResource branchValuation
      outerVariables boundTerm)
    branchResource

private theorem tokenSliceClosedTermBitUniversalPayloadEnvelope_eq_shortShell
    (valuation : Nat -> Nat) (tokenTable width offset : Nat)
    (sourceStartTerm targetStartTerm : ValuationTerm) :
    tokenSliceAtValuationBitUniversalPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        sourceStartTerm targetStartTerm offset =
      tokenSliceClosedTermBitUniversalShortShellEnvelope valuation tokenTable
        width offset sourceStartTerm targetStartTerm := by
  unfold tokenSliceAtValuationBitUniversalPayloadEnvelope
    tokenSliceClosedTermBitUniversalShortShellEnvelope
  simp only [termValue_shift, termValue_shortBinaryNumeralTerm]

private theorem
    tokenSliceClosedTermBitUniversalShortShellEnvelope_eq_closedSource
    (valuation : Nat -> Nat) (tokenTable width offset : Nat)
    (sourceStartTerm targetStartTerm : ValuationTerm) :
    tokenSliceClosedTermBitUniversalShortShellEnvelope valuation tokenTable
        width offset sourceStartTerm targetStartTerm =
      let tableTerm := shortBinaryNumeralTerm tokenTable
      let widthTerm := shortBinaryNumeralTerm width
      let branchValuation := extendValuation offset valuation
      let body := tokenSliceAtValuationBitBody tableTerm widthTerm
        sourceStartTerm targetStartTerm
      let boundTerm := Rew.shift widthTerm
      let outerFormula := ∀⁰ termBoundedUniversalBody
        (Rew.bShift boundTerm) body
      let outerVariables := outerFormula.freeVariables
      let Gamma := valuationContext outerVariables branchValuation
      let branchResource := contextualBranchesUnderBoundPayloadEnvelope
        (Gamma.image Rewriting.shift) width (Rewriting.free body)
        (tokenSliceAtValuationBitBranchesTransparentEnvelope valuation
          tableTerm widthTerm sourceStartTerm targetStartTerm offset)
      compileContextualTermBoundedUniversalPayloadEnvelope Gamma width
        (Rew.bShift widthTerm) body
        (compileShiftedBoundEqualityPayloadResource branchValuation
          outerVariables boundTerm)
        branchResource := by
  unfold tokenSliceClosedTermBitUniversalShortShellEnvelope
  simp

structure TokenSliceClosedTermBitUniversalShellFacts
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (width numericBound bitBound syntaxCode bodyCode : Nat)
    (boundResource branchResource boundEqualityBound branchBound : Nat) :
    Prop where
  hsyntax : width <= syntaxCode
  hbody : (binaryFormulaCode body).length <= bodyCode
  hbound : boundResource <= boundEqualityBound
  hbranch : branchResource <= branchBound
  hGammaCard : Gamma.card <= 1
  hGammaSource : FormulaCodeBound Gamma
    (closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
      syntaxCode bodyCode)
  hshiftedFormula : FormulaCodeBound (Gamma.image Rewriting.shift)
    (closedShortUniversalShellFormulaPolynomial numericBound bitBound
      syntaxCode bodyCode)

def closedShortUniversalShellBound
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (width numericBound bitBound syntaxCode bodyCode : Nat)
    (boundResource branchResource boundEqualityBound branchBound : Nat) :
    Prop :=
  compileContextualTermBoundedUniversalPayloadEnvelope Gamma width
      (Rew.bShift (shortBinaryNumeralTerm width)) body boundResource
      branchResource <=
    closedShortUniversalShellFixedPayloadPolynomial numericBound bitBound
      syntaxCode bodyCode branchBound boundEqualityBound

theorem closedShortUniversalShellBound_of_facts
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (width numericBound bitBound syntaxCode bodyCode : Nat)
    (boundResource branchResource boundEqualityBound branchBound : Nat)
    (hwidth : width <= numericBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hfacts : TokenSliceClosedTermBitUniversalShellFacts body Gamma width
      numericBound bitBound syntaxCode bodyCode boundResource branchResource
      boundEqualityBound branchBound) :
    closedShortUniversalShellBound body Gamma width numericBound bitBound
      syntaxCode bodyCode boundResource branchResource boundEqualityBound
      branchBound := by
  unfold closedShortUniversalShellBound
  exact
    compileContextualTermBoundedUniversalPayloadEnvelope_short_le_fixed_of_context
      body Gamma width numericBound bitBound syntaxCode bodyCode boundResource
      branchResource boundEqualityBound branchBound hwidth hwidthSize
      hfacts.hsyntax hfacts.hbody hfacts.hbound hfacts.hbranch
      hfacts.hGammaCard hfacts.hGammaSource hfacts.hshiftedFormula

theorem
    tokenSliceClosedTermBitUniversalShellFacts_closedFixed
    (valuation : Nat -> Nat)
    (tokenTable width offset numericBound termCode bitBound : Nat)
    (sourceStartTerm targetStartTerm : ValuationTerm)
    (hsourceClosed : sourceStartTerm.freeVariables = ∅)
    (htargetClosed : targetStartTerm.freeVariables = ∅)
    (htableCode :
      (binaryTermCode (shortBinaryNumeralTerm tokenTable)).length <= termCode)
    (hwidthCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= termCode)
    (hsourceCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (htargetCode : (binaryTermCode targetStartTerm).length <= termCode)
    (hwidth : width <= numericBound)
    (hsource : termValue valuation sourceStartTerm <= numericBound)
    (htarget : termValue valuation targetStartTerm <= numericBound)
    (hoffset : offset <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound) :
    let tableTerm := shortBinaryNumeralTerm tokenTable
    let widthTerm := shortBinaryNumeralTerm width
    let branchValuation := extendValuation offset valuation
    let body := tokenSliceAtValuationBitBody tableTerm widthTerm
      sourceStartTerm targetStartTerm
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
        widthTerm sourceStartTerm targetStartTerm offset)
    let syntaxCode :=
      tokenSliceClosedTermBitUniversalSyntaxFixedPolynomial numericBound
        termCode
    let bodyCode :=
      tokenSliceClosedTermBitUniversalShellBodyCodePolynomial numericBound
        termCode
    let branchBound :=
      tokenSliceClosedTermBitContextualBranchesFullyFixedPayloadPolynomial
        numericBound termCode bitBound
    let boundEqualityBound :=
      compileShiftedBoundEqualityFixedPayloadPolynomial
        (tokenSliceClosedTermBitShiftedBoundFixedScalePolynomial numericBound
          termCode)
    TokenSliceClosedTermBitUniversalShellFacts body Gamma width numericBound
      bitBound syntaxCode bodyCode boundResource branchResource
      boundEqualityBound branchBound := by
  dsimp only
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let branchValuation := extendValuation offset valuation
  let body := tokenSliceAtValuationBitBody tableTerm widthTerm sourceStartTerm
    targetStartTerm
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
      widthTerm sourceStartTerm targetStartTerm offset)
  let syntaxCode :=
    tokenSliceClosedTermBitUniversalSyntaxFixedPolynomial numericBound
      termCode
  let bodyCode :=
    tokenSliceClosedTermBitUniversalShellBodyCodePolynomial numericBound
      termCode
  let branchBound :=
    tokenSliceClosedTermBitContextualBranchesFullyFixedPayloadPolynomial
      numericBound termCode bitBound
  let scale :=
    tokenSliceClosedTermBitShiftedBoundFixedScalePolynomial numericBound
      termCode
  let boundEqualityBound :=
    compileShiftedBoundEqualityFixedPayloadPolynomial scale
  have htableClosed : tableTerm.freeVariables = ∅ := by
    dsimp only [tableTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  have hwidthClosed : widthTerm.freeVariables = ∅ := by
    dsimp only [widthTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  have hboundClosed : boundTerm.freeVariables = ∅ :=
    shiftedTerm_freeVariables_eq_empty_of_closed widthTerm hwidthClosed
  have hsourceVars :
      (tokenSliceAtValuationBitAtom tableTerm sourceStartTerm
        widthTerm).freeVariables ⊆ {0, 1} :=
    tokenSliceClosedTermBitAtom_freeVariables_subset tableTerm widthTerm
      sourceStartTerm htableClosed hwidthClosed hsourceClosed
  have htargetVars :
      (tokenSliceAtValuationBitAtom tableTerm targetStartTerm
        widthTerm).freeVariables ⊆ {0, 1} :=
    tokenSliceClosedTermBitAtom_freeVariables_subset tableTerm widthTerm
      targetStartTerm htableClosed hwidthClosed htargetClosed
  have houter : outerVariables ⊆ {0} := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      tokenSliceAtValuationBitUniversalOuterVariables_subset_singleton_of_atoms
        tableTerm widthTerm sourceStartTerm targetStartTerm boundTerm
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
    simpa only [extendValuation_zero] using hoffset
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
        tokenSliceClosedTermBitUniversalBodyCodePolynomial termCode := by
    dsimp only [body, tableTerm, widthTerm]
    exact tokenSliceAtValuationBitBody_code_length_le_closedFixed
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      sourceStartTerm targetStartTerm termCode htableCode hwidthCode
      hsourceCode htargetCode
  have hbodyShell : (binaryFormulaCode body).length <= bodyCode := by
    dsimp only [bodyCode]
    unfold tokenSliceClosedTermBitUniversalShellBodyCodePolynomial
    omega
  have hcontextSource :
      valuationContextFormulaCodeSumEnvelope 1 numericBound
          tokenSliceBitBranchVariableCodeCeiling <=
        closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
          syntaxCode bodyCode := by
    dsimp only [syntaxCode, bodyCode]
    unfold tokenSliceClosedTermBitUniversalShellBodyCodePolynomial
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
    unfold tokenSliceClosedTermBitUniversalShellBodyCodePolynomial
      closedShortUniversalShellSourceFormulaPolynomial
      closedShortUniversalShellRawFormulaPolynomial at hraw
    unfold tokenSliceClosedTermBitUniversalShellBodyCodePolynomial
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
    have hpublic :=
      compileShiftedBoundEqualityPayloadResource_le_publicPolynomial
        branchValuation outerVariables boundTerm hboundClosed
    have hboundCodeRaw := binaryTermCode_shift_length_le widthTerm
    have hboundCode : (binaryTermCode boundTerm).length <= scale := by
      dsimp only [boundTerm, widthTerm, scale] at hboundCodeRaw ⊢
      unfold tokenSliceClosedTermBitShiftedBoundFixedScalePolynomial
      omega
    have hfixed :=
      compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq_of_values
        branchValuation outerVariables boundTerm
        (compileShiftedBoundEqualityPayloadPublicPolynomial branchValuation
          outerVariables boundTerm)
        (compileShiftedBoundEqualityFixedPayloadPolynomial scale)
        scale rfl rfl hboundClosed houter
        (by
          intro index hindex
          have hsmall := houter hindex
          simp only [Finset.mem_singleton] at hsmall
          subst index
          dsimp only [branchValuation, scale]
          simp only [extendValuation_zero]
          unfold tokenSliceClosedTermBitShiftedBoundFixedScalePolynomial
          omega)
        (by
          dsimp only [branchValuation, boundTerm, widthTerm, scale]
          simp only [termValue_shift, termValue_shortBinaryNumeralTerm]
          unfold tokenSliceClosedTermBitShiftedBoundFixedScalePolynomial
          omega)
        hboundCode
    exact hpublic.trans hfixed
  have hbranchResource : branchResource <= branchBound := by
    simpa only [branchResource, branchBound, tableTerm, widthTerm,
      branchValuation, body, boundTerm, outerFormula, outerVariables, Gamma]
      using
        tokenSliceShortWidthContextualBranchesResource_le_closedFixed
          valuation tokenTable width offset numericBound termCode bitBound
          sourceStartTerm targetStartTerm hsourceClosed htargetClosed
          htableCode hwidthCode hsourceCode htargetCode hwidth hsource htarget
          hoffset htableSize
  exact {
    hsyntax := by
      unfold tokenSliceClosedTermBitUniversalSyntaxFixedPolynomial
      omega
    hbody := hbodyShell
    hbound := hboundResource
    hbranch := hbranchResource
    hGammaCard := hGammaCard
    hGammaSource := hGammaSource
    hshiftedFormula := hshiftedFormula
  }

theorem
    tokenSliceClosedTermBitUniversalShortShellEnvelope_le_closedFixed
    (valuation : Nat -> Nat)
    (tokenTable width offset numericBound termCode bitBound : Nat)
    (sourceStartTerm targetStartTerm : ValuationTerm)
    (hsourceClosed : sourceStartTerm.freeVariables = ∅)
    (htargetClosed : targetStartTerm.freeVariables = ∅)
    (htableCode :
      (binaryTermCode (shortBinaryNumeralTerm tokenTable)).length <= termCode)
    (hwidthCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= termCode)
    (hsourceCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (htargetCode : (binaryTermCode targetStartTerm).length <= termCode)
    (hwidth : width <= numericBound)
    (hsource : termValue valuation sourceStartTerm <= numericBound)
    (htarget : termValue valuation targetStartTerm <= numericBound)
    (hoffset : offset <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound) :
    let tableTerm := shortBinaryNumeralTerm tokenTable
    let widthTerm := shortBinaryNumeralTerm width
    let branchValuation := extendValuation offset valuation
    let body := tokenSliceAtValuationBitBody tableTerm widthTerm
      sourceStartTerm targetStartTerm
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
        widthTerm sourceStartTerm targetStartTerm offset)
    let syntaxCode :=
      tokenSliceClosedTermBitUniversalSyntaxFixedPolynomial numericBound
        termCode
    let bodyCode :=
      tokenSliceClosedTermBitUniversalShellBodyCodePolynomial numericBound
        termCode
    let branchBound :=
      tokenSliceClosedTermBitContextualBranchesFullyFixedPayloadPolynomial
        numericBound termCode bitBound
    let boundEqualityBound :=
      compileShiftedBoundEqualityFixedPayloadPolynomial
        (tokenSliceClosedTermBitShiftedBoundFixedScalePolynomial numericBound
          termCode)
    closedShortUniversalShellBound body Gamma width numericBound bitBound
      syntaxCode bodyCode boundResource branchResource boundEqualityBound
      branchBound := by
  intros tableTerm widthTerm branchValuation body boundTerm outerFormula
    outerVariables Gamma boundResource branchResource syntaxCode bodyCode
    branchBound boundEqualityBound
  have hfacts :=
    tokenSliceClosedTermBitUniversalShellFacts_closedFixed valuation tokenTable
      width offset numericBound termCode bitBound sourceStartTerm
      targetStartTerm hsourceClosed htargetClosed htableCode hwidthCode
      hsourceCode htargetCode hwidth hsource htarget hoffset htableSize
  exact closedShortUniversalShellBound_of_facts body Gamma width numericBound
    bitBound syntaxCode bodyCode boundResource branchResource
    boundEqualityBound branchBound hwidth hwidthSize hfacts

theorem
    tokenSliceAtValuationBitUniversalPayloadEnvelope_le_closedFixed
    (valuation : Nat -> Nat)
    (tokenTable width offset numericBound termCode bitBound : Nat)
    (sourceStartTerm targetStartTerm : ValuationTerm)
    (hsourceClosed : sourceStartTerm.freeVariables = ∅)
    (htargetClosed : targetStartTerm.freeVariables = ∅)
    (htableCode :
      (binaryTermCode (shortBinaryNumeralTerm tokenTable)).length <= termCode)
    (hwidthCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= termCode)
    (hsourceCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (htargetCode : (binaryTermCode targetStartTerm).length <= termCode)
    (hwidth : width <= numericBound)
    (hsource : termValue valuation sourceStartTerm <= numericBound)
    (htarget : termValue valuation targetStartTerm <= numericBound)
    (hoffset : offset <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound) :
    tokenSliceAtValuationBitUniversalPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        sourceStartTerm targetStartTerm offset <=
      tokenSliceClosedTermBitUniversalFullyFixedPayloadPolynomial numericBound
        termCode bitBound := by
  have hwrapped :=
    tokenSliceClosedTermBitUniversalShortShellEnvelope_le_closedFixed
      valuation tokenTable width offset numericBound termCode bitBound
      sourceStartTerm targetStartTerm hsourceClosed htargetClosed htableCode
      hwidthCode hsourceCode htargetCode hwidth hsource htarget hoffset
      htableSize hwidthSize
  dsimp only at hwrapped
  unfold closedShortUniversalShellBound at hwrapped
  rw [tokenSliceClosedTermBitUniversalPayloadEnvelope_eq_shortShell,
    tokenSliceClosedTermBitUniversalShortShellEnvelope_eq_closedSource]
  unfold tokenSliceClosedTermBitUniversalFullyFixedPayloadPolynomial
  exact hwrapped

#print axioms
  tokenSliceAtValuationBitUniversalPayloadEnvelope_le_closedFixed

end FoundationCompactNumericListedDirectTokenSliceBitClosedTermUniversalEndpointFixedBounds
