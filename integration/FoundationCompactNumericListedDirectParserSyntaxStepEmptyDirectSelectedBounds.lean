import integration.FoundationCompactNumericListedDirectParserEmptyUniformDirectOriginalFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxStepCleanGraphCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxStepFormulaSyntaxFixedBounds
import integration.FoundationCompactPADirectConnectiveTransparentBounds
import integration.FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactListedProofHonestWeight

/-! # Direct selected-empty path inside the six-way syntax step -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxStepEmptyDirectSelectedBounds

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactCertifiedContextProof
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserEmptyFormula
open FoundationCompactNumericListedDirectParserEmptyUniformDirectAlignment
open FoundationCompactNumericListedDirectParserEmptyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserEmptyUniformDirectOriginalFixedBounds
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepFormulaSyntaxFixedBounds
open FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds
open FoundationCompactListedProofHonestWeight

private abbrev stepEmptyZeroValuation : Nat -> Nat :=
  compactUnifiedParserSyntaxStepZeroValuation

def syntaxStepEmptyDirectSelectedPayloadEnvelope
    (a b c d e f : ValuationFormula) (resource : Nat) : Nat :=
  let inner := transparentHybridDisjunctionLeftPayloadEnvelope
    stepEmptyZeroValuation b (c ⋎ (d ⋎ (e ⋎ f))) resource
  transparentHybridDisjunctionRightPayloadEnvelope stepEmptyZeroValuation a
    (b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) inner

noncomputable def compileCompactUnifiedParserSyntaxStepFromEmptyDirectContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserEmptyGraphRows tokenTable width tokenCount
      current next witness.empty)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentTokensCount : current.tokensCount <= numericBound)
    (houtputBoundarySize :
      Nat.size witness.empty.targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width
          tokenCount current next witness).freeVariables
        stepEmptyZeroValuation)
      (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width
        tokenCount current next witness) := by
  let selected :=
    compileCompactUnifiedParserEmptyUniformDirectOriginalContext tokenTable
      width tokenCount current next witness.empty numericBound bitBound hgraph
      htokenCount hcurrentTokensCount houtputBoundarySize hnumericSize
  let a := compactUnifiedParserDoneClosedFormula tokenTable width tokenCount
    current next witness.done
  let b := compactUnifiedParserEmptyClosedFormula tokenTable width tokenCount
    current next witness.empty
  let c := compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width
    tokenCount current next witness.slot0 witness.slot1 witness.repeat
  let d := compactUnifiedParserSyntaxTermClosedFormula tokenTable width
    tokenCount current next witness.slot0 witness.term
  let e := compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width
    tokenCount current next witness.slot0 witness.formula
  let f := compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width
    tokenCount current next witness.invalid
  have hbClosed : b.freeVariables = ∅ := by
    dsimp only [b]
    unfold compactUnifiedParserEmptyClosedFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate <;>
      apply shortBinaryNumeralTerm_freeVariables_eq_empty
  let selectedAtStep : CertifiedPAContextProof
      (valuationContext b.freeVariables stepEmptyZeroValuation) b := by
    apply CertifiedPAContextProof.castContext (proof := selected)
    rw [hbClosed]
    simp [valuationContext]
  let inner := compileDirectDisjunctionLeft
    (right := c ⋎ (d ⋎ (e ⋎ f))) selectedAtStep
  let outer := compileDirectDisjunctionRight (left := a) inner
  simpa only [compactUnifiedParserSyntaxStepExplicitFormula, a, b, c, d, e, f,
    selected, selectedAtStep, inner, outer] using outer

theorem
    compileCompactUnifiedParserSyntaxStepFromEmptyDirectContext_payloadLength_le_selected
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserEmptyGraphRows tokenTable width tokenCount
      current next witness.empty)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (houtputBoundarySize :
      Nat.size witness.empty.targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compileCompactUnifiedParserSyntaxStepFromEmptyDirectContext tokenTable
      width tokenCount current next witness numericBound bitBound hgraph
      htokenCount
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          hcurrentValue (5 : Fin 8))
      houtputBoundarySize hnumericSize).payloadLength <=
      syntaxStepEmptyDirectSelectedPayloadEnvelope
        (compactUnifiedParserDoneClosedFormula tokenTable width tokenCount
          current next witness.done)
        (compactUnifiedParserEmptyClosedFormula tokenTable width tokenCount
          current next witness.empty)
        (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width
          tokenCount current next witness.slot0 witness.slot1 witness.repeat)
        (compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount
          current next witness.slot0 witness.term)
        (compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width
          tokenCount current next witness.slot0 witness.formula)
        (compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width
          tokenCount current next witness.invalid)
        (parserEmptyUniformDirectFixedPayloadPolynomial numericBound
          bitBound) := by
  let selected :=
    compileCompactUnifiedParserEmptyUniformDirectOriginalContext tokenTable
      width tokenCount current next witness.empty numericBound bitBound hgraph
      htokenCount
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          hcurrentValue (5 : Fin 8))
      houtputBoundarySize hnumericSize
  let a := compactUnifiedParserDoneClosedFormula tokenTable width tokenCount
    current next witness.done
  let b := compactUnifiedParserEmptyClosedFormula tokenTable width tokenCount
    current next witness.empty
  let c := compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width
    tokenCount current next witness.slot0 witness.slot1 witness.repeat
  let d := compactUnifiedParserSyntaxTermClosedFormula tokenTable width
    tokenCount current next witness.slot0 witness.term
  let e := compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width
    tokenCount current next witness.slot0 witness.formula
  let f := compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width
    tokenCount current next witness.invalid
  have hselected :=
    compileCompactUnifiedParserEmptyUniformDirectOriginalContext_payloadLength_le_fixed
      tokenTable width tokenCount current next witness.empty numericBound
      bitBound hgraph hwidth htokenCount hcurrentValue hnextValue
      htokenTableSize hcurrentSize hnextSize houtputBoundarySize hnumericSize
      hbitPositive
  have hbClosed : b.freeVariables = ∅ := by
    dsimp only [b]
    unfold compactUnifiedParserEmptyClosedFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate <;>
      apply shortBinaryNumeralTerm_freeVariables_eq_empty
  let selectedAtStep : CertifiedPAContextProof
      (valuationContext b.freeVariables stepEmptyZeroValuation) b := by
    apply CertifiedPAContextProof.castContext (proof := selected)
    rw [hbClosed]
    simp [valuationContext]
  have hselectedAtStep :
      selectedAtStep.payloadLength <=
        parserEmptyUniformDirectFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [selectedAtStep]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact hselected
  let inner := compileDirectDisjunctionLeft
    (right := c ⋎ (d ⋎ (e ⋎ f))) selectedAtStep
  have hinner := compileDirectDisjunctionLeft_payloadLength_le
    (right := c ⋎ (d ⋎ (e ⋎ f))) selectedAtStep
    (parserEmptyUniformDirectFixedPayloadPolynomial numericBound bitBound)
    hselectedAtStep
  let outer := compileDirectDisjunctionRight (left := a) inner
  have houter := compileDirectDisjunctionRight_payloadLength_le
    (left := a) inner _ hinner
  simpa only [compileCompactUnifiedParserSyntaxStepFromEmptyDirectContext,
    compactUnifiedParserSyntaxStepExplicitFormula,
    syntaxStepEmptyDirectSelectedPayloadEnvelope, selected, selectedAtStep, a,
    b, c, d, e, f, inner, outer, id_eq] using houter

#print axioms
  compileCompactUnifiedParserSyntaxStepFromEmptyDirectContext_payloadLength_le_selected

theorem
    compileCompactUnifiedParserSyntaxStepFromEmptyDirectContext_payloadLength_le_closedFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserEmptyGraphRows tokenTable width tokenCount
      current next witness.empty)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (houtputBoundarySize :
      Nat.size witness.empty.targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hstepSize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxStepFormulaEnvironment tokenTable width
          tokenCount current next witness coordinate) <= bitBound) :
    (compileCompactUnifiedParserSyntaxStepFromEmptyDirectContext tokenTable
      width tokenCount current next witness numericBound bitBound hgraph
      htokenCount
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          hcurrentValue (5 : Fin 8))
      houtputBoundarySize hnumericSize).payloadLength <=
      sixRightDisjunctionPathOnePayloadEnvelope
        (compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound)
        (parserEmptyUniformDirectFixedPayloadPolynomial numericBound
          bitBound) := by
  have hselected :=
    compileCompactUnifiedParserSyntaxStepFromEmptyDirectContext_payloadLength_le_selected
      tokenTable width tokenCount current next witness numericBound bitBound
      hgraph hwidth htokenCount hcurrentValue hnextValue htokenTableSize
      hcurrentSize hnextSize houtputBoundarySize hnumericSize hbitPositive
  have hclosed :=
    compactUnifiedParserSyntaxStepExplicitFormula_freeVariables_eq_empty
      tokenTable width tokenCount current next witness
  have hcode :=
    compactUnifiedParserSyntaxStepExplicitFormula_code_length_le_fixed tokenTable
      width tokenCount current next witness bitBound hstepSize
  have hpositive :
      1 <= compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound :=
    (one_le_binaryFormulaCode_length
      (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
        current next witness)).trans hcode
  exact hselected.trans
    (sixRightDisjunctionPathOneTransparentEnvelope_le_closedGeneral
      stepEmptyZeroValuation
      (compactUnifiedParserDoneClosedFormula tokenTable width tokenCount current
        next witness.done)
      (compactUnifiedParserEmptyClosedFormula tokenTable width tokenCount current
        next witness.empty)
      (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width tokenCount
        current next witness.slot0 witness.slot1 witness.repeat)
      (compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount
        current next witness.slot0 witness.term)
      (compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width tokenCount
        current next witness.slot0 witness.formula)
      (compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width tokenCount
        current next witness.invalid)
      (parserEmptyUniformDirectFixedPayloadPolynomial numericBound bitBound)
      (compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound)
      hpositive hclosed hcode)

end FoundationCompactNumericListedDirectParserSyntaxStepEmptyDirectSelectedBounds
