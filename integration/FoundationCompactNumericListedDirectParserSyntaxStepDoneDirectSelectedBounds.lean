import integration.FoundationCompactNumericListedDirectParserDoneWholeUniformDirectFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxStepCleanGraphCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxStepFormulaSyntaxFixedBounds
import integration.FoundationCompactPADirectConnectiveTransparentBounds
import integration.FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactListedProofHonestWeight

/-! # Direct selected-Done path inside the six-way syntax step -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxStepDoneDirectSelectedBounds

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactCertifiedContextProof
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserDoneWholeUniformDirectAlignment
open FoundationCompactNumericListedDirectParserDoneWholeUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserDoneFormulaEnvironmentAlignment
open FoundationCompactNumericListedDirectParserDoneFormulaSyntaxFixedBounds
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

private abbrev stepDoneZeroValuation : Nat -> Nat :=
  compactUnifiedParserSyntaxStepZeroValuation

def syntaxStepDoneDirectSelectedPayloadEnvelope
    (a b c d e f : ValuationFormula) (resource : Nat) : Nat :=
  transparentHybridDisjunctionLeftPayloadEnvelope stepDoneZeroValuation a
    (b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) resource

noncomputable def compileCompactUnifiedParserSyntaxStepFromDoneDirectContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserDoneGraphRows tokenTable width tokenCount
      current next witness.done)
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : witness.done.outputCount <= numericBound)
    (hsourceBoundarySize :
      Nat.size witness.done.sourceOutputBoundary <= bitBound)
    (htargetBoundarySize :
      Nat.size witness.done.targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width
          tokenCount current next witness).freeVariables stepDoneZeroValuation)
      (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width
        tokenCount current next witness) := by
  let selected :=
    compileCompactUnifiedParserDoneUniformDirectOriginalContext tokenTable
      width tokenCount current next witness.done numericBound bitBound hgraph
      htokenCount houtputCount hsourceBoundarySize htargetBoundarySize
      hnumericSize
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
  have haClosed : a.freeVariables = ∅ := by
    simpa only [a] using
      compactUnifiedParserDoneClosedFormula_freeVariables_eq_empty tokenTable
        width tokenCount current next witness.done
  let selectedAtStep : CertifiedPAContextProof
      (valuationContext a.freeVariables stepDoneZeroValuation) a := by
    apply CertifiedPAContextProof.castContext (proof := selected)
    rw [haClosed]
    simp [valuationContext]
  let outer := compileDirectDisjunctionLeft
    (right := b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) selectedAtStep
  simpa only [compactUnifiedParserSyntaxStepExplicitFormula, a, b, c, d, e, f,
    selected, selectedAtStep, outer] using outer

theorem
    compileCompactUnifiedParserSyntaxStepFromDoneDirectContext_payloadLength_le_selected
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserDoneGraphRows tokenTable width tokenCount
      current next witness.done)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : witness.done.outputCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (hdoneWitnessSize :
      CompactUnifiedParserDoneWitnessCoordinateSizeBound witness.done bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compileCompactUnifiedParserSyntaxStepFromDoneDirectContext tokenTable
      width tokenCount current next witness numericBound bitBound hgraph
      htokenCount houtputCount
      (by
        simpa [compactUnifiedParserDoneWitnessCoordinateValues] using
          hdoneWitnessSize (1 : Fin 7))
      (by
        simpa [compactUnifiedParserDoneWitnessCoordinateValues] using
          hdoneWitnessSize (4 : Fin 7))
      hnumericSize).payloadLength <=
      syntaxStepDoneDirectSelectedPayloadEnvelope
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
        (compactUnifiedParserDoneWholeUniformDirectFixedPayloadPolynomial
          numericBound bitBound) := by
  let selected :=
    compileCompactUnifiedParserDoneUniformDirectOriginalContext tokenTable
      width tokenCount current next witness.done numericBound bitBound hgraph
      htokenCount houtputCount
      (by
        simpa [compactUnifiedParserDoneWitnessCoordinateValues] using
          hdoneWitnessSize (1 : Fin 7))
      (by
        simpa [compactUnifiedParserDoneWitnessCoordinateValues] using
          hdoneWitnessSize (4 : Fin 7))
      hnumericSize
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
    compileCompactUnifiedParserDoneUniformDirectOriginalContext_payloadLength_le_fixed
      tokenTable width tokenCount current next witness.done numericBound
      bitBound hgraph hwidth htokenCount houtputCount hcurrentValue hnextValue
      htokenTableSize hcurrentSize hnextSize hdoneWitnessSize hnumericSize
      hbitPositive
  have haClosed : a.freeVariables = ∅ := by
    simpa only [a] using
      compactUnifiedParserDoneClosedFormula_freeVariables_eq_empty tokenTable
        width tokenCount current next witness.done
  let selectedAtStep : CertifiedPAContextProof
      (valuationContext a.freeVariables stepDoneZeroValuation) a := by
    apply CertifiedPAContextProof.castContext (proof := selected)
    rw [haClosed]
    simp [valuationContext]
  have hselectedAtStep :
      selectedAtStep.payloadLength <=
        compactUnifiedParserDoneWholeUniformDirectFixedPayloadPolynomial
          numericBound bitBound := by
    dsimp only [selectedAtStep]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact hselected
  let outer := compileDirectDisjunctionLeft
    (right := b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) selectedAtStep
  have houter := compileDirectDisjunctionLeft_payloadLength_le
    (right := b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) selectedAtStep
    (compactUnifiedParserDoneWholeUniformDirectFixedPayloadPolynomial
      numericBound bitBound) hselectedAtStep
  simpa only [compileCompactUnifiedParserSyntaxStepFromDoneDirectContext,
    compactUnifiedParserSyntaxStepExplicitFormula,
    syntaxStepDoneDirectSelectedPayloadEnvelope, selected, selectedAtStep, a,
    b, c, d, e, f, outer, id_eq] using houter

theorem
    compileCompactUnifiedParserSyntaxStepFromDoneDirectContext_payloadLength_le_closedFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserDoneGraphRows tokenTable width tokenCount
      current next witness.done)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : witness.done.outputCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (hdoneWitnessSize :
      CompactUnifiedParserDoneWitnessCoordinateSizeBound witness.done bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hstepSize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxStepFormulaEnvironment tokenTable width
          tokenCount current next witness coordinate) <= bitBound) :
    (compileCompactUnifiedParserSyntaxStepFromDoneDirectContext tokenTable width
      tokenCount current next witness numericBound bitBound hgraph htokenCount
      houtputCount
      (by
        simpa [compactUnifiedParserDoneWitnessCoordinateValues] using
          hdoneWitnessSize (1 : Fin 7))
      (by
        simpa [compactUnifiedParserDoneWitnessCoordinateValues] using
          hdoneWitnessSize (4 : Fin 7))
      hnumericSize).payloadLength <=
      sixRightDisjunctionPathZeroPayloadEnvelope
        (compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound)
        (compactUnifiedParserDoneWholeUniformDirectFixedPayloadPolynomial
          numericBound bitBound) := by
  have hselected :=
    compileCompactUnifiedParserSyntaxStepFromDoneDirectContext_payloadLength_le_selected
      tokenTable width tokenCount current next witness numericBound bitBound
      hgraph hwidth htokenCount houtputCount hcurrentValue hnextValue
      htokenTableSize hcurrentSize hnextSize hdoneWitnessSize hnumericSize
      hbitPositive
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
    (sixRightDisjunctionPathZeroTransparentEnvelope_le_closedGeneral
      stepDoneZeroValuation
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
      (compactUnifiedParserDoneWholeUniformDirectFixedPayloadPolynomial
        numericBound bitBound)
      (compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound)
      hpositive hclosed hcode)

end FoundationCompactNumericListedDirectParserSyntaxStepDoneDirectSelectedBounds
