import integration.FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietInvalidFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserDoneWholeUniformDirectFixedBounds
import integration.FoundationCompactPADirectConnectiveTransparentBounds

/-! # Fully fixed quiet-Done branch of one transform step -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietDoneFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridThreeRightDisjunctionClosedGeneralBounds
open FoundationCompactPAHybridFourRightDisjunctionClosedGeneralBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserDoneWholeUniformDirectAlignment
open FoundationCompactNumericListedDirectParserDoneWholeUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserDoneFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectFormulaTransformStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStepRowsFormulaFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate

private abbrev quietDoneZeroValuation : Nat -> Nat :=
  compactFormulaTransformStepRowsZeroValuation

private theorem binaryFormulaCode_left_le_and_done
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_right_le_and_done
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_left_le_or_done
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

def stepRowsQuietDoneFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    compactFormulaTransformStepRowsOuterSyntaxPolynomial bitBound
  let parserPathResource := fourRightDisjunctionPathZeroPayloadEnvelope
    syntaxResource
    (compactUnifiedParserDoneWholeUniformDirectFixedPayloadPolynomial
      numericBound bitBound)
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource parserPathResource
    (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
  threeRightDisjunctionPathZeroPayloadEnvelope syntaxResource selectedResource

noncomputable def compileCompactFormulaTransformStepRowsQuietDoneFullyFixedContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount
      numericBound bitBound : Nat)
    (hparser : CompactUnifiedParserDoneGraphRows tokenTable width tokenCount
      current.parser next.parser stepWitness.done)
    (hrows : CompactFormulaTransformOutputSameRows tokenTable width tokenCount
      current next)
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : stepWitness.done.outputCount <= numericBound)
    (hsourceBoundarySize :
      Nat.size stepWitness.done.sourceOutputBoundary <= bitBound)
    (htargetBoundarySize :
      Nat.size stepWitness.done.targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformStepRowsExplicitFormula tokenTable width
          tokenCount current next mode stepWitness consumedCount mappedHead
          witnessStart witnessFinish witnessCount).freeVariables
        quietDoneZeroValuation)
      (compactFormulaTransformStepRowsExplicitFormula tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount) := by
  let doneFormula := compactUnifiedParserDoneClosedFormula tokenTable width
    tokenCount current.parser next.parser stepWitness.done
  let emptyFormula := compactUnifiedParserEmptyClosedFormula tokenTable width
    tokenCount current.parser next.parser stepWitness.empty
  let repeatFormula := compactUnifiedParserSyntaxRepeatClosedFormula tokenTable
    width tokenCount current.parser next.parser stepWitness.slot0
    stepWitness.slot1 stepWitness.repeat
  let invalidFormula := compactUnifiedParserSyntaxInvalidClosedFormula
    tokenTable width tokenCount current.parser next.parser stepWitness.invalid
  let parserFormula :=
    doneFormula ⋎ (emptyFormula ⋎ (repeatFormula ⋎ invalidFormula))
  let rowsFormula := compactAdditiveNatListSameRowsClosedFormula tokenTable width
    tokenCount current.outputBoundary current.outputCount next.outputBoundary
    next.outputCount
  let quietFormula := parserFormula ⋏ rowsFormula
  let termFormula :=
    compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount
        current.parser next.parser stepWitness.slot0 stepWitness.term ⋏
      compactFormulaTransformTermOutputRowsClosedFormula tokenTable width
        tokenCount current next mode stepWitness.slot0 stepWitness.term.tag
        stepWitness.term.argument consumedCount witnessStart witnessFinish
        witnessCount
  let formulaFormula :=
    compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width tokenCount
        current.parser next.parser stepWitness.slot0 stepWitness.formula ⋏
      compactFormulaTransformFormulaOutputRowsClosedFormula tokenTable width
        tokenCount current next mode stepWitness.formula.tag consumedCount
        mappedHead
  let doneProof :=
    compileCompactUnifiedParserDoneUniformDirectOriginalContext tokenTable
      width tokenCount current.parser next.parser stepWitness.done numericBound
      bitBound hparser htokenCount houtputCount hsourceBoundarySize
      htargetBoundarySize hnumericSize
  let parserProof := compileDirectDisjunctionLeft
    (right := emptyFormula ⋎ (repeatFormula ⋎ invalidFormula)) doneProof
  let rowsProof :=
    (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hrows).compile
  let quietProof := compileDirectConjunction parserProof rowsProof
  let fullProof := compileDirectDisjunctionLeft
    (right := termFormula ⋎ formulaFormula) quietProof
  change CertifiedPAContextProof
    (valuationContext
      (quietFormula ⋎ (termFormula ⋎ formulaFormula)).freeVariables
      quietDoneZeroValuation)
    (quietFormula ⋎ (termFormula ⋎ formulaFormula))
  apply CertifiedPAContextProof.castContext (proof := fullProof)
  have hclosed :
      (quietFormula ⋎ (termFormula ⋎ formulaFormula)).freeVariables = ∅ := by
    rw [← show
      compactFormulaTransformStepRowsExplicitFormula tokenTable width
          tokenCount current next mode stepWitness consumedCount mappedHead
          witnessStart witnessFinish witnessCount =
        quietFormula ⋎ (termFormula ⋎ formulaFormula) from rfl]
    exact compactFormulaTransformStepRowsExplicitFormula_closed tokenTable
      width tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount
  rw [hclosed]
  simp [valuationContext]

theorem
    compileCompactFormulaTransformStepRowsQuietDoneFullyFixedContext_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount
      numericBound bitBound : Nat)
    (hparser : CompactUnifiedParserDoneGraphRows tokenTable width tokenCount
      current.parser next.parser stepWitness.done)
    (hrows : CompactFormulaTransformOutputSameRows tokenTable width tokenCount
      current next)
    (hstepEnvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount coordinate) <= bitBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : stepWitness.done.outputCount <= numericBound)
    (hcurrentOutputCount : current.outputCount <= numericBound)
    (hcurrentParserValue :
      CompactUnifiedParserStateCoordinateValueBound current.parser numericBound)
    (hnextParserValue :
      CompactUnifiedParserStateCoordinateValueBound next.parser numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentParserSize :
      CompactUnifiedParserStateCoordinateSizeBound current.parser bitBound)
    (hnextParserSize :
      CompactUnifiedParserStateCoordinateSizeBound next.parser bitBound)
    (hdoneWitnessSize :
      CompactUnifiedParserDoneWitnessCoordinateSizeBound stepWitness.done
        bitBound)
    (hcurrentOutputBoundarySize :
      Nat.size current.outputBoundary <= bitBound)
    (hnextOutputBoundarySize :
      Nat.size next.outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compileCompactFormulaTransformStepRowsQuietDoneFullyFixedContext tokenTable
      width tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount numericBound bitBound hparser
      hrows htokenCount houtputCount
      (by
        simpa [compactUnifiedParserDoneWitnessCoordinateValues] using
          hdoneWitnessSize (1 : Fin 7))
      (by
        simpa [compactUnifiedParserDoneWitnessCoordinateValues] using
          hdoneWitnessSize (4 : Fin 7))
      hnumericSize).payloadLength <=
      stepRowsQuietDoneFixedPayloadPolynomial numericBound bitBound := by
  let doneFormula := compactUnifiedParserDoneClosedFormula tokenTable width
    tokenCount current.parser next.parser stepWitness.done
  let emptyFormula := compactUnifiedParserEmptyClosedFormula tokenTable width
    tokenCount current.parser next.parser stepWitness.empty
  let repeatFormula := compactUnifiedParserSyntaxRepeatClosedFormula tokenTable
    width tokenCount current.parser next.parser stepWitness.slot0
    stepWitness.slot1 stepWitness.repeat
  let invalidFormula := compactUnifiedParserSyntaxInvalidClosedFormula
    tokenTable width tokenCount current.parser next.parser stepWitness.invalid
  let parserFormula :=
    doneFormula ⋎ (emptyFormula ⋎ (repeatFormula ⋎ invalidFormula))
  let rowsFormula := compactAdditiveNatListSameRowsClosedFormula tokenTable width
    tokenCount current.outputBoundary current.outputCount next.outputBoundary
    next.outputCount
  let quietFormula := parserFormula ⋏ rowsFormula
  let termFormula :=
    compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount
        current.parser next.parser stepWitness.slot0 stepWitness.term ⋏
      compactFormulaTransformTermOutputRowsClosedFormula tokenTable width
        tokenCount current next mode stepWitness.slot0 stepWitness.term.tag
        stepWitness.term.argument consumedCount witnessStart witnessFinish
        witnessCount
  let formulaFormula :=
    compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width tokenCount
        current.parser next.parser stepWitness.slot0 stepWitness.formula ⋏
      compactFormulaTransformFormulaOutputRowsClosedFormula tokenTable width
        tokenCount current next mode stepWitness.formula.tag consumedCount
        mappedHead
  let syntaxResource :=
    compactFormulaTransformStepRowsOuterSyntaxPolynomial bitBound
  let doneResource :=
    compactUnifiedParserDoneWholeUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  let parserPathResource := fourRightDisjunctionPathZeroPayloadEnvelope
    syntaxResource doneResource
  let rowsResource := sameRowsCompleteFullyFixedPayloadPolynomial numericBound
    bitBound
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource parserPathResource rowsResource
  let doneProof :=
    compileCompactUnifiedParserDoneUniformDirectOriginalContext tokenTable
      width tokenCount current.parser next.parser stepWitness.done numericBound
      bitBound hparser htokenCount houtputCount
      (by
        simpa [compactUnifiedParserDoneWitnessCoordinateValues] using
          hdoneWitnessSize (1 : Fin 7))
      (by
        simpa [compactUnifiedParserDoneWitnessCoordinateValues] using
          hdoneWitnessSize (4 : Fin 7))
      hnumericSize
  let parserProof := compileDirectDisjunctionLeft
    (right := emptyFormula ⋎ (repeatFormula ⋎ invalidFormula)) doneProof
  let rowsCertificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hrows
  let rowsProof := rowsCertificate.compile
  let quietProof := compileDirectConjunction parserProof rowsProof
  let fullProof := compileDirectDisjunctionLeft
    (right := termFormula ⋎ formulaFormula) quietProof
  have hdone :=
    compileCompactUnifiedParserDoneUniformDirectOriginalContext_payloadLength_le_fixed
      tokenTable width tokenCount current.parser next.parser stepWitness.done
      numericBound bitBound hparser hwidth htokenCount houtputCount
      hcurrentParserValue hnextParserValue htokenTableSize hcurrentParserSize
      hnextParserSize hdoneWitnessSize hnumericSize hbitPositive
  have hrowsTransparent :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hrows
  have hrowsFixed :=
    compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_fullyFixed tokenTable
      width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount numericBound bitBound hrows hwidth
      htokenCount hcurrentOutputCount htokenTableSize
      hcurrentOutputBoundarySize hnextOutputBoundarySize hnumericSize
  have hrowsCertificate :
      hybridFormulaStructuralPayloadBound rowsCertificate <= rowsResource :=
    hrowsTransparent.trans hrowsFixed
  have hrowsProof : rowsProof.payloadLength <= rowsResource :=
    (compile_payloadLength_le_hybridFormulaStructuralPayloadBound
      rowsCertificate).trans hrowsCertificate
  have hfullClosed := compactFormulaTransformStepRowsExplicitFormula_closed
    tokenTable width tokenCount current next mode stepWitness consumedCount
    mappedHead witnessStart witnessFinish witnessCount
  have hfullCode :=
    compactFormulaTransformStepRowsExplicitFormula_code_length_le_fixed
      tokenTable width tokenCount current next mode stepWitness consumedCount
      mappedHead witnessStart witnessFinish witnessCount bitBound
      hstepEnvironmentSize
  have hfullAlignment :
      compactFormulaTransformStepRowsExplicitFormula tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount =
        quietFormula ⋎ (termFormula ⋎ formulaFormula) := by
    rfl
  have hclosed :
      (quietFormula ⋎ (termFormula ⋎ formulaFormula)).freeVariables = ∅ := by
    rw [← hfullAlignment]
    exact hfullClosed
  have hcode :
      (binaryFormulaCode
        (quietFormula ⋎ (termFormula ⋎ formulaFormula))).length <=
        syntaxResource := by
    rw [← hfullAlignment]
    exact hfullCode
  have houterClosed := Finset.union_eq_empty.mp (by
    simpa only [LO.FirstOrder.Semiformula.freeVariables_or] using hclosed)
  have hquietPartsClosed := Finset.union_eq_empty.mp (by
    simpa only [quietFormula,
      LO.FirstOrder.Semiformula.freeVariables_and] using houterClosed.1)
  have hquietCode :=
    (binaryFormulaCode_left_le_or_done quietFormula
      (termFormula ⋎ formulaFormula)).trans hcode
  have hparserCode :=
    (binaryFormulaCode_left_le_and_done parserFormula rowsFormula).trans
      hquietCode
  have hrowsCode :=
    (binaryFormulaCode_right_le_and_done parserFormula rowsFormula).trans
      hquietCode
  have hsyntaxPositive :=
    compactFormulaTransformStepRowsOuterSyntaxPolynomial_positive bitBound
  have hparserRaw := compileDirectDisjunctionLeft_payloadLength_le
    (right := emptyFormula ⋎ (repeatFormula ⋎ invalidFormula)) doneProof
    doneResource hdone
  have hparserGeneral :=
    fourRightDisjunctionPathZeroTransparentEnvelope_le_closedGeneral
      quietDoneZeroValuation doneFormula emptyFormula repeatFormula
      invalidFormula doneResource syntaxResource hsyntaxPositive
      hquietPartsClosed.1 hparserCode
  have hparser : parserProof.payloadLength <= parserPathResource :=
    hparserRaw.trans hparserGeneral
  have hquietRaw := compileDirectConjunction_payloadLength_le parserProof
    rowsProof parserPathResource rowsResource hparser hrowsProof
  have hquietGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      quietDoneZeroValuation parserFormula rowsFormula parserPathResource
      rowsResource syntaxResource hsyntaxPositive hquietPartsClosed.1
      hquietPartsClosed.2 hparserCode hrowsCode hquietCode
  have hquiet : quietProof.payloadLength <= selectedResource :=
    hquietRaw.trans hquietGeneral
  have hfullRaw := compileDirectDisjunctionLeft_payloadLength_le
    (right := termFormula ⋎ formulaFormula) quietProof selectedResource hquiet
  have hfullGeneral :=
    threeRightDisjunctionPathZeroTransparentEnvelope_le_closedGeneral
      quietDoneZeroValuation quietFormula termFormula formulaFormula
      selectedResource syntaxResource hsyntaxPositive hclosed hcode
  unfold compileCompactFormulaTransformStepRowsQuietDoneFullyFixedContext
    stepRowsQuietDoneFixedPayloadPolynomial
  dsimp only [doneFormula, emptyFormula, repeatFormula, invalidFormula,
    parserFormula, rowsFormula, quietFormula, termFormula, formulaFormula,
    syntaxResource, doneResource, parserPathResource, rowsResource,
    selectedResource, doneProof, parserProof, rowsCertificate, rowsProof,
    quietProof, fullProof]
  exact hfullRaw.trans hfullGeneral

#print axioms
  compileCompactFormulaTransformStepRowsQuietDoneFullyFixedContext_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietDoneFullyFixedBounds
