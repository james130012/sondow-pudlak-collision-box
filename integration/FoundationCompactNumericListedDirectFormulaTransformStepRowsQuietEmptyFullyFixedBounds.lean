import integration.FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietDoneFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserEmptyUniformDirectOriginalFixedBounds

/-! # Fully fixed quiet-Empty branch of one transform step -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietEmptyFullyFixedBounds

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
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyFormula
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyUniformDirectAlignment
open FoundationCompactNumericListedDirectParserEmptyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserEmptyUniformDirectOriginalFixedBounds
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

private abbrev quietEmptyZeroValuation : Nat -> Nat :=
  compactFormulaTransformStepRowsZeroValuation

private theorem binaryFormulaCode_left_le_and_empty
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_right_le_and_empty
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_left_le_or_empty
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

def stepRowsQuietEmptyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    compactFormulaTransformStepRowsOuterSyntaxPolynomial bitBound
  let parserPathResource := fourRightDisjunctionPathOnePayloadEnvelope
    syntaxResource
    (parserEmptyUniformDirectFixedPayloadPolynomial numericBound bitBound)
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource parserPathResource
    (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
  threeRightDisjunctionPathZeroPayloadEnvelope syntaxResource selectedResource

noncomputable def compileCompactFormulaTransformStepRowsQuietEmptyFullyFixedContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount
      numericBound bitBound : Nat)
    (hparser : CompactUnifiedParserEmptyGraphRows tokenTable width tokenCount
      current.parser next.parser stepWitness.empty)
    (hrows : CompactFormulaTransformOutputSameRows tokenTable width tokenCount
      current next)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentTokensCount : current.parser.tokensCount <= numericBound)
    (houtputBoundarySize :
      Nat.size stepWitness.empty.targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformStepRowsExplicitFormula tokenTable width
          tokenCount current next mode stepWitness consumedCount mappedHead
          witnessStart witnessFinish witnessCount).freeVariables
        quietEmptyZeroValuation)
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
  let emptyProof :=
    compileCompactUnifiedParserEmptyUniformDirectOriginalContext tokenTable
      width tokenCount current.parser next.parser stepWitness.empty numericBound
      bitBound hparser htokenCount hcurrentTokensCount houtputBoundarySize
      hnumericSize
  let parserInner := compileDirectDisjunctionLeft
    (right := repeatFormula ⋎ invalidFormula) emptyProof
  let parserProof := compileDirectDisjunctionRight
    (left := doneFormula) parserInner
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
      quietEmptyZeroValuation)
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
    compileCompactFormulaTransformStepRowsQuietEmptyFullyFixedContext_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount
      numericBound bitBound : Nat)
    (hparser : CompactUnifiedParserEmptyGraphRows tokenTable width tokenCount
      current.parser next.parser stepWitness.empty)
    (hrows : CompactFormulaTransformOutputSameRows tokenTable width tokenCount
      current next)
    (hstepEnvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount coordinate) <= bitBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
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
    (houtputBoundarySize :
      Nat.size stepWitness.empty.targetOutputBoundary <= bitBound)
    (hcurrentOutputBoundarySize :
      Nat.size current.outputBoundary <= bitBound)
    (hnextOutputBoundarySize :
      Nat.size next.outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compileCompactFormulaTransformStepRowsQuietEmptyFullyFixedContext
      tokenTable width tokenCount current next mode stepWitness consumedCount
      mappedHead witnessStart witnessFinish witnessCount numericBound bitBound
      hparser hrows htokenCount
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          hcurrentParserValue (5 : Fin 8))
      houtputBoundarySize hnumericSize).payloadLength <=
      stepRowsQuietEmptyFixedPayloadPolynomial numericBound bitBound := by
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
  let emptyResource := parserEmptyUniformDirectFixedPayloadPolynomial
    numericBound bitBound
  let parserPathResource := fourRightDisjunctionPathOnePayloadEnvelope
    syntaxResource emptyResource
  let rowsResource := sameRowsCompleteFullyFixedPayloadPolynomial numericBound
    bitBound
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource parserPathResource rowsResource
  let emptyProof :=
    compileCompactUnifiedParserEmptyUniformDirectOriginalContext tokenTable
      width tokenCount current.parser next.parser stepWitness.empty numericBound
      bitBound hparser htokenCount
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          hcurrentParserValue (5 : Fin 8))
      houtputBoundarySize hnumericSize
  let parserInner := compileDirectDisjunctionLeft
    (right := repeatFormula ⋎ invalidFormula) emptyProof
  let parserProof := compileDirectDisjunctionRight
    (left := doneFormula) parserInner
  let rowsCertificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hrows
  let rowsProof := rowsCertificate.compile
  let quietProof := compileDirectConjunction parserProof rowsProof
  let fullProof := compileDirectDisjunctionLeft
    (right := termFormula ⋎ formulaFormula) quietProof
  have hempty :=
    compileCompactUnifiedParserEmptyUniformDirectOriginalContext_payloadLength_le_fixed
      tokenTable width tokenCount current.parser next.parser stepWitness.empty
      numericBound bitBound hparser hwidth htokenCount hcurrentParserValue
      hnextParserValue htokenTableSize hcurrentParserSize hnextParserSize
      houtputBoundarySize hnumericSize hbitPositive
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
    (binaryFormulaCode_left_le_or_empty quietFormula
      (termFormula ⋎ formulaFormula)).trans hcode
  have hparserCode :=
    (binaryFormulaCode_left_le_and_empty parserFormula rowsFormula).trans
      hquietCode
  have hrowsCode :=
    (binaryFormulaCode_right_le_and_empty parserFormula rowsFormula).trans
      hquietCode
  have hsyntaxPositive :=
    compactFormulaTransformStepRowsOuterSyntaxPolynomial_positive bitBound
  have hparserInner := compileDirectDisjunctionLeft_payloadLength_le
    (right := repeatFormula ⋎ invalidFormula) emptyProof emptyResource hempty
  have hparserRaw := compileDirectDisjunctionRight_payloadLength_le
    (left := doneFormula) parserInner _ hparserInner
  have hparserGeneral :=
    fourRightDisjunctionPathOneTransparentEnvelope_le_closedGeneral
      quietEmptyZeroValuation doneFormula emptyFormula repeatFormula
      invalidFormula emptyResource syntaxResource hsyntaxPositive
      hquietPartsClosed.1 hparserCode
  have hparser : parserProof.payloadLength <= parserPathResource :=
    hparserRaw.trans hparserGeneral
  have hquietRaw := compileDirectConjunction_payloadLength_le parserProof
    rowsProof parserPathResource rowsResource hparser hrowsProof
  have hquietGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      quietEmptyZeroValuation parserFormula rowsFormula parserPathResource
      rowsResource syntaxResource hsyntaxPositive hquietPartsClosed.1
      hquietPartsClosed.2 hparserCode hrowsCode hquietCode
  have hquiet : quietProof.payloadLength <= selectedResource :=
    hquietRaw.trans hquietGeneral
  have hfullRaw := compileDirectDisjunctionLeft_payloadLength_le
    (right := termFormula ⋎ formulaFormula) quietProof selectedResource hquiet
  have hfullGeneral :=
    threeRightDisjunctionPathZeroTransparentEnvelope_le_closedGeneral
      quietEmptyZeroValuation quietFormula termFormula formulaFormula
      selectedResource syntaxResource hsyntaxPositive hclosed hcode
  unfold compileCompactFormulaTransformStepRowsQuietEmptyFullyFixedContext
    stepRowsQuietEmptyFixedPayloadPolynomial
  dsimp only [doneFormula, emptyFormula, repeatFormula, invalidFormula,
    parserFormula, rowsFormula, quietFormula, termFormula, formulaFormula,
    syntaxResource, emptyResource, parserPathResource, rowsResource,
    selectedResource, emptyProof, parserInner, parserProof, rowsCertificate,
    rowsProof, quietProof, fullProof]
  exact hfullRaw.trans hfullGeneral

#print axioms
  compileCompactFormulaTransformStepRowsQuietEmptyFullyFixedContext_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietEmptyFullyFixedBounds
