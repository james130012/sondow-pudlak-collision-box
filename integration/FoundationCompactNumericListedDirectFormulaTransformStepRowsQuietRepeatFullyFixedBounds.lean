import integration.FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietEmptyFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatFullSelectedFixedBounds
import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds

/-! # Fully fixed quiet-Repeat branch of one transform step -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietRepeatFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactPAHybridThreeRightDisjunctionClosedGeneralBounds
open FoundationCompactPAHybridFourRightDisjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatBranchFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatZeroBranchFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatPositiveBranchFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatFullGraphFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatFullSelectedFixedBounds
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

private abbrev quietRepeatZeroValuation : Nat -> Nat :=
  compactFormulaTransformStepRowsZeroValuation

private abbrev QuietRepeatHybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate quietRepeatZeroValuation
    formula

private theorem binaryFormulaCode_left_le_and_repeat
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_right_le_and_repeat
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_left_le_or_repeat
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

def stepRowsQuietRepeatSelectedResource
    (tokenCount numericBound bitBound : Nat) : Nat :=
  max
    (repeatFullGraphPayloadEnvelope tokenCount numericBound bitBound
      (repeatSelectedBranchPayloadEnvelope bitBound
        (repeatZeroBranchPayloadEnvelope numericBound bitBound)))
    (repeatFullGraphPayloadEnvelope tokenCount numericBound bitBound
      (repeatSelectedBranchPayloadEnvelope bitBound
        (repeatPositiveBranchPayloadEnvelope numericBound bitBound)))

def stepRowsQuietRepeatFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    compactFormulaTransformStepRowsOuterSyntaxPolynomial bitBound
  let parserPathResource := fourRightDisjunctionPathTwoPayloadEnvelope
    syntaxResource
    (stepRowsQuietRepeatSelectedResource tokenCount numericBound bitBound)
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource parserPathResource
    (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
  threeRightDisjunctionPathZeroPayloadEnvelope syntaxResource selectedResource

noncomputable def compactFormulaTransformStepRowsQuietRepeatFromSelected
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (repeatCertificate : QuietRepeatHybridCertificate
      (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width tokenCount
        current.parser next.parser stepWitness.slot0 stepWitness.slot1
        stepWitness.repeat))
    (hrows : CompactFormulaTransformOutputSameRows tokenTable width tokenCount
      current next) :
    QuietRepeatHybridCertificate
      (compactFormulaTransformStepRowsExplicitFormula tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount) :=
  .disjunctionLeft (.conjunction
    (.disjunctionRight (.disjunctionRight (.disjunctionLeft
      repeatCertificate)))
    (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hrows))

theorem
    compactFormulaTransformStepRowsQuietRepeatFromSelected_structuralPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount
      repeatResource numericBound bitBound : Nat)
    (repeatCertificate : QuietRepeatHybridCertificate
      (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width tokenCount
        current.parser next.parser stepWitness.slot0 stepWitness.slot1
        stepWitness.repeat))
    (hrows : CompactFormulaTransformOutputSameRows tokenTable width tokenCount
      current next)
    (hrepeat : hybridFormulaStructuralPayloadBound repeatCertificate <=
      repeatResource)
    (hrepeatFixed : repeatResource <=
      stepRowsQuietRepeatSelectedResource tokenCount numericBound bitBound)
    (hstepEnvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount coordinate) <= bitBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentOutputCount : current.outputCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentOutputBoundarySize :
      Nat.size current.outputBoundary <= bitBound)
    (hnextOutputBoundarySize :
      Nat.size next.outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformStepRowsQuietRepeatFromSelected tokenTable width
          tokenCount current next mode stepWitness consumedCount mappedHead
          witnessStart witnessFinish witnessCount repeatCertificate hrows) <=
      stepRowsQuietRepeatFixedPayloadPolynomial tokenCount numericBound
        bitBound := by
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
  let repeatFixedResource :=
    stepRowsQuietRepeatSelectedResource tokenCount numericBound bitBound
  let parserPathResource := fourRightDisjunctionPathTwoPayloadEnvelope
    syntaxResource repeatFixedResource
  let rowsResource := sameRowsCompleteFullyFixedPayloadPolynomial numericBound
    bitBound
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource parserPathResource rowsResource
  let parserInner1 :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := invalidFormula) repeatCertificate
  let parserInner2 :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := emptyFormula) parserInner1
  let parserCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := doneFormula) parserInner2
  let rowsCertificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hrows
  let selectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      parserCertificate rowsCertificate
  have hrepeatResource :
      hybridFormulaStructuralPayloadBound repeatCertificate <=
        repeatFixedResource := hrepeat.trans hrepeatFixed
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
  have hrowsResource :
      hybridFormulaStructuralPayloadBound rowsCertificate <= rowsResource :=
    hrowsTransparent.trans hrowsFixed
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
    (binaryFormulaCode_left_le_or_repeat quietFormula
      (termFormula ⋎ formulaFormula)).trans hcode
  have hparserCode :=
    (binaryFormulaCode_left_le_and_repeat parserFormula rowsFormula).trans
      hquietCode
  have hrowsCode :=
    (binaryFormulaCode_right_le_and_repeat parserFormula rowsFormula).trans
      hquietCode
  have hsyntaxPositive :=
    compactFormulaTransformStepRowsOuterSyntaxPolynomial_positive bitBound
  have hparserRaw1 := transparentHybridDisjunctionLeftPayloadBound_le
    (right := invalidFormula) repeatCertificate repeatFixedResource
    hrepeatResource
  have hparserRaw2 := transparentHybridDisjunctionRightPayloadBound_le
    (left := emptyFormula) parserInner1 _ hparserRaw1
  have hparserRaw3 := transparentHybridDisjunctionRightPayloadBound_le
    (left := doneFormula) parserInner2 _ hparserRaw2
  have hparserGeneral :=
    fourRightDisjunctionPathTwoTransparentEnvelope_le_closedGeneral
      quietRepeatZeroValuation doneFormula emptyFormula repeatFormula
      invalidFormula repeatFixedResource syntaxResource hsyntaxPositive
      hquietPartsClosed.1 hparserCode
  have hparserResource :
      hybridFormulaStructuralPayloadBound parserCertificate <=
        parserPathResource := hparserRaw3.trans hparserGeneral
  have hselected :
      hybridFormulaStructuralPayloadBound selectedCertificate <=
        selectedResource := by
    exact checkedHybridConjunctionPayloadBound_le_closedGeneral
      parserCertificate rowsCertificate parserPathResource rowsResource
      syntaxResource hparserResource hrowsResource hsyntaxPositive
      hquietPartsClosed.1 hquietPartsClosed.2 hparserCode hrowsCode hquietCode
  have houter := transparentHybridDisjunctionLeftPayloadBound_le
    (right := termFormula ⋎ formulaFormula) selectedCertificate
    selectedResource hselected
  have hgeneral :=
    threeRightDisjunctionPathZeroTransparentEnvelope_le_closedGeneral
      quietRepeatZeroValuation quietFormula termFormula formulaFormula
      selectedResource syntaxResource hsyntaxPositive hclosed hcode
  unfold compactFormulaTransformStepRowsQuietRepeatFromSelected
    stepRowsQuietRepeatFixedPayloadPolynomial
  dsimp only [doneFormula, emptyFormula, repeatFormula, invalidFormula,
    parserFormula, rowsFormula, quietFormula, termFormula, formulaFormula,
    syntaxResource, repeatFixedResource, parserPathResource, rowsResource,
    selectedResource, parserInner1, parserInner2, parserCertificate,
    rowsCertificate, selectedCertificate]
  exact houter.trans hgeneral

noncomputable def compactFormulaTransformStepRowsQuietRepeatFullyFixedCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (hparser : CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount
      current.parser next.parser stepWitness.slot0 stepWitness.slot1
      stepWitness.repeat)
    (hrows : CompactFormulaTransformOutputSameRows tokenTable width tokenCount
      current next) :
    QuietRepeatHybridCertificate
      (compactFormulaTransformStepRowsExplicitFormula tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount) := by
  let branchData :=
    compactSyntaxRepeatCheckedBranchDataOfGraph tokenTable width tokenCount
      next.parser stepWitness.slot0 stepWitness.slot1 stepWitness.repeat
      hparser.2.2.2.2
  rcases branchData with ⟨hrepeatZero, hsame⟩ |
    ⟨hrepeatSuccessor, hdrop, htaskZero, htaskOne⟩
  ·
    let branchCertificate :=
      repeatZeroOriginalBranchCertificate tokenTable width tokenCount
        next.parser stepWitness.slot0 stepWitness.slot1 stepWitness.repeat
        hrepeatZero hsame
    let selected :=
      repeatFullGraphCertificate tokenTable width tokenCount current.parser
        next.parser stepWitness.slot0 stepWitness.slot1 stepWitness.repeat
        hparser.1 hparser.2.1 hparser.2.2.1 hparser.2.2.2.1
        branchCertificate
    exact compactFormulaTransformStepRowsQuietRepeatFromSelected tokenTable
      width tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount selected hrows
  ·
    let branchCertificate :=
      repeatPositiveOriginalBranchCertificate tokenTable width tokenCount
        next.parser stepWitness.slot0 stepWitness.slot1 stepWitness.repeat
        hrepeatSuccessor hdrop htaskZero htaskOne
    let selected :=
      repeatFullGraphCertificate tokenTable width tokenCount current.parser
        next.parser stepWitness.slot0 stepWitness.slot1 stepWitness.repeat
        hparser.1 hparser.2.1 hparser.2.2.1 hparser.2.2.2.1
        branchCertificate
    exact compactFormulaTransformStepRowsQuietRepeatFromSelected tokenTable
      width tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount selected hrows

theorem
    compactFormulaTransformStepRowsQuietRepeatFullyFixedCertificate_structuralPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount
      numericBound bitBound : Nat)
    (hparser : CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount
      current.parser next.parser stepWitness.slot0 stepWitness.slot1
      stepWitness.repeat)
    (hrows : CompactFormulaTransformOutputSameRows tokenTable width tokenCount
      current next)
    (hstepEnvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount coordinate) <= bitBound)
    (hrepeatEnvironmentSize : forall coordinate : Fin 25,
      Nat.size
        (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf tokenTable width
          tokenCount current.parser next.parser stepWitness.slot0
          stepWitness.slot1 stepWitness.repeat coordinate) <= bitBound)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcurrentTasksFinishValue : current.parser.tasksFinish <= numericBound)
    (hnextTasksFinishValue : next.parser.tasksFinish <= numericBound)
    (hcurrentTokensCountValue : current.parser.tokensCount <= numericBound)
    (hcurrentTasksCountValue : current.parser.tasksCount <= numericBound)
    (hnextTasksCountValue : next.parser.tasksCount <= numericBound)
    (htailCountValue : stepWitness.repeat.tailCount <= numericBound)
    (hcurrentOutputCountValue : current.outputCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentTasksFinishSize : Nat.size current.parser.tasksFinish <= bitBound)
    (hcurrentFinishSize : Nat.size current.parser.finish <= bitBound)
    (hnextTasksFinishSize : Nat.size next.parser.tasksFinish <= bitBound)
    (hnextFinishSize : Nat.size next.parser.finish <= bitBound)
    (hcurrentTokensBoundarySize :
      Nat.size current.parser.tokensBoundary <= bitBound)
    (hnextTokensBoundarySize :
      Nat.size next.parser.tokensBoundary <= bitBound)
    (hcurrentTasksBoundarySize :
      Nat.size current.parser.tasksBoundary <= bitBound)
    (hnextTasksBoundarySize :
      Nat.size next.parser.tasksBoundary <= bitBound)
    (hnextTasksCountSize : Nat.size next.parser.tasksCount <= bitBound)
    (htailBoundarySize :
      Nat.size stepWitness.repeat.tailBoundary <= bitBound)
    (hbinderSize : Nat.size stepWitness.slot0 <= bitBound)
    (hrepeatSize : Nat.size stepWitness.slot1 <= bitBound)
    (hdecrementedSize :
      Nat.size stepWitness.repeat.decrementedCount <= bitBound)
    (hcurrentOutputBoundarySize :
      Nat.size current.outputBoundary <= bitBound)
    (hnextOutputBoundarySize :
      Nat.size next.outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformStepRowsQuietRepeatFullyFixedCertificate
          tokenTable width tokenCount current next mode stepWitness
          consumedCount mappedHead witnessStart witnessFinish witnessCount
          hparser hrows) <=
      stepRowsQuietRepeatFixedPayloadPolynomial tokenCount numericBound
        bitBound := by
  let branchData :=
    compactSyntaxRepeatCheckedBranchDataOfGraph tokenTable width tokenCount
      next.parser stepWitness.slot0 stepWitness.slot1 stepWitness.repeat
      hparser.2.2.2.2
  rcases hbranch : branchData with ⟨hrepeatZero, hsame⟩ |
    ⟨hrepeatSuccessor, hdrop, htaskZero, htaskOne⟩
  ·
    let branchCertificate :=
      repeatZeroOriginalBranchCertificate tokenTable width tokenCount
        next.parser stepWitness.slot0 stepWitness.slot1 stepWitness.repeat
        hrepeatZero hsame
    let selected :=
      repeatFullGraphCertificate tokenTable width tokenCount current.parser
        next.parser stepWitness.slot0 stepWitness.slot1 stepWitness.repeat
        hparser.1 hparser.2.1 hparser.2.2.1 hparser.2.2.2.1
        branchCertificate
    have hselectedRaw :=
      repeatZeroFullGraphCertificate_structuralPayloadBound_le_fixed tokenTable
        width tokenCount current.parser next.parser stepWitness.slot0
        stepWitness.slot1 stepWitness.repeat numericBound bitBound hparser.1
        hparser.2.1 hparser.2.2.1 hparser.2.2.2.1 hrepeatZero hsame
        hrepeatEnvironmentSize hwidthValue htokenCountValue
        hcurrentTasksFinishValue hnextTasksFinishValue
        hcurrentTokensCountValue hcurrentTasksCountValue htailCountValue
        htableSize hwidthSize htokenCountSize hcurrentTasksFinishSize
        hcurrentFinishSize hnextTasksFinishSize hnextFinishSize
        hcurrentTokensBoundarySize hnextTokensBoundarySize
        hcurrentTasksBoundarySize hnextTasksBoundarySize htailBoundarySize
        hbinderSize hrepeatSize hnumericSize
    have hpath :=
      compactFormulaTransformStepRowsQuietRepeatFromSelected_structuralPayloadBound_le
        tokenTable width tokenCount current next mode stepWitness consumedCount
        mappedHead witnessStart witnessFinish witnessCount
        (repeatFullGraphPayloadEnvelope tokenCount numericBound bitBound
          (repeatSelectedBranchPayloadEnvelope bitBound
            (repeatZeroBranchPayloadEnvelope numericBound bitBound)))
        numericBound bitBound selected hrows hselectedRaw (Nat.le_max_left _ _)
        hstepEnvironmentSize hwidthValue htokenCountValue
        hcurrentOutputCountValue htableSize hcurrentOutputBoundarySize
        hnextOutputBoundarySize hnumericSize
    unfold compactFormulaTransformStepRowsQuietRepeatFullyFixedCertificate
    dsimp only [branchData] at hbranch
    rw [hbranch]
    simpa only [branchCertificate, selected] using hpath
  ·
    let branchCertificate :=
      repeatPositiveOriginalBranchCertificate tokenTable width tokenCount
        next.parser stepWitness.slot0 stepWitness.slot1 stepWitness.repeat
        hrepeatSuccessor hdrop htaskZero htaskOne
    let selected :=
      repeatFullGraphCertificate tokenTable width tokenCount current.parser
        next.parser stepWitness.slot0 stepWitness.slot1 stepWitness.repeat
        hparser.1 hparser.2.1 hparser.2.2.1 hparser.2.2.2.1
        branchCertificate
    have hselectedRaw :=
      repeatPositiveFullGraphCertificate_structuralPayloadBound_le_fixed
        tokenTable width tokenCount current.parser next.parser
        stepWitness.slot0 stepWitness.slot1 stepWitness.repeat numericBound
        bitBound hparser.1 hparser.2.1 hparser.2.2.1 hparser.2.2.2.1
        hrepeatSuccessor hdrop htaskZero htaskOne hrepeatEnvironmentSize
        hwidthValue htokenCountValue hcurrentTasksFinishValue
        hnextTasksFinishValue hcurrentTokensCountValue hcurrentTasksCountValue
        hnextTasksCountValue htailCountValue htableSize hwidthSize
        htokenCountSize hcurrentTasksFinishSize hcurrentFinishSize
        hnextTasksFinishSize hnextFinishSize hcurrentTokensBoundarySize
        hnextTokensBoundarySize hcurrentTasksBoundarySize
        hnextTasksBoundarySize hnextTasksCountSize htailBoundarySize
        hbinderSize hrepeatSize hdecrementedSize hnumericSize
    have hpath :=
      compactFormulaTransformStepRowsQuietRepeatFromSelected_structuralPayloadBound_le
        tokenTable width tokenCount current next mode stepWitness consumedCount
        mappedHead witnessStart witnessFinish witnessCount
        (repeatFullGraphPayloadEnvelope tokenCount numericBound bitBound
          (repeatSelectedBranchPayloadEnvelope bitBound
            (repeatPositiveBranchPayloadEnvelope numericBound bitBound)))
        numericBound bitBound selected hrows hselectedRaw
        (Nat.le_max_right _ _) hstepEnvironmentSize hwidthValue
        htokenCountValue hcurrentOutputCountValue htableSize
        hcurrentOutputBoundarySize hnextOutputBoundarySize hnumericSize
    unfold compactFormulaTransformStepRowsQuietRepeatFullyFixedCertificate
    dsimp only [branchData] at hbranch
    rw [hbranch]
    simpa only [branchCertificate, selected] using hpath

#print axioms
  compactFormulaTransformStepRowsQuietRepeatFullyFixedCertificate_structuralPayloadBound_le

end FoundationCompactNumericListedDirectFormulaTransformStepRowsQuietRepeatFullyFixedBounds
