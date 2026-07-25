import integration.FoundationCompactNumericListedDirectParserDoneWholeUniformDirectBounds
import integration.FoundationCompactNumericListedDirectParserDoneFormulaSyntaxFixedBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactPAHybridDisjunctionGeneralContextBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Fully fixed payload bound for the complete direct Done proof -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserDoneWholeUniformDirectFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserDoneUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserDoneStatusUniformDirectBounds
open FoundationCompactNumericListedDirectParserDoneWholeUniformDirectCompiler
open FoundationCompactNumericListedDirectParserDoneWholeUniformDirectAlignment
open FoundationCompactNumericListedDirectParserDoneWholeUniformDirectBounds
open FoundationCompactNumericListedDirectParserDoneFormulaEnvironmentAlignment
open FoundationCompactNumericListedDirectParserDoneFormulaSyntaxFixedBounds

private abbrev doneWholeFixedZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate.zeroValuation

private theorem binaryFormulaCode_left_length_le_and
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_right_length_le_and
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_left_length_le_or
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_right_length_le_or
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

def compactUnifiedParserDoneWholeUniformDirectSyntaxResource
    (bitBound : Nat) : Nat :=
  compactUnifiedParserDoneFormulaSyntaxFixedPolynomial bitBound + 1

def compactUnifiedParserDoneStatusUniformDirectFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    compactUnifiedParserDoneWholeUniformDirectSyntaxResource bitBound
  let failedLeaf :=
    binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
      bitBound
  let failedPair :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource failedLeaf failedLeaf
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource failedPair +
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource
      (completedSameRowsUniformDirectFixedPayloadPolynomial numericBound
        bitBound)

def compactUnifiedParserDoneWholeUniformDirectFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    compactUnifiedParserDoneWholeUniformDirectSyntaxResource bitBound
  let statusResource :=
    compactUnifiedParserDoneStatusUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  let tasksTail :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      statusResource
  hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    tasksTail

theorem compactUnifiedParserDoneWholeUniformDirectPayloadEnvelope_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (numericBound bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (hwitnessSize :
      CompactUnifiedParserDoneWitnessCoordinateSizeBound witness bitBound) :
    compactUnifiedParserDoneWholeUniformDirectPayloadEnvelope tokenTable width
        tokenCount current next witness numericBound bitBound <=
      compactUnifiedParserDoneWholeUniformDirectFixedPayloadPolynomial
        numericBound bitBound := by
  let tokens := compactAdditiveNatListSameRowsClosedFormula tokenTable width
    tokenCount current.tokensBoundary current.tokensCount next.tokensBoundary
    next.tokensCount
  let tasks := compactAdditiveSyntaxTaskListSameRowsClosedFormula tokenTable
    width tokenCount current.tasksBoundary current.tasksCount
    next.tasksBoundary next.tasksCount
  let currentFailed := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount current.tasksFinish current.finish
  let nextFailed := compactBinaryNatFailedStatusSliceClosedFormula tokenTable
    width tokenCount next.tasksFinish next.finish
  let failedPair := currentFailed ⋏ nextFailed
  let completed :=
    compactBinaryNatCompletedStatusSameRowsWithSizeExplicitFormula tokenTable
      width tokenCount current.tasksFinish current.finish next.tasksFinish
      next.finish witness.sourceOutputStart witness.sourceOutputBoundary
      witness.sourceOutputBoundarySize witness.targetOutputStart
      witness.targetOutputBoundary witness.targetOutputBoundarySize
      witness.outputCount
  let status := failedPair ⋎ completed
  let tasksTail := tasks ⋏ status
  let full := tokens ⋏ tasksTail
  let syntaxResource :=
    compactUnifiedParserDoneWholeUniformDirectSyntaxResource bitBound
  let failedLeafResource :=
    binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
      bitBound
  let failedPairExact := transparentHybridConjunctionPayloadEnvelope
    doneWholeFixedZeroValuation currentFailed nextFailed failedLeafResource
    failedLeafResource
  let failedPairFixed := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    failedLeafResource failedLeafResource
  let failedExact := transparentHybridDisjunctionLeftPayloadEnvelope
    doneWholeFixedZeroValuation failedPair completed failedPairExact
  let failedFixed := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    failedPairFixed
  let completedExact := transparentHybridDisjunctionRightPayloadEnvelope
    doneWholeFixedZeroValuation failedPair completed
      (completedSameRowsUniformDirectFixedPayloadPolynomial numericBound
        bitBound)
  let completedFixed := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (completedSameRowsUniformDirectFixedPayloadPolynomial numericBound
      bitBound)
  let statusExact := failedExact + completedExact
  let statusFixed := failedFixed + completedFixed
  let tasksTailExact := transparentHybridConjunctionPayloadEnvelope
    doneWholeFixedZeroValuation tasks status
    (taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    statusExact
  let tasksTailFixed := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    statusFixed
  let totalExact := transparentHybridConjunctionPayloadEnvelope
    doneWholeFixedZeroValuation tokens tasksTail
    (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    tasksTailExact
  let totalFixed := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    tasksTailFixed
  have henvironment :=
    compactUnifiedParserDoneFormulaEnvironmentOf_size_le tokenTable width
      tokenCount current next witness bitBound htokenTableSize hwidthSize
      htokenCountSize hcurrentSize hnextSize hwitnessSize
  have hfullCodeRaw :=
    compactUnifiedParserDoneExplicitFormula_code_length_le_fixed tokenTable
      width tokenCount current next witness bitBound henvironment
  have hfullEq :
      compactUnifiedParserDoneExplicitFormula tokenTable width tokenCount
          current next witness =
        full := by
    rfl
  have hfullCode :
      (binaryFormulaCode full).length <= syntaxResource := by
    rw [← hfullEq]
    exact hfullCodeRaw.trans (by
      unfold syntaxResource
        compactUnifiedParserDoneWholeUniformDirectSyntaxResource
      omega)
  have hfullClosedRaw :
      (compactUnifiedParserDoneExplicitFormula tokenTable width tokenCount
        current next witness).freeVariables = ∅ := by
    rw [← compactUnifiedParserDoneClosedFormula_alignment tokenTable width
      tokenCount current next witness]
    exact compactUnifiedParserDoneClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount current next witness
  have hfullClosed : full.freeVariables = ∅ := by
    rw [← hfullEq]
    exact hfullClosedRaw
  have houterClosed :
      tokens.freeVariables = ∅ ∧ tasksTail.freeVariables = ∅ := by
    simpa only [full, LO.FirstOrder.Semiformula.freeVariables_and,
      Finset.union_eq_empty] using hfullClosed
  have htailClosed :
      tasks.freeVariables = ∅ ∧ status.freeVariables = ∅ := by
    simpa only [tasksTail, LO.FirstOrder.Semiformula.freeVariables_and,
      Finset.union_eq_empty] using houterClosed.2
  have hstatusClosed :
      failedPair.freeVariables = ∅ ∧ completed.freeVariables = ∅ := by
    simpa only [status, LO.FirstOrder.Semiformula.freeVariables_or,
      Finset.union_eq_empty] using htailClosed.2
  have hfailedClosed :
      currentFailed.freeVariables = ∅ ∧ nextFailed.freeVariables = ∅ := by
    simpa only [failedPair, LO.FirstOrder.Semiformula.freeVariables_and,
      Finset.union_eq_empty] using hstatusClosed.1
  have htasksTailCode :
      (binaryFormulaCode tasksTail).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_and tokens tasksTail).trans hfullCode
  have htokensCode :
      (binaryFormulaCode tokens).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_and tokens tasksTail).trans hfullCode
  have htasksCode :
      (binaryFormulaCode tasks).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_and tasks status).trans htasksTailCode
  have hstatusCode :
      (binaryFormulaCode status).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_and tasks status).trans htasksTailCode
  have hfailedPairCode :
      (binaryFormulaCode failedPair).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_or failedPair completed).trans
      hstatusCode
  have hcompletedCode :
      (binaryFormulaCode completed).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_or failedPair completed).trans
      hstatusCode
  have hcurrentFailedCode :
      (binaryFormulaCode currentFailed).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_and currentFailed nextFailed).trans
      hfailedPairCode
  have hnextFailedCode :
      (binaryFormulaCode nextFailed).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_and currentFailed nextFailed).trans
      hfailedPairCode
  have hsyntaxPositive : 1 <= syntaxResource := by
    unfold syntaxResource
      compactUnifiedParserDoneWholeUniformDirectSyntaxResource
    omega
  have hfailedPair :
      failedPairExact <= failedPairFixed := by
    exact transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      doneWholeFixedZeroValuation currentFailed nextFailed failedLeafResource
      failedLeafResource syntaxResource hsyntaxPositive hfailedClosed.1
      hfailedClosed.2 hcurrentFailedCode hnextFailedCode hfailedPairCode
  have hstatusContext :
      formulaCodeSum
        (valuationContext status.freeVariables
          doneWholeFixedZeroValuation) <= syntaxResource := by
    rw [show status.freeVariables = ∅ by
      rw [LO.FirstOrder.Semiformula.freeVariables_or, hstatusClosed.1,
        hstatusClosed.2]
      simp]
    simp [valuationContext, formulaCodeSum]
  have hfailedMono :=
    transparentHybridDisjunctionLeftPayloadEnvelope_mono
      doneWholeFixedZeroValuation failedPair completed hfailedPair
  have hfailedGeneral :=
    transparentHybridDisjunctionLeftPayloadEnvelope_le_general
      doneWholeFixedZeroValuation failedPair completed failedPairFixed
      syntaxResource hsyntaxPositive hstatusContext hfailedPairCode
      hcompletedCode hstatusCode
  have hfailed : failedExact <= failedFixed := by
    exact hfailedMono.trans hfailedGeneral
  have hcompleted :
      completedExact <= completedFixed := by
    exact transparentHybridDisjunctionRightPayloadEnvelope_le_general
      doneWholeFixedZeroValuation failedPair completed
      (completedSameRowsUniformDirectFixedPayloadPolynomial numericBound
        bitBound) syntaxResource hsyntaxPositive hstatusContext hfailedPairCode
      hcompletedCode hstatusCode
  have hstatus : statusExact <= statusFixed := by
    dsimp only [statusExact, statusFixed]
    omega
  have htasksTailMono :=
    transparentHybridConjunctionPayloadEnvelope_mono
      doneWholeFixedZeroValuation tasks status
      (Nat.le_refl
        (taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound
          bitBound))
      hstatus
  have htasksTailGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      doneWholeFixedZeroValuation tasks status
      (taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      statusFixed syntaxResource hsyntaxPositive htailClosed.1 htailClosed.2
      htasksCode hstatusCode htasksTailCode
  have htasksTail : tasksTailExact <= tasksTailFixed :=
    htasksTailMono.trans htasksTailGeneral
  have htotalMono :=
    transparentHybridConjunctionPayloadEnvelope_mono
      doneWholeFixedZeroValuation tokens tasksTail
      (Nat.le_refl
        (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound))
      htasksTail
  have htotalGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      doneWholeFixedZeroValuation tokens tasksTail
      (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      tasksTailFixed syntaxResource hsyntaxPositive houterClosed.1
      houterClosed.2 htokensCode htasksTailCode hfullCode
  have htotal : totalExact <= totalFixed :=
    htotalMono.trans htotalGeneral
  change totalExact <= _
  unfold compactUnifiedParserDoneWholeUniformDirectFixedPayloadPolynomial
  unfold compactUnifiedParserDoneStatusUniformDirectFixedPayloadPolynomial
  simpa only [tokens, tasks, currentFailed, nextFailed, failedPair, completed,
    status, tasksTail, syntaxResource, failedLeafResource, failedPairExact,
    failedPairFixed, failedExact, failedFixed, completedExact, completedFixed,
    statusExact, statusFixed, tasksTailExact, tasksTailFixed, totalFixed] using
      htotal

theorem
    compileCompactUnifiedParserDoneUniformDirectOriginalContext_payloadLength_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserDoneGraphRows tokenTable width tokenCount
      current next witness)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : witness.outputCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (hwitnessSize :
      CompactUnifiedParserDoneWitnessCoordinateSizeBound witness bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compileCompactUnifiedParserDoneUniformDirectOriginalContext tokenTable
      width tokenCount current next witness numericBound bitBound hgraph
      htokenCount houtputCount
      (by
        simpa [compactUnifiedParserDoneWitnessCoordinateValues] using
          hwitnessSize (1 : Fin 7))
      (by
        simpa [compactUnifiedParserDoneWitnessCoordinateValues] using
          hwitnessSize (4 : Fin 7))
      hnumericSize).payloadLength <=
        compactUnifiedParserDoneWholeUniformDirectFixedPayloadPolynomial
          numericBound bitBound := by
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  exact
    (compileCompactUnifiedParserDoneUniformDirectOriginalContext_payloadLength_le
      tokenTable width tokenCount current next witness numericBound bitBound
      hgraph hwidth htokenCount houtputCount hcurrentValue hnextValue
      htokenTableSize hcurrentSize hnextSize
      (by
        simpa [compactUnifiedParserDoneWitnessCoordinateValues] using
          hwitnessSize (1 : Fin 7))
      (by
        simpa [compactUnifiedParserDoneWitnessCoordinateValues] using
          hwitnessSize (4 : Fin 7))
      hnumericSize hbitPositive).trans
    (compactUnifiedParserDoneWholeUniformDirectPayloadEnvelope_le_fixed
      tokenTable width tokenCount current next witness numericBound bitBound
      htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
      hwitnessSize)

end FoundationCompactNumericListedDirectParserDoneWholeUniformDirectFixedBounds
