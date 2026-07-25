import integration.FoundationCompactNumericListedDirectParserDoneWholeUniformDirectAlignment
import integration.FoundationCompactNumericListedDirectParserDoneStatusUniformDirectBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
import integration.FoundationCompactPADirectConnectiveTransparentBounds

/-! # Transparent fixed-child bound for the complete direct Done proof -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserDoneWholeUniformDirectBounds

open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsFullyFixedBounds
open FoundationCompactNumericListedDirectParserDoneStatusUniformDirectCompiler
open FoundationCompactNumericListedDirectParserDoneStatusUniformDirectBounds
open FoundationCompactNumericListedDirectParserDoneWholeUniformDirectCompiler
open FoundationCompactNumericListedDirectParserDoneWholeUniformDirectAlignment

private abbrev doneWholeBoundZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate.zeroValuation

def compactUnifiedParserDoneWholeUniformDirectPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (numericBound bitBound : Nat) : Nat :=
  let tokens := compactAdditiveNatListSameRowsClosedFormula tokenTable width
    tokenCount current.tokensBoundary current.tokensCount next.tokensBoundary
    next.tokensCount
  let tasks := compactAdditiveSyntaxTaskListSameRowsClosedFormula tokenTable
    width tokenCount current.tasksBoundary current.tasksCount
    next.tasksBoundary next.tasksCount
  let status :=
    (compactBinaryNatFailedStatusSliceClosedFormula tokenTable width tokenCount
        current.tasksFinish current.finish ⋏
      compactBinaryNatFailedStatusSliceClosedFormula tokenTable width tokenCount
        next.tasksFinish next.finish) ⋎
      compactBinaryNatCompletedStatusSameRowsWithSizeExplicitFormula tokenTable
        width tokenCount current.tasksFinish current.finish next.tasksFinish
        next.finish witness.sourceOutputStart witness.sourceOutputBoundary
        witness.sourceOutputBoundarySize witness.targetOutputStart
        witness.targetOutputBoundary witness.targetOutputBoundarySize
        witness.outputCount
  let statusResource :=
    compactUnifiedParserDoneStatusUniformDirectPayloadEnvelope tokenTable width
      tokenCount current next witness numericBound bitBound
  let tasksTailResource := transparentHybridConjunctionPayloadEnvelope
    doneWholeBoundZeroValuation tasks status
    (taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    statusResource
  transparentHybridConjunctionPayloadEnvelope doneWholeBoundZeroValuation
    tokens (tasks ⋏ status)
    (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    tasksTailResource

theorem
    compileCompactUnifiedParserDoneUniformDirectExplicitContext_payloadLength_le
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
    (hsourceBoundarySize :
      Nat.size witness.sourceOutputBoundary <= bitBound)
    (htargetBoundarySize :
      Nat.size witness.targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compileCompactUnifiedParserDoneUniformDirectExplicitContext tokenTable
      width tokenCount current next witness numericBound bitBound hgraph
      htokenCount houtputCount hsourceBoundarySize htargetBoundarySize
      hnumericSize).payloadLength <=
        compactUnifiedParserDoneWholeUniformDirectPayloadEnvelope tokenTable
          width tokenCount current next witness numericBound bitBound := by
  rcases hgraph with ⟨htokens, htasks, hstatus⟩
  let tokensFormula := compactAdditiveNatListSameRowsClosedFormula tokenTable
    width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount
  let tasksFormula := compactAdditiveSyntaxTaskListSameRowsClosedFormula
    tokenTable width tokenCount current.tasksBoundary current.tasksCount
    next.tasksBoundary next.tasksCount
  let statusFormula :=
    (compactBinaryNatFailedStatusSliceClosedFormula tokenTable width tokenCount
        current.tasksFinish current.finish ⋏
      compactBinaryNatFailedStatusSliceClosedFormula tokenTable width tokenCount
        next.tasksFinish next.finish) ⋎
      compactBinaryNatCompletedStatusSameRowsWithSizeExplicitFormula tokenTable
        width tokenCount current.tasksFinish current.finish next.tasksFinish
        next.finish witness.sourceOutputStart witness.sourceOutputBoundary
        witness.sourceOutputBoundarySize witness.targetOutputStart
        witness.targetOutputBoundary witness.targetOutputBoundarySize
        witness.outputCount
  let tokens :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount htokens
  let tasks :=
    compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      next.tasksBoundary next.tasksCount htasks
  let status :=
    compileCompactUnifiedParserDoneStatusUniformDirect tokenTable width
      tokenCount current next witness numericBound bitBound hstatus
      htokenCount houtputCount hsourceBoundarySize htargetBoundarySize
      hnumericSize
  have hcurrentTokensCount : current.tokensCount <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (5 : Fin 8)
  have hcurrentTasksCount : current.tasksCount <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (7 : Fin 8)
  have hcurrentTasksFinish : current.tasksFinish <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (3 : Fin 8)
  have hnextTasksFinish : next.tasksFinish <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextValue (3 : Fin 8)
  have hcurrentTokensBoundarySize :
      Nat.size current.tokensBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (4 : Fin 8)
  have hnextTokensBoundarySize :
      Nat.size next.tokensBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextSize (4 : Fin 8)
  have hcurrentTasksBoundarySize :
      Nat.size current.tasksBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (6 : Fin 8)
  have hnextTasksBoundarySize :
      Nat.size next.tasksBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextSize (6 : Fin 8)
  have hcurrentTasksFinishSize :
      Nat.size current.tasksFinish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (3 : Fin 8)
  have hnextTasksFinishSize :
      Nat.size next.tasksFinish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextSize (3 : Fin 8)
  have hcurrentFinishSize : Nat.size current.finish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (1 : Fin 8)
  have hnextFinishSize : Nat.size next.finish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextSize (1 : Fin 8)
  have htokensResource :
      tokens.compile.payloadLength <=
        sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound :=
    compile_payloadLength_le_hybridFormulaStructuralPayloadBound tokens |>.trans
      ((compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
        tokenTable width tokenCount current.tokensBoundary
        current.tokensCount next.tokensBoundary next.tokensCount htokens).trans
        (compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_fullyFixed
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount next.tokensBoundary next.tokensCount numericBound
          bitBound htokens hwidth htokenCount hcurrentTokensCount
          htokenTableSize hcurrentTokensBoundarySize
          hnextTokensBoundarySize hnumericSize))
  have htasksResource :
      tasks.compile.payloadLength <=
        taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound :=
    compile_payloadLength_le_hybridFormulaStructuralPayloadBound tasks |>.trans
      ((compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
        tokenTable width tokenCount current.tasksBoundary
        current.tasksCount next.tasksBoundary next.tasksCount htasks).trans
        (compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope_le_fullyFixed
          tokenTable width tokenCount current.tasksBoundary
          current.tasksCount next.tasksBoundary next.tasksCount numericBound
          bitBound htasks hwidth htokenCount hcurrentTasksCount
          htokenTableSize hcurrentTasksBoundarySize hnextTasksBoundarySize
          hnumericSize))
  have hstatusResource :=
    compileCompactUnifiedParserDoneStatusUniformDirect_payloadLength_le
      tokenTable width tokenCount current next witness numericBound bitBound
      hstatus hwidth htokenCount houtputCount hcurrentTasksFinish
      hnextTasksFinish htokenTableSize hcurrentTasksFinishSize
      hnextTasksFinishSize hcurrentFinishSize hnextFinishSize
      hsourceBoundarySize htargetBoundarySize hnumericSize hbitPositive
  let tasksTail := compileDirectConjunction tasks.compile status
  let statusResource :=
    compactUnifiedParserDoneStatusUniformDirectPayloadEnvelope tokenTable width
      tokenCount current next witness numericBound bitBound
  let tasksTailResource := transparentHybridConjunctionPayloadEnvelope
    doneWholeBoundZeroValuation tasksFormula statusFormula
    (taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    statusResource
  have htasksTail : tasksTail.payloadLength <= tasksTailResource := by
    exact compileDirectConjunction_payloadLength_le tasks.compile status
      (taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      statusResource htasksResource hstatusResource
  let total := compileDirectConjunction tokens.compile tasksTail
  have htotal := compileDirectConjunction_payloadLength_le tokens.compile
    tasksTail (sameRowsCompleteFullyFixedPayloadPolynomial numericBound
      bitBound) tasksTailResource htokensResource htasksTail
  unfold compileCompactUnifiedParserDoneUniformDirectExplicitContext
  unfold compactUnifiedParserDoneWholeUniformDirectPayloadEnvelope
  dsimp only [tokensFormula, tasksFormula, statusFormula, tokens, tasks, status,
    tasksTail, statusResource, tasksTailResource, total]
  exact htotal

theorem
    compileCompactUnifiedParserDoneUniformDirectOriginalContext_payloadLength_le
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
    (hsourceBoundarySize :
      Nat.size witness.sourceOutputBoundary <= bitBound)
    (htargetBoundarySize :
      Nat.size witness.targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compileCompactUnifiedParserDoneUniformDirectOriginalContext tokenTable
      width tokenCount current next witness numericBound bitBound hgraph
      htokenCount houtputCount hsourceBoundarySize htargetBoundarySize
      hnumericSize).payloadLength <=
        compactUnifiedParserDoneWholeUniformDirectPayloadEnvelope tokenTable
          width tokenCount current next witness numericBound bitBound := by
  rw [compileCompactUnifiedParserDoneUniformDirectOriginalContext_payloadLength_eq]
  exact
    compileCompactUnifiedParserDoneUniformDirectExplicitContext_payloadLength_le
      tokenTable width tokenCount current next witness numericBound bitBound
      hgraph hwidth htokenCount houtputCount hcurrentValue hnextValue
      htokenTableSize hcurrentSize hnextSize hsourceBoundarySize
      htargetBoundarySize hnumericSize hbitPositive

end FoundationCompactNumericListedDirectParserDoneWholeUniformDirectBounds
