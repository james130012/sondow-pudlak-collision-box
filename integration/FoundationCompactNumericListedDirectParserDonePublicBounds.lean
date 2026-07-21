import integration.FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds
import integration.FoundationCompactNumericListedDirectCompletedStatusSameRowsPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resource for the finished parser branch

The token rows, syntax-task rows, and failed/completed status alternative are
charged separately and assembled into the original closed formula.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserDonePublicBounds

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds
open FoundationCompactNumericListedDirectCompletedStatusSameRows
open FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectCompletedStatusSameRowsPublicBounds

private abbrev doneZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate.zeroValuation

noncomputable def compactUnifiedParserDoneStatusGraphPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (hstatus :
      (CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          current.tasksFinish current.finish ∧
        CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          next.tasksFinish next.finish) ∨
      CompactBinaryNatCompletedStatusSameRowsWithSize tokenTable width tokenCount
        current.tasksFinish current.finish next.tasksFinish next.finish
        witness.sourceOutputStart witness.sourceOutputBoundary
        witness.sourceOutputBoundarySize witness.targetOutputStart
        witness.targetOutputBoundary witness.targetOutputBoundarySize
        witness.outputCount) : Nat := by
  let currentFailedFormula := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount current.tasksFinish current.finish
  let nextFailedFormula := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let failedPairFormula := currentFailedFormula ⋏ nextFailedFormula
  let completedFormula :=
    compactBinaryNatCompletedStatusSameRowsWithSizeExplicitFormula tokenTable
      width tokenCount current.tasksFinish current.finish next.tasksFinish
      next.finish witness.sourceOutputStart witness.sourceOutputBoundary
      witness.sourceOutputBoundarySize witness.targetOutputStart
      witness.targetOutputBoundary witness.targetOutputBoundarySize
      witness.outputCount
  by_cases hfailed :
      CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          current.tasksFinish current.finish ∧
        CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          next.tasksFinish next.finish
  · let currentResource :=
      compactBinaryNatFailedStatusSliceStructuralPayloadPolynomial tokenTable
        width tokenCount current.tasksFinish current.finish
    let nextResource :=
      compactBinaryNatFailedStatusSliceStructuralPayloadPolynomial tokenTable
        width tokenCount next.tasksFinish next.finish
    let pairResource := transparentHybridConjunctionPayloadEnvelope
      doneZeroValuation currentFailedFormula nextFailedFormula currentResource
      nextResource
    exact transparentHybridDisjunctionLeftPayloadEnvelope doneZeroValuation
      failedPairFormula completedFormula pairResource
  · have hcompleted : CompactBinaryNatCompletedStatusSameRowsWithSize
        tokenTable width tokenCount current.tasksFinish current.finish
        next.tasksFinish next.finish witness.sourceOutputStart
        witness.sourceOutputBoundary witness.sourceOutputBoundarySize
        witness.targetOutputStart witness.targetOutputBoundary
        witness.targetOutputBoundarySize witness.outputCount := by
      rcases hstatus with hfailed' | hcompleted
      · exact False.elim (hfailed hfailed')
      · exact hcompleted
    let completedResource :=
      compactBinaryNatCompletedStatusSameRowsWithSizeGraphPayloadEnvelope
        tokenTable width tokenCount current.tasksFinish current.finish
        next.tasksFinish next.finish witness.sourceOutputStart
        witness.sourceOutputBoundary witness.sourceOutputBoundarySize
        witness.targetOutputStart witness.targetOutputBoundary
        witness.targetOutputBoundarySize witness.outputCount hcompleted
    exact transparentHybridDisjunctionRightPayloadEnvelope doneZeroValuation
      failedPairFormula completedFormula completedResource

theorem
    compactUnifiedParserDoneStatusExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (hstatus :
      (CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          current.tasksFinish current.finish ∧
        CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          next.tasksFinish next.finish) ∨
      CompactBinaryNatCompletedStatusSameRowsWithSize tokenTable width tokenCount
        current.tasksFinish current.finish next.tasksFinish next.finish
        witness.sourceOutputStart witness.sourceOutputBoundary
        witness.sourceOutputBoundarySize witness.targetOutputStart
        witness.targetOutputBoundary witness.targetOutputBoundarySize
        witness.outputCount) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserDoneStatusExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness hstatus) ≤
      compactUnifiedParserDoneStatusGraphPayloadEnvelope tokenTable width
        tokenCount current next witness hstatus := by
  let currentFailedFormula := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount current.tasksFinish current.finish
  let nextFailedFormula := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let failedPairFormula := currentFailedFormula ⋏ nextFailedFormula
  let completedFormula :=
    compactBinaryNatCompletedStatusSameRowsWithSizeExplicitFormula tokenTable
      width tokenCount current.tasksFinish current.finish next.tasksFinish
      next.finish witness.sourceOutputStart witness.sourceOutputBoundary
      witness.sourceOutputBoundarySize witness.targetOutputStart
      witness.targetOutputBoundary witness.targetOutputBoundarySize
      witness.outputCount
  by_cases hfailed :
      CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          current.tasksFinish current.finish ∧
        CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          next.tasksFinish next.finish
  · let currentCertificate :
        CheckedHybridValuationBoundedFormulaCertificate doneZeroValuation
          currentFailedFormula :=
      compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current.tasksFinish current.finish hfailed.1
    let nextCertificate :
        CheckedHybridValuationBoundedFormulaCertificate doneZeroValuation
          nextFailedFormula :=
      compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
        tokenTable width tokenCount next.tasksFinish next.finish hfailed.2
    have hcurrent :=
      compactBinaryNatFailedStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
        tokenTable width tokenCount current.tasksFinish current.finish hfailed.1
    have hnext :=
      compactBinaryNatFailedStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
        tokenTable width tokenCount next.tasksFinish next.finish hfailed.2
    let pairCertificate :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        currentCertificate nextCertificate
    have hpair := transparentHybridConjunctionPayloadBound_le
      currentCertificate nextCertificate _ _ hcurrent hnext
    let statusCertificate :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := completedFormula) pairCertificate
    have hstatusResource := transparentHybridDisjunctionLeftPayloadBound_le
      (right := completedFormula) pairCertificate _ hpair
    unfold compactUnifiedParserDoneStatusExplicitHybridCertificateOfGraph
    rw [dif_pos hfailed]
    unfold compactUnifiedParserDoneStatusGraphPayloadEnvelope
    rw [dif_pos hfailed]
    simpa only [hybridFormulaStructuralPayloadBound, currentFailedFormula,
      nextFailedFormula, failedPairFormula, completedFormula,
      currentCertificate, nextCertificate, pairCertificate,
      statusCertificate] using hstatusResource
  · have hcompleted : CompactBinaryNatCompletedStatusSameRowsWithSize
        tokenTable width tokenCount current.tasksFinish current.finish
        next.tasksFinish next.finish witness.sourceOutputStart
        witness.sourceOutputBoundary witness.sourceOutputBoundarySize
        witness.targetOutputStart witness.targetOutputBoundary
        witness.targetOutputBoundarySize witness.outputCount := by
      rcases hstatus with hfailed' | hcompleted
      · exact False.elim (hfailed hfailed')
      · exact hcompleted
    let completedCertificate :
        CheckedHybridValuationBoundedFormulaCertificate doneZeroValuation
          completedFormula :=
      compactBinaryNatCompletedStatusSameRowsWithSizeExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current.tasksFinish current.finish
        next.tasksFinish next.finish witness.sourceOutputStart
        witness.sourceOutputBoundary witness.sourceOutputBoundarySize
        witness.targetOutputStart witness.targetOutputBoundary
        witness.targetOutputBoundarySize witness.outputCount hcompleted
    have hcompletedResource :=
      compactBinaryNatCompletedStatusSameRowsWithSizeExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
        tokenTable width tokenCount current.tasksFinish current.finish
        next.tasksFinish next.finish witness.sourceOutputStart
        witness.sourceOutputBoundary witness.sourceOutputBoundarySize
        witness.targetOutputStart witness.targetOutputBoundary
        witness.targetOutputBoundarySize witness.outputCount hcompleted
    have hstatusResource := transparentHybridDisjunctionRightPayloadBound_le
      (left := failedPairFormula) completedCertificate _ hcompletedResource
    unfold compactUnifiedParserDoneStatusExplicitHybridCertificateOfGraph
    rw [dif_neg hfailed]
    unfold compactUnifiedParserDoneStatusGraphPayloadEnvelope
    rw [dif_neg hfailed]
    simpa only [hybridFormulaStructuralPayloadBound, currentFailedFormula,
      nextFailedFormula, failedPairFormula, completedFormula,
      completedCertificate] using hstatusResource

noncomputable def compactUnifiedParserDoneGraphPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (hgraph : CompactUnifiedParserDoneGraphRows tokenTable width tokenCount
      current next witness) : Nat := by
  rcases hgraph with ⟨htokens, htasks, hstatus⟩
  let tokenFormula := compactAdditiveNatListSameRowsClosedFormula tokenTable
    width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount
  let taskFormula := compactAdditiveSyntaxTaskListSameRowsClosedFormula
    tokenTable width tokenCount current.tasksBoundary current.tasksCount
    next.tasksBoundary next.tasksCount
  let statusFormula :=
    ((compactBinaryNatFailedStatusSliceClosedFormula tokenTable width tokenCount
          current.tasksFinish current.finish ⋏
        compactBinaryNatFailedStatusSliceClosedFormula tokenTable width tokenCount
          next.tasksFinish next.finish) ⋎
      compactBinaryNatCompletedStatusSameRowsWithSizeExplicitFormula tokenTable
        width tokenCount current.tasksFinish current.finish next.tasksFinish
        next.finish witness.sourceOutputStart witness.sourceOutputBoundary
        witness.sourceOutputBoundarySize witness.targetOutputStart
        witness.targetOutputBoundary witness.targetOutputBoundarySize
        witness.outputCount)
  let tokenResource := compactAdditiveNatListSameRowsGraphPayloadEnvelope
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount htokens
  let taskResource :=
    compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope tokenTable width
      tokenCount current.tasksBoundary current.tasksCount next.tasksBoundary
      next.tasksCount htasks
  let statusResource := compactUnifiedParserDoneStatusGraphPayloadEnvelope
    tokenTable width tokenCount current next witness hstatus
  let taskStatusResource := transparentHybridConjunctionPayloadEnvelope
    doneZeroValuation taskFormula statusFormula taskResource statusResource
  exact transparentHybridConjunctionPayloadEnvelope doneZeroValuation
    tokenFormula (taskFormula ⋏ statusFormula) tokenResource taskStatusResource

theorem
    compactUnifiedParserDoneExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (hgraph : CompactUnifiedParserDoneGraphRows tokenTable width tokenCount
      current next witness) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserDoneExplicitHybridCertificateOfGraph tokenTable
          width tokenCount current next witness hgraph) ≤
      compactUnifiedParserDoneGraphPayloadEnvelope tokenTable width tokenCount
        current next witness hgraph := by
  rcases hgraph with ⟨htokens, htasks, hstatus⟩
  let tokenCertificate :
      CheckedHybridValuationBoundedFormulaCertificate doneZeroValuation
        (compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
          current.tokensBoundary current.tokensCount next.tokensBoundary
          next.tokensCount) :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount htokens
  let taskCertificate :
      CheckedHybridValuationBoundedFormulaCertificate doneZeroValuation
        (compactAdditiveSyntaxTaskListSameRowsClosedFormula tokenTable width
          tokenCount current.tasksBoundary current.tasksCount
          next.tasksBoundary next.tasksCount) :=
    compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      next.tasksBoundary next.tasksCount htasks
  let statusCertificate :=
    compactUnifiedParserDoneStatusExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current next witness hstatus
  have htokenResource :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount htokens
  have htaskResource :=
    compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      next.tasksBoundary next.tasksCount htasks
  have hstatusResource :=
    compactUnifiedParserDoneStatusExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next witness hstatus
  let taskStatus := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    taskCertificate statusCertificate
  have htaskStatus := transparentHybridConjunctionPayloadBound_le
    taskCertificate statusCertificate _ _ htaskResource hstatusResource
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    tokenCertificate taskStatus
  have hparts := transparentHybridConjunctionPayloadBound_le
    tokenCertificate taskStatus _ _ htokenResource htaskStatus
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactUnifiedParserDoneClosedFormula_alignment tokenTable width
          tokenCount current next witness).symm parts) ≤ _
  unfold compactUnifiedParserDoneGraphPayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound, tokenCertificate,
    taskCertificate, statusCertificate, taskStatus, parts] using hparts

#print axioms
  compactUnifiedParserDoneStatusExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserDoneExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectParserDonePublicBounds
