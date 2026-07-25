import integration.FoundationCompactNumericListedDirectParserDoneStatusUniformDirectCompiler
import integration.FoundationCompactNumericListedDirectParserDoneUniformDirectFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
import integration.FoundationCompactPADirectConnectiveTransparentBounds

/-! # Transparent bound for the direct completed parser status alternative -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserDoneStatusUniformDirectBounds

open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectCompletedStatusSameRows
open FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserDoneUniformDirectCompiler
open FoundationCompactNumericListedDirectParserDoneUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserDoneStatusUniformDirectCompiler

private abbrev doneStatusBoundZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate.zeroValuation

def compactUnifiedParserDoneStatusUniformDirectPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (numericBound bitBound : Nat) : Nat :=
  let currentFailed := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount current.tasksFinish current.finish
  let nextFailed := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let failedPair := currentFailed ⋏ nextFailed
  let completed :=
    compactBinaryNatCompletedStatusSameRowsWithSizeExplicitFormula tokenTable
      width tokenCount current.tasksFinish current.finish next.tasksFinish
      next.finish witness.sourceOutputStart witness.sourceOutputBoundary
      witness.sourceOutputBoundarySize witness.targetOutputStart
      witness.targetOutputBoundary witness.targetOutputBoundarySize
      witness.outputCount
  let failedLeafResource :=
    binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
      bitBound
  let failedPairResource := transparentHybridConjunctionPayloadEnvelope
    doneStatusBoundZeroValuation currentFailed nextFailed failedLeafResource
    failedLeafResource
  let failedResource := transparentHybridDisjunctionLeftPayloadEnvelope
    doneStatusBoundZeroValuation failedPair completed failedPairResource
  let completedResource := transparentHybridDisjunctionRightPayloadEnvelope
    doneStatusBoundZeroValuation failedPair completed
      (completedSameRowsUniformDirectFixedPayloadPolynomial numericBound
        bitBound)
  failedResource + completedResource

private theorem compiledFailedStatus_payloadLength_le_fixed
    (tokenTable width tokenCount start finish numericBound bitBound : Nat)
    (hgraph : CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
      start finish)
    (hwidth : width <= numericBound)
    (hstart : start <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount start finish hgraph).compile.payloadLength <=
      binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
        bitBound := by
  rcases hgraph with ⟨innerStart, hinnerLe, hfirstCell, hsecondCell⟩
  have hinnerEq : innerStart = start + 1 := hfirstCell.2.1
  have hinnerValue : start + 1 <= numericBound := by
    rw [← hinnerEq]
    exact hinnerLe.trans htokenCount
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hinnerSize : Nat.size (start + 1) <= bitBound :=
    (Nat.size_le_size hinnerValue).trans hnumericSize
  exact
    compile_payloadLength_le_hybridFormulaStructuralPayloadBound _ |>.trans
      (compactBinaryNatFailedStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
        tokenTable width tokenCount start finish numericBound bitBound hwidth
        hstart hinnerValue htokenTableSize hwidthSize htokenCountSize
        hstartSize hfinishSize hinnerSize hbitPositive
        ⟨innerStart, hinnerLe, hfirstCell, hsecondCell⟩)

theorem compileCompactUnifiedParserDoneStatusUniformDirect_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hstatus :
      (CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          current.tasksFinish current.finish ∧
        CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          next.tasksFinish next.finish) ∨
      CompactBinaryNatCompletedStatusSameRowsWithSize tokenTable width
        tokenCount current.tasksFinish current.finish next.tasksFinish
        next.finish witness.sourceOutputStart witness.sourceOutputBoundary
        witness.sourceOutputBoundarySize witness.targetOutputStart
        witness.targetOutputBoundary witness.targetOutputBoundarySize
        witness.outputCount)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : witness.outputCount <= numericBound)
    (hcurrentStart : current.tasksFinish <= numericBound)
    (hnextStart : next.tasksFinish <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentStartSize : Nat.size current.tasksFinish <= bitBound)
    (hnextStartSize : Nat.size next.tasksFinish <= bitBound)
    (hcurrentFinishSize : Nat.size current.finish <= bitBound)
    (hnextFinishSize : Nat.size next.finish <= bitBound)
    (hsourceBoundarySize :
      Nat.size witness.sourceOutputBoundary <= bitBound)
    (htargetBoundarySize :
      Nat.size witness.targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compileCompactUnifiedParserDoneStatusUniformDirect tokenTable width
      tokenCount current next witness numericBound bitBound hstatus
      htokenCount houtputCount hsourceBoundarySize htargetBoundarySize
      hnumericSize).payloadLength <=
        compactUnifiedParserDoneStatusUniformDirectPayloadEnvelope tokenTable
          width tokenCount current next witness numericBound bitBound := by
  let currentFailed := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount current.tasksFinish current.finish
  let nextFailed := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let failedPair := currentFailed ⋏ nextFailed
  let completed :=
    compactBinaryNatCompletedStatusSameRowsWithSizeExplicitFormula tokenTable
      width tokenCount current.tasksFinish current.finish next.tasksFinish
      next.finish witness.sourceOutputStart witness.sourceOutputBoundary
      witness.sourceOutputBoundarySize witness.targetOutputStart
      witness.targetOutputBoundary witness.targetOutputBoundarySize
      witness.outputCount
  let failedLeafResource :=
    binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
      bitBound
  let failedPairResource := transparentHybridConjunctionPayloadEnvelope
    doneStatusBoundZeroValuation currentFailed nextFailed failedLeafResource
    failedLeafResource
  let failedResource := transparentHybridDisjunctionLeftPayloadEnvelope
    doneStatusBoundZeroValuation failedPair completed failedPairResource
  let completedResource := transparentHybridDisjunctionRightPayloadEnvelope
    doneStatusBoundZeroValuation failedPair completed
      (completedSameRowsUniformDirectFixedPayloadPolynomial numericBound
        bitBound)
  by_cases hfailed :
      CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          current.tasksFinish current.finish ∧
        CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          next.tasksFinish next.finish
  · let currentCertificate :=
      compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current.tasksFinish current.finish
        hfailed.1
    let nextCertificate :=
      compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
        tokenTable width tokenCount next.tasksFinish next.finish hfailed.2
    have hcurrent := compiledFailedStatus_payloadLength_le_fixed tokenTable
      width tokenCount current.tasksFinish current.finish numericBound bitBound
      hfailed.1 hwidth hcurrentStart htokenCount htokenTableSize
      hcurrentStartSize hcurrentFinishSize hnumericSize hbitPositive
    have hnext := compiledFailedStatus_payloadLength_le_fixed tokenTable width
      tokenCount next.tasksFinish next.finish numericBound bitBound hfailed.2
      hwidth hnextStart htokenCount htokenTableSize hnextStartSize
      hnextFinishSize hnumericSize hbitPositive
    let pair := compileDirectConjunction currentCertificate.compile
      nextCertificate.compile
    have hpair : pair.payloadLength <= failedPairResource := by
      exact compileDirectConjunction_payloadLength_le
        currentCertificate.compile nextCertificate.compile failedLeafResource
        failedLeafResource hcurrent hnext
    let selected := compileDirectDisjunctionLeft
      (right := completed) pair
    have hselected : selected.payloadLength <= failedResource := by
      exact compileDirectDisjunctionLeft_payloadLength_le
        (right := completed) pair failedPairResource hpair
    have hsum : selected.payloadLength <= failedResource +
        completedResource := hselected.trans (by omega)
    unfold compileCompactUnifiedParserDoneStatusUniformDirect
    rw [dif_pos hfailed]
    change selected.payloadLength <= _
    unfold compactUnifiedParserDoneStatusUniformDirectPayloadEnvelope
    simpa only [currentFailed, nextFailed, failedPair, completed,
      failedLeafResource, failedPairResource, failedResource,
      completedResource] using hsum
  · have hcompleted : CompactBinaryNatCompletedStatusSameRowsWithSize
        tokenTable width tokenCount current.tasksFinish current.finish
        next.tasksFinish next.finish witness.sourceOutputStart
        witness.sourceOutputBoundary witness.sourceOutputBoundarySize
        witness.targetOutputStart witness.targetOutputBoundary
        witness.targetOutputBoundarySize witness.outputCount := by
      rcases hstatus with hfailed' | hcompleted
      · exact False.elim (hfailed hfailed')
      · exact hcompleted
    let completedProof :=
      compileCompactBinaryNatCompletedStatusSameRowsUniformDirect tokenTable
        width tokenCount current.tasksFinish current.finish next.tasksFinish
        next.finish witness.sourceOutputStart witness.sourceOutputBoundary
        witness.sourceOutputBoundarySize witness.targetOutputStart
        witness.targetOutputBoundary witness.targetOutputBoundarySize
        witness.outputCount numericBound bitBound hcompleted htokenCount
        houtputCount hsourceBoundarySize htargetBoundarySize hnumericSize
    have hcompletedProof :=
      compileCompactBinaryNatCompletedStatusSameRowsUniformDirect_payloadLength_le_fixed
        tokenTable width tokenCount current.tasksFinish current.finish
        next.tasksFinish next.finish witness.sourceOutputStart
        witness.sourceOutputBoundary witness.sourceOutputBoundarySize
        witness.targetOutputStart witness.targetOutputBoundary
        witness.targetOutputBoundarySize witness.outputCount numericBound
        bitBound hcompleted hwidth htokenCount houtputCount hcurrentStart
        hnextStart htokenTableSize hcurrentStartSize hnextStartSize
        hsourceBoundarySize htargetBoundarySize hnumericSize hbitPositive
    let selected := compileDirectDisjunctionRight
      (left := failedPair) completedProof
    have hselected : selected.payloadLength <= completedResource := by
      exact compileDirectDisjunctionRight_payloadLength_le
        (left := failedPair) completedProof
        (completedSameRowsUniformDirectFixedPayloadPolynomial numericBound
          bitBound) hcompletedProof
    have hsum : selected.payloadLength <= failedResource +
        completedResource := hselected.trans (by omega)
    unfold compileCompactUnifiedParserDoneStatusUniformDirect
    rw [dif_neg hfailed]
    change selected.payloadLength <= _
    unfold compactUnifiedParserDoneStatusUniformDirectPayloadEnvelope
    simpa only [currentFailed, nextFailed, failedPair, completed,
      failedLeafResource, failedPairResource, failedResource,
      completedResource] using hsum

end FoundationCompactNumericListedDirectParserDoneStatusUniformDirectBounds
