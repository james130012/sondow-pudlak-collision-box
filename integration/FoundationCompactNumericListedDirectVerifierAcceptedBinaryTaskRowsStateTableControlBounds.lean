import integration.FoundationCompactNumericListedDirectVerifierAcceptedTreeRowStateTableControlBounds
import integration.FoundationCompactNumericListedDirectVerifierAcceptedBinaryTaskRowsGlobalBound

/-!
# Accepted binary task rows with numeric state-table controls

The generic theorem below splices a controlled canonical root row, both
controlled child executions, and a controlled combine row at the exact binary
execution offsets.  The concrete `and` and `cut` instances follow below.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedBinaryTaskRowsStateTableControlBounds

open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierAcceptedTreeTaskRowsGlobalBound
open FoundationCompactNumericListedDirectVerifierCanonicalNonLeafExactSteps
open FoundationCompactNumericListedDirectVerifierCanonicalCombineExactSteps
open FoundationCompactNumericListedDirectVerifierAcceptedTreeRowStateTableControlBounds
open FoundationCompactNumericListedPAAxiomLeafOccurrence

set_option maxRecDepth 4000 in
set_option maxHeartbeats 12000000 in
theorem exists_compactNumericVerifierAcceptedBinaryTaskRow_at_offset_with_control
    (tree certificateTreeLeft certificateTreeRight : ListedCheckedPAProofTree)
    (certificate leftCertificate rightCertificate :
      StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (tag : Nat)
    {rowWeight offset : Nat} :
    let fields := (compactListedProofNodeExpectedFields tree proofSuffix).2
    let combineTask := compactNumericCombineTask tag fields
    let leftResult : CompactNumericChildResult :=
      (arithmeticPropositionTokenValues certificateTreeLeft.conclusionList,
        (listedCertificateValidTrace certificateTreeLeft leftCertificate).1)
    let rightResult : CompactNumericChildResult :=
      (arithmeticPropositionTokenValues certificateTreeRight.conclusionList,
        (listedCertificateValidTrace certificateTreeRight rightCertificate).1)
    let parentResult : CompactNumericChildResult :=
      (arithmeticPropositionTokenValues tree.conclusionList,
        (listedCertificateValidTrace tree certificate).1)
    let start := compactNumericTreeTaskStartState tree certificate
      proofSuffix certificateSuffix restTasks values
    let leftStart := compactNumericTreeTaskStartState certificateTreeLeft
      leftCertificate
      (compactListedProofTokens certificateTreeRight ++ proofSuffix)
      (compactStructuralCertificateTokens rightCertificate ++
        certificateSuffix)
      (compactNumericParseTask :: combineTask :: restTasks) values
    let rightStart := compactNumericTreeTaskStartState certificateTreeRight
      rightCertificate proofSuffix certificateSuffix
      (combineTask :: restTasks) (leftResult :: values)
    let beforeCombine := compactNumericTreeTaskSuccessState
      certificateTreeRight rightCertificate proofSuffix certificateSuffix
      (combineTask :: restTasks) (leftResult :: values)
    let finish := compactNumericTreeTaskSuccessState tree certificate
      proofSuffix certificateSuffix restTasks values
    let leftSteps := compactNumericTreeTaskSteps certificateTreeLeft
      leftCertificate
    let rightSteps := compactNumericTreeTaskSteps certificateTreeRight
      rightCertificate
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let certificateNode :=
      compactStructuralCertificateNodeExpected certificate certificateSuffix
    let nextProofTokens := compactListedProofTokens certificateTreeLeft ++
      compactListedProofTokens certificateTreeRight ++ proofSuffix
    let nextCertificateTokens :=
      compactStructuralCertificateTokens leftCertificate ++
        compactStructuralCertificateTokens rightCertificate ++
          certificateSuffix
    let nextTasks := compactNumericParseTask :: compactNumericParseTask ::
      combineTask :: restTasks
    compactNumericTreeCertificateShapeMatches certificateTreeLeft
        leftCertificate = true ->
    compactNumericTreeCertificateShapeMatches certificateTreeRight
        rightCertificate = true ->
    tag ≠ 10 ->
    (proofNode.1 = 3 \/ proofNode.1 = 4 \/ proofNode.1 = 5 \/
      proofNode.1 = 6 \/ proofNode.1 = 7 \/ proofNode.1 = 8 \/
      proofNode.1 = 9) ->
    compactNumericNodeTransition proofNode certificateNode restTasks values =
      some ((nextProofTokens, nextCertificateTokens), (nextTasks, values)) ->
    compactNumericVerifierStep start = leftStart ->
    compactNumericCombineState combineTask
        ((proofSuffix, certificateSuffix),
          (restTasks, rightResult :: leftResult :: values)) =
      (((proofSuffix, certificateSuffix),
        (restTasks, parentResult :: values)), none) ->
    compactNumericVerifierStep beforeCombine = finish ->
    compactNumericTreeTaskSteps tree certificate =
      1 + leftSteps + rightSteps + 1 ->
    (forall parentOffset,
      parentOffset <= compactNumericTreeTaskSteps tree certificate ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt start parentOffset) <= rowWeight) ->
    (forall leftOffset, leftOffset < leftSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt leftStart leftOffset /\
          row.nextState =
            compactNumericVerifierStateAt leftStart (leftOffset + 1) /\
          CompactNumericVerifierAcceptedTreeControlledRowBound
            rowWeight row) ->
    (forall rightOffset, rightOffset < rightSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt rightStart rightOffset /\
          row.nextState =
            compactNumericVerifierStateAt rightStart (rightOffset + 1) /\
          CompactNumericVerifierAcceptedTreeControlledRowBound
            rowWeight row) ->
    offset < compactNumericTreeTaskSteps tree certificate ->
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt start offset /\
        row.nextState = compactNumericVerifierStateAt start (offset + 1) /\
        CompactNumericVerifierAcceptedTreeControlledRowBound
          rowWeight row := by
  dsimp only
  intro hleftShape hrightShape htagNe hproofTag hrootTransition hrootStep
    hcombineTransition hcombineStep htaskSteps hweights hleftRows hrightRows
    hoffset
  let fields := (compactListedProofNodeExpectedFields tree proofSuffix).2
  let combineTask := compactNumericCombineTask tag fields
  let leftResult : CompactNumericChildResult :=
    (arithmeticPropositionTokenValues certificateTreeLeft.conclusionList,
      (listedCertificateValidTrace certificateTreeLeft leftCertificate).1)
  let rightResult : CompactNumericChildResult :=
    (arithmeticPropositionTokenValues certificateTreeRight.conclusionList,
      (listedCertificateValidTrace certificateTreeRight rightCertificate).1)
  let parentResult : CompactNumericChildResult :=
    (arithmeticPropositionTokenValues tree.conclusionList,
      (listedCertificateValidTrace tree certificate).1)
  let start := compactNumericTreeTaskStartState tree certificate
    proofSuffix certificateSuffix restTasks values
  let leftStart := compactNumericTreeTaskStartState certificateTreeLeft
    leftCertificate
    (compactListedProofTokens certificateTreeRight ++ proofSuffix)
    (compactStructuralCertificateTokens rightCertificate ++ certificateSuffix)
    (compactNumericParseTask :: combineTask :: restTasks) values
  let rightStart := compactNumericTreeTaskStartState certificateTreeRight
    rightCertificate proofSuffix certificateSuffix
    (combineTask :: restTasks) (leftResult :: values)
  let beforeCombine := compactNumericTreeTaskSuccessState
    certificateTreeRight rightCertificate proofSuffix certificateSuffix
    (combineTask :: restTasks) (leftResult :: values)
  let finish := compactNumericTreeTaskSuccessState tree certificate
    proofSuffix certificateSuffix restTasks values
  let leftSteps := compactNumericTreeTaskSteps certificateTreeLeft leftCertificate
  let rightSteps :=
    compactNumericTreeTaskSteps certificateTreeRight rightCertificate
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected certificate certificateSuffix
  let nextProofTokens := compactListedProofTokens certificateTreeLeft ++
    compactListedProofTokens certificateTreeRight ++ proofSuffix
  let nextCertificateTokens :=
    compactStructuralCertificateTokens leftCertificate ++
      compactStructuralCertificateTokens rightCertificate ++ certificateSuffix
  let nextTasks := compactNumericParseTask :: compactNumericParseTask ::
    combineTask :: restTasks
  have hleftExecuteRaw := compactNumericTreeTask_execute_of_shape
    certificateTreeLeft leftCertificate
      (compactListedProofTokens certificateTreeRight ++ proofSuffix)
      (compactStructuralCertificateTokens rightCertificate ++
        certificateSuffix)
      (compactNumericParseTask :: combineTask :: restTasks) values hleftShape
  have hleftExecute :
      (compactNumericVerifierStep^[leftSteps]) leftStart = rightStart := by
    simpa only [leftSteps, leftStart, rightStart, leftResult,
      compactNumericTreeTaskStartState,
      compactNumericTreeTaskSuccessState] using hleftExecuteRaw
  have hrightExecuteRaw := compactNumericTreeTask_execute_of_shape
    certificateTreeRight rightCertificate proofSuffix certificateSuffix
      (combineTask :: restTasks) (leftResult :: values) hrightShape
  have hrightExecute :
      (compactNumericVerifierStep^[rightSteps]) rightStart = beforeCombine := by
    simpa only [rightSteps, rightStart, beforeCombine,
      compactNumericTreeTaskStartState] using hrightExecuteRaw
  have hparentWeights : forall parentOffset,
      parentOffset <= 1 + leftSteps + rightSteps + 1 ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt start parentOffset) <= rowWeight := by
    intro parentOffset hparentOffset
    exact hweights parentOffset (by omega)
  have hexecutionBounds : CompactNumericVerifierBinaryExecutionWeightBounds
      start leftStart rightStart beforeCombine finish leftSteps rightSteps
        rowWeight :=
    compactNumericVerifierBinaryExecutionWeightBounds_of_parent hrootStep
      hleftExecute hrightExecute hcombineStep hparentWeights
  have hrootRowRaw :=
    exists_compactNumericVerifierCanonicalNonLeafCheckedStepRow_with_globalControlBound
      tree certificate proofSuffix certificateSuffix nextProofTokens
        nextCertificateTokens restTasks nextTasks values values hproofTag
        hrootTransition
        (by simpa only [start, compactNumericTreeTaskStartState] using
          hexecutionBounds.rootCurrent)
        (by simpa only [leftStart, nextProofTokens, nextCertificateTokens,
          nextTasks, combineTask, compactNumericTreeTaskStartState,
          List.append_assoc] using hexecutionBounds.rootNext)
  have hrootRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = start /\ row.nextState = leftStart /\
        CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row := by
    simpa only [start, leftStart, combineTask, proofNode, nextProofTokens,
      nextCertificateTokens, nextTasks, compactNumericTreeTaskStartState,
      List.append_assoc] using hrootRowRaw
  have hcombineCurrent : compactNumericVerifierStateWeight
      ((((proofSuffix, certificateSuffix),
        (combineTask :: restTasks,
          rightResult :: leftResult :: values)), none)) <= rowWeight := by
    simpa only [beforeCombine, rightResult,
      compactNumericTreeTaskSuccessState] using
      hexecutionBounds.combineCurrent
  have hcombineNext : compactNumericVerifierStateWeight
      ((((proofSuffix, certificateSuffix),
        (restTasks, parentResult :: values)), none)) <= rowWeight := by
    simpa only [finish, parentResult,
      compactNumericTreeTaskSuccessState] using hexecutionBounds.combineNext
  have hcombineRowRaw :=
    exists_compactNumericVerifierPublicCombineCheckedStepRow_with_globalControlBound_of_transition
      (rowWeight := rowWeight) proofSuffix certificateSuffix combineTask
      restTasks (rightResult :: leftResult :: values)
      (parentResult :: values) none
      (by simpa only [combineTask, compactNumericCombineTask] using htagNe)
      hcombineTransition hcombineCurrent hcombineNext
  have hcombineRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = beforeCombine /\ row.nextState = finish /\
        CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row := by
    simpa only [beforeCombine, finish, rightResult, parentResult,
      compactNumericTreeTaskSuccessState] using hcombineRowRaw
  have hparentOffset : offset < 1 + leftSteps + rightSteps + 1 := by omega
  exact exists_compactNumericVerifierAcceptedTreeControlledRow_at_binary_offset
    hrootStep hleftExecute hrightExecute hcombineStep hrootRow hleftRows
      hrightRows hcombineRow hparentOffset

set_option maxRecDepth 4000 in
set_option maxHeartbeats 12000000 in
theorem exists_compactNumericVerifierAcceptedAndTaskRow_at_offset_with_control
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
    (left right : ListedCheckedPAProofTree)
    (leftCertificate rightCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid
      (.and Gamma leftFormula rightFormula left right)
      (.binary leftCertificate rightCertificate))
    {rowWeight offset : Nat}
    (hweights : forall parentOffset,
      parentOffset <= compactNumericTreeTaskSteps
          (.and Gamma leftFormula rightFormula left right)
          (.binary leftCertificate rightCertificate) ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState
              (.and Gamma leftFormula rightFormula left right)
              (.binary leftCertificate rightCertificate)
              proofSuffix certificateSuffix restTasks values)
            parentOffset) <= rowWeight)
    (hleftRows : forall leftOffset,
      leftOffset < compactNumericTreeTaskSteps left leftCertificate ->
        exists row : CompactNumericVerifierCheckedStepRow,
          row.currentState = compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState left leftCertificate
              (compactListedProofTokens right ++ proofSuffix)
              (compactStructuralCertificateTokens rightCertificate ++
                certificateSuffix)
              (compactNumericParseTask ::
                compactNumericCombineTask 3
                  (compactListedProofNodeExpectedFields
                    (.and Gamma leftFormula rightFormula left right)
                    proofSuffix).2 :: restTasks)
              values) leftOffset /\
          row.nextState = compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState left leftCertificate
              (compactListedProofTokens right ++ proofSuffix)
              (compactStructuralCertificateTokens rightCertificate ++
                certificateSuffix)
              (compactNumericParseTask ::
                compactNumericCombineTask 3
                  (compactListedProofNodeExpectedFields
                    (.and Gamma leftFormula rightFormula left right)
                    proofSuffix).2 :: restTasks)
              values) (leftOffset + 1) /\
          CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row)
    (hrightRows : forall rightOffset,
      rightOffset < compactNumericTreeTaskSteps right rightCertificate ->
        exists row : CompactNumericVerifierCheckedStepRow,
          row.currentState = compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState right rightCertificate
              proofSuffix certificateSuffix
              (compactNumericCombineTask 3
                (compactListedProofNodeExpectedFields
                  (.and Gamma leftFormula rightFormula left right)
                  proofSuffix).2 :: restTasks)
              ((arithmeticPropositionTokenValues left.conclusionList,
                (listedCertificateValidTrace left leftCertificate).1) ::
                values)) rightOffset /\
          row.nextState = compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState right rightCertificate
              proofSuffix certificateSuffix
              (compactNumericCombineTask 3
                (compactListedProofNodeExpectedFields
                  (.and Gamma leftFormula rightFormula left right)
                  proofSuffix).2 :: restTasks)
              ((arithmeticPropositionTokenValues left.conclusionList,
                (listedCertificateValidTrace left leftCertificate).1) ::
                values)) (rightOffset + 1) /\
          CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row)
    (hoffset : offset < compactNumericTreeTaskSteps
      (.and Gamma leftFormula rightFormula left right)
      (.binary leftCertificate rightCertificate)) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState
          (.and Gamma leftFormula rightFormula left right)
          (.binary leftCertificate rightCertificate)
          proofSuffix certificateSuffix restTasks values) offset /\
      row.nextState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState
          (.and Gamma leftFormula rightFormula left right)
          (.binary leftCertificate rightCertificate)
          proofSuffix certificateSuffix restTasks values) (offset + 1) /\
      CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row := by
  let tree : ListedCheckedPAProofTree :=
    .and Gamma leftFormula rightFormula left right
  let certificate : StructuralValidityCertificate :=
    .binary leftCertificate rightCertificate
  let fields := (compactListedProofNodeExpectedFields tree proofSuffix).2
  let combineTask := compactNumericCombineTask 3 fields
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected certificate certificateSuffix
  let nextProofTokens := compactListedProofTokens left ++
    compactListedProofTokens right ++ proofSuffix
  let nextCertificateTokens :=
    compactStructuralCertificateTokens leftCertificate ++
      compactStructuralCertificateTokens rightCertificate ++ certificateSuffix
  let nextTasks := compactNumericParseTask :: compactNumericParseTask ::
    combineTask :: restTasks
  have hshape :
      compactNumericTreeCertificateShapeMatches tree certificate = true :=
    compactNumericTreeCertificateShapeMatches_eq_true_of_valid tree
      certificate (by simpa only [tree, certificate] using hvalid)
  have hchildShapes :
      compactNumericTreeCertificateShapeMatches left leftCertificate = true /\
        compactNumericTreeCertificateShapeMatches right rightCertificate =
          true := by
    simpa only [tree, certificate,
      compactNumericTreeCertificateShapeMatches, Bool.and_eq_true] using hshape
  rcases hchildShapes with ⟨hleftShape, hrightShape⟩
  have hrootTransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((nextProofTokens, nextCertificateTokens), (nextTasks, values)) := by
    simp [proofNode, certificateNode, tree, certificate, nextProofTokens,
      nextCertificateTokens, nextTasks, fields, combineTask,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix, compactNumericNodeTransition,
      List.append_assoc]
  have hrootStep : compactNumericVerifierStep
      (compactNumericTreeTaskStartState tree certificate proofSuffix
        certificateSuffix restTasks values) =
      compactNumericTreeTaskStartState left leftCertificate
        (compactListedProofTokens right ++ proofSuffix)
        (compactStructuralCertificateTokens rightCertificate ++
          certificateSuffix)
        (compactNumericParseTask :: combineTask :: restTasks) values := by
    simpa only [tree, certificate, fields, combineTask,
      compactNumericTreeTaskStartState, List.append_assoc] using
      compactNumericVerifierCanonicalAnd_step Gamma leftFormula rightFormula
        left right leftCertificate rightCertificate proofSuffix
        certificateSuffix restTasks values
  have hcombineTransition :=
    compactNumericVerifierCanonicalAnd_combine_transition Gamma leftFormula
      rightFormula left right leftCertificate rightCertificate proofSuffix
      certificateSuffix restTasks values
  have hcombineStep := compactNumericVerifierCanonicalAnd_combine_step Gamma
    leftFormula rightFormula left right leftCertificate rightCertificate
      proofSuffix certificateSuffix restTasks values
  have htaskSteps : compactNumericTreeTaskSteps tree certificate =
      1 + compactNumericTreeTaskSteps left leftCertificate +
        compactNumericTreeTaskSteps right rightCertificate + 1 := by
    simp [tree, certificate, compactNumericTreeTaskSteps]
  have hrow :=
    exists_compactNumericVerifierAcceptedBinaryTaskRow_at_offset_with_control
      tree left right certificate leftCertificate rightCertificate proofSuffix
        certificateSuffix restTasks values 3 hleftShape hrightShape (by omega)
        (by simp [tree, compactListedProofNodeExpectedFields]) hrootTransition
        hrootStep
        (by simpa only [tree, certificate, fields, combineTask,
          compactNumericTreeTaskSuccessState] using hcombineTransition)
        (by simpa only [tree, certificate, fields, combineTask] using
          hcombineStep)
        htaskSteps
        (by simpa only [tree, certificate] using hweights)
        (by simpa only [tree, fields, combineTask] using hleftRows)
        (by simpa only [tree, fields, combineTask] using hrightRows)
        (by simpa only [tree, certificate] using hoffset)
  simpa only [tree, certificate] using hrow

set_option maxRecDepth 4000 in
set_option maxHeartbeats 12000000 in
theorem exists_compactNumericVerifierAcceptedCutTaskRow_at_offset_with_control
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (left right : ListedCheckedPAProofTree)
    (leftCertificate rightCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.cut Gamma formula left right)
      (.binary leftCertificate rightCertificate))
    {rowWeight offset : Nat}
    (hweights : forall parentOffset,
      parentOffset <= compactNumericTreeTaskSteps
          (.cut Gamma formula left right)
          (.binary leftCertificate rightCertificate) ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState
              (.cut Gamma formula left right)
              (.binary leftCertificate rightCertificate)
              proofSuffix certificateSuffix restTasks values)
            parentOffset) <= rowWeight)
    (hleftRows : forall leftOffset,
      leftOffset < compactNumericTreeTaskSteps left leftCertificate ->
        exists row : CompactNumericVerifierCheckedStepRow,
          row.currentState = compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState left leftCertificate
              (compactListedProofTokens right ++ proofSuffix)
              (compactStructuralCertificateTokens rightCertificate ++
                certificateSuffix)
              (compactNumericParseTask ::
                compactNumericCombineTask 9
                  (compactListedProofNodeExpectedFields
                    (.cut Gamma formula left right) proofSuffix).2 :: restTasks)
              values) leftOffset /\
          row.nextState = compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState left leftCertificate
              (compactListedProofTokens right ++ proofSuffix)
              (compactStructuralCertificateTokens rightCertificate ++
                certificateSuffix)
              (compactNumericParseTask ::
                compactNumericCombineTask 9
                  (compactListedProofNodeExpectedFields
                    (.cut Gamma formula left right) proofSuffix).2 :: restTasks)
              values) (leftOffset + 1) /\
          CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row)
    (hrightRows : forall rightOffset,
      rightOffset < compactNumericTreeTaskSteps right rightCertificate ->
        exists row : CompactNumericVerifierCheckedStepRow,
          row.currentState = compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState right rightCertificate
              proofSuffix certificateSuffix
              (compactNumericCombineTask 9
                (compactListedProofNodeExpectedFields
                  (.cut Gamma formula left right) proofSuffix).2 :: restTasks)
              ((arithmeticPropositionTokenValues left.conclusionList,
                (listedCertificateValidTrace left leftCertificate).1) ::
                values)) rightOffset /\
          row.nextState = compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState right rightCertificate
              proofSuffix certificateSuffix
              (compactNumericCombineTask 9
                (compactListedProofNodeExpectedFields
                  (.cut Gamma formula left right) proofSuffix).2 :: restTasks)
              ((arithmeticPropositionTokenValues left.conclusionList,
                (listedCertificateValidTrace left leftCertificate).1) ::
                values)) (rightOffset + 1) /\
          CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row)
    (hoffset : offset < compactNumericTreeTaskSteps
      (.cut Gamma formula left right)
      (.binary leftCertificate rightCertificate)) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.cut Gamma formula left right)
          (.binary leftCertificate rightCertificate)
          proofSuffix certificateSuffix restTasks values) offset /\
      row.nextState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.cut Gamma formula left right)
          (.binary leftCertificate rightCertificate)
          proofSuffix certificateSuffix restTasks values) (offset + 1) /\
      CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row := by
  let tree : ListedCheckedPAProofTree := .cut Gamma formula left right
  let certificate : StructuralValidityCertificate :=
    .binary leftCertificate rightCertificate
  let fields := (compactListedProofNodeExpectedFields tree proofSuffix).2
  let combineTask := compactNumericCombineTask 9 fields
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected certificate certificateSuffix
  let nextProofTokens := compactListedProofTokens left ++
    compactListedProofTokens right ++ proofSuffix
  let nextCertificateTokens :=
    compactStructuralCertificateTokens leftCertificate ++
      compactStructuralCertificateTokens rightCertificate ++ certificateSuffix
  let nextTasks := compactNumericParseTask :: compactNumericParseTask ::
    combineTask :: restTasks
  have hshape :
      compactNumericTreeCertificateShapeMatches tree certificate = true :=
    compactNumericTreeCertificateShapeMatches_eq_true_of_valid tree
      certificate (by simpa only [tree, certificate] using hvalid)
  have hchildShapes :
      compactNumericTreeCertificateShapeMatches left leftCertificate = true /\
        compactNumericTreeCertificateShapeMatches right rightCertificate =
          true := by
    simpa only [tree, certificate,
      compactNumericTreeCertificateShapeMatches, Bool.and_eq_true] using hshape
  rcases hchildShapes with ⟨hleftShape, hrightShape⟩
  have hrootTransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((nextProofTokens, nextCertificateTokens), (nextTasks, values)) := by
    simp [proofNode, certificateNode, tree, certificate, nextProofTokens,
      nextCertificateTokens, nextTasks, fields, combineTask,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix, compactNumericNodeTransition,
      List.append_assoc]
  have hrootStep : compactNumericVerifierStep
      (compactNumericTreeTaskStartState tree certificate proofSuffix
        certificateSuffix restTasks values) =
      compactNumericTreeTaskStartState left leftCertificate
        (compactListedProofTokens right ++ proofSuffix)
        (compactStructuralCertificateTokens rightCertificate ++
          certificateSuffix)
        (compactNumericParseTask :: combineTask :: restTasks) values := by
    simpa only [tree, certificate, fields, combineTask,
      compactNumericTreeTaskStartState, List.append_assoc] using
      compactNumericVerifierCanonicalCut_step Gamma formula left right
        leftCertificate rightCertificate proofSuffix certificateSuffix
        restTasks values
  have hcombineTransition :=
    compactNumericVerifierCanonicalCut_combine_transition Gamma formula left
      right leftCertificate rightCertificate proofSuffix certificateSuffix
      restTasks values
  have hcombineStep := compactNumericVerifierCanonicalCut_combine_step Gamma
    formula left right leftCertificate rightCertificate proofSuffix
      certificateSuffix restTasks values
  have htaskSteps : compactNumericTreeTaskSteps tree certificate =
      1 + compactNumericTreeTaskSteps left leftCertificate +
        compactNumericTreeTaskSteps right rightCertificate + 1 := by
    simp [tree, certificate, compactNumericTreeTaskSteps]
  have hrow :=
    exists_compactNumericVerifierAcceptedBinaryTaskRow_at_offset_with_control
      tree left right certificate leftCertificate rightCertificate proofSuffix
        certificateSuffix restTasks values 9 hleftShape hrightShape (by omega)
        (by simp [tree, compactListedProofNodeExpectedFields]) hrootTransition
        hrootStep
        (by simpa only [tree, certificate, fields, combineTask,
          compactNumericTreeTaskSuccessState] using hcombineTransition)
        (by simpa only [tree, certificate, fields, combineTask] using
          hcombineStep)
        htaskSteps
        (by simpa only [tree, certificate] using hweights)
        (by simpa only [tree, fields, combineTask] using hleftRows)
        (by simpa only [tree, fields, combineTask] using hrightRows)
        (by simpa only [tree, certificate] using hoffset)
  simpa only [tree, certificate] using hrow

#print axioms
  exists_compactNumericVerifierAcceptedBinaryTaskRow_at_offset_with_control
#print axioms
  exists_compactNumericVerifierAcceptedAndTaskRow_at_offset_with_control
#print axioms
  exists_compactNumericVerifierAcceptedCutTaskRow_at_offset_with_control

end FoundationCompactNumericListedDirectVerifierAcceptedBinaryTaskRowsStateTableControlBounds
