import integration.FoundationCompactNumericListedDirectVerifierAcceptedTreeTaskRowsGlobalBound
import integration.FoundationCompactNumericListedDirectVerifierCanonicalNonLeafExactSteps
import integration.FoundationCompactNumericListedDirectVerifierCanonicalCombineExactSteps

/-!
# Globally bounded checked rows for accepted binary tree tasks

The two theorems below splice the canonical root and combine rows around the
accepted rows supplied for the left and right subtrees.  The child starts use
the exact depth-first suffixes and value stack of the numeric task machine.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedBinaryTaskRowsGlobalBound

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
open FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsGlobalBound
open FoundationCompactNumericListedDirectVerifierTypedNonLeafGlobalBound
open FoundationCompactNumericListedDirectVerifierAcceptedTreeTaskRowsGlobalBound
open FoundationCompactNumericListedDirectVerifierCanonicalNonLeafRowsGlobalBound
open FoundationCompactNumericListedDirectVerifierCanonicalNonLeafExactSteps
open FoundationCompactNumericListedDirectVerifierCanonicalCombineExactSteps
open FoundationCompactNumericListedPAAxiomLeafOccurrence

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem exists_compactNumericVerifierAcceptedAndRow_at_offset
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
          compactNumericVerifierAcceptedTreeRowBound rowWeight row)
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
          compactNumericVerifierAcceptedTreeRowBound rowWeight row)
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
      compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
  let tree : ListedCheckedPAProofTree :=
    .and Gamma leftFormula rightFormula left right
  let certificate : StructuralValidityCertificate :=
    .binary leftCertificate rightCertificate
  let fields := (compactListedProofNodeExpectedFields tree proofSuffix).2
  let combineTask := compactNumericCombineTask 3 fields
  let leftResult : CompactNumericChildResult :=
    (arithmeticPropositionTokenValues left.conclusionList,
      (listedCertificateValidTrace left leftCertificate).1)
  let rightResult : CompactNumericChildResult :=
    (arithmeticPropositionTokenValues right.conclusionList,
      (listedCertificateValidTrace right rightCertificate).1)
  let parentResult : CompactNumericChildResult :=
    (arithmeticPropositionTokenValues tree.conclusionList,
      (listedCertificateValidTrace tree certificate).1)
  let start := compactNumericTreeTaskStartState tree certificate
    proofSuffix certificateSuffix restTasks values
  let leftStart := compactNumericTreeTaskStartState left leftCertificate
    (compactListedProofTokens right ++ proofSuffix)
    (compactStructuralCertificateTokens rightCertificate ++
      certificateSuffix)
    (compactNumericParseTask :: combineTask :: restTasks) values
  let rightStart := compactNumericTreeTaskStartState right rightCertificate
    proofSuffix certificateSuffix (combineTask :: restTasks)
    (leftResult :: values)
  let beforeCombine := compactNumericTreeTaskSuccessState right
    rightCertificate proofSuffix certificateSuffix
    (combineTask :: restTasks) (leftResult :: values)
  let finish := compactNumericTreeTaskSuccessState tree certificate
    proofSuffix certificateSuffix restTasks values
  let leftSteps := compactNumericTreeTaskSteps left leftCertificate
  let rightSteps := compactNumericTreeTaskSteps right rightCertificate

  have hshape :
      compactNumericTreeCertificateShapeMatches tree certificate = true :=
    compactNumericTreeCertificateShapeMatches_eq_true_of_valid tree
      certificate (by simpa [tree, certificate] using hvalid)
  have hchildShapes :
      compactNumericTreeCertificateShapeMatches left leftCertificate = true /\
        compactNumericTreeCertificateShapeMatches right rightCertificate =
          true := by
    simpa only [tree, certificate,
      compactNumericTreeCertificateShapeMatches, Bool.and_eq_true] using
      hshape
  rcases hchildShapes with ⟨hleftShape, hrightShape⟩

  have hrootStep : compactNumericVerifierStep start = leftStart := by
    simpa [start, leftStart, tree, certificate, fields, combineTask,
      compactNumericTreeTaskStartState, List.append_assoc] using
      (compactNumericVerifierCanonicalAnd_step Gamma leftFormula
        rightFormula left right leftCertificate rightCertificate proofSuffix
        certificateSuffix restTasks values)
  have hleftRun := compactNumericTreeTask_execute_of_shape left
    leftCertificate (compactListedProofTokens right ++ proofSuffix)
    (compactStructuralCertificateTokens rightCertificate ++
      certificateSuffix)
    (compactNumericParseTask :: combineTask :: restTasks) values hleftShape
  have hleftExecute :
      (compactNumericVerifierStep^[leftSteps]) leftStart = rightStart := by
    simpa [leftSteps, leftStart, rightStart, leftResult,
      compactNumericTreeTaskStartState,
      compactNumericTreeTaskSuccessState] using hleftRun
  have hrightRun := compactNumericTreeTask_execute_of_shape right
    rightCertificate proofSuffix certificateSuffix
    (combineTask :: restTasks) (leftResult :: values) hrightShape
  have hrightExecute :
      (compactNumericVerifierStep^[rightSteps]) rightStart =
        beforeCombine := by
    simpa [rightSteps, rightStart, beforeCombine,
      compactNumericTreeTaskStartState] using hrightRun
  have hcombineStep :
      compactNumericVerifierStep beforeCombine = finish := by
    simpa [beforeCombine, finish, tree, certificate, fields, combineTask,
      leftResult] using
      (compactNumericVerifierCanonicalAnd_combine_step Gamma leftFormula
        rightFormula left right leftCertificate rightCertificate proofSuffix
        certificateSuffix restTasks values)

  have hparentWeights : forall parentOffset,
      parentOffset <= 1 + leftSteps + rightSteps + 1 ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt start parentOffset) <= rowWeight := by
    simpa [start, tree, certificate, leftSteps, rightSteps,
      compactNumericTreeTaskSteps] using hweights
  have hexecutionBounds :
      CompactNumericVerifierBinaryExecutionWeightBounds start leftStart
        rightStart beforeCombine finish leftSteps rightSteps rowWeight :=
    compactNumericVerifierBinaryExecutionWeightBounds_of_parent hrootStep
      hleftExecute hrightExecute hcombineStep hparentWeights

  have hrootRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = start /\ row.nextState = leftStart /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound
              rowWeight := by
    have hrow :=
      exists_compactNumericVerifierCanonicalAndCheckedStepRow_with_globalBound
        Gamma leftFormula rightFormula left right leftCertificate
        rightCertificate proofSuffix certificateSuffix restTasks values
        (by
          simpa [start, tree, certificate,
            compactNumericTreeTaskStartState] using
            hexecutionBounds.rootCurrent)
        (by
          simpa [leftStart, tree, fields, combineTask,
            compactNumericTreeTaskStartState, List.append_assoc] using
            hexecutionBounds.rootNext)
    simpa [start, leftStart, tree, certificate, fields, combineTask,
      compactNumericTreeTaskStartState, List.append_assoc] using hrow

  have hleftRows' : forall leftOffset, leftOffset < leftSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt leftStart leftOffset /\
          row.nextState =
            compactNumericVerifierStateAt leftStart (leftOffset + 1) /\
          compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
    intro leftOffset hleftOffset
    have hrow := hleftRows leftOffset (by
      simpa [leftSteps] using hleftOffset)
    simpa [leftStart, tree, fields, combineTask] using hrow
  have hrightRows' : forall rightOffset, rightOffset < rightSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt rightStart rightOffset /\
          row.nextState =
            compactNumericVerifierStateAt rightStart (rightOffset + 1) /\
          compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
    intro rightOffset hrightOffset
    have hrow := hrightRows rightOffset (by
      simpa [rightSteps] using hrightOffset)
    simpa [rightStart, tree, fields, combineTask, leftResult] using hrow

  have hcombineTaskNe : combineTask.1 ≠ 10 := by
    simp [combineTask, compactNumericCombineTask]
  have hcombineTransition :
      compactNumericCombineState combineTask
          ((proofSuffix, certificateSuffix),
            (restTasks, rightResult :: leftResult :: values)) =
        (((proofSuffix, certificateSuffix),
          (restTasks, parentResult :: values)), none) := by
    simpa [tree, certificate, fields, combineTask, leftResult, rightResult,
      parentResult, compactNumericTreeTaskSuccessState] using
      (compactNumericVerifierCanonicalAnd_combine_transition Gamma
        leftFormula rightFormula left right leftCertificate rightCertificate
        proofSuffix certificateSuffix restTasks values)
  have hcombineCurrent :
      compactNumericVerifierStateWeight
          ((((proofSuffix, certificateSuffix),
            (combineTask :: restTasks,
              rightResult :: leftResult :: values)), none)) <= rowWeight := by
    simpa [beforeCombine, rightResult,
      compactNumericTreeTaskSuccessState] using
      hexecutionBounds.combineCurrent
  have hcombineNext :
      compactNumericVerifierStateWeight
          ((((proofSuffix, certificateSuffix),
            (restTasks, parentResult :: values)), none)) <= rowWeight := by
    simpa [finish, parentResult, compactNumericTreeTaskSuccessState] using
      hexecutionBounds.combineNext
  have hcombineRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = beforeCombine /\ row.nextState = finish /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierNonParseGlobalCoordinateSizeBound
              rowWeight := by
    have hrow :=
      exists_compactNumericVerifierPublicCombineCheckedStepRow_with_globalBound_of_transition
        proofSuffix certificateSuffix combineTask restTasks
        (rightResult :: leftResult :: values) (parentResult :: values) none
        hcombineTaskNe hcombineTransition hcombineCurrent hcombineNext
    simpa [beforeCombine, finish, rightResult, parentResult,
      compactNumericTreeTaskSuccessState] using hrow

  have hoffset' : offset < 1 + leftSteps + rightSteps + 1 := by
    simpa [tree, certificate, leftSteps, rightSteps,
      compactNumericTreeTaskSteps] using hoffset
  have hrow := exists_compactNumericVerifierAcceptedTreeRow_at_binary_offset
    hrootStep hleftExecute hrightExecute hcombineStep hrootRow hleftRows'
    hrightRows' hcombineRow hoffset'
  simpa [start, tree, certificate] using hrow

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem exists_compactNumericVerifierAcceptedCutRow_at_offset
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
                    (.cut Gamma formula left right) proofSuffix).2 ::
                  restTasks)
              values) leftOffset /\
          row.nextState = compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState left leftCertificate
              (compactListedProofTokens right ++ proofSuffix)
              (compactStructuralCertificateTokens rightCertificate ++
                certificateSuffix)
              (compactNumericParseTask ::
                compactNumericCombineTask 9
                  (compactListedProofNodeExpectedFields
                    (.cut Gamma formula left right) proofSuffix).2 ::
                  restTasks)
              values) (leftOffset + 1) /\
          compactNumericVerifierAcceptedTreeRowBound rowWeight row)
    (hrightRows : forall rightOffset,
      rightOffset < compactNumericTreeTaskSteps right rightCertificate ->
        exists row : CompactNumericVerifierCheckedStepRow,
          row.currentState = compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState right rightCertificate
              proofSuffix certificateSuffix
              (compactNumericCombineTask 9
                (compactListedProofNodeExpectedFields
                  (.cut Gamma formula left right) proofSuffix).2 ::
                restTasks)
              ((arithmeticPropositionTokenValues left.conclusionList,
                (listedCertificateValidTrace left leftCertificate).1) ::
                values)) rightOffset /\
          row.nextState = compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState right rightCertificate
              proofSuffix certificateSuffix
              (compactNumericCombineTask 9
                (compactListedProofNodeExpectedFields
                  (.cut Gamma formula left right) proofSuffix).2 ::
                restTasks)
              ((arithmeticPropositionTokenValues left.conclusionList,
                (listedCertificateValidTrace left leftCertificate).1) ::
                values)) (rightOffset + 1) /\
          compactNumericVerifierAcceptedTreeRowBound rowWeight row)
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
      compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
  let tree : ListedCheckedPAProofTree := .cut Gamma formula left right
  let certificate : StructuralValidityCertificate :=
    .binary leftCertificate rightCertificate
  let fields := (compactListedProofNodeExpectedFields tree proofSuffix).2
  let combineTask := compactNumericCombineTask 9 fields
  let leftResult : CompactNumericChildResult :=
    (arithmeticPropositionTokenValues left.conclusionList,
      (listedCertificateValidTrace left leftCertificate).1)
  let rightResult : CompactNumericChildResult :=
    (arithmeticPropositionTokenValues right.conclusionList,
      (listedCertificateValidTrace right rightCertificate).1)
  let parentResult : CompactNumericChildResult :=
    (arithmeticPropositionTokenValues tree.conclusionList,
      (listedCertificateValidTrace tree certificate).1)
  let start := compactNumericTreeTaskStartState tree certificate
    proofSuffix certificateSuffix restTasks values
  let leftStart := compactNumericTreeTaskStartState left leftCertificate
    (compactListedProofTokens right ++ proofSuffix)
    (compactStructuralCertificateTokens rightCertificate ++
      certificateSuffix)
    (compactNumericParseTask :: combineTask :: restTasks) values
  let rightStart := compactNumericTreeTaskStartState right rightCertificate
    proofSuffix certificateSuffix (combineTask :: restTasks)
    (leftResult :: values)
  let beforeCombine := compactNumericTreeTaskSuccessState right
    rightCertificate proofSuffix certificateSuffix
    (combineTask :: restTasks) (leftResult :: values)
  let finish := compactNumericTreeTaskSuccessState tree certificate
    proofSuffix certificateSuffix restTasks values
  let leftSteps := compactNumericTreeTaskSteps left leftCertificate
  let rightSteps := compactNumericTreeTaskSteps right rightCertificate

  have hshape :
      compactNumericTreeCertificateShapeMatches tree certificate = true :=
    compactNumericTreeCertificateShapeMatches_eq_true_of_valid tree
      certificate (by simpa [tree, certificate] using hvalid)
  have hchildShapes :
      compactNumericTreeCertificateShapeMatches left leftCertificate = true /\
        compactNumericTreeCertificateShapeMatches right rightCertificate =
          true := by
    simpa only [tree, certificate,
      compactNumericTreeCertificateShapeMatches, Bool.and_eq_true] using
      hshape
  rcases hchildShapes with ⟨hleftShape, hrightShape⟩

  have hrootStep : compactNumericVerifierStep start = leftStart := by
    simpa [start, leftStart, tree, certificate, fields, combineTask,
      compactNumericTreeTaskStartState, List.append_assoc] using
      (compactNumericVerifierCanonicalCut_step Gamma formula left right
        leftCertificate rightCertificate proofSuffix certificateSuffix
        restTasks values)
  have hleftRun := compactNumericTreeTask_execute_of_shape left
    leftCertificate (compactListedProofTokens right ++ proofSuffix)
    (compactStructuralCertificateTokens rightCertificate ++
      certificateSuffix)
    (compactNumericParseTask :: combineTask :: restTasks) values hleftShape
  have hleftExecute :
      (compactNumericVerifierStep^[leftSteps]) leftStart = rightStart := by
    simpa [leftSteps, leftStart, rightStart, leftResult,
      compactNumericTreeTaskStartState,
      compactNumericTreeTaskSuccessState] using hleftRun
  have hrightRun := compactNumericTreeTask_execute_of_shape right
    rightCertificate proofSuffix certificateSuffix
    (combineTask :: restTasks) (leftResult :: values) hrightShape
  have hrightExecute :
      (compactNumericVerifierStep^[rightSteps]) rightStart =
        beforeCombine := by
    simpa [rightSteps, rightStart, beforeCombine,
      compactNumericTreeTaskStartState] using hrightRun
  have hcombineStep :
      compactNumericVerifierStep beforeCombine = finish := by
    simpa [beforeCombine, finish, tree, certificate, fields, combineTask,
      leftResult] using
      (compactNumericVerifierCanonicalCut_combine_step Gamma formula left
        right leftCertificate rightCertificate proofSuffix certificateSuffix
        restTasks values)

  have hparentWeights : forall parentOffset,
      parentOffset <= 1 + leftSteps + rightSteps + 1 ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt start parentOffset) <= rowWeight := by
    simpa [start, tree, certificate, leftSteps, rightSteps,
      compactNumericTreeTaskSteps] using hweights
  have hexecutionBounds :
      CompactNumericVerifierBinaryExecutionWeightBounds start leftStart
        rightStart beforeCombine finish leftSteps rightSteps rowWeight :=
    compactNumericVerifierBinaryExecutionWeightBounds_of_parent hrootStep
      hleftExecute hrightExecute hcombineStep hparentWeights

  have hrootRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = start /\ row.nextState = leftStart /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound
              rowWeight := by
    have hrow :=
      exists_compactNumericVerifierCanonicalCutCheckedStepRow_with_globalBound
        Gamma formula left right leftCertificate rightCertificate
        proofSuffix certificateSuffix restTasks values
        (by
          simpa [start, tree, certificate,
            compactNumericTreeTaskStartState] using
            hexecutionBounds.rootCurrent)
        (by
          simpa [leftStart, tree, fields, combineTask,
            compactNumericTreeTaskStartState, List.append_assoc] using
            hexecutionBounds.rootNext)
    simpa [start, leftStart, tree, certificate, fields, combineTask,
      compactNumericTreeTaskStartState, List.append_assoc] using hrow

  have hleftRows' : forall leftOffset, leftOffset < leftSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt leftStart leftOffset /\
          row.nextState =
            compactNumericVerifierStateAt leftStart (leftOffset + 1) /\
          compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
    intro leftOffset hleftOffset
    have hrow := hleftRows leftOffset (by
      simpa [leftSteps] using hleftOffset)
    simpa [leftStart, tree, fields, combineTask] using hrow
  have hrightRows' : forall rightOffset, rightOffset < rightSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt rightStart rightOffset /\
          row.nextState =
            compactNumericVerifierStateAt rightStart (rightOffset + 1) /\
          compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
    intro rightOffset hrightOffset
    have hrow := hrightRows rightOffset (by
      simpa [rightSteps] using hrightOffset)
    simpa [rightStart, tree, fields, combineTask, leftResult] using hrow

  have hcombineTaskNe : combineTask.1 ≠ 10 := by
    simp [combineTask, compactNumericCombineTask]
  have hcombineTransition :
      compactNumericCombineState combineTask
          ((proofSuffix, certificateSuffix),
            (restTasks, rightResult :: leftResult :: values)) =
        (((proofSuffix, certificateSuffix),
          (restTasks, parentResult :: values)), none) := by
    simpa [tree, certificate, fields, combineTask, leftResult, rightResult,
      parentResult, compactNumericTreeTaskSuccessState] using
      (compactNumericVerifierCanonicalCut_combine_transition Gamma formula
        left right leftCertificate rightCertificate proofSuffix
        certificateSuffix restTasks values)
  have hcombineCurrent :
      compactNumericVerifierStateWeight
          ((((proofSuffix, certificateSuffix),
            (combineTask :: restTasks,
              rightResult :: leftResult :: values)), none)) <= rowWeight := by
    simpa [beforeCombine, rightResult,
      compactNumericTreeTaskSuccessState] using
      hexecutionBounds.combineCurrent
  have hcombineNext :
      compactNumericVerifierStateWeight
          ((((proofSuffix, certificateSuffix),
            (restTasks, parentResult :: values)), none)) <= rowWeight := by
    simpa [finish, parentResult, compactNumericTreeTaskSuccessState] using
      hexecutionBounds.combineNext
  have hcombineRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = beforeCombine /\ row.nextState = finish /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierNonParseGlobalCoordinateSizeBound
              rowWeight := by
    have hrow :=
      exists_compactNumericVerifierPublicCombineCheckedStepRow_with_globalBound_of_transition
        proofSuffix certificateSuffix combineTask restTasks
        (rightResult :: leftResult :: values) (parentResult :: values) none
        hcombineTaskNe hcombineTransition hcombineCurrent hcombineNext
    simpa [beforeCombine, finish, rightResult, parentResult,
      compactNumericTreeTaskSuccessState] using hrow

  have hoffset' : offset < 1 + leftSteps + rightSteps + 1 := by
    simpa [tree, certificate, leftSteps, rightSteps,
      compactNumericTreeTaskSteps] using hoffset
  have hrow := exists_compactNumericVerifierAcceptedTreeRow_at_binary_offset
    hrootStep hleftExecute hrightExecute hcombineStep hrootRow hleftRows'
    hrightRows' hcombineRow hoffset'
  simpa [start, tree, certificate] using hrow

#print axioms exists_compactNumericVerifierAcceptedAndRow_at_offset
#print axioms exists_compactNumericVerifierAcceptedCutRow_at_offset

end FoundationCompactNumericListedDirectVerifierAcceptedBinaryTaskRowsGlobalBound
