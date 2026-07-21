import integration.FoundationCompactNumericListedDirectVerifierAcceptedTreeRowStateTableControlBounds
import integration.FoundationCompactNumericListedDirectVerifierAcceptedUnaryTaskRowsGlobalBound

/-!
# Accepted unary task rows with numeric state-table controls

These theorems splice the controlled canonical root, premise, and combine rows
at the exact execution offsets.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedUnaryTaskRowsStateTableControlBounds

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
theorem exists_compactNumericVerifierAcceptedOrTaskRow_at_offset_with_control
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid
      (.or Gamma leftFormula rightFormula premise)
      (.unary premiseCertificate))
    {rowWeight offset : Nat}
    (hweights : forall parentOffset,
      parentOffset <= compactNumericTreeTaskSteps
          (.or Gamma leftFormula rightFormula premise)
          (.unary premiseCertificate) ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState
              (.or Gamma leftFormula rightFormula premise)
              (.unary premiseCertificate) proofSuffix certificateSuffix
              restTasks values) parentOffset) <= rowWeight)
    (hpremiseRows :
      let fields := (compactListedProofNodeExpectedFields
        (.or Gamma leftFormula rightFormula premise) proofSuffix).2
      forall premiseOffset,
        premiseOffset <
            compactNumericTreeTaskSteps premise premiseCertificate ->
          exists row : CompactNumericVerifierCheckedStepRow,
            row.currentState = compactNumericVerifierStateAt
              (compactNumericTreeTaskStartState premise premiseCertificate
                proofSuffix certificateSuffix
                (compactNumericCombineTask 4 fields :: restTasks) values)
              premiseOffset /\
            row.nextState = compactNumericVerifierStateAt
              (compactNumericTreeTaskStartState premise premiseCertificate
                proofSuffix certificateSuffix
                (compactNumericCombineTask 4 fields :: restTasks) values)
              (premiseOffset + 1) /\
            CompactNumericVerifierAcceptedTreeControlledRowBound
              rowWeight row)
    (hoffset : offset < compactNumericTreeTaskSteps
      (.or Gamma leftFormula rightFormula premise)
      (.unary premiseCertificate)) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState
          (.or Gamma leftFormula rightFormula premise)
          (.unary premiseCertificate) proofSuffix certificateSuffix
          restTasks values) offset /\
      row.nextState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState
          (.or Gamma leftFormula rightFormula premise)
          (.unary premiseCertificate) proofSuffix certificateSuffix
          restTasks values) (offset + 1) /\
      CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row := by
  let tree : ListedCheckedPAProofTree :=
    .or Gamma leftFormula rightFormula premise
  let certificate : StructuralValidityCertificate :=
    .unary premiseCertificate
  let fields := (compactListedProofNodeExpectedFields tree proofSuffix).2
  let start := compactNumericTreeTaskStartState tree certificate
    proofSuffix certificateSuffix restTasks values
  let childStart := compactNumericTreeTaskStartState premise
    premiseCertificate proofSuffix certificateSuffix
    (compactNumericCombineTask 4 fields :: restTasks) values
  let childSteps := compactNumericTreeTaskSteps premise premiseCertificate
  let beforeCombine := compactNumericTreeTaskSuccessState premise
    premiseCertificate proofSuffix certificateSuffix
    (compactNumericCombineTask 4 fields :: restTasks) values
  let finish := compactNumericTreeTaskSuccessState tree certificate
    proofSuffix certificateSuffix restTasks values
  let premiseResult : CompactNumericChildResult :=
    (arithmeticPropositionTokenValues premise.conclusionList,
      (listedCertificateValidTrace premise premiseCertificate).1)
  let parentResult : CompactNumericChildResult :=
    (arithmeticPropositionTokenValues tree.conclusionList,
      (listedCertificateValidTrace tree certificate).1)
  have hpremiseValid :
      listedCertificateValid premise premiseCertificate := hvalid.2.2
  have hpremiseShape :=
    compactNumericTreeCertificateShapeMatches_eq_true_of_valid
      premise premiseCertificate hpremiseValid
  have hchildExecuteRaw := compactNumericTreeTask_execute_of_shape
    premise premiseCertificate proofSuffix certificateSuffix
    (compactNumericCombineTask 4 fields :: restTasks) values hpremiseShape
  have hchildExecute :
      (compactNumericVerifierStep^[childSteps]) childStart = beforeCombine := by
    simpa only [childSteps, childStart, beforeCombine,
      compactNumericTreeTaskStartState] using hchildExecuteRaw
  have hrootStep : compactNumericVerifierStep start = childStart := by
    simpa only [start, childStart, tree, certificate, fields,
      compactNumericTreeTaskStartState] using
      compactNumericVerifierCanonicalOr_step Gamma leftFormula rightFormula
        premise premiseCertificate proofSuffix certificateSuffix restTasks
        values
  have hcombineStep :
      compactNumericVerifierStep beforeCombine = finish := by
    simpa only [beforeCombine, finish, tree, certificate, fields] using
      compactNumericVerifierCanonicalOr_combine_step Gamma leftFormula
        rightFormula premise premiseCertificate proofSuffix certificateSuffix
        restTasks values
  have hparentWeights : forall parentOffset,
      parentOffset <= 1 + childSteps + 1 ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt start parentOffset) <= rowWeight := by
    intro parentOffset hparentOffset
    have hparentOffset' : parentOffset <= compactNumericTreeTaskSteps
        (.or Gamma leftFormula rightFormula premise)
        (.unary premiseCertificate) := by
      simpa only [childSteps, compactNumericTreeTaskSteps] using hparentOffset
    simpa only [start, tree, certificate] using
      hweights parentOffset hparentOffset'
  have hexecutionBounds : CompactNumericVerifierUnaryExecutionWeightBounds
      start childStart beforeCombine finish childSteps rowWeight :=
    compactNumericVerifierUnaryExecutionWeightBounds_of_parent
      hrootStep hchildExecute hcombineStep hparentWeights
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected certificate certificateSuffix
  let nextProofTokens := compactListedProofTokens premise ++ proofSuffix
  let nextCertificateTokens :=
    compactStructuralCertificateTokens premiseCertificate ++
      certificateSuffix
  let nextTasks := compactNumericParseTask ::
    compactNumericCombineTask 4 fields :: restTasks
  have hrootTransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, values)) := by
    simp [proofNode, certificateNode, tree, certificate, nextProofTokens,
      nextCertificateTokens, nextTasks, fields,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix, compactNumericNodeTransition]
  have hrootRowRaw :=
    exists_compactNumericVerifierCanonicalNonLeafCheckedStepRow_with_globalControlBound
      tree certificate proofSuffix certificateSuffix nextProofTokens
        nextCertificateTokens restTasks nextTasks values values
        (by simp [tree, compactListedProofNodeExpectedFields])
        hrootTransition hexecutionBounds.rootCurrent hexecutionBounds.rootNext
  have hrootRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = start /\ row.nextState = childStart /\
        CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row := by
    simpa only [start, childStart, tree, certificate, fields, proofNode,
      nextProofTokens, nextCertificateTokens, nextTasks,
      compactNumericTreeTaskStartState] using hrootRowRaw
  have hchildRows : forall childOffset, childOffset < childSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt childStart childOffset /\
          row.nextState =
            compactNumericVerifierStateAt childStart (childOffset + 1) /\
          CompactNumericVerifierAcceptedTreeControlledRowBound
            rowWeight row := by
    intro childOffset hchildOffset
    have hrow := hpremiseRows childOffset (by
      simpa only [childSteps] using hchildOffset)
    simpa only [childStart, fields] using hrow
  have hcombineTransition :
      compactNumericCombineState (compactNumericCombineTask 4 fields)
          ((proofSuffix, certificateSuffix),
            (restTasks, premiseResult :: values)) =
        (((proofSuffix, certificateSuffix),
          (restTasks, parentResult :: values)), none) := by
    simpa only [fields, premiseResult, parentResult, tree, certificate,
      compactNumericTreeTaskSuccessState] using
      compactNumericVerifierCanonicalOr_combine_transition Gamma leftFormula
        rightFormula premise premiseCertificate proofSuffix certificateSuffix
        restTasks values
  have hcombineCurrent : compactNumericVerifierStateWeight
      ((((proofSuffix, certificateSuffix),
        (compactNumericCombineTask 4 fields :: restTasks,
          premiseResult :: values)), none)) <= rowWeight := by
    simpa only [beforeCombine, premiseResult,
      compactNumericTreeTaskSuccessState] using
      hexecutionBounds.combineCurrent
  have hcombineNext : compactNumericVerifierStateWeight
      ((((proofSuffix, certificateSuffix),
        (restTasks, parentResult :: values)), none)) <= rowWeight := by
    simpa only [finish, parentResult, tree, certificate,
      compactNumericTreeTaskSuccessState] using hexecutionBounds.combineNext
  have hcombineRowRaw :=
    exists_compactNumericVerifierPublicCombineCheckedStepRow_with_globalControlBound_of_transition
      (rowWeight := rowWeight) proofSuffix certificateSuffix
      (compactNumericCombineTask 4 fields) restTasks
      (premiseResult :: values) (parentResult :: values) none
      (by simp [compactNumericCombineTask]) hcombineTransition
      hcombineCurrent hcombineNext
  have hcombineRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = beforeCombine /\ row.nextState = finish /\
        CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row := by
    simpa only [beforeCombine, finish, premiseResult, parentResult, tree,
      certificate, compactNumericTreeTaskSuccessState] using hcombineRowRaw
  have hparentOffset : offset < 1 + childSteps + 1 := by
    simpa only [childSteps, compactNumericTreeTaskSteps] using hoffset
  have hrow :=
    exists_compactNumericVerifierAcceptedTreeControlledRow_at_unary_offset
      hrootStep hchildExecute hcombineStep hrootRow hchildRows hcombineRow
        hparentOffset
  simpa only [start, tree, certificate] using hrow

set_option maxRecDepth 4000 in
set_option maxHeartbeats 12000000 in
theorem exists_compactNumericVerifierAcceptedUnaryTaskRow_at_offset_with_control
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (tag : Nat)
    (hpremiseValid : listedCertificateValid premise premiseCertificate)
    {rowWeight offset : Nat} :
    let fields := (compactListedProofNodeExpectedFields tree proofSuffix).2
    let combineTask := compactNumericCombineTask tag fields
    let start := compactNumericTreeTaskStartState tree certificate
      proofSuffix certificateSuffix restTasks values
    let childStart := compactNumericTreeTaskStartState premise
      premiseCertificate proofSuffix certificateSuffix
      (combineTask :: restTasks) values
    let childSteps := compactNumericTreeTaskSteps premise premiseCertificate
    let beforeCombine := compactNumericTreeTaskSuccessState premise
      premiseCertificate proofSuffix certificateSuffix
      (combineTask :: restTasks) values
    let finish := compactNumericTreeTaskSuccessState tree certificate
      proofSuffix certificateSuffix restTasks values
    let premiseResult : CompactNumericChildResult :=
      (arithmeticPropositionTokenValues premise.conclusionList,
        (listedCertificateValidTrace premise premiseCertificate).1)
    let parentResult : CompactNumericChildResult :=
      (arithmeticPropositionTokenValues tree.conclusionList,
        (listedCertificateValidTrace tree certificate).1)
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let certificateNode :=
      compactStructuralCertificateNodeExpected certificate certificateSuffix
    let nextProofTokens := compactListedProofTokens premise ++ proofSuffix
    let nextCertificateTokens :=
      compactStructuralCertificateTokens premiseCertificate ++
        certificateSuffix
    let nextTasks := compactNumericParseTask :: combineTask :: restTasks
    tag ≠ 10 ->
    (proofNode.1 = 3 \/ proofNode.1 = 4 \/ proofNode.1 = 5 \/
      proofNode.1 = 6 \/ proofNode.1 = 7 \/ proofNode.1 = 8 \/
      proofNode.1 = 9) ->
    compactNumericNodeTransition proofNode certificateNode restTasks values =
      some ((nextProofTokens, nextCertificateTokens), (nextTasks, values)) ->
    compactNumericVerifierStep start = childStart ->
    compactNumericCombineState combineTask
        ((proofSuffix, certificateSuffix),
          (restTasks, premiseResult :: values)) =
      (((proofSuffix, certificateSuffix),
        (restTasks, parentResult :: values)), none) ->
    compactNumericVerifierStep beforeCombine = finish ->
    compactNumericTreeTaskSteps tree certificate = 1 + childSteps + 1 ->
    (forall parentOffset,
      parentOffset <= compactNumericTreeTaskSteps tree certificate ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt start parentOffset) <= rowWeight) ->
    (forall childOffset, childOffset < childSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt childStart childOffset /\
          row.nextState =
            compactNumericVerifierStateAt childStart (childOffset + 1) /\
          CompactNumericVerifierAcceptedTreeControlledRowBound
            rowWeight row) ->
    offset < compactNumericTreeTaskSteps tree certificate ->
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt start offset /\
        row.nextState = compactNumericVerifierStateAt start (offset + 1) /\
        CompactNumericVerifierAcceptedTreeControlledRowBound
          rowWeight row := by
  dsimp only
  intro htagNe hproofTag hrootTransition hrootStep hcombineTransition
    hcombineStep htaskSteps hweights hchildRows hoffset
  let fields := (compactListedProofNodeExpectedFields tree proofSuffix).2
  let combineTask := compactNumericCombineTask tag fields
  let start := compactNumericTreeTaskStartState tree certificate
    proofSuffix certificateSuffix restTasks values
  let childStart := compactNumericTreeTaskStartState premise
    premiseCertificate proofSuffix certificateSuffix
    (combineTask :: restTasks) values
  let childSteps := compactNumericTreeTaskSteps premise premiseCertificate
  let beforeCombine := compactNumericTreeTaskSuccessState premise
    premiseCertificate proofSuffix certificateSuffix
    (combineTask :: restTasks) values
  let finish := compactNumericTreeTaskSuccessState tree certificate
    proofSuffix certificateSuffix restTasks values
  let premiseResult : CompactNumericChildResult :=
    (arithmeticPropositionTokenValues premise.conclusionList,
      (listedCertificateValidTrace premise premiseCertificate).1)
  let parentResult : CompactNumericChildResult :=
    (arithmeticPropositionTokenValues tree.conclusionList,
      (listedCertificateValidTrace tree certificate).1)
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected certificate certificateSuffix
  let nextProofTokens := compactListedProofTokens premise ++ proofSuffix
  let nextCertificateTokens :=
    compactStructuralCertificateTokens premiseCertificate ++
      certificateSuffix
  let nextTasks := compactNumericParseTask :: combineTask :: restTasks
  have hpremiseShape :=
    compactNumericTreeCertificateShapeMatches_eq_true_of_valid
      premise premiseCertificate hpremiseValid
  have hchildExecuteRaw := compactNumericTreeTask_execute_of_shape
    premise premiseCertificate proofSuffix certificateSuffix
      (combineTask :: restTasks) values hpremiseShape
  have hchildExecute :
      (compactNumericVerifierStep^[childSteps]) childStart = beforeCombine := by
    simpa only [childSteps, childStart, beforeCombine, combineTask,
      compactNumericTreeTaskStartState] using hchildExecuteRaw
  have hparentWeights : forall parentOffset,
      parentOffset <= 1 + childSteps + 1 ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt start parentOffset) <= rowWeight := by
    intro parentOffset hparentOffset
    exact hweights parentOffset (by omega)
  have hexecutionBounds : CompactNumericVerifierUnaryExecutionWeightBounds
      start childStart beforeCombine finish childSteps rowWeight :=
    compactNumericVerifierUnaryExecutionWeightBounds_of_parent
      hrootStep hchildExecute hcombineStep hparentWeights
  have hrootRowRaw :=
    exists_compactNumericVerifierCanonicalNonLeafCheckedStepRow_with_globalControlBound
      tree certificate proofSuffix certificateSuffix nextProofTokens
        nextCertificateTokens restTasks nextTasks values values hproofTag
        hrootTransition hexecutionBounds.rootCurrent hexecutionBounds.rootNext
  have hrootRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = start /\ row.nextState = childStart /\
        CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row := by
    simpa only [start, childStart, fields, combineTask, proofNode,
      nextProofTokens, nextCertificateTokens, nextTasks,
      compactNumericTreeTaskStartState] using hrootRowRaw
  have hcombineCurrent : compactNumericVerifierStateWeight
      ((((proofSuffix, certificateSuffix),
        (combineTask :: restTasks, premiseResult :: values)), none)) <=
        rowWeight := by
    simpa only [beforeCombine, premiseResult,
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
      restTasks (premiseResult :: values) (parentResult :: values) none
      (by simpa only [combineTask, compactNumericCombineTask] using htagNe)
      hcombineTransition
      hcombineCurrent hcombineNext
  have hcombineRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = beforeCombine /\ row.nextState = finish /\
        CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row := by
    simpa only [beforeCombine, finish, premiseResult, parentResult,
      compactNumericTreeTaskSuccessState] using hcombineRowRaw
  have hparentOffset : offset < 1 + childSteps + 1 := by omega
  exact exists_compactNumericVerifierAcceptedTreeControlledRow_at_unary_offset
    hrootStep hchildExecute hcombineStep hrootRow hchildRows hcombineRow
      hparentOffset

set_option maxRecDepth 4000 in
set_option maxHeartbeats 10000000 in
theorem exists_compactNumericVerifierAcceptedExsTaskRow_at_offset_with_control
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid
      (.exs Gamma formula witness premise) (.unary premiseCertificate))
    {rowWeight offset : Nat}
    (hweights : forall parentOffset,
      parentOffset <= compactNumericTreeTaskSteps
          (.exs Gamma formula witness premise)
          (.unary premiseCertificate) ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState
              (.exs Gamma formula witness premise)
              (.unary premiseCertificate) proofSuffix certificateSuffix
              restTasks values) parentOffset) <= rowWeight)
    (hpremiseRows :
      let fields := (compactListedProofNodeExpectedFields
        (.exs Gamma formula witness premise) proofSuffix).2
      forall premiseOffset,
        premiseOffset <
            compactNumericTreeTaskSteps premise premiseCertificate ->
          exists row : CompactNumericVerifierCheckedStepRow,
            row.currentState = compactNumericVerifierStateAt
              (compactNumericTreeTaskStartState premise premiseCertificate
                proofSuffix certificateSuffix
                (compactNumericCombineTask 6 fields :: restTasks) values)
              premiseOffset /\
            row.nextState = compactNumericVerifierStateAt
              (compactNumericTreeTaskStartState premise premiseCertificate
                proofSuffix certificateSuffix
                (compactNumericCombineTask 6 fields :: restTasks) values)
              (premiseOffset + 1) /\
            CompactNumericVerifierAcceptedTreeControlledRowBound
              rowWeight row)
    (hoffset : offset < compactNumericTreeTaskSteps
      (.exs Gamma formula witness premise) (.unary premiseCertificate)) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState
          (.exs Gamma formula witness premise)
          (.unary premiseCertificate) proofSuffix certificateSuffix
          restTasks values) offset /\
      row.nextState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState
          (.exs Gamma formula witness premise)
          (.unary premiseCertificate) proofSuffix certificateSuffix
          restTasks values) (offset + 1) /\
      CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row := by
  let tree : ListedCheckedPAProofTree :=
    .exs Gamma formula witness premise
  let certificate : StructuralValidityCertificate :=
    .unary premiseCertificate
  let fields := (compactListedProofNodeExpectedFields tree proofSuffix).2
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected certificate certificateSuffix
  let nextProofTokens := compactListedProofTokens premise ++ proofSuffix
  let nextCertificateTokens :=
    compactStructuralCertificateTokens premiseCertificate ++
      certificateSuffix
  let nextTasks := compactNumericParseTask ::
    compactNumericCombineTask 6 fields :: restTasks
  have hrootTransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, values)) := by
    simp [proofNode, certificateNode, tree, certificate, nextProofTokens,
      nextCertificateTokens, nextTasks, fields,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix, compactNumericNodeTransition]
  have hrootStep : compactNumericVerifierStep
      (compactNumericTreeTaskStartState tree certificate proofSuffix
        certificateSuffix restTasks values) =
      compactNumericTreeTaskStartState premise premiseCertificate proofSuffix
        certificateSuffix (compactNumericCombineTask 6 fields :: restTasks)
          values := by
    simpa only [tree, certificate, fields,
      compactNumericTreeTaskStartState] using
      compactNumericVerifierCanonicalExs_step Gamma formula witness premise
        premiseCertificate proofSuffix certificateSuffix restTasks values
  have hcombineTransition :=
    compactNumericVerifierCanonicalExs_combine_transition Gamma formula
      witness premise premiseCertificate proofSuffix certificateSuffix
        restTasks values
  have hcombineStep := compactNumericVerifierCanonicalExs_combine_step Gamma
    formula witness premise premiseCertificate proofSuffix certificateSuffix
      restTasks values
  have htaskSteps : compactNumericTreeTaskSteps tree certificate =
      1 + compactNumericTreeTaskSteps premise premiseCertificate + 1 := by
    simp [tree, certificate, compactNumericTreeTaskSteps]
  have hrow :=
    exists_compactNumericVerifierAcceptedUnaryTaskRow_at_offset_with_control
      tree certificate premise premiseCertificate proofSuffix certificateSuffix
        restTasks values 6 hvalid.2.2 (by omega)
        (by simp [tree, compactListedProofNodeExpectedFields])
        hrootTransition hrootStep
        (by simpa only [tree, certificate, fields,
          compactNumericTreeTaskSuccessState] using hcombineTransition)
        (by simpa only [tree, certificate, fields] using hcombineStep)
        htaskSteps
        (by simpa only [tree, certificate] using hweights)
        (by simpa only [tree, fields] using hpremiseRows)
        (by simpa only [tree, certificate] using hoffset)
  simpa only [tree, certificate] using hrow

set_option maxRecDepth 4000 in
set_option maxHeartbeats 10000000 in
theorem exists_compactNumericVerifierAcceptedAllTaskRow_at_offset_with_control
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.all Gamma formula premise)
      (.unary premiseCertificate))
    {rowWeight offset : Nat}
    (hweights : forall parentOffset,
      parentOffset <= compactNumericTreeTaskSteps
          (.all Gamma formula premise) (.unary premiseCertificate) ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState (.all Gamma formula premise)
              (.unary premiseCertificate) proofSuffix certificateSuffix
              restTasks values) parentOffset) <= rowWeight)
    (hpremiseRows :
      let fields := (compactListedProofNodeExpectedFields
        (.all Gamma formula premise) proofSuffix).2
      forall premiseOffset,
        premiseOffset <
            compactNumericTreeTaskSteps premise premiseCertificate ->
          exists row : CompactNumericVerifierCheckedStepRow,
            row.currentState = compactNumericVerifierStateAt
              (compactNumericTreeTaskStartState premise premiseCertificate
                proofSuffix certificateSuffix
                (compactNumericCombineTask 5 fields :: restTasks) values)
              premiseOffset /\
            row.nextState = compactNumericVerifierStateAt
              (compactNumericTreeTaskStartState premise premiseCertificate
                proofSuffix certificateSuffix
                (compactNumericCombineTask 5 fields :: restTasks) values)
              (premiseOffset + 1) /\
            CompactNumericVerifierAcceptedTreeControlledRowBound
              rowWeight row)
    (hoffset : offset < compactNumericTreeTaskSteps
      (.all Gamma formula premise) (.unary premiseCertificate)) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.all Gamma formula premise)
          (.unary premiseCertificate) proofSuffix certificateSuffix
          restTasks values) offset /\
      row.nextState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.all Gamma formula premise)
          (.unary premiseCertificate) proofSuffix certificateSuffix
          restTasks values) (offset + 1) /\
      CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row := by
  let tree : ListedCheckedPAProofTree := .all Gamma formula premise
  let certificate : StructuralValidityCertificate :=
    .unary premiseCertificate
  let fields := (compactListedProofNodeExpectedFields tree proofSuffix).2
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected certificate certificateSuffix
  let nextProofTokens := compactListedProofTokens premise ++ proofSuffix
  let nextCertificateTokens :=
    compactStructuralCertificateTokens premiseCertificate ++
      certificateSuffix
  let nextTasks := compactNumericParseTask ::
    compactNumericCombineTask 5 fields :: restTasks
  have hrootTransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, values)) := by
    simp [proofNode, certificateNode, tree, certificate, nextProofTokens,
      nextCertificateTokens, nextTasks, fields,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix, compactNumericNodeTransition]
  have hrootStep : compactNumericVerifierStep
      (compactNumericTreeTaskStartState tree certificate proofSuffix
        certificateSuffix restTasks values) =
      compactNumericTreeTaskStartState premise premiseCertificate proofSuffix
        certificateSuffix (compactNumericCombineTask 5 fields :: restTasks)
          values := by
    simpa only [tree, certificate, fields,
      compactNumericTreeTaskStartState] using
      compactNumericVerifierCanonicalAll_step Gamma formula premise
        premiseCertificate proofSuffix certificateSuffix restTasks values
  have hcombineTransition :=
    compactNumericVerifierCanonicalAll_combine_transition Gamma formula premise
      premiseCertificate proofSuffix certificateSuffix restTasks values
  have hcombineStep := compactNumericVerifierCanonicalAll_combine_step Gamma
    formula premise premiseCertificate proofSuffix certificateSuffix restTasks
      values
  have htaskSteps : compactNumericTreeTaskSteps tree certificate =
      1 + compactNumericTreeTaskSteps premise premiseCertificate + 1 := by
    simp [tree, certificate, compactNumericTreeTaskSteps]
  have hrow :=
    exists_compactNumericVerifierAcceptedUnaryTaskRow_at_offset_with_control
      tree certificate premise premiseCertificate proofSuffix certificateSuffix
        restTasks values 5 hvalid.2.2 (by omega)
        (by simp [tree, compactListedProofNodeExpectedFields])
        hrootTransition hrootStep
        (by simpa only [tree, certificate, fields,
          compactNumericTreeTaskSuccessState] using hcombineTransition)
        (by simpa only [tree, certificate, fields] using hcombineStep)
        htaskSteps
        (by simpa only [tree, certificate] using hweights)
        (by simpa only [tree, fields] using hpremiseRows)
        (by simpa only [tree, certificate] using hoffset)
  simpa only [tree, certificate] using hrow

set_option maxRecDepth 4000 in
set_option maxHeartbeats 10000000 in
theorem exists_compactNumericVerifierAcceptedWkTaskRow_at_offset_with_control
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.wk Gamma premise)
      (.unary premiseCertificate))
    {rowWeight offset : Nat}
    (hweights : forall parentOffset,
      parentOffset <= compactNumericTreeTaskSteps (.wk Gamma premise)
          (.unary premiseCertificate) ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState (.wk Gamma premise)
              (.unary premiseCertificate) proofSuffix certificateSuffix
              restTasks values) parentOffset) <= rowWeight)
    (hpremiseRows :
      let fields := (compactListedProofNodeExpectedFields
        (.wk Gamma premise) proofSuffix).2
      forall premiseOffset,
        premiseOffset <
            compactNumericTreeTaskSteps premise premiseCertificate ->
          exists row : CompactNumericVerifierCheckedStepRow,
            row.currentState = compactNumericVerifierStateAt
              (compactNumericTreeTaskStartState premise premiseCertificate
                proofSuffix certificateSuffix
                (compactNumericCombineTask 7 fields :: restTasks) values)
              premiseOffset /\
            row.nextState = compactNumericVerifierStateAt
              (compactNumericTreeTaskStartState premise premiseCertificate
                proofSuffix certificateSuffix
                (compactNumericCombineTask 7 fields :: restTasks) values)
              (premiseOffset + 1) /\
            CompactNumericVerifierAcceptedTreeControlledRowBound
              rowWeight row)
    (hoffset : offset < compactNumericTreeTaskSteps (.wk Gamma premise)
      (.unary premiseCertificate)) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.wk Gamma premise)
          (.unary premiseCertificate) proofSuffix certificateSuffix
          restTasks values) offset /\
      row.nextState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.wk Gamma premise)
          (.unary premiseCertificate) proofSuffix certificateSuffix
          restTasks values) (offset + 1) /\
      CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row := by
  let tree : ListedCheckedPAProofTree := .wk Gamma premise
  let certificate : StructuralValidityCertificate :=
    .unary premiseCertificate
  let fields := (compactListedProofNodeExpectedFields tree proofSuffix).2
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected certificate certificateSuffix
  let nextProofTokens := compactListedProofTokens premise ++ proofSuffix
  let nextCertificateTokens :=
    compactStructuralCertificateTokens premiseCertificate ++
      certificateSuffix
  let nextTasks := compactNumericParseTask ::
    compactNumericCombineTask 7 fields :: restTasks
  have hrootTransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, values)) := by
    simp [proofNode, certificateNode, tree, certificate, nextProofTokens,
      nextCertificateTokens, nextTasks, fields,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix, compactNumericNodeTransition]
  have hrootStep : compactNumericVerifierStep
      (compactNumericTreeTaskStartState tree certificate proofSuffix
        certificateSuffix restTasks values) =
      compactNumericTreeTaskStartState premise premiseCertificate proofSuffix
        certificateSuffix (compactNumericCombineTask 7 fields :: restTasks)
          values := by
    simpa only [tree, certificate, fields,
      compactNumericTreeTaskStartState] using
      compactNumericVerifierCanonicalWk_step Gamma premise premiseCertificate
        proofSuffix certificateSuffix restTasks values
  have hcombineTransition :=
    compactNumericVerifierCanonicalWk_combine_transition Gamma premise
      premiseCertificate proofSuffix certificateSuffix restTasks values
  have hcombineStep := compactNumericVerifierCanonicalWk_combine_step Gamma
    premise premiseCertificate proofSuffix certificateSuffix restTasks values
  have htaskSteps : compactNumericTreeTaskSteps tree certificate =
      1 + compactNumericTreeTaskSteps premise premiseCertificate + 1 := by
    simp [tree, certificate, compactNumericTreeTaskSteps]
  have hrow :=
    exists_compactNumericVerifierAcceptedUnaryTaskRow_at_offset_with_control
      tree certificate premise premiseCertificate proofSuffix certificateSuffix
        restTasks values 7 hvalid.2 (by omega)
        (by simp [tree, compactListedProofNodeExpectedFields])
        hrootTransition hrootStep
        (by simpa only [tree, certificate, fields,
          compactNumericTreeTaskSuccessState] using hcombineTransition)
        (by simpa only [tree, certificate, fields] using hcombineStep)
        htaskSteps
        (by simpa only [tree, certificate] using hweights)
        (by simpa only [tree, fields] using hpremiseRows)
        (by simpa only [tree, certificate] using hoffset)
  simpa only [tree, certificate] using hrow

set_option maxRecDepth 4000 in
set_option maxHeartbeats 10000000 in
theorem exists_compactNumericVerifierAcceptedShiftTaskRow_at_offset_with_control
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.shift Gamma premise)
      (.unary premiseCertificate))
    {rowWeight offset : Nat}
    (hweights : forall parentOffset,
      parentOffset <= compactNumericTreeTaskSteps (.shift Gamma premise)
          (.unary premiseCertificate) ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState (.shift Gamma premise)
              (.unary premiseCertificate) proofSuffix certificateSuffix
              restTasks values) parentOffset) <= rowWeight)
    (hpremiseRows :
      let fields := (compactListedProofNodeExpectedFields
        (.shift Gamma premise) proofSuffix).2
      forall premiseOffset,
        premiseOffset <
            compactNumericTreeTaskSteps premise premiseCertificate ->
          exists row : CompactNumericVerifierCheckedStepRow,
            row.currentState = compactNumericVerifierStateAt
              (compactNumericTreeTaskStartState premise premiseCertificate
                proofSuffix certificateSuffix
                (compactNumericCombineTask 8 fields :: restTasks) values)
              premiseOffset /\
            row.nextState = compactNumericVerifierStateAt
              (compactNumericTreeTaskStartState premise premiseCertificate
                proofSuffix certificateSuffix
                (compactNumericCombineTask 8 fields :: restTasks) values)
              (premiseOffset + 1) /\
            CompactNumericVerifierAcceptedTreeControlledRowBound
              rowWeight row)
    (hoffset : offset < compactNumericTreeTaskSteps (.shift Gamma premise)
      (.unary premiseCertificate)) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.shift Gamma premise)
          (.unary premiseCertificate) proofSuffix certificateSuffix
          restTasks values) offset /\
      row.nextState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.shift Gamma premise)
          (.unary premiseCertificate) proofSuffix certificateSuffix
          restTasks values) (offset + 1) /\
      CompactNumericVerifierAcceptedTreeControlledRowBound rowWeight row := by
  let tree : ListedCheckedPAProofTree := .shift Gamma premise
  let certificate : StructuralValidityCertificate :=
    .unary premiseCertificate
  let fields := (compactListedProofNodeExpectedFields tree proofSuffix).2
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected certificate certificateSuffix
  let nextProofTokens := compactListedProofTokens premise ++ proofSuffix
  let nextCertificateTokens :=
    compactStructuralCertificateTokens premiseCertificate ++
      certificateSuffix
  let nextTasks := compactNumericParseTask ::
    compactNumericCombineTask 8 fields :: restTasks
  have hrootTransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, values)) := by
    simp [proofNode, certificateNode, tree, certificate, nextProofTokens,
      nextCertificateTokens, nextTasks, fields,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix, compactNumericNodeTransition]
  have hrootStep : compactNumericVerifierStep
      (compactNumericTreeTaskStartState tree certificate proofSuffix
        certificateSuffix restTasks values) =
      compactNumericTreeTaskStartState premise premiseCertificate proofSuffix
        certificateSuffix (compactNumericCombineTask 8 fields :: restTasks)
          values := by
    simpa only [tree, certificate, fields,
      compactNumericTreeTaskStartState] using
      compactNumericVerifierCanonicalShift_step Gamma premise
        premiseCertificate proofSuffix certificateSuffix restTasks values
  have hcombineTransition :=
    compactNumericVerifierCanonicalShift_combine_transition Gamma premise
      premiseCertificate proofSuffix certificateSuffix restTasks values
  have hcombineStep := compactNumericVerifierCanonicalShift_combine_step Gamma
    premise premiseCertificate proofSuffix certificateSuffix restTasks values
  have htaskSteps : compactNumericTreeTaskSteps tree certificate =
      1 + compactNumericTreeTaskSteps premise premiseCertificate + 1 := by
    simp [tree, certificate, compactNumericTreeTaskSteps]
  have hrow :=
    exists_compactNumericVerifierAcceptedUnaryTaskRow_at_offset_with_control
      tree certificate premise premiseCertificate proofSuffix certificateSuffix
        restTasks values 8 hvalid.2 (by omega)
        (by simp [tree, compactListedProofNodeExpectedFields])
        hrootTransition hrootStep
        (by simpa only [tree, certificate, fields,
          compactNumericTreeTaskSuccessState] using hcombineTransition)
        (by simpa only [tree, certificate, fields] using hcombineStep)
        htaskSteps
        (by simpa only [tree, certificate] using hweights)
        (by simpa only [tree, fields] using hpremiseRows)
        (by simpa only [tree, certificate] using hoffset)
  simpa only [tree, certificate] using hrow

#print axioms
  exists_compactNumericVerifierAcceptedOrTaskRow_at_offset_with_control
#print axioms
  exists_compactNumericVerifierAcceptedUnaryTaskRow_at_offset_with_control
#print axioms
  exists_compactNumericVerifierAcceptedExsTaskRow_at_offset_with_control
#print axioms
  exists_compactNumericVerifierAcceptedAllTaskRow_at_offset_with_control
#print axioms
  exists_compactNumericVerifierAcceptedWkTaskRow_at_offset_with_control
#print axioms
  exists_compactNumericVerifierAcceptedShiftTaskRow_at_offset_with_control

end FoundationCompactNumericListedDirectVerifierAcceptedUnaryTaskRowsStateTableControlBounds
