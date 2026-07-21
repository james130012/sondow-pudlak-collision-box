import integration.FoundationCompactNumericListedDirectVerifierAcceptedTreeTaskRowsGlobalBound
import integration.FoundationCompactNumericListedDirectVerifierCanonicalNonLeafExactSteps
import integration.FoundationCompactNumericListedDirectVerifierCanonicalCombineExactSteps

/-!
# Globally bounded checked rows for accepted unary tree tasks

Each theorem splices the canonical root row, all premise rows, and the
canonical combine row at the exact offsets used by the numeric listed task
machine.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedUnaryTaskRowsGlobalBound

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
theorem exists_compactNumericVerifierAcceptedOrTaskRow_at_offset
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
            compactNumericVerifierAcceptedTreeRowBound rowWeight row)
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
      compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
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
  have hrootRowRaw :=
    exists_compactNumericVerifierCanonicalOrCheckedStepRow_with_globalBound
      Gamma leftFormula rightFormula premise premiseCertificate proofSuffix
      certificateSuffix restTasks values
      hexecutionBounds.rootCurrent hexecutionBounds.rootNext
  have hrootRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = start /\ row.nextState = childStart /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound
              rowWeight := by
    simpa only [start, childStart, tree, certificate, fields,
      compactNumericTreeTaskStartState] using hrootRowRaw
  have hchildRows : forall childOffset, childOffset < childSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt childStart childOffset /\
          row.nextState =
            compactNumericVerifierStateAt childStart (childOffset + 1) /\
          compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
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
    exists_compactNumericVerifierPublicCombineCheckedStepRow_with_globalBound_of_transition
      (rowWeight := rowWeight) proofSuffix certificateSuffix
      (compactNumericCombineTask 4 fields) restTasks
      (premiseResult :: values) (parentResult :: values) none
      (by simp [compactNumericCombineTask]) hcombineTransition
      hcombineCurrent hcombineNext
  have hcombineRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = beforeCombine /\ row.nextState = finish /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierNonParseGlobalCoordinateSizeBound
              rowWeight := by
    simpa only [beforeCombine, finish, premiseResult, parentResult, tree,
      certificate, compactNumericTreeTaskSuccessState] using hcombineRowRaw
  have hparentOffset : offset < 1 + childSteps + 1 := by
    simpa only [childSteps, compactNumericTreeTaskSteps] using hoffset
  have hrow := exists_compactNumericVerifierAcceptedTreeRow_at_unary_offset
    hrootStep hchildExecute hcombineStep hrootRow hchildRows hcombineRow
    hparentOffset
  simpa only [start, tree, certificate] using hrow

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem exists_compactNumericVerifierAcceptedExsTaskRow_at_offset
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
            compactNumericVerifierAcceptedTreeRowBound rowWeight row)
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
      compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
  let tree : ListedCheckedPAProofTree :=
    .exs Gamma formula witness premise
  let certificate : StructuralValidityCertificate :=
    .unary premiseCertificate
  let fields := (compactListedProofNodeExpectedFields tree proofSuffix).2
  let start := compactNumericTreeTaskStartState tree certificate
    proofSuffix certificateSuffix restTasks values
  let childStart := compactNumericTreeTaskStartState premise
    premiseCertificate proofSuffix certificateSuffix
    (compactNumericCombineTask 6 fields :: restTasks) values
  let childSteps := compactNumericTreeTaskSteps premise premiseCertificate
  let beforeCombine := compactNumericTreeTaskSuccessState premise
    premiseCertificate proofSuffix certificateSuffix
    (compactNumericCombineTask 6 fields :: restTasks) values
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
    (compactNumericCombineTask 6 fields :: restTasks) values hpremiseShape
  have hchildExecute :
      (compactNumericVerifierStep^[childSteps]) childStart = beforeCombine := by
    simpa only [childSteps, childStart, beforeCombine,
      compactNumericTreeTaskStartState] using hchildExecuteRaw
  have hrootStep : compactNumericVerifierStep start = childStart := by
    simpa only [start, childStart, tree, certificate, fields,
      compactNumericTreeTaskStartState] using
      compactNumericVerifierCanonicalExs_step Gamma formula witness premise
        premiseCertificate proofSuffix certificateSuffix restTasks values
  have hcombineStep :
      compactNumericVerifierStep beforeCombine = finish := by
    simpa only [beforeCombine, finish, tree, certificate, fields] using
      compactNumericVerifierCanonicalExs_combine_step Gamma formula witness
        premise premiseCertificate proofSuffix certificateSuffix restTasks
        values
  have hparentWeights : forall parentOffset,
      parentOffset <= 1 + childSteps + 1 ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt start parentOffset) <= rowWeight := by
    intro parentOffset hparentOffset
    have hparentOffset' : parentOffset <= compactNumericTreeTaskSteps
        (.exs Gamma formula witness premise)
        (.unary premiseCertificate) := by
      simpa only [childSteps, compactNumericTreeTaskSteps] using hparentOffset
    simpa only [start, tree, certificate] using
      hweights parentOffset hparentOffset'
  have hexecutionBounds : CompactNumericVerifierUnaryExecutionWeightBounds
      start childStart beforeCombine finish childSteps rowWeight :=
    compactNumericVerifierUnaryExecutionWeightBounds_of_parent
      hrootStep hchildExecute hcombineStep hparentWeights
  have hrootRowRaw :=
    exists_compactNumericVerifierCanonicalExsCheckedStepRow_with_globalBound
      Gamma formula witness premise premiseCertificate proofSuffix
      certificateSuffix restTasks values hexecutionBounds.rootCurrent
      hexecutionBounds.rootNext
  have hrootRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = start /\ row.nextState = childStart /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound
              rowWeight := by
    simpa only [start, childStart, tree, certificate, fields,
      compactNumericTreeTaskStartState] using hrootRowRaw
  have hchildRows : forall childOffset, childOffset < childSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt childStart childOffset /\
          row.nextState =
            compactNumericVerifierStateAt childStart (childOffset + 1) /\
          compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
    intro childOffset hchildOffset
    have hrow := hpremiseRows childOffset (by
      simpa only [childSteps] using hchildOffset)
    simpa only [childStart, fields] using hrow
  have hcombineTransition :
      compactNumericCombineState (compactNumericCombineTask 6 fields)
          ((proofSuffix, certificateSuffix),
            (restTasks, premiseResult :: values)) =
        (((proofSuffix, certificateSuffix),
          (restTasks, parentResult :: values)), none) := by
    simpa only [fields, premiseResult, parentResult, tree, certificate,
      compactNumericTreeTaskSuccessState] using
      compactNumericVerifierCanonicalExs_combine_transition Gamma formula
        witness premise premiseCertificate proofSuffix certificateSuffix
        restTasks values
  have hcombineCurrent : compactNumericVerifierStateWeight
      ((((proofSuffix, certificateSuffix),
        (compactNumericCombineTask 6 fields :: restTasks,
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
    exists_compactNumericVerifierPublicCombineCheckedStepRow_with_globalBound_of_transition
      (rowWeight := rowWeight) proofSuffix certificateSuffix
      (compactNumericCombineTask 6 fields) restTasks
      (premiseResult :: values) (parentResult :: values) none
      (by simp [compactNumericCombineTask]) hcombineTransition
      hcombineCurrent hcombineNext
  have hcombineRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = beforeCombine /\ row.nextState = finish /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierNonParseGlobalCoordinateSizeBound
              rowWeight := by
    simpa only [beforeCombine, finish, premiseResult, parentResult, tree,
      certificate, compactNumericTreeTaskSuccessState] using hcombineRowRaw
  have hparentOffset : offset < 1 + childSteps + 1 := by
    simpa only [childSteps, compactNumericTreeTaskSteps] using hoffset
  have hrow := exists_compactNumericVerifierAcceptedTreeRow_at_unary_offset
    hrootStep hchildExecute hcombineStep hrootRow hchildRows hcombineRow
    hparentOffset
  simpa only [start, tree, certificate] using hrow

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem exists_compactNumericVerifierAcceptedAllTaskRow_at_offset
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
            compactNumericVerifierAcceptedTreeRowBound rowWeight row)
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
      compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
  let tree : ListedCheckedPAProofTree := .all Gamma formula premise
  let certificate : StructuralValidityCertificate :=
    .unary premiseCertificate
  let fields := (compactListedProofNodeExpectedFields tree proofSuffix).2
  let start := compactNumericTreeTaskStartState tree certificate
    proofSuffix certificateSuffix restTasks values
  let childStart := compactNumericTreeTaskStartState premise
    premiseCertificate proofSuffix certificateSuffix
    (compactNumericCombineTask 5 fields :: restTasks) values
  let childSteps := compactNumericTreeTaskSteps premise premiseCertificate
  let beforeCombine := compactNumericTreeTaskSuccessState premise
    premiseCertificate proofSuffix certificateSuffix
    (compactNumericCombineTask 5 fields :: restTasks) values
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
    (compactNumericCombineTask 5 fields :: restTasks) values hpremiseShape
  have hchildExecute :
      (compactNumericVerifierStep^[childSteps]) childStart = beforeCombine := by
    simpa only [childSteps, childStart, beforeCombine,
      compactNumericTreeTaskStartState] using hchildExecuteRaw
  have hrootStep : compactNumericVerifierStep start = childStart := by
    simpa only [start, childStart, tree, certificate, fields,
      compactNumericTreeTaskStartState] using
      compactNumericVerifierCanonicalAll_step Gamma formula premise
        premiseCertificate proofSuffix certificateSuffix restTasks values
  have hcombineStep :
      compactNumericVerifierStep beforeCombine = finish := by
    simpa only [beforeCombine, finish, tree, certificate, fields] using
      compactNumericVerifierCanonicalAll_combine_step Gamma formula premise
        premiseCertificate proofSuffix certificateSuffix restTasks values
  have hparentWeights : forall parentOffset,
      parentOffset <= 1 + childSteps + 1 ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt start parentOffset) <= rowWeight := by
    intro parentOffset hparentOffset
    have hparentOffset' : parentOffset <= compactNumericTreeTaskSteps
        (.all Gamma formula premise) (.unary premiseCertificate) := by
      simpa only [childSteps, compactNumericTreeTaskSteps] using hparentOffset
    simpa only [start, tree, certificate] using
      hweights parentOffset hparentOffset'
  have hexecutionBounds : CompactNumericVerifierUnaryExecutionWeightBounds
      start childStart beforeCombine finish childSteps rowWeight :=
    compactNumericVerifierUnaryExecutionWeightBounds_of_parent
      hrootStep hchildExecute hcombineStep hparentWeights
  have hrootRowRaw :=
    exists_compactNumericVerifierCanonicalAllCheckedStepRow_with_globalBound
      Gamma formula premise premiseCertificate proofSuffix certificateSuffix
      restTasks values hexecutionBounds.rootCurrent
      hexecutionBounds.rootNext
  have hrootRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = start /\ row.nextState = childStart /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound
              rowWeight := by
    simpa only [start, childStart, tree, certificate, fields,
      compactNumericTreeTaskStartState] using hrootRowRaw
  have hchildRows : forall childOffset, childOffset < childSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt childStart childOffset /\
          row.nextState =
            compactNumericVerifierStateAt childStart (childOffset + 1) /\
          compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
    intro childOffset hchildOffset
    have hrow := hpremiseRows childOffset (by
      simpa only [childSteps] using hchildOffset)
    simpa only [childStart, fields] using hrow
  have hcombineTransition :
      compactNumericCombineState (compactNumericCombineTask 5 fields)
          ((proofSuffix, certificateSuffix),
            (restTasks, premiseResult :: values)) =
        (((proofSuffix, certificateSuffix),
          (restTasks, parentResult :: values)), none) := by
    simpa only [fields, premiseResult, parentResult, tree, certificate,
      compactNumericTreeTaskSuccessState] using
      compactNumericVerifierCanonicalAll_combine_transition Gamma formula
        premise premiseCertificate proofSuffix certificateSuffix restTasks
        values
  have hcombineCurrent : compactNumericVerifierStateWeight
      ((((proofSuffix, certificateSuffix),
        (compactNumericCombineTask 5 fields :: restTasks,
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
    exists_compactNumericVerifierPublicCombineCheckedStepRow_with_globalBound_of_transition
      (rowWeight := rowWeight) proofSuffix certificateSuffix
      (compactNumericCombineTask 5 fields) restTasks
      (premiseResult :: values) (parentResult :: values) none
      (by simp [compactNumericCombineTask]) hcombineTransition
      hcombineCurrent hcombineNext
  have hcombineRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = beforeCombine /\ row.nextState = finish /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierNonParseGlobalCoordinateSizeBound
              rowWeight := by
    simpa only [beforeCombine, finish, premiseResult, parentResult, tree,
      certificate, compactNumericTreeTaskSuccessState] using hcombineRowRaw
  have hparentOffset : offset < 1 + childSteps + 1 := by
    simpa only [childSteps, compactNumericTreeTaskSteps] using hoffset
  have hrow := exists_compactNumericVerifierAcceptedTreeRow_at_unary_offset
    hrootStep hchildExecute hcombineStep hrootRow hchildRows hcombineRow
    hparentOffset
  simpa only [start, tree, certificate] using hrow

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem exists_compactNumericVerifierAcceptedWkTaskRow_at_offset
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
            compactNumericVerifierAcceptedTreeRowBound rowWeight row)
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
      compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
  let tree : ListedCheckedPAProofTree := .wk Gamma premise
  let certificate : StructuralValidityCertificate :=
    .unary premiseCertificate
  let fields := (compactListedProofNodeExpectedFields tree proofSuffix).2
  let start := compactNumericTreeTaskStartState tree certificate
    proofSuffix certificateSuffix restTasks values
  let childStart := compactNumericTreeTaskStartState premise
    premiseCertificate proofSuffix certificateSuffix
    (compactNumericCombineTask 7 fields :: restTasks) values
  let childSteps := compactNumericTreeTaskSteps premise premiseCertificate
  let beforeCombine := compactNumericTreeTaskSuccessState premise
    premiseCertificate proofSuffix certificateSuffix
    (compactNumericCombineTask 7 fields :: restTasks) values
  let finish := compactNumericTreeTaskSuccessState tree certificate
    proofSuffix certificateSuffix restTasks values
  let premiseResult : CompactNumericChildResult :=
    (arithmeticPropositionTokenValues premise.conclusionList,
      (listedCertificateValidTrace premise premiseCertificate).1)
  let parentResult : CompactNumericChildResult :=
    (arithmeticPropositionTokenValues tree.conclusionList,
      (listedCertificateValidTrace tree certificate).1)
  have hpremiseValid :
      listedCertificateValid premise premiseCertificate := hvalid.2
  have hpremiseShape :=
    compactNumericTreeCertificateShapeMatches_eq_true_of_valid
      premise premiseCertificate hpremiseValid
  have hchildExecuteRaw := compactNumericTreeTask_execute_of_shape
    premise premiseCertificate proofSuffix certificateSuffix
    (compactNumericCombineTask 7 fields :: restTasks) values hpremiseShape
  have hchildExecute :
      (compactNumericVerifierStep^[childSteps]) childStart = beforeCombine := by
    simpa only [childSteps, childStart, beforeCombine,
      compactNumericTreeTaskStartState] using hchildExecuteRaw
  have hrootStep : compactNumericVerifierStep start = childStart := by
    simpa only [start, childStart, tree, certificate, fields,
      compactNumericTreeTaskStartState] using
      compactNumericVerifierCanonicalWk_step Gamma premise premiseCertificate
        proofSuffix certificateSuffix restTasks values
  have hcombineStep :
      compactNumericVerifierStep beforeCombine = finish := by
    simpa only [beforeCombine, finish, tree, certificate, fields] using
      compactNumericVerifierCanonicalWk_combine_step Gamma premise
        premiseCertificate proofSuffix certificateSuffix restTasks values
  have hparentWeights : forall parentOffset,
      parentOffset <= 1 + childSteps + 1 ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt start parentOffset) <= rowWeight := by
    intro parentOffset hparentOffset
    have hparentOffset' : parentOffset <= compactNumericTreeTaskSteps
        (.wk Gamma premise) (.unary premiseCertificate) := by
      simpa only [childSteps, compactNumericTreeTaskSteps] using hparentOffset
    simpa only [start, tree, certificate] using
      hweights parentOffset hparentOffset'
  have hexecutionBounds : CompactNumericVerifierUnaryExecutionWeightBounds
      start childStart beforeCombine finish childSteps rowWeight :=
    compactNumericVerifierUnaryExecutionWeightBounds_of_parent
      hrootStep hchildExecute hcombineStep hparentWeights
  have hrootRowRaw :=
    exists_compactNumericVerifierCanonicalWkCheckedStepRow_with_globalBound
      Gamma premise premiseCertificate proofSuffix certificateSuffix
      restTasks values hexecutionBounds.rootCurrent
      hexecutionBounds.rootNext
  have hrootRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = start /\ row.nextState = childStart /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound
              rowWeight := by
    simpa only [start, childStart, tree, certificate, fields,
      compactNumericTreeTaskStartState] using hrootRowRaw
  have hchildRows : forall childOffset, childOffset < childSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt childStart childOffset /\
          row.nextState =
            compactNumericVerifierStateAt childStart (childOffset + 1) /\
          compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
    intro childOffset hchildOffset
    have hrow := hpremiseRows childOffset (by
      simpa only [childSteps] using hchildOffset)
    simpa only [childStart, fields] using hrow
  have hcombineTransition :
      compactNumericCombineState (compactNumericCombineTask 7 fields)
          ((proofSuffix, certificateSuffix),
            (restTasks, premiseResult :: values)) =
        (((proofSuffix, certificateSuffix),
          (restTasks, parentResult :: values)), none) := by
    simpa only [fields, premiseResult, parentResult, tree, certificate,
      compactNumericTreeTaskSuccessState] using
      compactNumericVerifierCanonicalWk_combine_transition Gamma premise
        premiseCertificate proofSuffix certificateSuffix restTasks values
  have hcombineCurrent : compactNumericVerifierStateWeight
      ((((proofSuffix, certificateSuffix),
        (compactNumericCombineTask 7 fields :: restTasks,
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
    exists_compactNumericVerifierPublicCombineCheckedStepRow_with_globalBound_of_transition
      (rowWeight := rowWeight) proofSuffix certificateSuffix
      (compactNumericCombineTask 7 fields) restTasks
      (premiseResult :: values) (parentResult :: values) none
      (by simp [compactNumericCombineTask]) hcombineTransition
      hcombineCurrent hcombineNext
  have hcombineRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = beforeCombine /\ row.nextState = finish /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierNonParseGlobalCoordinateSizeBound
              rowWeight := by
    simpa only [beforeCombine, finish, premiseResult, parentResult, tree,
      certificate, compactNumericTreeTaskSuccessState] using hcombineRowRaw
  have hparentOffset : offset < 1 + childSteps + 1 := by
    simpa only [childSteps, compactNumericTreeTaskSteps] using hoffset
  have hrow := exists_compactNumericVerifierAcceptedTreeRow_at_unary_offset
    hrootStep hchildExecute hcombineStep hrootRow hchildRows hcombineRow
    hparentOffset
  simpa only [start, tree, certificate] using hrow

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem exists_compactNumericVerifierAcceptedShiftTaskRow_at_offset
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
            compactNumericVerifierAcceptedTreeRowBound rowWeight row)
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
      compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
  let tree : ListedCheckedPAProofTree := .shift Gamma premise
  let certificate : StructuralValidityCertificate :=
    .unary premiseCertificate
  let fields := (compactListedProofNodeExpectedFields tree proofSuffix).2
  let start := compactNumericTreeTaskStartState tree certificate
    proofSuffix certificateSuffix restTasks values
  let childStart := compactNumericTreeTaskStartState premise
    premiseCertificate proofSuffix certificateSuffix
    (compactNumericCombineTask 8 fields :: restTasks) values
  let childSteps := compactNumericTreeTaskSteps premise premiseCertificate
  let beforeCombine := compactNumericTreeTaskSuccessState premise
    premiseCertificate proofSuffix certificateSuffix
    (compactNumericCombineTask 8 fields :: restTasks) values
  let finish := compactNumericTreeTaskSuccessState tree certificate
    proofSuffix certificateSuffix restTasks values
  let premiseResult : CompactNumericChildResult :=
    (arithmeticPropositionTokenValues premise.conclusionList,
      (listedCertificateValidTrace premise premiseCertificate).1)
  let parentResult : CompactNumericChildResult :=
    (arithmeticPropositionTokenValues tree.conclusionList,
      (listedCertificateValidTrace tree certificate).1)
  have hpremiseValid :
      listedCertificateValid premise premiseCertificate := hvalid.2
  have hpremiseShape :=
    compactNumericTreeCertificateShapeMatches_eq_true_of_valid
      premise premiseCertificate hpremiseValid
  have hchildExecuteRaw := compactNumericTreeTask_execute_of_shape
    premise premiseCertificate proofSuffix certificateSuffix
    (compactNumericCombineTask 8 fields :: restTasks) values hpremiseShape
  have hchildExecute :
      (compactNumericVerifierStep^[childSteps]) childStart = beforeCombine := by
    simpa only [childSteps, childStart, beforeCombine,
      compactNumericTreeTaskStartState] using hchildExecuteRaw
  have hrootStep : compactNumericVerifierStep start = childStart := by
    simpa only [start, childStart, tree, certificate, fields,
      compactNumericTreeTaskStartState] using
      compactNumericVerifierCanonicalShift_step Gamma premise
        premiseCertificate proofSuffix certificateSuffix restTasks values
  have hcombineStep :
      compactNumericVerifierStep beforeCombine = finish := by
    simpa only [beforeCombine, finish, tree, certificate, fields] using
      compactNumericVerifierCanonicalShift_combine_step Gamma premise
        premiseCertificate proofSuffix certificateSuffix restTasks values
  have hparentWeights : forall parentOffset,
      parentOffset <= 1 + childSteps + 1 ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt start parentOffset) <= rowWeight := by
    intro parentOffset hparentOffset
    have hparentOffset' : parentOffset <= compactNumericTreeTaskSteps
        (.shift Gamma premise) (.unary premiseCertificate) := by
      simpa only [childSteps, compactNumericTreeTaskSteps] using hparentOffset
    simpa only [start, tree, certificate] using
      hweights parentOffset hparentOffset'
  have hexecutionBounds : CompactNumericVerifierUnaryExecutionWeightBounds
      start childStart beforeCombine finish childSteps rowWeight :=
    compactNumericVerifierUnaryExecutionWeightBounds_of_parent
      hrootStep hchildExecute hcombineStep hparentWeights
  have hrootRowRaw :=
    exists_compactNumericVerifierCanonicalShiftCheckedStepRow_with_globalBound
      Gamma premise premiseCertificate proofSuffix certificateSuffix
      restTasks values hexecutionBounds.rootCurrent
      hexecutionBounds.rootNext
  have hrootRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = start /\ row.nextState = childStart /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound
              rowWeight := by
    simpa only [start, childStart, tree, certificate, fields,
      compactNumericTreeTaskStartState] using hrootRowRaw
  have hchildRows : forall childOffset, childOffset < childSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt childStart childOffset /\
          row.nextState =
            compactNumericVerifierStateAt childStart (childOffset + 1) /\
          compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
    intro childOffset hchildOffset
    have hrow := hpremiseRows childOffset (by
      simpa only [childSteps] using hchildOffset)
    simpa only [childStart, fields] using hrow
  have hcombineTransition :
      compactNumericCombineState (compactNumericCombineTask 8 fields)
          ((proofSuffix, certificateSuffix),
            (restTasks, premiseResult :: values)) =
        (((proofSuffix, certificateSuffix),
          (restTasks, parentResult :: values)), none) := by
    simpa only [fields, premiseResult, parentResult, tree, certificate,
      compactNumericTreeTaskSuccessState] using
      compactNumericVerifierCanonicalShift_combine_transition Gamma premise
        premiseCertificate proofSuffix certificateSuffix restTasks values
  have hcombineCurrent : compactNumericVerifierStateWeight
      ((((proofSuffix, certificateSuffix),
        (compactNumericCombineTask 8 fields :: restTasks,
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
    exists_compactNumericVerifierPublicCombineCheckedStepRow_with_globalBound_of_transition
      (rowWeight := rowWeight) proofSuffix certificateSuffix
      (compactNumericCombineTask 8 fields) restTasks
      (premiseResult :: values) (parentResult :: values) none
      (by simp [compactNumericCombineTask]) hcombineTransition
      hcombineCurrent hcombineNext
  have hcombineRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = beforeCombine /\ row.nextState = finish /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierNonParseGlobalCoordinateSizeBound
              rowWeight := by
    simpa only [beforeCombine, finish, premiseResult, parentResult, tree,
      certificate, compactNumericTreeTaskSuccessState] using hcombineRowRaw
  have hparentOffset : offset < 1 + childSteps + 1 := by
    simpa only [childSteps, compactNumericTreeTaskSteps] using hoffset
  have hrow := exists_compactNumericVerifierAcceptedTreeRow_at_unary_offset
    hrootStep hchildExecute hcombineStep hrootRow hchildRows hcombineRow
    hparentOffset
  simpa only [start, tree, certificate] using hrow

#print axioms exists_compactNumericVerifierAcceptedOrTaskRow_at_offset
#print axioms exists_compactNumericVerifierAcceptedAllTaskRow_at_offset
#print axioms exists_compactNumericVerifierAcceptedExsTaskRow_at_offset
#print axioms exists_compactNumericVerifierAcceptedWkTaskRow_at_offset
#print axioms exists_compactNumericVerifierAcceptedShiftTaskRow_at_offset

end FoundationCompactNumericListedDirectVerifierAcceptedUnaryTaskRowsGlobalBound
