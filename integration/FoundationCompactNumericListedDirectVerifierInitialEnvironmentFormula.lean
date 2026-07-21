import integration.FoundationCompactNumericListedDirectCrossTableSliceEquality
import integration.FoundationCompactNumericListedDirectVerifierParseTaskHeadFormula
import integration.FoundationCompactNumericListedDirectVerifierStepEnvironmentSurjectivity
import integration.FoundationCompactNumericListedDirectVerifierStateRealization
import integration.FoundationCompactNumericListedDirectVerifierStateCrossTableEquality

/-!
# Exact arithmetic initial condition for one verifier-step environment

The first 24 columns are the current-state core.  The formula compares its
proof and certificate streams bit-for-bit with the two public input streams,
requires the unique parse task, an empty child-result stack, and a running
status.  It is designed to be inserted into the row-zero witness-table check.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierInitialEnvironmentFormula

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierStateRealization
open FoundationCompactNumericListedDirectVerifierStateCrossTableEquality
open FoundationCompactNumericListedDirectVerifierParseTaskHeadFormula
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepEnvironmentSurjectivity

def CompactNumericVerifierInitialEnvironment
    (environment : Fin 429 -> Nat)
    (proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat) : Prop :=
  CompactFixedWidthCrossTableSlicesEq
      proofTable proofWidth proofTokenCount proofStart proofFinish
      (environment 0) (environment 1) (environment 2)
      (environment 3) (environment 5) ∧
    CompactFixedWidthCrossTableSlicesEq
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish
      (environment 0) (environment 1) (environment 2)
      (environment 5) (environment 7) ∧
    CompactNumericVerifierParseTaskHead
      (environment 0) (environment 1) (environment 2)
      (environment 11) (environment 21) ∧
    environment 10 = 1 ∧
    environment 13 = 0 ∧
    environment 15 = 0

private def environmentVariable (coordinate : Fin 429) : Fin (10 + 429) :=
  Fin.castAdd 10 coordinate

private def inputVariable (coordinate : Fin 10) : Fin (10 + 429) :=
  Fin.natAdd 429 coordinate

@[simp] private theorem environmentVariable_val
    (environment : Fin 429 -> Nat) (inputs : Fin 10 -> Nat)
    (coordinate : Fin 429) :
    Semiterm.val (Matrix.appendr environment inputs) Empty.elim
        (#(environmentVariable coordinate) :
          ArithmeticSemiterm Empty (10 + 429)) =
      environment coordinate := by
  simp [environmentVariable, Matrix.appendr, Matrix.vecAppend_eq_ite]

set_option maxRecDepth 4096 in
@[simp] private theorem inputVariable_val
    (environment : Fin 429 -> Nat) (inputs : Fin 10 -> Nat)
    (coordinate : Fin 10) :
    Semiterm.val (Matrix.appendr environment inputs) Empty.elim
        (#(inputVariable coordinate) : ArithmeticSemiterm Empty (10 + 429)) =
      inputs coordinate := by
  change Matrix.appendr environment inputs (Fin.natAdd 429 coordinate) =
    inputs coordinate
  simp [Matrix.appendr, Matrix.vecAppend_eq_ite]

private def arithmeticNumeral (value : Nat) :
    ArithmeticSemiterm Empty (10 + 429) :=
  Semiterm.Operator.operator
    (Semiterm.Operator.numeral ℒₒᵣ value) ![]

private def arithmeticEq
    (left right : ArithmeticSemiterm Empty (10 + 429)) :
    ArithmeticSemiformula Empty (10 + 429) :=
  Semiformula.Operator.Eq.eq.operator ![left, right]

private def compactNumericVerifierInitialProofTerms :
    Fin 10 -> ArithmeticSemiterm Empty (10 + 429) :=
  ![(#(inputVariable 0) : ArithmeticSemiterm Empty (10 + 429)),
    #(inputVariable 1), #(inputVariable 2), #(inputVariable 3),
    #(inputVariable 4),
    #(environmentVariable 0), #(environmentVariable 1),
    #(environmentVariable 2), #(environmentVariable 3),
    #(environmentVariable 5)]

private def compactNumericVerifierInitialCertificateTerms :
    Fin 10 -> ArithmeticSemiterm Empty (10 + 429) :=
  ![(#(inputVariable 5) : ArithmeticSemiterm Empty (10 + 429)),
    #(inputVariable 6), #(inputVariable 7), #(inputVariable 8),
    #(inputVariable 9),
    #(environmentVariable 0), #(environmentVariable 1),
    #(environmentVariable 2), #(environmentVariable 5),
    #(environmentVariable 7)]

private def compactNumericVerifierInitialParseTaskTerms :
    Fin 5 -> ArithmeticSemiterm Empty (10 + 429) :=
  ![(#(environmentVariable 0) : ArithmeticSemiterm Empty (10 + 429)),
    #(environmentVariable 1), #(environmentVariable 2),
    #(environmentVariable 11), #(environmentVariable 21)]

def compactNumericVerifierInitialEnvironmentDef :
    HierarchySymbol.sigmaZero.Semisentence (10 + 429) := .mkSigma
  [compactFixedWidthCrossTableSlicesEqDef.val ⇜
      compactNumericVerifierInitialProofTerms,
    compactFixedWidthCrossTableSlicesEqDef.val ⇜
      compactNumericVerifierInitialCertificateTerms,
    compactNumericVerifierParseTaskHeadDef.val ⇜
      compactNumericVerifierInitialParseTaskTerms,
    arithmeticEq (#(environmentVariable 10)) (arithmeticNumeral 1),
    arithmeticEq (#(environmentVariable 13)) (arithmeticNumeral 0),
    arithmeticEq (#(environmentVariable 15)) (arithmeticNumeral 0)].conj₂
  (by
    simp [compactNumericVerifierInitialProofTerms,
      compactNumericVerifierInitialCertificateTerms,
      compactNumericVerifierInitialParseTaskTerms,
      arithmeticEq, arithmeticNumeral])

private theorem compactNumericVerifierInitialProofFormula_eval
    (environment : Fin 429 -> Nat) (inputs : Fin 10 -> Nat) :
    (compactFixedWidthCrossTableSlicesEqDef.val ⇜
        compactNumericVerifierInitialProofTerms).Evalb
        (Matrix.appendr environment inputs) ↔
      CompactFixedWidthCrossTableSlicesEq
        (inputs 0) (inputs 1) (inputs 2) (inputs 3) (inputs 4)
        (environment 0) (environment 1) (environment 2)
        (environment 3) (environment 5) := by
  rw [Semiformula.eval_substs]
  have henv :
      (Semiterm.val (Matrix.appendr environment inputs) Empty.elim ∘
        compactNumericVerifierInitialProofTerms) =
        ![inputs 0, inputs 1, inputs 2, inputs 3, inputs 4,
          environment 0, environment 1, environment 2,
          environment 3, environment 5] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  rw [henv]
  exact compactFixedWidthCrossTableSlicesEqDef_spec
    (inputs 0) (inputs 1) (inputs 2) (inputs 3) (inputs 4)
    (environment 0) (environment 1) (environment 2)
    (environment 3) (environment 5)

private theorem compactNumericVerifierInitialCertificateFormula_eval
    (environment : Fin 429 -> Nat) (inputs : Fin 10 -> Nat) :
    (compactFixedWidthCrossTableSlicesEqDef.val ⇜
        compactNumericVerifierInitialCertificateTerms).Evalb
        (Matrix.appendr environment inputs) ↔
      CompactFixedWidthCrossTableSlicesEq
        (inputs 5) (inputs 6) (inputs 7) (inputs 8) (inputs 9)
        (environment 0) (environment 1) (environment 2)
        (environment 5) (environment 7) := by
  rw [Semiformula.eval_substs]
  have henv :
      (Semiterm.val (Matrix.appendr environment inputs) Empty.elim ∘
        compactNumericVerifierInitialCertificateTerms) =
        ![inputs 5, inputs 6, inputs 7, inputs 8, inputs 9,
          environment 0, environment 1, environment 2,
          environment 5, environment 7] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  rw [henv]
  exact compactFixedWidthCrossTableSlicesEqDef_spec
    (inputs 5) (inputs 6) (inputs 7) (inputs 8) (inputs 9)
    (environment 0) (environment 1) (environment 2)
    (environment 5) (environment 7)

private theorem compactNumericVerifierInitialParseTaskFormula_eval
    (environment : Fin 429 -> Nat) (inputs : Fin 10 -> Nat) :
    (compactNumericVerifierParseTaskHeadDef.val ⇜
        compactNumericVerifierInitialParseTaskTerms).Evalb
        (Matrix.appendr environment inputs) ↔
      CompactNumericVerifierParseTaskHead
        (environment 0) (environment 1) (environment 2)
        (environment 11) (environment 21) := by
  rw [Semiformula.eval_substs]
  have henv :
      (Semiterm.val (Matrix.appendr environment inputs) Empty.elim ∘
        compactNumericVerifierInitialParseTaskTerms) =
        ![environment 0, environment 1, environment 2,
          environment 11, environment 21] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  rw [henv]
  exact compactNumericVerifierParseTaskHeadDef_spec
    (environment 0) (environment 1) (environment 2)
    (environment 11) (environment 21)

@[simp] theorem compactNumericVerifierInitialEnvironmentDef_spec
    (environment : Fin 429 -> Nat)
    (proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat) :
    compactNumericVerifierInitialEnvironmentDef.val.Evalb
        (Matrix.appendr environment
          ![proofTable, proofWidth, proofTokenCount, proofStart, proofFinish,
            certificateTable, certificateWidth, certificateTokenCount,
            certificateStart, certificateFinish]) ↔
      CompactNumericVerifierInitialEnvironment environment
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish := by
  let inputs : Fin 10 -> Nat :=
    ![proofTable, proofWidth, proofTokenCount, proofStart, proofFinish,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateStart, certificateFinish]
  change compactNumericVerifierInitialEnvironmentDef.val.Evalb
      (Matrix.appendr environment inputs) ↔ _
  change
    ((compactFixedWidthCrossTableSlicesEqDef.val ⇜
        compactNumericVerifierInitialProofTerms).Evalb
          (Matrix.appendr environment inputs) ∧
      (compactFixedWidthCrossTableSlicesEqDef.val ⇜
        compactNumericVerifierInitialCertificateTerms).Evalb
          (Matrix.appendr environment inputs) ∧
      (compactNumericVerifierParseTaskHeadDef.val ⇜
        compactNumericVerifierInitialParseTaskTerms).Evalb
          (Matrix.appendr environment inputs) ∧
      (arithmeticEq (#(environmentVariable 10))
        (arithmeticNumeral 1)).Evalb (Matrix.appendr environment inputs) ∧
      (arithmeticEq (#(environmentVariable 13))
        (arithmeticNumeral 0)).Evalb (Matrix.appendr environment inputs) ∧
      (arithmeticEq (#(environmentVariable 15))
        (arithmeticNumeral 0)).Evalb (Matrix.appendr environment inputs)) ↔ _
  rw [compactNumericVerifierInitialProofFormula_eval,
    compactNumericVerifierInitialCertificateFormula_eval,
    compactNumericVerifierInitialParseTaskFormula_eval]
  simp [CompactNumericVerifierInitialEnvironment,
    arithmeticEq, arithmeticNumeral, environmentVariable,
    Matrix.appendr, Matrix.vecAppend_eq_ite, inputs]

theorem compactNumericVerifierInitialEnvironmentDef_sigmaZero :
    Hierarchy Polarity.sigma 0
      compactNumericVerifierInitialEnvironmentDef.val :=
  compactNumericVerifierInitialEnvironmentDef.sigma_prop

theorem CompactNumericVerifierInitialEnvironment.realizeInitialShape
    {environment : Fin 429 -> Nat}
    {proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat}
    (hstep : compactNumericVerifierStepGraphDef.val.Evalb environment)
    (hinitial : CompactNumericVerifierInitialEnvironment environment
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish) :
    exists proofTokens certificateTokens : List Nat,
    exists state : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
          (environment 0) (environment 1) (environment 2)
          (environment 3) (environment 4) state /\
        CompactAdditiveNatListDirectLayout
          (environment 0) (environment 1) (environment 2)
          (environment 3) (environment 5) proofTokens /\
        CompactAdditiveNatListDirectLayout
          (environment 0) (environment 1) (environment 2)
          (environment 5) (environment 7) certificateTokens /\
        state = compactNumericVerifierInitialState
          proofTokens certificateTokens := by
  let coordinates := compactNumericVerifierStepCurrentCoordinates environment
  let sizeWitness := compactNumericVerifierStepCurrentSizeWitness environment
  have hcore : CompactNumericVerifierStateCoreGraph
      (environment 0) (environment 1) (environment 2)
      coordinates sizeWitness := by
    exact compactNumericVerifierStepGraphDef_evalb_currentCore
      environment hstep
  rcases
      FoundationCompactNumericListedDirectVerifierStateRealization.CompactNumericVerifierStateCoreGraph.realizeDirectLayout
        hcore with
    ⟨decodedProof, decodedCertificate, tasks, values, status,
      _hproofLength, _hcertificateLength, htasksLength, hvaluesLength,
      hstateLayout, hproofLayout, hcertificateLayout,
      _htaskListLayout, htaskRows,
      _hvalueListLayout, _hvalueRows, hstatusCase⟩
  have hcoordinateFields :=
    compactNumericVerifierStepCurrentCoordinates_fields environment
  change
    coordinates.start = environment 3 ∧
      coordinates.finish = environment 4 ∧
      coordinates.proofFinish = environment 5 ∧
      coordinates.proofCount = environment 6 ∧
      coordinates.certificateFinish = environment 7 ∧
      coordinates.certificateCount = environment 8 ∧
      coordinates.tasksFinish = environment 9 ∧
      coordinates.taskCount = environment 10 ∧
      coordinates.taskBoundary = environment 11 ∧
      coordinates.valuesFinish = environment 12 ∧
      coordinates.valueCount = environment 13 ∧
      coordinates.valueBoundary = environment 14 ∧
      coordinates.statusTag = environment 15 ∧
      coordinates.statusPayloadStart = environment 16 ∧
      coordinates.statusBool = environment 17 at hcoordinateFields
  rcases hcoordinateFields with
    ⟨hstart, hfinish, hproofFinish, _hproofCount,
      hcertificateFinish, _hcertificateCount,
      _htasksFinish, htaskCount, htaskBoundary,
      _hvaluesFinish, hvalueCount, _hvalueBoundary,
      hstatusTag, _hstatusPayloadStart, _hstatusBool⟩
  have hsizeFields :=
    compactNumericVerifierStepCurrentSizeWitness_fields environment
  change
    sizeWitness.taskBoundarySize = environment 18 ∧
      sizeWitness.valueBoundarySize = environment 19 ∧
      sizeWitness.taskTableWidth = environment 20 ∧
      sizeWitness.taskValueBound = environment 21 ∧
      sizeWitness.valueTableWidth = environment 22 ∧
      sizeWitness.valueValueBound = environment 23 at hsizeFields
  rcases hsizeFields with
    ⟨_hTaskBoundarySize, _hValueBoundarySize, _hTaskTableWidth,
      htaskValueBound, _hValueTableWidth, _hValueValueBound⟩
  rcases hinitial with
    ⟨_hproofCross, _hcertificateCross, hparse,
      hinitialTaskCount, hinitialValueCount, hinitialStatus⟩
  have htasksLength' : tasks.length = 1 :=
    htasksLength.trans (htaskCount.trans hinitialTaskCount)
  have htaskRows' : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 11) tasks := by
    simpa only [htaskBoundary] using htaskRows
  have htasksEq : tasks = [compactNumericParseTask] :=
    hparse.taskList_eq_singleton htasksLength' htaskRows'
  have hvaluesLength' : values.length = 0 :=
    hvaluesLength.trans (hvalueCount.trans hinitialValueCount)
  have hvaluesEq : values = [] :=
    List.length_eq_zero_iff.mp hvaluesLength'
  have hstatusEq : status = none := by
    rcases hstatusCase with hnone | hsome
    · exact hnone.1
    · rcases hsome with ⟨result, _hstatus, htag, _hbool⟩
      have : coordinates.statusTag = 0 :=
        hstatusTag.trans hinitialStatus
      omega
  have hstateLayout' : CompactNumericVerifierStateDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 3) (environment 4)
      (((decodedProof, decodedCertificate), (tasks, values)), status) := by
    simpa only [hstart, hfinish] using hstateLayout
  have hproofLayout' : CompactAdditiveNatListDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 3) (environment 5) decodedProof := by
    simpa only [hstart, hproofFinish] using hproofLayout
  have hcertificateLayout' : CompactAdditiveNatListDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 5) (environment 7) decodedCertificate := by
    simpa only [hproofFinish, hcertificateFinish] using hcertificateLayout
  refine ⟨decodedProof, decodedCertificate,
    (((decodedProof, decodedCertificate), (tasks, values)), status),
    hstateLayout', hproofLayout', hcertificateLayout', ?_⟩
  rw [htasksEq, hvaluesEq, hstatusEq]
  rfl

theorem CompactNumericVerifierInitialEnvironment.realizeInitialState
    {environment : Fin 429 -> Nat}
    {proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    (hstep : compactNumericVerifierStepGraphDef.val.Evalb environment)
    (hinitial : CompactNumericVerifierInitialEnvironment environment
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish)
    (hproofSource : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount proofStart proofFinish proofTokens)
    (hcertificateSource : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish certificateTokens) :
    ∃ state : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
          (environment 0) (environment 1) (environment 2)
          (environment 3) (environment 4) state ∧
        state = compactNumericVerifierInitialState proofTokens certificateTokens := by
  let coordinates := compactNumericVerifierStepCurrentCoordinates environment
  let sizeWitness := compactNumericVerifierStepCurrentSizeWitness environment
  have hcore : CompactNumericVerifierStateCoreGraph
      (environment 0) (environment 1) (environment 2)
      coordinates sizeWitness := by
    exact compactNumericVerifierStepGraphDef_evalb_currentCore
      environment hstep
  rcases
      FoundationCompactNumericListedDirectVerifierStateRealization.CompactNumericVerifierStateCoreGraph.realizeDirectLayout
        hcore with
    ⟨decodedProof, decodedCertificate, tasks, values, status,
      hproofLength, hcertificateLength, htasksLength, hvaluesLength,
      hstateLayout, hproofLayout, hcertificateLayout,
      _htaskListLayout, htaskRows,
      _hvalueListLayout, _hvalueRows, hstatusCase⟩
  have hcoordinateFields :=
    compactNumericVerifierStepCurrentCoordinates_fields environment
  change
    coordinates.start = environment 3 ∧
      coordinates.finish = environment 4 ∧
      coordinates.proofFinish = environment 5 ∧
      coordinates.proofCount = environment 6 ∧
      coordinates.certificateFinish = environment 7 ∧
      coordinates.certificateCount = environment 8 ∧
      coordinates.tasksFinish = environment 9 ∧
      coordinates.taskCount = environment 10 ∧
      coordinates.taskBoundary = environment 11 ∧
      coordinates.valuesFinish = environment 12 ∧
      coordinates.valueCount = environment 13 ∧
      coordinates.valueBoundary = environment 14 ∧
      coordinates.statusTag = environment 15 ∧
      coordinates.statusPayloadStart = environment 16 ∧
      coordinates.statusBool = environment 17 at hcoordinateFields
  rcases hcoordinateFields with
    ⟨hstart, hfinish, hproofFinish, _hproofCount,
      hcertificateFinish, _hcertificateCount,
      _htasksFinish, htaskCount, htaskBoundary,
      _hvaluesFinish, hvalueCount, _hvalueBoundary,
      hstatusTag, _hstatusPayloadStart, _hstatusBool⟩
  have hsizeFields :=
    compactNumericVerifierStepCurrentSizeWitness_fields environment
  change
    sizeWitness.taskBoundarySize = environment 18 ∧
      sizeWitness.valueBoundarySize = environment 19 ∧
      sizeWitness.taskTableWidth = environment 20 ∧
      sizeWitness.taskValueBound = environment 21 ∧
      sizeWitness.valueTableWidth = environment 22 ∧
      sizeWitness.valueValueBound = environment 23 at hsizeFields
  rcases hsizeFields with
    ⟨_hTaskBoundarySize, _hValueBoundarySize, _hTaskTableWidth,
      htaskValueBound, _hValueTableWidth, _hValueValueBound⟩
  rcases hinitial with
    ⟨hproofCross, hcertificateCross, hparse,
      hinitialTaskCount, hinitialValueCount, hinitialStatus⟩
  have hproofLayout' : CompactAdditiveNatListDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 3) (environment 5) decodedProof := by
    simpa only [hstart, hproofFinish] using hproofLayout
  have hcertificateLayout' : CompactAdditiveNatListDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 5) (environment 7) decodedCertificate := by
    simpa only [hproofFinish, hcertificateFinish] using hcertificateLayout
  have hproofEq : decodedProof = proofTokens :=
    hproofCross.natListValues_eq hproofSource hproofLayout'
  have hcertificateEq : decodedCertificate = certificateTokens :=
    hcertificateCross.natListValues_eq
      hcertificateSource hcertificateLayout'
  have htasksLength' : tasks.length = 1 :=
    htasksLength.trans (htaskCount.trans hinitialTaskCount)
  have htaskRows' : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 11) tasks := by
    simpa only [htaskBoundary] using htaskRows
  have htasksEq : tasks = [compactNumericParseTask] :=
    hparse.taskList_eq_singleton htasksLength' htaskRows'
  have hvaluesLength' : values.length = 0 :=
    hvaluesLength.trans (hvalueCount.trans hinitialValueCount)
  have hvaluesEq : values = [] :=
    List.length_eq_zero_iff.mp hvaluesLength'
  have hstatusEq : status = none := by
    rcases hstatusCase with hnone | hsome
    · exact hnone.1
    · rcases hsome with ⟨result, _hstatus, htag, _hbool⟩
      have : coordinates.statusTag = 0 :=
        hstatusTag.trans hinitialStatus
      omega
  have hstateLayout' : CompactNumericVerifierStateDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 3) (environment 4)
      (((decodedProof, decodedCertificate), (tasks, values)), status) := by
    simpa only [hstart, hfinish] using hstateLayout
  refine ⟨(((decodedProof, decodedCertificate), (tasks, values)), status),
    hstateLayout', ?_⟩
  rw [hproofEq, hcertificateEq, htasksEq, hvaluesEq, hstatusEq]
  rfl

theorem CompactNumericVerifierInitialEnvironment.ofInitialState
    {environment : Fin 429 -> Nat}
    {proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    (hstep : compactNumericVerifierStepGraphDef.val.Evalb environment)
    (hcurrent : CompactNumericVerifierStateDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 3) (environment 4)
      (compactNumericVerifierInitialState proofTokens certificateTokens))
    (hproofSource : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount proofStart proofFinish proofTokens)
    (hcertificateSource : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish certificateTokens) :
    CompactNumericVerifierInitialEnvironment environment
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish := by
  let coordinates := compactNumericVerifierStepCurrentCoordinates environment
  let sizeWitness := compactNumericVerifierStepCurrentSizeWitness environment
  have hcore : CompactNumericVerifierStateCoreGraph
      (environment 0) (environment 1) (environment 2)
      coordinates sizeWitness := by
    exact compactNumericVerifierStepGraphDef_evalb_currentCore
      environment hstep
  have hcoreCopy := hcore
  rcases
      FoundationCompactNumericListedDirectVerifierStateRealization.CompactNumericVerifierStateCoreGraph.realizeDirectLayout
        hcore with
    ⟨decodedProof, decodedCertificate, tasks, values, status,
      hproofLength, hcertificateLength, htasksLength, hvaluesLength,
      hdecodedLayout, hproofLayout, hcertificateLayout,
      _htaskListLayout, htaskRows,
      _hvalueListLayout, _hvalueRows, hstatusCase⟩
  have hcoordinateFields :=
    compactNumericVerifierStepCurrentCoordinates_fields environment
  change
    coordinates.start = environment 3 ∧
      coordinates.finish = environment 4 ∧
      coordinates.proofFinish = environment 5 ∧
      coordinates.proofCount = environment 6 ∧
      coordinates.certificateFinish = environment 7 ∧
      coordinates.certificateCount = environment 8 ∧
      coordinates.tasksFinish = environment 9 ∧
      coordinates.taskCount = environment 10 ∧
      coordinates.taskBoundary = environment 11 ∧
      coordinates.valuesFinish = environment 12 ∧
      coordinates.valueCount = environment 13 ∧
      coordinates.valueBoundary = environment 14 ∧
      coordinates.statusTag = environment 15 ∧
      coordinates.statusPayloadStart = environment 16 ∧
      coordinates.statusBool = environment 17 at hcoordinateFields
  rcases hcoordinateFields with
    ⟨hstart, hfinish, hproofFinish, _hproofCount,
      hcertificateFinish, _hcertificateCount,
      _htasksFinish, htaskCount, htaskBoundary,
      _hvaluesFinish, hvalueCount, _hvalueBoundary,
      hstatusTag, _hstatusPayloadStart, _hstatusBool⟩
  have hsizeFields :=
    compactNumericVerifierStepCurrentSizeWitness_fields environment
  change
    sizeWitness.taskBoundarySize = environment 18 ∧
      sizeWitness.valueBoundarySize = environment 19 ∧
      sizeWitness.taskTableWidth = environment 20 ∧
      sizeWitness.taskValueBound = environment 21 ∧
      sizeWitness.valueTableWidth = environment 22 ∧
      sizeWitness.valueValueBound = environment 23 at hsizeFields
  rcases hsizeFields with
    ⟨_hTaskBoundarySize, _hValueBoundarySize, htaskTableWidth,
      htaskValueBound, _hValueTableWidth, _hValueValueBound⟩
  have hdecodedLayout' : CompactNumericVerifierStateDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 3) (environment 4)
      (((decodedProof, decodedCertificate), (tasks, values)), status) := by
    simpa only [hstart, hfinish] using hdecodedLayout
  rcases
      FoundationCompactNumericListedDirectVerifierStateCrossTableEquality.CompactNumericVerifierStateDirectLayout.toSliceCarries
        hcurrent with
    ⟨_hcurrentFinish, hcurrentBound, _hcurrentEntries⟩
  have hslices : CompactFixedWidthTokenSlicesEq
      (environment 0) (environment 1) (environment 2)
      (environment 3) (environment 4)
      (environment 3) (environment 4) :=
    CompactFixedWidthTokenSlicesEq.refl (by omega) hcurrentBound
  have hstateEq :
      (((decodedProof, decodedCertificate), (tasks, values)), status) =
        compactNumericVerifierInitialState proofTokens certificateTokens :=
    CompactFixedWidthTokenSlicesEq.verifierStateValue_eq
      hslices hcurrent hdecodedLayout'
  have hproofEq : decodedProof = proofTokens :=
    congrArg (fun state : CompactNumericVerifierState => state.1.1.1) hstateEq
  have hcertificateEq : decodedCertificate = certificateTokens :=
    congrArg (fun state : CompactNumericVerifierState => state.1.1.2) hstateEq
  have htasksEq : tasks = [compactNumericParseTask] :=
    congrArg (fun state : CompactNumericVerifierState => state.1.2.1) hstateEq
  have hvaluesEq : values = [] :=
    congrArg (fun state : CompactNumericVerifierState => state.1.2.2) hstateEq
  have hstatusEq : status = none :=
    congrArg (fun state : CompactNumericVerifierState => state.2) hstateEq
  have hproofLayout' : CompactAdditiveNatListDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 3) (environment 5) proofTokens := by
    simpa only [hstart, hproofFinish, hproofEq] using hproofLayout
  have hcertificateLayout' : CompactAdditiveNatListDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 5) (environment 7) certificateTokens := by
    simpa only [hproofFinish, hcertificateFinish, hcertificateEq] using
      hcertificateLayout
  have hproofCross := CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
    hproofSource hproofLayout'
  have hcertificateCross :=
    CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
      hcertificateSource hcertificateLayout'
  have htaskCountOne : coordinates.taskCount = 1 := by
    rw [← htasksLength, htasksEq]
    rfl
  have hvalueCountZero : coordinates.valueCount = 0 := by
    rw [← hvaluesLength, hvaluesEq]
    rfl
  have htaskGraph : CompactNumericVerifierTaskListRowsGraph
      (environment 0) (environment 1) (environment 2)
      coordinates.taskBoundary coordinates.taskCount
      sizeWitness.taskTableWidth sizeWitness.taskValueBound :=
    hcoreCopy.2.2.2.1
  have htaskGraph' : CompactNumericVerifierTaskListRowsGraph
      (environment 0) (environment 1) (environment 2)
      (environment 11) 1 (environment 20) (environment 21) := by
    simpa only [htaskBoundary, htaskCountOne,
      htaskTableWidth, htaskValueBound] using htaskGraph
  have htaskRows' : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 11) [compactNumericParseTask] := by
    simpa only [htaskBoundary, htasksEq] using htaskRows
  have hparse := exists_compactNumericVerifierParseTaskHead_of_rows
    htaskGraph' htaskRows'
  have hstatusZero : coordinates.statusTag = 0 := by
    rcases hstatusCase with hnone | hsome
    · exact hnone.2
    · rcases hsome with ⟨result, hsome, _htag, _hbool⟩
      rw [hstatusEq] at hsome
      simp at hsome
  exact ⟨hproofCross, hcertificateCross, hparse,
    htaskCount.symm.trans htaskCountOne,
    hvalueCount.symm.trans hvalueCountZero,
    hstatusTag.symm.trans hstatusZero⟩

#print axioms compactNumericVerifierInitialEnvironmentDef_spec
#print axioms compactNumericVerifierInitialEnvironmentDef_sigmaZero
#print axioms CompactNumericVerifierInitialEnvironment.realizeInitialShape
#print axioms CompactNumericVerifierInitialEnvironment.realizeInitialState
#print axioms CompactNumericVerifierInitialEnvironment.ofInitialState

end FoundationCompactNumericListedDirectVerifierInitialEnvironmentFormula
