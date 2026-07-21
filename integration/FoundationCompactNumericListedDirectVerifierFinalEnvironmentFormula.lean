import integration.FoundationCompactNumericListedDirectVerifierStepEnvironmentSurjectivity
import integration.FoundationCompactNumericListedDirectVerifierStateRealization
import integration.FoundationCompactNumericListedDirectVerifierStateCrossTableEquality

/-!
# Exact accepted final condition for one verifier-step environment

The final trace row is accepted exactly when its next-state option tag is
`some` and its Boolean payload is `true`.  These are columns 36 and 38 of the
same 429-column step environment.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierFinalEnvironmentFormula

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierStateRealization
open FoundationCompactNumericListedDirectVerifierStateCrossTableEquality
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepEnvironmentSurjectivity

def CompactNumericVerifierAcceptedEnvironment
    (environment : Fin 429 -> Nat) : Prop :=
  environment 36 = 1 ∧ environment 38 = 1

private def arithmeticNumeral (value : Nat) :
    ArithmeticSemiterm Empty 429 :=
  Semiterm.Operator.operator
    (Semiterm.Operator.numeral ℒₒᵣ value) ![]

private def arithmeticEq
    (left right : ArithmeticSemiterm Empty 429) :
    ArithmeticSemiformula Empty 429 :=
  Semiformula.Operator.Eq.eq.operator ![left, right]

def compactNumericVerifierAcceptedEnvironmentDef :
    HierarchySymbol.sigmaZero.Semisentence 429 := .mkSigma
  (arithmeticEq (#36 : ArithmeticSemiterm Empty 429)
      (arithmeticNumeral 1) ⋏
    arithmeticEq (#38 : ArithmeticSemiterm Empty 429)
      (arithmeticNumeral 1))
  (by simp [arithmeticEq, arithmeticNumeral])

@[simp] theorem compactNumericVerifierAcceptedEnvironmentDef_spec
    (environment : Fin 429 -> Nat) :
    compactNumericVerifierAcceptedEnvironmentDef.val.Evalb environment ↔
      CompactNumericVerifierAcceptedEnvironment environment := by
  simp [compactNumericVerifierAcceptedEnvironmentDef,
    CompactNumericVerifierAcceptedEnvironment,
    arithmeticEq, arithmeticNumeral]

theorem compactNumericVerifierAcceptedEnvironmentDef_sigmaZero :
    Hierarchy Polarity.sigma 0
      compactNumericVerifierAcceptedEnvironmentDef.val :=
  compactNumericVerifierAcceptedEnvironmentDef.sigma_prop

theorem CompactNumericVerifierAcceptedEnvironment.realizeAcceptedState
    {environment : Fin 429 -> Nat}
    (hstep : compactNumericVerifierStepGraphDef.val.Evalb environment)
    (haccepted : CompactNumericVerifierAcceptedEnvironment environment) :
    ∃ state : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
          (environment 0) (environment 1) (environment 2)
          (environment 24) (environment 25) state ∧
        state.2 = some true := by
  let coordinates := compactNumericVerifierStepNextCoordinates environment
  let sizeWitness := compactNumericVerifierStepNextSizeWitness environment
  have hcore : CompactNumericVerifierStateCoreGraph
      (environment 0) (environment 1) (environment 2)
      coordinates sizeWitness := by
    exact compactNumericVerifierStepGraphDef_evalb_nextCore environment hstep
  rcases
      FoundationCompactNumericListedDirectVerifierStateRealization.CompactNumericVerifierStateCoreGraph.realizeDirectLayout
        hcore with
    ⟨proofTokens, certificateTokens, tasks, values, status,
      _hproofLength, _hcertificateLength, _htasksLength, _hvaluesLength,
      hstateLayout, _hproofLayout, _hcertificateLayout,
      _htaskListLayout, _htaskRows,
      _hvalueListLayout, _hvalueRows, hstatusCase⟩
  have hcoordinateFields :=
    compactNumericVerifierStepNextCoordinates_fields environment
  change
    coordinates.start = environment 24 ∧
      coordinates.finish = environment 25 ∧
      coordinates.proofFinish = environment 26 ∧
      coordinates.proofCount = environment 27 ∧
      coordinates.certificateFinish = environment 28 ∧
      coordinates.certificateCount = environment 29 ∧
      coordinates.tasksFinish = environment 30 ∧
      coordinates.taskCount = environment 31 ∧
      coordinates.taskBoundary = environment 32 ∧
      coordinates.valuesFinish = environment 33 ∧
      coordinates.valueCount = environment 34 ∧
      coordinates.valueBoundary = environment 35 ∧
      coordinates.statusTag = environment 36 ∧
      coordinates.statusPayloadStart = environment 37 ∧
      coordinates.statusBool = environment 38 at hcoordinateFields
  rcases hcoordinateFields with
    ⟨hstart, hfinish, _hproofFinish, _hproofCount,
      _hcertificateFinish, _hcertificateCount,
      _htasksFinish, _htaskCount, _htaskBoundary,
      _hvaluesFinish, _hvalueCount, _hvalueBoundary,
      hstatusTag, _hstatusPayloadStart, hstatusBool⟩
  have hstatus : status = some true := by
    rcases hstatusCase with hnone | hsome
    · have hzero : coordinates.statusTag = 0 := hnone.2
      have hone : coordinates.statusTag = 1 :=
        hstatusTag.trans haccepted.1
      omega
    · rcases hsome with ⟨result, hresult, _htag, hbool⟩
      have hboolOne : compactAdditiveBoolTag result = 1 :=
        hbool.trans (hstatusBool.trans haccepted.2)
      have hresultTrue : result = true := by
        cases result <;> simp [compactAdditiveBoolTag] at hboolOne ⊢
      simpa [hresultTrue] using hresult
  have hstateLayout' : CompactNumericVerifierStateDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 24) (environment 25)
      (((proofTokens, certificateTokens), (tasks, values)), status) := by
    simpa only [hstart, hfinish] using hstateLayout
  exact ⟨(((proofTokens, certificateTokens), (tasks, values)), status),
    hstateLayout', hstatus⟩

theorem CompactNumericVerifierAcceptedEnvironment.ofAcceptedState
    {environment : Fin 429 -> Nat}
    {state : CompactNumericVerifierState}
    (hstep : compactNumericVerifierStepGraphDef.val.Evalb environment)
    (hnext : CompactNumericVerifierStateDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 24) (environment 25) state)
    (haccepted : state.2 = some true) :
    CompactNumericVerifierAcceptedEnvironment environment := by
  let coordinates := compactNumericVerifierStepNextCoordinates environment
  let sizeWitness := compactNumericVerifierStepNextSizeWitness environment
  have hcore : CompactNumericVerifierStateCoreGraph
      (environment 0) (environment 1) (environment 2)
      coordinates sizeWitness := by
    exact compactNumericVerifierStepGraphDef_evalb_nextCore environment hstep
  rcases
      FoundationCompactNumericListedDirectVerifierStateRealization.CompactNumericVerifierStateCoreGraph.realizeDirectLayout
        hcore with
    ⟨proofTokens, certificateTokens, tasks, values, status,
      _hproofLength, _hcertificateLength, _htasksLength, _hvaluesLength,
      hdecodedLayout, _hproofLayout, _hcertificateLayout,
      _htaskListLayout, _htaskRows,
      _hvalueListLayout, _hvalueRows, hstatusCase⟩
  have hcoordinateFields :=
    compactNumericVerifierStepNextCoordinates_fields environment
  change
    coordinates.start = environment 24 ∧
      coordinates.finish = environment 25 ∧
      coordinates.proofFinish = environment 26 ∧
      coordinates.proofCount = environment 27 ∧
      coordinates.certificateFinish = environment 28 ∧
      coordinates.certificateCount = environment 29 ∧
      coordinates.tasksFinish = environment 30 ∧
      coordinates.taskCount = environment 31 ∧
      coordinates.taskBoundary = environment 32 ∧
      coordinates.valuesFinish = environment 33 ∧
      coordinates.valueCount = environment 34 ∧
      coordinates.valueBoundary = environment 35 ∧
      coordinates.statusTag = environment 36 ∧
      coordinates.statusPayloadStart = environment 37 ∧
      coordinates.statusBool = environment 38 at hcoordinateFields
  rcases hcoordinateFields with
    ⟨hstart, hfinish, _hproofFinish, _hproofCount,
      _hcertificateFinish, _hcertificateCount,
      _htasksFinish, _htaskCount, _htaskBoundary,
      _hvaluesFinish, _hvalueCount, _hvalueBoundary,
      hstatusTag, _hstatusPayloadStart, hstatusBool⟩
  have hdecodedLayout' : CompactNumericVerifierStateDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 24) (environment 25)
      (((proofTokens, certificateTokens), (tasks, values)), status) := by
    simpa only [hstart, hfinish] using hdecodedLayout
  rcases
      FoundationCompactNumericListedDirectVerifierStateCrossTableEquality.CompactNumericVerifierStateDirectLayout.toSliceCarries
        hnext with
    ⟨_hnextFinish, hnextBound, _hnextEntries⟩
  have hslices : CompactFixedWidthTokenSlicesEq
      (environment 0) (environment 1) (environment 2)
      (environment 24) (environment 25)
      (environment 24) (environment 25) :=
    CompactFixedWidthTokenSlicesEq.refl (by omega) hnextBound
  have hstateEq :
      (((proofTokens, certificateTokens), (tasks, values)), status) = state :=
    CompactFixedWidthTokenSlicesEq.verifierStateValue_eq
      hslices hnext hdecodedLayout'
  have hstatusEq : status = some true :=
    (congrArg (fun value : CompactNumericVerifierState => value.2)
      hstateEq).trans haccepted
  rcases hstatusCase with hnone | hsome
  · rw [hstatusEq] at hnone
    simp at hnone
  · rcases hsome with ⟨result, hresult, htag, hbool⟩
    have hresultTrue : result = true := by
      rw [hstatusEq] at hresult
      exact (Option.some.inj hresult).symm
    subst result
    have hboolOne : coordinates.statusBool = 1 := by
      simpa [compactAdditiveBoolTag] using hbool.symm
    exact ⟨hstatusTag.symm.trans htag,
      hstatusBool.symm.trans hboolOne⟩

#print axioms compactNumericVerifierAcceptedEnvironmentDef_spec
#print axioms compactNumericVerifierAcceptedEnvironmentDef_sigmaZero
#print axioms CompactNumericVerifierAcceptedEnvironment.realizeAcceptedState
#print axioms CompactNumericVerifierAcceptedEnvironment.ofAcceptedState

end FoundationCompactNumericListedDirectVerifierFinalEnvironmentFormula
