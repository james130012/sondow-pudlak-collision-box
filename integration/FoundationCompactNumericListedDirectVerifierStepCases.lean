import integration.FoundationCompactNumericListedTaskMachine

/-!
# Exact control-flow cases for one compact numeric verifier step

This module removes the outer pattern matching around
`compactNumericVerifierStep`.  The four public cases are halted, finish,
parse, and combine.  The latter three are further split at the exact option
result used by the executable verifier.  No representability or proof-length
assumption occurs here; these equivalences are the semantic specification
that the later bounded arithmetic graph must implement branch by branch.
-/

namespace FoundationCompactNumericListedDirectVerifierStepCases

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine

def CompactNumericVerifierHaltedStepCase
    (current next : CompactNumericVerifierState) : Prop :=
  current.2.isSome = true ∧ next = current

def CompactNumericVerifierFinishStepCase
    (current next : CompactNumericVerifierState) : Prop :=
  current.2 = none ∧
    current.1.2.1 = [] ∧
    next = compactNumericFinishState current.1

def CompactNumericVerifierParseStepCase
    (current next : CompactNumericVerifierState) : Prop :=
  ∃ task restTasks,
    current.2 = none ∧
    current.1.2.1 = task :: restTasks ∧
    task.1 = 10 ∧
    next = compactNumericParseState
      (current.1.1, (restTasks, current.1.2.2))

def CompactNumericVerifierCombineStepCase
    (current next : CompactNumericVerifierState) : Prop :=
  ∃ task restTasks,
    current.2 = none ∧
    current.1.2.1 = task :: restTasks ∧
    task.1 ≠ 10 ∧
    next = compactNumericCombineState task
      (current.1.1, (restTasks, current.1.2.2))

def CompactNumericVerifierStepCases
    (current next : CompactNumericVerifierState) : Prop :=
  CompactNumericVerifierHaltedStepCase current next ∨
    CompactNumericVerifierFinishStepCase current next ∨
    CompactNumericVerifierParseStepCase current next ∨
    CompactNumericVerifierCombineStepCase current next

theorem compactNumericVerifierStep_cases_iff
    (current next : CompactNumericVerifierState) :
    CompactNumericVerifierStepCases current next ↔
      next = compactNumericVerifierStep current := by
  rcases current with ⟨payload, status⟩
  rcases payload with ⟨streams, tasks, values⟩
  rcases status with _ | result
  · rcases tasks with _ | ⟨task, restTasks⟩
    · simp [CompactNumericVerifierStepCases,
        CompactNumericVerifierHaltedStepCase,
        CompactNumericVerifierFinishStepCase,
        CompactNumericVerifierParseStepCase,
        CompactNumericVerifierCombineStepCase,
        compactNumericVerifierStep, compactNumericRunningStep]
    · by_cases htag : task.1 = 10
      · simp [CompactNumericVerifierStepCases,
          CompactNumericVerifierHaltedStepCase,
          CompactNumericVerifierFinishStepCase,
          CompactNumericVerifierParseStepCase,
          CompactNumericVerifierCombineStepCase,
          compactNumericVerifierStep, compactNumericRunningStep, htag]
      · simp [CompactNumericVerifierStepCases,
          CompactNumericVerifierHaltedStepCase,
          CompactNumericVerifierFinishStepCase,
          CompactNumericVerifierParseStepCase,
          CompactNumericVerifierCombineStepCase,
          compactNumericVerifierStep, compactNumericRunningStep, htag]
  · simp [CompactNumericVerifierStepCases,
      CompactNumericVerifierHaltedStepCase,
      CompactNumericVerifierFinishStepCase,
      CompactNumericVerifierParseStepCase,
      CompactNumericVerifierCombineStepCase,
      compactNumericVerifierStep]

def CompactNumericFinishSuccessCase
    (payload : CompactNumericRunningPayload)
    (next : CompactNumericVerifierState) : Prop :=
  payload.1.1 = [] ∧
    payload.1.2 = [] ∧
    payload.2.1 = [] ∧
    payload.2.2.length = 1 ∧
    next = (payload, some
      (payload.2.2.head?.getD compactNumericDefaultChildResult).2)

def CompactNumericFinishFailureCase
    (payload : CompactNumericRunningPayload)
    (next : CompactNumericVerifierState) : Prop :=
  ¬(payload.1.1 = [] ∧
      payload.1.2 = [] ∧
      payload.2.1 = [] ∧
      payload.2.2.length = 1) ∧
    next = (payload, some false)

theorem compactNumericFinishState_cases_iff
    (payload : CompactNumericRunningPayload)
    (next : CompactNumericVerifierState) :
    CompactNumericFinishSuccessCase payload next ∨
      CompactNumericFinishFailureCase payload next ↔
        next = compactNumericFinishState payload := by
  by_cases hguard : payload.1.1 = [] ∧
      payload.1.2 = [] ∧ payload.2.1 = [] ∧ payload.2.2.length = 1
  · simp [CompactNumericFinishSuccessCase,
      CompactNumericFinishFailureCase, compactNumericFinishState, hguard]
  · have hfinish : compactNumericFinishState payload =
        (payload, some false) := by
      simp [compactNumericFinishState, hguard]
    rw [hfinish]
    constructor
    · intro hcases
      rcases hcases with hsuccess | hfailure
      · rcases hsuccess with ⟨hproof, hcertificate, htasks,
          hlength, _hnext⟩
        exact (hguard ⟨hproof, hcertificate, htasks, hlength⟩).elim
      · exact hfailure.2
    · intro hnext
      exact Or.inr ⟨hguard, hnext⟩

def CompactNumericParseSuccessCase
    (payload : CompactNumericRunningPayload)
    (next : CompactNumericVerifierState) : Prop :=
  ∃ parsed,
    compactNumericParsePayload payload = some parsed ∧
    next = (parsed, none)

def CompactNumericParseFailureCase
    (payload : CompactNumericRunningPayload)
    (next : CompactNumericVerifierState) : Prop :=
  compactNumericParsePayload payload = none ∧
    next = (payload, some false)

theorem compactNumericParseState_cases_iff
    (payload : CompactNumericRunningPayload)
    (next : CompactNumericVerifierState) :
    CompactNumericParseSuccessCase payload next ∨
      CompactNumericParseFailureCase payload next ↔
        next = compactNumericParseState payload := by
  cases hparse : compactNumericParsePayload payload with
  | none =>
      simp [CompactNumericParseSuccessCase,
        CompactNumericParseFailureCase, compactNumericParseState, hparse]
  | some parsed =>
      simp [CompactNumericParseSuccessCase,
        CompactNumericParseFailureCase, compactNumericParseState, hparse]

def CompactNumericParsePayloadSuccessCase
    (payload parsed : CompactNumericRunningPayload) : Prop :=
  ∃ proofNode certificateNode,
    compactListedProofNodeFieldsParser payload.1.1 = some proofNode ∧
    compactStructuralCertificateNodeParser payload.1.2 =
      some certificateNode ∧
    compactNumericNodeTransition proofNode certificateNode
      payload.2.1 payload.2.2 = some parsed

def CompactNumericParsePayloadProofFailureCase
    (payload : CompactNumericRunningPayload) : Prop :=
  compactListedProofNodeFieldsParser payload.1.1 = none

def CompactNumericParsePayloadCertificateFailureCase
    (payload : CompactNumericRunningPayload) : Prop :=
  ∃ proofNode,
    compactListedProofNodeFieldsParser payload.1.1 = some proofNode ∧
    compactStructuralCertificateNodeParser payload.1.2 = none

def CompactNumericParsePayloadTransitionFailureCase
    (payload : CompactNumericRunningPayload) : Prop :=
  ∃ proofNode certificateNode,
    compactListedProofNodeFieldsParser payload.1.1 = some proofNode ∧
    compactStructuralCertificateNodeParser payload.1.2 =
      some certificateNode ∧
    compactNumericNodeTransition proofNode certificateNode
      payload.2.1 payload.2.2 = none

theorem compactNumericParsePayload_eq_some_iff
    (payload parsed : CompactNumericRunningPayload) :
    compactNumericParsePayload payload = some parsed ↔
      CompactNumericParsePayloadSuccessCase payload parsed := by
  cases hproof : compactListedProofNodeFieldsParser payload.1.1 with
  | none =>
      simp [compactNumericParsePayload,
        CompactNumericParsePayloadSuccessCase, hproof]
  | some proofNode =>
      cases hcertificate :
          compactStructuralCertificateNodeParser payload.1.2 with
      | none =>
          simp [compactNumericParsePayload,
            CompactNumericParsePayloadSuccessCase,
            hproof, hcertificate]
      | some certificateNode =>
          cases htransition : compactNumericNodeTransition proofNode
              certificateNode payload.2.1 payload.2.2 with
          | none =>
              simp [compactNumericParsePayload,
                CompactNumericParsePayloadSuccessCase,
                hproof, hcertificate, htransition]
          | some result =>
              simp [compactNumericParsePayload,
                CompactNumericParsePayloadSuccessCase,
                hproof, hcertificate, htransition]

theorem compactNumericParsePayload_eq_none_iff
    (payload : CompactNumericRunningPayload) :
    compactNumericParsePayload payload = none ↔
      CompactNumericParsePayloadProofFailureCase payload ∨
      CompactNumericParsePayloadCertificateFailureCase payload ∨
      CompactNumericParsePayloadTransitionFailureCase payload := by
  cases hproof : compactListedProofNodeFieldsParser payload.1.1 with
  | none =>
      simp [compactNumericParsePayload,
        CompactNumericParsePayloadProofFailureCase,
        CompactNumericParsePayloadCertificateFailureCase,
        CompactNumericParsePayloadTransitionFailureCase, hproof]
  | some proofNode =>
      cases hcertificate :
          compactStructuralCertificateNodeParser payload.1.2 with
      | none =>
          simp [compactNumericParsePayload,
            CompactNumericParsePayloadProofFailureCase,
            CompactNumericParsePayloadCertificateFailureCase,
            CompactNumericParsePayloadTransitionFailureCase,
            hproof, hcertificate]
      | some certificateNode =>
          cases htransition : compactNumericNodeTransition proofNode
              certificateNode payload.2.1 payload.2.2 with
          | none =>
              simp [compactNumericParsePayload,
                CompactNumericParsePayloadProofFailureCase,
                CompactNumericParsePayloadCertificateFailureCase,
                CompactNumericParsePayloadTransitionFailureCase,
                hproof, hcertificate, htransition]
          | some parsed =>
              simp [compactNumericParsePayload,
                CompactNumericParsePayloadProofFailureCase,
                CompactNumericParsePayloadCertificateFailureCase,
                CompactNumericParsePayloadTransitionFailureCase,
                hproof, hcertificate, htransition]

def CompactNumericCombineSuccessCase
    (task : CompactNumericVerifierTask)
    (payload : CompactNumericRunningPayload)
    (next : CompactNumericVerifierState) : Prop :=
  ∃ combined,
    compactNumericCombineTransition task payload.2.2 = some combined ∧
    next =
      ((payload.1, (payload.2.1, combined.1 :: combined.2)), none)

def CompactNumericCombineFailureCase
    (task : CompactNumericVerifierTask)
    (payload : CompactNumericRunningPayload)
    (next : CompactNumericVerifierState) : Prop :=
  compactNumericCombineTransition task payload.2.2 = none ∧
    next = (payload, some false)

theorem compactNumericCombineState_cases_iff
    (task : CompactNumericVerifierTask)
    (payload : CompactNumericRunningPayload)
    (next : CompactNumericVerifierState) :
    CompactNumericCombineSuccessCase task payload next ∨
      CompactNumericCombineFailureCase task payload next ↔
        next = compactNumericCombineState task payload := by
  cases hcombine : compactNumericCombineTransition task payload.2.2 with
  | none =>
      simp [CompactNumericCombineSuccessCase,
        CompactNumericCombineFailureCase, compactNumericCombineState,
        hcombine]
  | some combined =>
      simp [CompactNumericCombineSuccessCase,
        CompactNumericCombineFailureCase, compactNumericCombineState,
        hcombine]

#print axioms compactNumericVerifierStep_cases_iff
#print axioms compactNumericFinishState_cases_iff
#print axioms compactNumericParseState_cases_iff
#print axioms compactNumericParsePayload_eq_some_iff
#print axioms compactNumericParsePayload_eq_none_iff
#print axioms compactNumericCombineState_cases_iff

end FoundationCompactNumericListedDirectVerifierStepCases
