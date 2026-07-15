import integration.FoundationCompactNumericListedDirectChildResultListDropRows

/-!
# Exact bounded rows for a failed verifier combine

The public combine transition fails exactly when a binary rule has fewer than
two child results, a unary rule has no child result, or the task tag is not a
combine tag.  The failed state preserves the complete child-result stack and
stores `some false`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineFailureRows

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectChildResultListDropRows

def CompactNumericCombineFailureGuard (taskTag valueCount : Nat) : Prop :=
  (((taskTag = 3 ∨ taskTag = 9) ∧ valueCount < 2) ∨
    ((taskTag = 4 ∨ taskTag = 5 ∨ taskTag = 6 ∨
        taskTag = 7 ∨ taskTag = 8) ∧ valueCount < 1) ∨
    (taskTag < 3 ∨ 9 < taskTag))

def compactNumericCombineFailureGuardDef :
    𝚺₀.Semisentence 2 := .mkSigma
  “taskTag valueCount.
    (((taskTag = 3 ∨ taskTag = 9) ∧ valueCount < 2) ∨
      ((taskTag = 4 ∨ taskTag = 5 ∨ taskTag = 6 ∨
          taskTag = 7 ∨ taskTag = 8) ∧ valueCount < 1) ∨
      (taskTag < 3 ∨ 9 < taskTag))”

@[simp] theorem compactNumericCombineFailureGuardDef_spec
    (taskTag valueCount : Nat) :
    compactNumericCombineFailureGuardDef.val.Evalb
        ![taskTag, valueCount] ↔
      CompactNumericCombineFailureGuard taskTag valueCount := by
  simp [compactNumericCombineFailureGuardDef,
    CompactNumericCombineFailureGuard]
  omega

theorem compactNumericCombineFailureGuardDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericCombineFailureGuardDef.val := by
  simp [compactNumericCombineFailureGuardDef]

theorem compactNumericCombineFailureGuard_iff_transition_none
    (task : CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    CompactNumericCombineFailureGuard task.1 values.length ↔
      compactNumericCombineTransition task values = none := by
  by_cases h3 : task.1 = 3
  · rw [h3]
    cases values with
    | nil =>
        simp_all [CompactNumericCombineFailureGuard,
          compactNumericCombineTransition]
    | cons first rest =>
        cases rest with
        | nil =>
            simp_all [CompactNumericCombineFailureGuard,
              compactNumericCombineTransition]
        | cons second tail =>
            simp_all [CompactNumericCombineFailureGuard,
              compactNumericCombineTransition]
  by_cases h4 : task.1 = 4
  · rw [h4]
    cases values <;>
      simp_all [CompactNumericCombineFailureGuard,
        compactNumericCombineTransition]
  by_cases h5 : task.1 = 5
  · rw [h5]
    cases values <;>
      simp_all [CompactNumericCombineFailureGuard,
        compactNumericCombineTransition]
  by_cases h6 : task.1 = 6
  · rw [h6]
    cases values <;>
      simp_all [CompactNumericCombineFailureGuard,
        compactNumericCombineTransition]
  by_cases h7 : task.1 = 7
  · rw [h7]
    cases values <;>
      simp_all [CompactNumericCombineFailureGuard,
        compactNumericCombineTransition]
  by_cases h8 : task.1 = 8
  · rw [h8]
    cases values <;>
      simp_all [CompactNumericCombineFailureGuard,
        compactNumericCombineTransition]
  by_cases h9 : task.1 = 9
  · rw [h9]
    cases values with
    | nil =>
        simp_all [CompactNumericCombineFailureGuard,
          compactNumericCombineTransition]
    | cons first rest =>
        cases rest with
        | nil =>
            simp_all [CompactNumericCombineFailureGuard,
              compactNumericCombineTransition]
        | cons second tail =>
            simp_all [CompactNumericCombineFailureGuard,
              compactNumericCombineTransition]
  have houtside : task.1 < 3 ∨ 9 < task.1 := by omega
  simp [CompactNumericCombineFailureGuard,
    compactNumericCombineTransition,
    h3, h4, h5, h6, h7, h8, h9, houtside]

def CompactNumericVerifierCombineFailureRows
    (tokenTable width tokenCount taskTag
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound nextStatusTag nextStatusBool : Nat) : Prop :=
  CompactNumericCombineFailureGuard taskTag sourceCount ∧
    CompactNumericChildResultListDropRows
      tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound 0 ∧
    nextStatusTag = 1 ∧
    nextStatusBool = 0

def compactNumericVerifierCombineFailureRowsDef :
    𝚺₀.Semisentence 12 := .mkSigma
  “tokenTable width tokenCount taskTag
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound nextStatusTag nextStatusBool.
    !(compactNumericCombineFailureGuardDef) taskTag sourceCount ∧
    !(compactNumericChildResultListDropRowsDef)
      tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound 0 ∧
    nextStatusTag = 1 ∧
    nextStatusBool = 0”

@[simp] theorem compactNumericVerifierCombineFailureRowsDef_spec
    (tokenTable width tokenCount taskTag
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound nextStatusTag nextStatusBool : Nat) :
    compactNumericVerifierCombineFailureRowsDef.val.Evalb
        ![tokenTable, width, tokenCount, taskTag,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          tableWidth, valueBound, nextStatusTag, nextStatusBool] ↔
      CompactNumericVerifierCombineFailureRows
        tokenTable width tokenCount taskTag
        sourceBoundary sourceCount targetBoundary targetCount
        tableWidth valueBound nextStatusTag nextStatusBool := by
  have hguardEnv :
      (Semiterm.val
          ![tokenTable, width, tokenCount, taskTag,
            sourceBoundary, sourceCount, targetBoundary, targetCount,
            tableWidth, valueBound, nextStatusTag, nextStatusBool]
          Empty.elim ∘
        ![(#3 : Semiterm ℒₒᵣ Empty 12), #5]) =
        ![taskTag, sourceCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hdropEnv :
      (Semiterm.val
          ![tokenTable, width, tokenCount, taskTag,
            sourceBoundary, sourceCount, targetBoundary, targetCount,
            tableWidth, valueBound, nextStatusTag, nextStatusBool]
          Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 12), #1, #2,
          #4, #5, #6, #7, #8, #9, (‘0’ : Semiterm ℒₒᵣ Empty 12)]) =
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          tableWidth, valueBound, 0] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierCombineFailureRowsDef,
    CompactNumericVerifierCombineFailureRows, hguardEnv, hdropEnv]

theorem compactNumericVerifierCombineFailureRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierCombineFailureRowsDef.val := by
  simp [compactNumericVerifierCombineFailureRowsDef]

theorem CompactNumericVerifierCombineFailureRows.sound
    {tokenTable width tokenCount taskTag
      sourceBoundary targetBoundary tableWidth valueBound
      nextStatusTag nextStatusBool : Nat}
    {task : CompactNumericVerifierTask}
    {source target : List CompactNumericChildResult}
    (hrows : CompactNumericVerifierCombineFailureRows
      tokenTable width tokenCount taskTag
      sourceBoundary source.length targetBoundary target.length
      tableWidth valueBound nextStatusTag nextStatusBool)
    (htaskTag : task.1 = taskTag)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target) :
    compactNumericCombineTransition task source = none ∧
      target = source ∧
      nextStatusTag = 1 ∧
      nextStatusBool = compactAdditiveBoolTag false := by
  rcases hrows with ⟨hguard, hdrop, hstatusTag, hstatusBool⟩
  have hguard' : CompactNumericCombineFailureGuard task.1 source.length := by
    simpa [htaskTag] using hguard
  have htransition :=
    (compactNumericCombineFailureGuard_iff_transition_none
      task source).mp hguard'
  have htarget := hdrop.eq_drop_of_rows hsourceRows htargetRows
  refine ⟨htransition, ?_, hstatusTag, ?_⟩
  · simpa using htarget
  · simpa [compactAdditiveBoolTag] using hstatusBool

theorem CompactNumericVerifierCombineFailureRows.of_transition_none
    {tokenTable width tokenCount taskTag
      sourceBoundary targetBoundary tableWidth valueBound
      nextStatusTag nextStatusBool : Nat}
    {task : CompactNumericVerifierTask}
    {source target : List CompactNumericChildResult}
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hsourceGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount sourceBoundary source.length
        tableWidth valueBound)
    (htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound)
    (htaskTag : task.1 = taskTag)
    (htransition : compactNumericCombineTransition task source = none)
    (htarget : target = source)
    (hnextStatusTag : nextStatusTag = 1)
    (hnextStatusBool : nextStatusBool = compactAdditiveBoolTag false) :
    CompactNumericVerifierCombineFailureRows
      tokenTable width tokenCount taskTag
      sourceBoundary source.length targetBoundary target.length
      tableWidth valueBound nextStatusTag nextStatusBool := by
  have hguardActual : CompactNumericCombineFailureGuard
      task.1 source.length :=
    (compactNumericCombineFailureGuard_iff_transition_none
      task source).mpr htransition
  have hguard : CompactNumericCombineFailureGuard
      taskTag source.length := by
    simpa only [htaskTag] using hguardActual
  have hdrop : CompactNumericChildResultListDropRows
      tokenTable width tokenCount
      sourceBoundary source.length targetBoundary target.length
      tableWidth valueBound 0 :=
    CompactAdditiveStructuredListElementRowLayouts.childResultDropRows
      hsourceRows htargetRows hsourceGraph htargetGraph
      (by omega) (by simpa using htarget)
  refine ⟨hguard, hdrop, hnextStatusTag, ?_⟩
  simpa [compactAdditiveBoolTag] using hnextStatusBool

#print axioms compactNumericCombineFailureGuardDef_spec
#print axioms compactNumericCombineFailureGuardDef_sigmaZero
#print axioms compactNumericCombineFailureGuard_iff_transition_none
#print axioms compactNumericVerifierCombineFailureRowsDef_spec
#print axioms compactNumericVerifierCombineFailureRowsDef_sigmaZero
#print axioms CompactNumericVerifierCombineFailureRows.sound
#print axioms CompactNumericVerifierCombineFailureRows.of_transition_none

end FoundationCompactNumericListedDirectVerifierCombineFailureRows
