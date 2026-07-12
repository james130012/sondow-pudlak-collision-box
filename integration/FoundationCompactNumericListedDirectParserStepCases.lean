import integration.FoundationCompactNumericListedDirectParserStateFormula
import integration.FoundationCompactProofTokenMachine
import integration.FoundationCompactCertificateTokenMachine

/-!
# Exact common outer cases for the three parser steps

The syntax, proof, and certificate parsers share the same outer control flow:
an already finished state is fixed, an empty running task stack completes with
the remaining tokens, and a nonempty running stack executes its head task.
This module proves that three-way normal form exactly, before arithmeticizing
the individual task branches.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserStepCases

open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactParserDirectTrace

def CompactUnifiedParserOuterStep
    (taskStep : CompactSyntaxTask × List Nat × List CompactSyntaxTask →
      CompactUnifiedParserState)
    (state : CompactUnifiedParserState) : CompactUnifiedParserState :=
  if state.2.2.isSome then state
  else
    match state.2.1 with
    | [] => (state.1, [], some (some state.1))
    | task :: tasks => taskStep (task, state.1, tasks)

def CompactUnifiedParserOuterStepCases
    (taskStep : CompactSyntaxTask × List Nat × List CompactSyntaxTask →
      CompactUnifiedParserState)
    (current next : CompactUnifiedParserState) : Prop :=
  (current.2.2.isSome = true ∧ next = current) ∨
    (current.2.2 = none ∧ current.2.1 = [] ∧
      next = (current.1, [], some (some current.1))) ∨
    (current.2.2 = none ∧
      ∃ task tasks,
        current.2.1 = task :: tasks ∧
        next = taskStep (task, current.1, tasks))

theorem compactUnifiedParserOuterStepCases_iff
    (taskStep : CompactSyntaxTask × List Nat × List CompactSyntaxTask →
      CompactUnifiedParserState)
    (current next : CompactUnifiedParserState) :
    CompactUnifiedParserOuterStepCases taskStep current next ↔
      next = CompactUnifiedParserOuterStep taskStep current := by
  rcases current with ⟨tokens, tasks, status⟩
  cases status with
  | none =>
      cases tasks with
      | nil =>
          simp [CompactUnifiedParserOuterStepCases,
            CompactUnifiedParserOuterStep]
      | cons task tasks =>
          simp [CompactUnifiedParserOuterStepCases,
            CompactUnifiedParserOuterStep]
  | some result =>
      simp [CompactUnifiedParserOuterStepCases,
        CompactUnifiedParserOuterStep]

theorem compactSyntaxParserStep_cases_iff
    (current next : CompactUnifiedParserState) :
    CompactUnifiedParserOuterStepCases
        compactSyntaxTaskTokenStep current next ↔
      next = compactSyntaxParserStep current := by
  rcases current with ⟨tokens, tasks, status⟩
  cases status with
  | none =>
      cases tasks with
      | nil =>
          simp [CompactUnifiedParserOuterStepCases,
            compactSyntaxParserStep, compactSyntaxRunningStep]
      | cons task tasks =>
          simp [CompactUnifiedParserOuterStepCases,
            compactSyntaxParserStep, compactSyntaxRunningStep]
  | some result =>
    simp [CompactUnifiedParserOuterStepCases,
        compactSyntaxParserStep]

theorem compactProofParserStep_cases_iff
    (current next : CompactProofParserState) :
    CompactUnifiedParserOuterStepCases
        compactProofParserTaskTokenStep current next ↔
      next = compactProofParserStep current := by
  rcases current with ⟨tokens, tasks, status⟩
  cases status with
  | none =>
      cases tasks with
      | nil =>
          simp [CompactUnifiedParserOuterStepCases,
            compactProofParserStep, compactProofParserRunningStep]
      | cons task tasks =>
          simp [CompactUnifiedParserOuterStepCases,
            compactProofParserStep, compactProofParserRunningStep]
  | some result =>
    simp [CompactUnifiedParserOuterStepCases,
        compactProofParserStep]

theorem compactCertificateParserStep_cases_iff
    (current next : CompactCertificateParserState) :
    CompactUnifiedParserOuterStepCases
        compactCertificateTaskTokenStep current next ↔
      next = compactCertificateParserStep current := by
  rcases current with ⟨tokens, tasks, status⟩
  cases status with
  | none =>
      cases tasks with
      | nil =>
          simp [CompactUnifiedParserOuterStepCases,
            compactCertificateParserStep,
            compactCertificateParserRunningStep]
      | cons task tasks =>
          simp [CompactUnifiedParserOuterStepCases,
            compactCertificateParserStep,
            compactCertificateParserRunningStep]
  | some result =>
    simp [CompactUnifiedParserOuterStepCases,
        compactCertificateParserStep]

#print axioms compactUnifiedParserOuterStepCases_iff
#print axioms compactSyntaxParserStep_cases_iff
#print axioms compactProofParserStep_cases_iff
#print axioms compactCertificateParserStep_cases_iff

end FoundationCompactNumericListedDirectParserStepCases
