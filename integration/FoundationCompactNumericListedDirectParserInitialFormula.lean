import integration.FoundationCompactNumericListedDirectParserStateAtRows
import integration.FoundationCompactNumericListedDirectNatListSameRows
import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRows
import integration.FoundationCompactNumericListedDirectBinaryNatStatusCases

/-!
# Handwritten bounded formula for a parser initial-state row

An initial row copies one supplied natural-token list, contains exactly one
specified three-field task, and carries the running status tag.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserInitialFormula

open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows

def CompactUnifiedParserInitialStateRows
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount taskKind taskBinderArity taskRepeatCount : Nat) :
    Prop :=
  CompactAdditiveNatListSameRows
      tokenTable width tokenCount sourceBoundary sourceCount
        coordinates.tokensBoundary coordinates.tokensCount ∧
    coordinates.tasksCount = 1 ∧
    CompactAdditiveSyntaxTaskListAtRows
      tokenTable width tokenCount
        coordinates.tasksBoundary coordinates.tasksCount
        0 taskKind taskBinderArity taskRepeatCount ∧
    CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount coordinates.tasksFinish coordinates.finish

def compactUnifiedParserInitialStateRowsDef : 𝚺₀.Semisentence 16 := .mkSigma
  “tokenTable width tokenCount
      start finish tokensFinish tasksFinish
      tokensBoundary tokensCount tasksBoundary tasksCount
      sourceBoundary sourceCount taskKind taskBinderArity taskRepeatCount.
    !(compactAdditiveNatListSameRowsDef)
      tokenTable width tokenCount
        sourceBoundary sourceCount tokensBoundary tokensCount ∧
    tasksCount = 1 ∧
    !(compactAdditiveSyntaxTaskListAtRowsDef)
      tokenTable width tokenCount tasksBoundary tasksCount
        0 taskKind taskBinderArity taskRepeatCount ∧
    !(compactBinaryNatRunningStatusSliceDef)
      tokenTable width tokenCount tasksFinish finish”

def compactUnifiedParserInitialStateRowsEnvironment
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount taskKind taskBinderArity taskRepeatCount : Nat) :
    Fin 16 → Nat :=
  ![tokenTable, width, tokenCount,
    coordinates.start, coordinates.finish,
    coordinates.tokensFinish, coordinates.tasksFinish,
    coordinates.tokensBoundary, coordinates.tokensCount,
    coordinates.tasksBoundary, coordinates.tasksCount,
    sourceBoundary, sourceCount, taskKind, taskBinderArity, taskRepeatCount]

@[simp] theorem compactUnifiedParserInitialStateRowsDef_spec
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount taskKind taskBinderArity taskRepeatCount : Nat) :
    compactUnifiedParserInitialStateRowsDef.val.Evalb
        (compactUnifiedParserInitialStateRowsEnvironment
          tokenTable width tokenCount coordinates sourceBoundary sourceCount
            taskKind taskBinderArity taskRepeatCount) ↔
      CompactUnifiedParserInitialStateRows
        tokenTable width tokenCount coordinates sourceBoundary sourceCount
          taskKind taskBinderArity taskRepeatCount := by
  let env := compactUnifiedParserInitialStateRowsEnvironment
    tokenTable width tokenCount coordinates sourceBoundary sourceCount
      taskKind taskBinderArity taskRepeatCount
  change compactUnifiedParserInitialStateRowsDef.val.Evalb env ↔ _
  have htokensEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 16), #1, #2,
          #11, #12, #7, #8]) =
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount,
          coordinates.tokensBoundary, coordinates.tokensCount] := by
    funext index
    fin_cases index <;> rfl
  have htaskEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 16), #1, #2, #9, #10,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 16), #13, #14, #15]) =
        compactAdditiveSyntaxTaskListAtRowsEnvironment
          tokenTable width tokenCount
            coordinates.tasksBoundary coordinates.tasksCount
            0 taskKind taskBinderArity taskRepeatCount := by
    funext index
    fin_cases index <;> rfl
  have hrunningEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 16), #1, #2, #6, #4]) =
        ![tokenTable, width, tokenCount,
          coordinates.tasksFinish, coordinates.finish] := by
    funext index
    fin_cases index <;> rfl
  have htasksCountValue : env 10 = coordinates.tasksCount := rfl
  simp [compactUnifiedParserInitialStateRowsDef,
    CompactUnifiedParserInitialStateRows,
    htokensEnv, htaskEnv, hrunningEnv, htasksCountValue]

theorem compactUnifiedParserInitialStateRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserInitialStateRowsDef.val := by
  simp [compactUnifiedParserInitialStateRowsDef]

private theorem list_eq_singleton_of_length_getI
    {α : Type*} [Inhabited α] {values : List α} {value : α}
    (hlength : values.length = 1)
    (hvalue : values.getI 0 = value) :
    values = [value] := by
  cases values with
  | nil => simp at hlength
  | cons head tail =>
      cases tail with
      | nil =>
          simp only [List.getI_cons_zero] at hvalue
          subst head
          rfl
      | cons next rest => simp at hlength

theorem compactUnifiedParserInitialStateRows_iff
    {tokenTable width tokenCount sourceBoundary : Nat}
    {coordinates : CompactUnifiedParserStateRowCoordinates}
    {source : List Nat} {state : CompactUnifiedParserState}
    {taskKind taskBinderArity taskRepeatCount : Nat}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (hstate : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount coordinates state) :
    CompactUnifiedParserInitialStateRows
        tokenTable width tokenCount coordinates sourceBoundary source.length
          taskKind taskBinderArity taskRepeatCount ↔
      state =
        (source, [(taskKind, taskBinderArity, taskRepeatCount)], none) := by
  constructor
  · rintro ⟨hsameRows, htasksCount, htaskRows, hrunning⟩
    have hsameRows' : CompactAdditiveNatListSameRows
        tokenTable width tokenCount sourceBoundary source.length
          coordinates.tokensBoundary state.1.length := by
      simpa only [hstate.tokensCount_eq] using hsameRows
    have htokens : state.1 = source :=
      CompactAdditiveNatListSameRows.eq_of_rows
        hsameRows' hsource hstate.tokensRows
    have htaskRows' :=
      (compactAdditiveSyntaxTaskListAtRows_iff_getI
        hstate.tasksRows 0 taskKind taskBinderArity taskRepeatCount).mp (by
          simpa only [hstate.tasksCount_eq] using htaskRows)
    have htasksLength : state.2.1.length = 1 := by
      exact hstate.tasksCount_eq.symm.trans htasksCount
    have htasks : state.2.1 =
        [(taskKind, taskBinderArity, taskRepeatCount)] :=
      list_eq_singleton_of_length_getI htasksLength htaskRows'.2
    have hstatus : state.2.2 = none :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hstate.statusLayout).mp hrunning
    rcases state with ⟨tokens, tasks, status⟩
    simp only at htokens htasks hstatus ⊢
    subst tokens
    subst tasks
    subst status
    rfl
  · intro hstateEq
    subst state
    have hsameRows : CompactAdditiveNatListSameRows
        tokenTable width tokenCount sourceBoundary source.length
          coordinates.tokensBoundary source.length :=
      CompactAdditiveStructuredListElementRowLayouts.natSameRows
        hsource hstate.tokensRows rfl
    have htaskRows : CompactAdditiveSyntaxTaskListAtRows
        tokenTable width tokenCount coordinates.tasksBoundary
          [(taskKind, taskBinderArity, taskRepeatCount)].length
          0 taskKind taskBinderArity taskRepeatCount :=
      (compactAdditiveSyntaxTaskListAtRows_iff_getI
        hstate.tasksRows 0 taskKind taskBinderArity taskRepeatCount).mpr (by simp)
    have hrunning : CompactBinaryNatRunningStatusSlice
        tokenTable width tokenCount coordinates.tasksFinish coordinates.finish :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hstate.statusLayout).mpr rfl
    refine ⟨?_, ?_, ?_, hrunning⟩
    · simpa only [hstate.tokensCount_eq] using hsameRows
    · simpa only [hstate.tasksCount_eq, List.length_cons,
        List.length_nil, Nat.zero_add]
    · simpa only [hstate.tasksCount_eq] using htaskRows

#print axioms compactUnifiedParserInitialStateRowsDef_spec
#print axioms compactUnifiedParserInitialStateRowsDef_sigmaZero
#print axioms compactUnifiedParserInitialStateRows_iff

end FoundationCompactNumericListedDirectParserInitialFormula
