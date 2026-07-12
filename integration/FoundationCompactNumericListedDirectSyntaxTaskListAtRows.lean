import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRows

/-!
# Direct bounded lookup of one syntax-task-list row

The formula reads the two boundary cursors around a selected task row and binds
the three consecutive token values to an explicit kind, binder arity, and
repeat count.  Under real row layouts this is exactly lookup in the typed task
list, not merely a same-width row check.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSyntaxTaskListAtRows

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows

def CompactAdditiveSyntaxTaskListAtRows
    (tokenTable width tokenCount boundaryTable count index
      kind binderArity repeatCount : Nat) : Prop :=
  index < count ∧
    ∃ left, left ≤ tokenCount ∧
    ∃ right, right ≤ tokenCount ∧
      CompactFixedWidthEntry boundaryTable tokenCount index left ∧
      CompactFixedWidthEntry boundaryTable tokenCount (index + 1) right ∧
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        left right (kind, binderArity, repeatCount)

def compactAdditiveSyntaxTaskListAtRowsDef : 𝚺₀.Semisentence 9 := .mkSigma
  “tokenTable width tokenCount boundaryTable count index
      kind binderArity repeatCount.
    index < count ∧
    ∃ left <⁺ tokenCount,
      ∃ right <⁺ tokenCount,
        !(compactFixedWidthEntryDef)
          boundaryTable tokenCount index left ∧
        !(compactFixedWidthEntryDef)
          boundaryTable tokenCount (index + 1) right ∧
        !(compactSyntaxTaskDirectLayoutDef)
          tokenTable width tokenCount left right
            kind binderArity repeatCount”

def compactAdditiveSyntaxTaskListAtRowsEnvironment
    (tokenTable width tokenCount boundaryTable count index
      kind binderArity repeatCount : Nat) : Fin 9 → Nat :=
  ![tokenTable, width, tokenCount, boundaryTable, count, index,
    kind, binderArity, repeatCount]

@[simp] theorem compactAdditiveSyntaxTaskListAtRowsDef_spec
    (tokenTable width tokenCount boundaryTable count index
      kind binderArity repeatCount : Nat) :
    compactAdditiveSyntaxTaskListAtRowsDef.val.Evalb
        (compactAdditiveSyntaxTaskListAtRowsEnvironment
          tokenTable width tokenCount boundaryTable count index
            kind binderArity repeatCount) ↔
      CompactAdditiveSyntaxTaskListAtRows
        tokenTable width tokenCount boundaryTable count index
          kind binderArity repeatCount := by
  have hlayout
      (right left : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![right, left,
                tokenTable, width, tokenCount, boundaryTable, count, index,
                kind, binderArity, repeatCount]
              Empty.elim ∘
            ![(#2 : Semiterm ℒₒᵣ Empty 11), #3, #4, #1, #0,
              #8, #9, #10])
          Empty.elim) compactSyntaxTaskDirectLayoutDef.val ↔
        CompactSyntaxTaskDirectLayout tokenTable width tokenCount
          left right (kind, binderArity, repeatCount) := by
    have henv :
        (Semiterm.val
            ![right, left,
              tokenTable, width, tokenCount, boundaryTable, count, index,
              kind, binderArity, repeatCount]
            Empty.elim ∘
          ![(#2 : Semiterm ℒₒᵣ Empty 11), #3, #4, #1, #0,
            #8, #9, #10]) =
          ![tokenTable, width, tokenCount,
            left, right, kind, binderArity, repeatCount] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    simp
  simp [compactAdditiveSyntaxTaskListAtRowsDef,
    CompactAdditiveSyntaxTaskListAtRows,
    compactAdditiveSyntaxTaskListAtRowsEnvironment, hlayout]

theorem compactAdditiveSyntaxTaskListAtRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveSyntaxTaskListAtRowsDef.val := by
  simp [compactAdditiveSyntaxTaskListAtRowsDef]

theorem compactAdditiveSyntaxTaskListAtRows_iff_getI
    {tokenTable width tokenCount boundaryTable : Nat}
    {tasks : List CompactSyntaxTask}
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        boundaryTable tasks)
    (index kind binderArity repeatCount : Nat) :
    CompactAdditiveSyntaxTaskListAtRows
        tokenTable width tokenCount boundaryTable tasks.length index
          kind binderArity repeatCount ↔
      index < tasks.length ∧
        tasks.getI index = (kind, binderArity, repeatCount) := by
  constructor
  · rintro ⟨hindex, left, _hleft, right, _hright,
      hleftEntry, hrightEntry, hdirect⟩
    rcases hrows index hindex with
      ⟨rowLeft, _hrowLeft, rowRight, _hrowRight,
        hrowLeftEntry, hrowRightEntry, hrowLayout⟩
    have hleft : left = rowLeft :=
      (CompactFixedWidthEntry.value_eq_tableValue hleftEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue hrowLeftEntry).symm
    have hright : right = rowRight :=
      (CompactFixedWidthEntry.value_eq_tableValue hrightEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue hrowRightEntry).symm
    subst left
    subst right
    have hrowEq : CompactAdditiveSyntaxTaskRowEq
        tokenTable width tokenCount
          rowLeft rowRight rowLeft rowRight :=
      CompactSyntaxTaskDirectLayout.rowEq hdirect hdirect
    have hvalue := hrowEq.value_eq hdirect hrowLayout
    exact ⟨hindex, hvalue.symm⟩
  · rintro ⟨hindex, hvalue⟩
    rcases hrows index hindex with
      ⟨left, hleft, right, hright,
        hleftEntry, hrightEntry, hlayout⟩
    rw [hvalue] at hlayout
    exact ⟨hindex, left, hleft, right, hright,
      hleftEntry, hrightEntry, hlayout⟩

#print axioms compactAdditiveSyntaxTaskListAtRowsDef_spec
#print axioms compactAdditiveSyntaxTaskListAtRowsDef_sigmaZero
#print axioms compactAdditiveSyntaxTaskListAtRows_iff_getI

end FoundationCompactNumericListedDirectSyntaxTaskListAtRows
