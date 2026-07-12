import integration.FoundationCompactNumericListedDirectSyntaxTaskLayout
import integration.FoundationCompactNumericListedDirectAtomicListRowRealization

/-!
# Pure numeric realization of syntax-task list rows

Every compact syntax task occupies exactly three natural-number token cells.
A bounded boundary-table formula enforces that fixed row width, after which
the common token table deterministically reconstructs the task kind, binder
arity, and repeat count without taking a typed task list as input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSyntaxTaskRowRealization

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskLayout

def CompactAdditiveTripleBoundaryRows
    (tokenCount count boundaryTable : Nat) : Prop :=
  ∀ index < count,
    ∃ left, left ≤ tokenCount ∧
    ∃ right, right ≤ tokenCount ∧
      CompactFixedWidthEntry boundaryTable tokenCount index left ∧
      CompactFixedWidthEntry boundaryTable tokenCount (index + 1) right ∧
      right = left + 3

def compactSyntaxTaskDirectLayoutDef : 𝚺₀.Semisentence 8 := .mkSigma
  “tokenTable width tokenCount start finish
      kind binderArity repeatCount.
    ∃ binderStart <⁺ tokenCount,
      ∃ countStart <⁺ tokenCount,
        !(compactAdditiveTokenCellDef)
          tokenTable width tokenCount start kind binderStart ∧
        !(compactAdditiveTokenCellDef)
          tokenTable width tokenCount
            binderStart binderArity countStart ∧
        !(compactAdditiveTokenCellDef)
          tokenTable width tokenCount
            countStart repeatCount finish”

@[simp] theorem compactSyntaxTaskDirectLayoutDef_spec
    (tokenTable width tokenCount start finish
      kind binderArity repeatCount : Nat) :
    compactSyntaxTaskDirectLayoutDef.val.Evalb
        ![tokenTable, width, tokenCount, start, finish,
          kind, binderArity, repeatCount] ↔
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        start finish (kind, binderArity, repeatCount) := by
  have hfirst (countStart binderStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![countStart, binderStart,
                tokenTable, width, tokenCount, start, finish,
                kind, binderArity, repeatCount]
              Empty.elim ∘
            ![(#2 : Semiterm ℒₒᵣ Empty 10), #3, #4, #5, #7, #1])
          Empty.elim) compactAdditiveTokenCellDef.val ↔
        CompactAdditiveTokenCell
          tokenTable width tokenCount start kind binderStart := by
    have henv :
        (Semiterm.val
            ![countStart, binderStart,
              tokenTable, width, tokenCount, start, finish,
              kind, binderArity, repeatCount]
            Empty.elim ∘
          ![(#2 : Semiterm ℒₒᵣ Empty 10), #3, #4, #5, #7, #1]) =
          ![tokenTable, width, tokenCount, start, kind, binderStart] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    simp
  have hsecond (countStart binderStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![countStart, binderStart,
                tokenTable, width, tokenCount, start, finish,
                kind, binderArity, repeatCount]
              Empty.elim ∘
            ![(#2 : Semiterm ℒₒᵣ Empty 10), #3, #4, #1, #8, #0])
          Empty.elim) compactAdditiveTokenCellDef.val ↔
        CompactAdditiveTokenCell
          tokenTable width tokenCount
            binderStart binderArity countStart := by
    have henv :
        (Semiterm.val
            ![countStart, binderStart,
              tokenTable, width, tokenCount, start, finish,
              kind, binderArity, repeatCount]
            Empty.elim ∘
          ![(#2 : Semiterm ℒₒᵣ Empty 10), #3, #4, #1, #8, #0]) =
          ![tokenTable, width, tokenCount,
            binderStart, binderArity, countStart] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    simp
  have hthird (countStart binderStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![countStart, binderStart,
                tokenTable, width, tokenCount, start, finish,
                kind, binderArity, repeatCount]
              Empty.elim ∘
            ![(#2 : Semiterm ℒₒᵣ Empty 10), #3, #4, #0, #9, #6])
          Empty.elim) compactAdditiveTokenCellDef.val ↔
        CompactAdditiveTokenCell
          tokenTable width tokenCount
            countStart repeatCount finish := by
    have henv :
        (Semiterm.val
            ![countStart, binderStart,
              tokenTable, width, tokenCount, start, finish,
              kind, binderArity, repeatCount]
            Empty.elim ∘
          ![(#2 : Semiterm ℒₒᵣ Empty 10), #3, #4, #0, #9, #6]) =
          ![tokenTable, width, tokenCount,
            countStart, repeatCount, finish] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    simp
  simp [compactSyntaxTaskDirectLayoutDef,
    CompactSyntaxTaskDirectLayout, hfirst, hsecond, hthird]
  constructor
  · rintro ⟨binderStart, _hbinderBound,
      countStart, _hcountBound, hkind, hbinder, hcount⟩
    exact ⟨binderStart, hkind, countStart, hbinder, hcount⟩
  · rintro ⟨binderStart, hkind, countStart, hbinder, hcount⟩
    exact ⟨binderStart, Nat.le_of_lt hbinder.1,
      countStart, Nat.le_of_lt hcount.1,
      hkind, hbinder, hcount⟩

theorem compactSyntaxTaskDirectLayoutDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactSyntaxTaskDirectLayoutDef.val := by
  simp [compactSyntaxTaskDirectLayoutDef]

def compactAdditiveTripleBoundaryRowsDef : 𝚺₀.Semisentence 3 := .mkSigma
  “tokenCount count boundaryTable.
    ∀ index < count,
      ∃ left <⁺ tokenCount,
        ∃ right <⁺ tokenCount,
          !(compactFixedWidthEntryDef)
            boundaryTable tokenCount index left ∧
          !(compactFixedWidthEntryDef)
            boundaryTable tokenCount (index + 1) right ∧
          right = left + 3”

@[simp] theorem compactAdditiveTripleBoundaryRowsDef_spec
    (tokenCount count boundaryTable : Nat) :
    compactAdditiveTripleBoundaryRowsDef.val.Evalb
        ![tokenCount, count, boundaryTable] ↔
      CompactAdditiveTripleBoundaryRows
        tokenCount count boundaryTable := by
  simp [compactAdditiveTripleBoundaryRowsDef,
    CompactAdditiveTripleBoundaryRows]
  constructor
  · intro h index hindex
    rcases h index hindex with
      ⟨left, hleft, hright, hleftEntry, hrightEntry⟩
    exact ⟨left, hleft, hright, hleftEntry, hrightEntry⟩
  · intro h index hindex
    rcases h index hindex with
      ⟨left, hleft, hright, hleftEntry, hrightEntry⟩
    exact ⟨left, hleft, hright, hleftEntry, hrightEntry⟩

theorem compactAdditiveTripleBoundaryRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveTripleBoundaryRowsDef.val := by
  simp [compactAdditiveTripleBoundaryRowsDef]

def compactAdditiveSyntaxTaskRowValue
    (tokenTable width tokenCount boundaryTable index : Nat) :
    CompactSyntaxTask :=
  let left := compactAdditiveBoundaryCursor
    tokenCount boundaryTable index
  (compactFixedWidthTableValue tokenTable width left,
    compactFixedWidthTableValue tokenTable width (left + 1),
    compactFixedWidthTableValue tokenTable width (left + 2))

def compactAdditiveSyntaxTaskListRowValues
    (tokenTable width tokenCount boundaryTable count : Nat) :
    List CompactSyntaxTask :=
  (List.range count).map fun index =>
    compactAdditiveSyntaxTaskRowValue
      tokenTable width tokenCount boundaryTable index

@[simp] theorem compactAdditiveSyntaxTaskListRowValues_length
    (tokenTable width tokenCount boundaryTable count : Nat) :
    (compactAdditiveSyntaxTaskListRowValues
      tokenTable width tokenCount boundaryTable count).length = count := by
  simp [compactAdditiveSyntaxTaskListRowValues]

theorem compactAdditiveSyntaxTaskListRowValues_getI
    (tokenTable width tokenCount boundaryTable count index : Nat)
    (hindex : index < count) :
    (compactAdditiveSyntaxTaskListRowValues
      tokenTable width tokenCount boundaryTable count).getI index =
        compactAdditiveSyntaxTaskRowValue
          tokenTable width tokenCount boundaryTable index := by
  rw [List.getI_eq_getElem _ (by simpa using hindex)]
  simp [compactAdditiveSyntaxTaskListRowValues]

theorem CompactAdditiveStructuredListElementRowLayouts.tripleBoundaryRows
    {tokenTable width tokenCount boundaryTable : Nat}
    {tasks : List CompactSyntaxTask}
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        boundaryTable tasks) :
    CompactAdditiveTripleBoundaryRows
      tokenCount tasks.length boundaryTable := by
  intro index hindex
  rcases hrows index hindex with
    ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry,
      binderStart, countStart, hkind, hbinder, hcount⟩
  refine ⟨left, hleft, right, hright,
    hleftEntry, hrightEntry, ?_⟩
  dsimp [CompactAdditiveTokenCell] at hkind hbinder hcount
  omega

theorem CompactAdditiveTripleBoundaryRows.realizedTaskRows
    {tokenTable width tokenCount boundaryTable count : Nat}
    (htriple : CompactAdditiveTripleBoundaryRows
      tokenCount count boundaryTable) :
    CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        boundaryTable
        (compactAdditiveSyntaxTaskListRowValues
          tokenTable width tokenCount boundaryTable count) := by
  intro index hindex
  have hcount : index < count := by simpa using hindex
  rcases htriple index hcount with
    ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, hrightEq⟩
  have hleftValue : left =
      compactAdditiveBoundaryCursor tokenCount boundaryTable index :=
    CompactFixedWidthEntry.value_eq_tableValue hleftEntry
  let kind := compactFixedWidthTableValue tokenTable width left
  let binderArity :=
    compactFixedWidthTableValue tokenTable width (left + 1)
  let repeatCount :=
    compactFixedWidthTableValue tokenTable width (left + 2)
  have htaskValue := compactAdditiveSyntaxTaskListRowValues_getI
    tokenTable width tokenCount boundaryTable count index hcount
  have htaskValue' :
      (compactAdditiveSyntaxTaskListRowValues
        tokenTable width tokenCount boundaryTable count).getI index =
        (kind, binderArity, repeatCount) := by
    rw [htaskValue]
    simp [compactAdditiveSyntaxTaskRowValue, hleftValue,
      kind, binderArity, repeatCount]
  have hkindCell : CompactAdditiveTokenCell
      tokenTable width tokenCount left kind (left + 1) := by
    exact ⟨by omega, rfl,
      compactFixedWidthTableValue_entry tokenTable width left⟩
  have hbinderCell : CompactAdditiveTokenCell
      tokenTable width tokenCount (left + 1) binderArity (left + 2) := by
    exact ⟨by omega, rfl,
      compactFixedWidthTableValue_entry tokenTable width (left + 1)⟩
  have hcountCell : CompactAdditiveTokenCell
      tokenTable width tokenCount (left + 2) repeatCount right := by
    exact ⟨by omega, by omega,
      compactFixedWidthTableValue_entry tokenTable width (left + 2)⟩
  refine ⟨left, hleft, right, hright,
    hleftEntry, hrightEntry, ?_⟩
  rw [htaskValue']
  exact ⟨left + 1, left + 2,
    hkindCell, hbinderCell, hcountCell⟩

#print axioms compactAdditiveTripleBoundaryRowsDef_spec
#print axioms compactAdditiveTripleBoundaryRowsDef_sigmaZero
#print axioms compactSyntaxTaskDirectLayoutDef_spec
#print axioms compactSyntaxTaskDirectLayoutDef_sigmaZero
#print axioms CompactAdditiveStructuredListElementRowLayouts.tripleBoundaryRows
#print axioms CompactAdditiveTripleBoundaryRows.realizedTaskRows

end FoundationCompactNumericListedDirectSyntaxTaskRowRealization
