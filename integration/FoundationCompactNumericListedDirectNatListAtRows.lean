import integration.FoundationCompactNumericListedDirectAtomicRowEquality

/-!
# Direct bounded lookup of one natural-number-list row

The formula reads the two boundary cursors around a selected atomic row and
checks that the intervening token carries an explicit natural-number value.
Under the real row layout this is exactly indexed lookup in the typed list.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListAtRows

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAtomicListLayouts

def CompactAdditiveNatListAtRows
    (tokenTable width tokenCount boundaryTable count index value : Nat) :
    Prop :=
  index < count ∧
    ∃ left, left ≤ tokenCount ∧
    ∃ right, right ≤ tokenCount ∧
      CompactFixedWidthEntry boundaryTable tokenCount index left ∧
      CompactFixedWidthEntry boundaryTable tokenCount (index + 1) right ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount left value right

def compactAdditiveNatListAtRowsDef : 𝚺₀.Semisentence 7 := .mkSigma
  “tokenTable width tokenCount boundaryTable count index value.
    index < count ∧
    ∃ left <⁺ tokenCount,
      ∃ right <⁺ tokenCount,
        !(compactFixedWidthEntryDef)
          boundaryTable tokenCount index left ∧
        !(compactFixedWidthEntryDef)
          boundaryTable tokenCount (index + 1) right ∧
        !(compactAdditiveTokenCellDef)
          tokenTable width tokenCount left value right”

def compactAdditiveNatListAtRowsEnvironment
    (tokenTable width tokenCount boundaryTable count index value : Nat) :
    Fin 7 → Nat :=
  ![tokenTable, width, tokenCount, boundaryTable, count, index, value]

@[simp] theorem compactAdditiveNatListAtRowsDef_spec
    (tokenTable width tokenCount boundaryTable count index value : Nat) :
    compactAdditiveNatListAtRowsDef.val.Evalb
        (compactAdditiveNatListAtRowsEnvironment
          tokenTable width tokenCount boundaryTable count index value) ↔
      CompactAdditiveNatListAtRows
        tokenTable width tokenCount boundaryTable count index value := by
  have hcell (right left : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![right, left,
                tokenTable, width, tokenCount, boundaryTable,
                count, index, value]
              Empty.elim ∘
            ![(#2 : Semiterm ℒₒᵣ Empty 9), #3, #4, #1, #8, #0])
          Empty.elim) compactAdditiveTokenCellDef.val ↔
        CompactAdditiveTokenCell
          tokenTable width tokenCount left value right := by
    have henv :
        (Semiterm.val
            ![right, left,
              tokenTable, width, tokenCount, boundaryTable,
              count, index, value]
            Empty.elim ∘
          ![(#2 : Semiterm ℒₒᵣ Empty 9), #3, #4, #1, #8, #0]) =
        ![tokenTable, width, tokenCount, left, value, right] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    simp
  simp [compactAdditiveNatListAtRowsDef,
    CompactAdditiveNatListAtRows,
    compactAdditiveNatListAtRowsEnvironment, hcell]

theorem compactAdditiveNatListAtRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveNatListAtRowsDef.val := by
  simp [compactAdditiveNatListAtRowsDef]

theorem compactAdditiveNatListAtRows_iff_getI
    {tokenTable width tokenCount boundaryTable : Nat}
    {values : List Nat}
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        boundaryTable values)
    (index value : Nat) :
    CompactAdditiveNatListAtRows
        tokenTable width tokenCount boundaryTable values.length index value ↔
      index < values.length ∧ values.getI index = value := by
  constructor
  · rintro ⟨hindex, left, _hleft, right, _hright,
      hleftEntry, hrightEntry, hcell⟩
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
    have hvalue : value = values.getI index :=
      (CompactAdditiveTokenCell.value_eq_tableValue hcell).trans
        (CompactAdditiveTokenCell.value_eq_tableValue hrowLayout).symm
    exact ⟨hindex, hvalue.symm⟩
  · rintro ⟨hindex, hvalue⟩
    rcases hrows index hindex with
      ⟨left, hleft, right, hright,
        hleftEntry, hrightEntry, hlayout⟩
    rw [hvalue] at hlayout
    exact ⟨hindex, left, hleft, right, hright,
      hleftEntry, hrightEntry, hlayout⟩

#print axioms compactAdditiveNatListAtRowsDef_spec
#print axioms compactAdditiveNatListAtRowsDef_sigmaZero
#print axioms compactAdditiveNatListAtRows_iff_getI

end FoundationCompactNumericListedDirectNatListAtRows
