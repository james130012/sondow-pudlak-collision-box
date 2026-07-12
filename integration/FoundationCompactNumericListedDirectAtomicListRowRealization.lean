import integration.FoundationCompactNumericListedDirectNatListBoundaryRigidity

/-!
# Realization of direct atomic list rows

The fixed-width boundary table deterministically supplies every row cursor.
Natural rows read the token value at that cursor; Boolean rows additionally
check that this value is exactly zero or one.  The resulting typed lists carry
the same row layouts, so later arithmetic graphs no longer need typed lists as
inputs.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectAtomicListRowRealization

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity

theorem compactFixedWidthTableValue_size_le
    (table width index : Nat) :
    Nat.size (compactFixedWidthTableValue table width index) ≤ width := by
  rw [Nat.size_le]
  simpa [compactFixedWidthTableValue] using
    natOfBitsList_lt_two_pow_length
      ((List.range width).map fun bitIndex =>
        table.testBit (index * width + bitIndex))

theorem compactFixedWidthTableValue_entry
    (table width index : Nat) :
    CompactFixedWidthEntry table width index
      (compactFixedWidthTableValue table width index) := by
  refine ⟨compactFixedWidthTableValue_size_le table width index, ?_⟩
  intro bitIndex hbitIndex
  exact (compactFixedWidthTableValue_testBit
    table width index bitIndex hbitIndex).symm

def CompactAdditiveBoolListRowsWellFormed
    (tokenTable width tokenCount boundaryTable count : Nat) : Prop :=
  ∀ index < count,
    ∃ left, left ≤ tokenCount ∧
    ∃ right, right ≤ tokenCount ∧
      CompactFixedWidthEntry boundaryTable tokenCount index left ∧
      CompactFixedWidthEntry boundaryTable tokenCount (index + 1) right ∧
      (CompactAdditiveBoolSlice
          tokenTable width tokenCount left 0 right ∨
        CompactAdditiveBoolSlice
          tokenTable width tokenCount left 1 right)

def compactAdditiveBoolListRowsWellFormedDef :
    𝚺₀.Semisentence 5 := .mkSigma
  “tokenTable width tokenCount boundaryTable count.
    ∀ index < count,
      ∃ left <⁺ tokenCount,
        ∃ right <⁺ tokenCount,
          !(compactFixedWidthEntryDef)
            boundaryTable tokenCount index left ∧
          !(compactFixedWidthEntryDef)
            boundaryTable tokenCount (index + 1) right ∧
          (!(compactAdditiveBoolSliceDef)
              tokenTable width tokenCount left 0 right ∨
            !(compactAdditiveBoolSliceDef)
              tokenTable width tokenCount left 1 right)”

@[simp] theorem compactAdditiveBoolListRowsWellFormedDef_spec
    (tokenTable width tokenCount boundaryTable count : Nat) :
    compactAdditiveBoolListRowsWellFormedDef.val.Evalb
        ![tokenTable, width, tokenCount, boundaryTable, count] ↔
      CompactAdditiveBoolListRowsWellFormed
        tokenTable width tokenCount boundaryTable count := by
  have hslice (right left index value : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![right, left, index, tokenTable, width,
                tokenCount, boundaryTable, count]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 8), #4, #5, #1,
              (value : Semiterm ℒₒᵣ Empty 8), #0])
          Empty.elim)
        compactAdditiveBoolSliceDef.val ↔
      CompactAdditiveBoolSlice
        tokenTable width tokenCount left value right := by
    have henv :
        (Semiterm.val
            ![right, left, index, tokenTable, width,
              tokenCount, boundaryTable, count]
            Empty.elim ∘
          ![(#3 : Semiterm ℒₒᵣ Empty 8), #4, #5, #1,
            (value : Semiterm ℒₒᵣ Empty 8), #0]) =
          ![tokenTable, width, tokenCount, left, value, right] := by
      funext coordinate
      fin_cases coordinate <;> simp
    rw [henv]
    simp
  simp [compactAdditiveBoolListRowsWellFormedDef,
    CompactAdditiveBoolListRowsWellFormed, hslice]

theorem compactAdditiveBoolListRowsWellFormedDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveBoolListRowsWellFormedDef.val := by
  simp [compactAdditiveBoolListRowsWellFormedDef]

def compactAdditiveUnitBoundaryRowsDef : 𝚺₀.Semisentence 3 := .mkSigma
  “tokenCount count boundaryTable.
    ∀ index < count,
      ∃ left <⁺ tokenCount,
        ∃ right <⁺ tokenCount,
          !(compactFixedWidthEntryDef)
            boundaryTable tokenCount index left ∧
          !(compactFixedWidthEntryDef)
            boundaryTable tokenCount (index + 1) right ∧
          right = left + 1”

@[simp] theorem compactAdditiveUnitBoundaryRowsDef_spec
    (tokenCount count boundaryTable : Nat) :
    compactAdditiveUnitBoundaryRowsDef.val.Evalb
        ![tokenCount, count, boundaryTable] ↔
      CompactAdditiveUnitBoundaryRows
        tokenCount count boundaryTable := by
  simp [compactAdditiveUnitBoundaryRowsDef,
    CompactAdditiveUnitBoundaryRows]

theorem compactAdditiveUnitBoundaryRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveUnitBoundaryRowsDef.val := by
  simp [compactAdditiveUnitBoundaryRowsDef]

def compactAdditiveBoundaryCursor
    (tokenCount boundaryTable index : Nat) : Nat :=
  compactFixedWidthTableValue boundaryTable tokenCount index

def compactAdditiveRowTokenValue
    (tokenTable width tokenCount boundaryTable index : Nat) : Nat :=
  compactFixedWidthTableValue tokenTable width
    (compactAdditiveBoundaryCursor tokenCount boundaryTable index)

def compactAdditiveBoolListRowValues
  (tokenTable width tokenCount boundaryTable count : Nat) : List Bool :=
  (List.range count).map fun index =>
    decide (compactAdditiveRowTokenValue
      tokenTable width tokenCount boundaryTable index = 1)

def compactAdditiveNatListRowValues
    (tokenTable width tokenCount boundaryTable count : Nat) : List Nat :=
  (List.range count).map fun index =>
    compactAdditiveRowTokenValue
      tokenTable width tokenCount boundaryTable index

@[simp] theorem compactAdditiveBoolListRowValues_length
    (tokenTable width tokenCount boundaryTable count : Nat) :
    (compactAdditiveBoolListRowValues
      tokenTable width tokenCount boundaryTable count).length = count := by
  simp [compactAdditiveBoolListRowValues]

@[simp] theorem compactAdditiveNatListRowValues_length
    (tokenTable width tokenCount boundaryTable count : Nat) :
    (compactAdditiveNatListRowValues
      tokenTable width tokenCount boundaryTable count).length = count := by
  simp [compactAdditiveNatListRowValues]

theorem compactAdditiveBoolListRowValues_getI
    (tokenTable width tokenCount boundaryTable count index : Nat)
    (hindex : index < count) :
    (compactAdditiveBoolListRowValues
      tokenTable width tokenCount boundaryTable count).getI index =
        decide (compactAdditiveRowTokenValue
          tokenTable width tokenCount boundaryTable index = 1) := by
  rw [List.getI_eq_getElem _ (by simpa using hindex)]
  simp [compactAdditiveBoolListRowValues]

theorem compactAdditiveNatListRowValues_getI
    (tokenTable width tokenCount boundaryTable count index : Nat)
    (hindex : index < count) :
    (compactAdditiveNatListRowValues
      tokenTable width tokenCount boundaryTable count).getI index =
        compactAdditiveRowTokenValue
          tokenTable width tokenCount boundaryTable index := by
  rw [List.getI_eq_getElem _ (by simpa using hindex)]
  simp [compactAdditiveNatListRowValues]

theorem CompactAdditiveStructuredListElementRowLayouts.boolRowsWellFormed
    {tokenTable width tokenCount boundaryTable : Nat}
    {values : List Bool}
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveBoolValueDirectLayout tokenTable width tokenCount
        boundaryTable values) :
    CompactAdditiveBoolListRowsWellFormed
      tokenTable width tokenCount boundaryTable values.length := by
  intro index hindex
  rcases hrows index hindex with
    ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, hlayout⟩
  refine ⟨left, hleft, right, hright,
    hleftEntry, hrightEntry, ?_⟩
  cases hvalue : values.getI index with
  | false =>
      left
      simpa [CompactAdditiveBoolValueDirectLayout,
        compactAdditiveBoolTag, hvalue] using hlayout
  | true =>
      right
      simpa [CompactAdditiveBoolValueDirectLayout,
        compactAdditiveBoolTag, hvalue] using hlayout

theorem CompactAdditiveBoolListRowsWellFormed.realizedRows
    {tokenTable width tokenCount boundaryTable count : Nat}
    (hwellFormed : CompactAdditiveBoolListRowsWellFormed
      tokenTable width tokenCount boundaryTable count) :
    CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveBoolValueDirectLayout tokenTable width tokenCount
        boundaryTable
        (compactAdditiveBoolListRowValues
          tokenTable width tokenCount boundaryTable count) := by
  intro index hindex
  have hcount : index < count := by simpa using hindex
  rcases hwellFormed index hcount with
    ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, hzero | hone⟩
  · have hleftValue : left =
        compactAdditiveBoundaryCursor tokenCount boundaryTable index := by
      exact CompactFixedWidthEntry.value_eq_tableValue hleftEntry
    have htokenValue : compactAdditiveRowTokenValue
        tokenTable width tokenCount boundaryTable index = 0 := by
      rw [compactAdditiveRowTokenValue, ← hleftValue]
      exact (CompactFixedWidthEntry.value_eq_tableValue hzero.1.2.2).symm
    refine ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, ?_⟩
    have hvalue := compactAdditiveBoolListRowValues_getI
      tokenTable width tokenCount boundaryTable count index hcount
    have hvalueFalse :
        (compactAdditiveBoolListRowValues
          tokenTable width tokenCount boundaryTable count).getI index =
          false := by
      rw [hvalue, htokenValue]
      decide
    rw [hvalueFalse]
    simpa [CompactAdditiveBoolValueDirectLayout,
      compactAdditiveBoolTag] using hzero
  · have hleftValue : left =
        compactAdditiveBoundaryCursor tokenCount boundaryTable index := by
      exact CompactFixedWidthEntry.value_eq_tableValue hleftEntry
    have htokenValue : compactAdditiveRowTokenValue
        tokenTable width tokenCount boundaryTable index = 1 := by
      rw [compactAdditiveRowTokenValue, ← hleftValue]
      exact (CompactFixedWidthEntry.value_eq_tableValue hone.1.2.2).symm
    refine ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, ?_⟩
    have hvalue := compactAdditiveBoolListRowValues_getI
      tokenTable width tokenCount boundaryTable count index hcount
    have hvalueTrue :
        (compactAdditiveBoolListRowValues
          tokenTable width tokenCount boundaryTable count).getI index =
          true := by
      rw [hvalue, htokenValue]
      decide
    rw [hvalueTrue]
    simpa [CompactAdditiveBoolValueDirectLayout,
      compactAdditiveBoolTag] using hone

theorem CompactAdditiveBoolListRowsWellFormed.unitBoundaryRows
    {tokenTable width tokenCount boundaryTable count : Nat}
    (hwellFormed : CompactAdditiveBoolListRowsWellFormed
      tokenTable width tokenCount boundaryTable count) :
    CompactAdditiveUnitBoundaryRows tokenCount count boundaryTable := by
  intro index hindex
  rcases hwellFormed index hindex with
    ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, hzero | hone⟩
  · exact ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, hzero.1.2.1⟩
  · exact ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, hone.1.2.1⟩

theorem CompactAdditiveUnitBoundaryRows.realizedNatRows
    {tokenTable width tokenCount boundaryTable count : Nat}
    (hunit : CompactAdditiveUnitBoundaryRows
      tokenCount count boundaryTable) :
    CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        boundaryTable
        (compactAdditiveNatListRowValues
          tokenTable width tokenCount boundaryTable count) := by
  intro index hindex
  have hcount : index < count := by simpa using hindex
  rcases hunit index hcount with
    ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, hnext⟩
  have hleftValue : left =
      compactAdditiveBoundaryCursor tokenCount boundaryTable index :=
    CompactFixedWidthEntry.value_eq_tableValue hleftEntry
  have hleftLt : left < tokenCount := by omega
  have hvalue := compactAdditiveNatListRowValues_getI
    tokenTable width tokenCount boundaryTable count index hcount
  refine ⟨left, hleft, right, hright,
    hleftEntry, hrightEntry, ?_⟩
  rw [hvalue, compactAdditiveRowTokenValue, ← hleftValue]
  exact ⟨hleftLt, hnext,
    compactFixedWidthTableValue_entry tokenTable width left⟩

#print axioms compactFixedWidthTableValue_entry
#print axioms compactAdditiveBoolListRowsWellFormedDef_spec
#print axioms compactAdditiveBoolListRowsWellFormedDef_sigmaZero
#print axioms compactAdditiveUnitBoundaryRowsDef_spec
#print axioms compactAdditiveUnitBoundaryRowsDef_sigmaZero
#print axioms CompactAdditiveStructuredListElementRowLayouts.boolRowsWellFormed
#print axioms CompactAdditiveBoolListRowsWellFormed.realizedRows
#print axioms CompactAdditiveBoolListRowsWellFormed.unitBoundaryRows
#print axioms CompactAdditiveUnitBoundaryRows.realizedNatRows

end FoundationCompactNumericListedDirectAtomicListRowRealization
