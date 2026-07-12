import integration.FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormula
import integration.FoundationCompactNumericListedDirectAtomicListRowRealization

/-!
# Semantic bridge for the bounded stream-step witness-table formula

The fixed-width table determines one canonical 32-coordinate row.  This file
identifies the handwritten bounded formula with the existing table graph, so
the arithmetic formula cannot choose values different from the table bits.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormulaBridge

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectTokenStreamInverse.CompactFixedWidthEntry
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectBinaryNatStreamStepRows
open FoundationCompactNumericListedDirectBinaryNatStreamStepFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStateFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStepStateFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTable
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormula

def compactBinaryNatStreamStepWitnessTableCanonicalRow
    (tableWidth table rowIndex : Nat) : CompactBinaryNatStreamStepStateRow :=
  compactBinaryNatStreamStepStateRowOfValues
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 0)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 1)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 2)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 3)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 4)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 5)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 6)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 7)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 8)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 9)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 10)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 11)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 12)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 13)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 14)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 15)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 16)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 17)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 18)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 19)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 20)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 21)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 22)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 23)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 24)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 25)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 26)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 27)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 28)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 29)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 30)
    (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 31)

theorem compactBinaryNatStreamStepWitnessTableColumnValue_entry
    (tableWidth table rowIndex column : Nat) :
    CompactFixedWidthEntry table tableWidth
      (rowIndex * 32 + column)
      (compactBinaryNatStreamStepWitnessTableColumnValue
        tableWidth table rowIndex column) := by
  simpa [compactBinaryNatStreamStepWitnessTableColumnValue,
    compactBinaryNatStreamStepWitnessColumnCount] using
    compactFixedWidthTableValue_entry table tableWidth
      (rowIndex * compactBinaryNatStreamStepWitnessColumnCount + column)

theorem compactBinaryNatStreamStepWitnessTableColumnValue_le_pow
    (tableWidth table rowIndex column : Nat) :
    compactBinaryNatStreamStepWitnessTableColumnValue
        tableWidth table rowIndex column ≤ 2 ^ tableWidth := by
  apply Nat.le_of_lt
  apply Nat.size_le.mp
  simpa [compactBinaryNatStreamStepWitnessTableColumnValue] using
    compactFixedWidthTableValue_size_le table tableWidth
      (rowIndex * compactBinaryNatStreamStepWitnessColumnCount + column)

theorem compactBinaryNatStreamStepWitnessTableCanonicalRow_environment
    (tokenTable width tokenCount tableWidth table rowIndex : Nat) :
    compactBinaryNatStreamStepWitnessTableFormulaEnvironment
        tokenTable width tokenCount tableWidth table rowIndex =
      compactBinaryNatStreamStepStateRowFormulaEnvironment
        tokenTable width tokenCount
        (compactBinaryNatStreamStepWitnessTableCanonicalRow
          tableWidth table rowIndex) := by
  funext coordinate
  fin_cases coordinate <;> rfl

theorem compactBinaryNatStreamStepWitnessTableCanonicalRow_core_iff
    (tokenTable width tokenCount tableWidth table rowIndex : Nat) :
    CompactBinaryNatStreamStepWitnessTableRowCore
        tokenTable width tokenCount tableWidth table rowIndex
        (compactBinaryNatStreamStepWitnessTableCanonicalRow
          tableWidth table rowIndex) ↔
      compactBinaryNatStreamStepStateGraphDef.val.Evalb
        (compactBinaryNatStreamStepWitnessTableFormulaEnvironment
          tokenTable width tokenCount tableWidth table rowIndex) := by
  rw [compactBinaryNatStreamStepWitnessTableCanonicalRow_environment]
  rw [compactBinaryNatStreamStepStateRowFormulaEnvironment_spec]
  constructor
  · intro hcore
    exact hcore.2.2.2.2
  · intro hstate
    refine ⟨?_, ?_, ?_, ?_, hstate⟩
    · change CompactBinaryNatStreamStepWitnessTableCurrentEntries
        tableWidth table rowIndex
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 0)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 1)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 2)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 3)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 4)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 5)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 6)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 7)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 8)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 9)
      exact ⟨(by simpa using
          (compactBinaryNatStreamStepWitnessTableColumnValue_entry
            tableWidth table rowIndex 0)),
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 1,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 2,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 3,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 4,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 5,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 6,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 7,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 8,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 9⟩
    · change CompactBinaryNatStreamStepWitnessTableNextEntries
        tableWidth table rowIndex
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 10)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 11)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 12)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 13)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 14)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 15)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 16)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 17)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 18)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 19)
      exact ⟨compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 10,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 11,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 12,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 13,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 14,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 15,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 16,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 17,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 18,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 19⟩
    · change CompactBinaryNatStreamStepWitnessTableWitnessHeadEntries
        tableWidth table rowIndex
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 20)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 21)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 22)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 23)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 24)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 25)
      exact ⟨compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 20,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 21,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 22,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 23,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 24,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 25⟩
    · change CompactBinaryNatStreamStepWitnessTableWitnessTailEntries
        tableWidth table rowIndex
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 26)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 27)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 28)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 29)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 30)
        (compactBinaryNatStreamStepWitnessTableColumnValue tableWidth table rowIndex 31)
      exact ⟨compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 26,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 27,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 28,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 29,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 30,
        compactBinaryNatStreamStepWitnessTableColumnValue_entry tableWidth table rowIndex 31⟩

theorem CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue
    {tableWidth table rowIndex column value : Nat}
    (hentry : CompactFixedWidthEntry table tableWidth
      (rowIndex * 32 + column) value) :
    value = compactBinaryNatStreamStepWitnessTableColumnValue
      tableWidth table rowIndex column := by
  simpa [compactBinaryNatStreamStepWitnessTableColumnValue,
    compactBinaryNatStreamStepWitnessColumnCount] using
      value_eq_tableValue hentry

theorem compactBinaryNatStreamStepWitnessTableCanonicalRow_currentBounded
    (tokenTable width tokenCount tableWidth table rowIndex : Nat)
    (hcore : CompactBinaryNatStreamStepWitnessTableRowCore
      tokenTable width tokenCount tableWidth table rowIndex
      (compactBinaryNatStreamStepWitnessTableCanonicalRow
        tableWidth table rowIndex)) :
    CompactBinaryNatStreamStepWitnessTableCurrentBounded
      tokenTable width tokenCount tableWidth table (2 ^ tableWidth) rowIndex := by
  let value := fun column =>
    compactBinaryNatStreamStepWitnessTableColumnValue
      tableWidth table rowIndex column
  have hvalue (column : Nat) : value column ≤ 2 ^ tableWidth :=
    compactBinaryNatStreamStepWitnessTableColumnValue_le_pow
      tableWidth table rowIndex column
  unfold CompactBinaryNatStreamStepWitnessTableCurrentBounded
    CompactBinaryNatStreamStepWitnessTableNextBounded
    CompactBinaryNatStreamStepWitnessTableHeadBounded
    CompactBinaryNatStreamStepWitnessTableTailBounded
  refine ⟨value 0, hvalue 0,
    value 1, hvalue 1,
    value 2, hvalue 2,
    value 3, hvalue 3,
    value 4, hvalue 4,
    value 5, hvalue 5,
    value 6, hvalue 6,
    value 7, hvalue 7,
    value 8, hvalue 8,
    value 9, hvalue 9,
    value 10, hvalue 10,
    value 11, hvalue 11,
    value 12, hvalue 12,
    value 13, hvalue 13,
    value 14, hvalue 14,
    value 15, hvalue 15,
    value 16, hvalue 16,
    value 17, hvalue 17,
    value 18, hvalue 18,
    value 19, hvalue 19,
    value 20, hvalue 20,
    value 21, hvalue 21,
    value 22, hvalue 22,
    value 23, hvalue 23,
    value 24, hvalue 24,
    value 25, hvalue 25,
    value 26, hvalue 26,
    value 27, hvalue 27,
    value 28, hvalue 28,
    value 29, hvalue 29,
    value 30, hvalue 30,
    value 31, hvalue 31, ?_⟩
  simpa [value, compactBinaryNatStreamStepWitnessTableCanonicalRow] using hcore

theorem compactBinaryNatStreamStepWitnessTableCurrentBounded_canonicalRow_core
    (tokenTable width tokenCount tableWidth table rowIndex : Nat)
    (hbounded : CompactBinaryNatStreamStepWitnessTableCurrentBounded
      tokenTable width tokenCount tableWidth table (2 ^ tableWidth) rowIndex) :
    CompactBinaryNatStreamStepWitnessTableRowCore
      tokenTable width tokenCount tableWidth table rowIndex
      (compactBinaryNatStreamStepWitnessTableCanonicalRow
        tableWidth table rowIndex) := by
  rcases hbounded with
    ⟨currentStart, _hcurrentStart,
      currentFinish, _hcurrentFinish,
      currentBitsFinish, _hcurrentBitsFinish,
      currentDecodedFinish, _hcurrentDecodedFinish,
      currentBitsBoundary, _hcurrentBitsBoundary,
      currentBitsCount, _hcurrentBitsCount,
      currentDecodedBoundary, _hcurrentDecodedBoundary,
      currentDecodedCount, _hcurrentDecodedCount,
      currentBitsBoundarySize, _hcurrentBitsBoundarySize,
      currentDecodedBoundarySize, _hcurrentDecodedBoundarySize,
      hnext⟩
  rcases hnext with
    ⟨nextStart, _hnextStart,
      nextFinish, _hnextFinish,
      nextBitsFinish, _hnextBitsFinish,
      nextDecodedFinish, _hnextDecodedFinish,
      nextBitsBoundary, _hnextBitsBoundary,
      nextBitsCount, _hnextBitsCount,
      nextDecodedBoundary, _hnextDecodedBoundary,
      nextDecodedCount, _hnextDecodedCount,
      nextBitsBoundarySize, _hnextBitsBoundarySize,
      nextDecodedBoundarySize, _hnextDecodedBoundarySize,
      hhead⟩
  rcases hhead with
    ⟨branch, _hbranch, payload, _hpayload,
      digitCount, _hdigitCount, token, _htoken,
      consumed, _hconsumed, sourceOutputStart, _hsourceOutputStart,
      htail⟩
  rcases htail with
    ⟨sourceOutputBoundary, _hsourceOutputBoundary,
      sourceOutputBoundarySize, _hsourceOutputBoundarySize,
      targetOutputStart, _htargetOutputStart,
      targetOutputBoundary, _htargetOutputBoundary,
      targetOutputBoundarySize, _htargetOutputBoundarySize,
      outputCount, _houtputCount, hcore⟩
  have hcoreOriginal := hcore
  rcases hcore with
    ⟨hcurrentEntries, hnextEntries, hheadEntries, htailEntries, _hstate⟩
  rcases hcurrentEntries with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  rcases hnextEntries with
    ⟨h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩
  rcases hheadEntries with ⟨h20, h21, h22, h23, h24, h25⟩
  rcases htailEntries with ⟨h26, h27, h28, h29, h30, h31⟩
  let value := fun column =>
    compactBinaryNatStreamStepWitnessTableColumnValue
      tableWidth table rowIndex column
  have heq0 : currentStart = value 0 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h0)
  have heq1 : currentFinish = value 1 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h1)
  have heq2 : currentBitsFinish = value 2 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h2)
  have heq3 : currentDecodedFinish = value 3 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h3)
  have heq4 : currentBitsBoundary = value 4 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h4)
  have heq5 : currentBitsCount = value 5 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h5)
  have heq6 : currentDecodedBoundary = value 6 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h6)
  have heq7 : currentDecodedCount = value 7 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h7)
  have heq8 : currentBitsBoundarySize = value 8 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h8)
  have heq9 : currentDecodedBoundarySize = value 9 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h9)
  have heq10 : nextStart = value 10 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h10)
  have heq11 : nextFinish = value 11 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h11)
  have heq12 : nextBitsFinish = value 12 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h12)
  have heq13 : nextDecodedFinish = value 13 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h13)
  have heq14 : nextBitsBoundary = value 14 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h14)
  have heq15 : nextBitsCount = value 15 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h15)
  have heq16 : nextDecodedBoundary = value 16 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h16)
  have heq17 : nextDecodedCount = value 17 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h17)
  have heq18 : nextBitsBoundarySize = value 18 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h18)
  have heq19 : nextDecodedBoundarySize = value 19 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h19)
  have heq20 : branch = value 20 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h20)
  have heq21 : payload = value 21 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h21)
  have heq22 : digitCount = value 22 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h22)
  have heq23 : token = value 23 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h23)
  have heq24 : consumed = value 24 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h24)
  have heq25 : sourceOutputStart = value 25 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h25)
  have heq26 : sourceOutputBoundary = value 26 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h26)
  have heq27 : sourceOutputBoundarySize = value 27 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h27)
  have heq28 : targetOutputStart = value 28 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h28)
  have heq29 : targetOutputBoundary = value 29 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h29)
  have heq30 : targetOutputBoundarySize = value 30 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h30)
  have heq31 : outputCount = value 31 := by
    simpa [compactBinaryNatStreamStepStateRowOfValues, value] using
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h31)
  simpa [compactBinaryNatStreamStepWitnessTableCanonicalRow,
    compactBinaryNatStreamStepStateRowOfValues, value,
    heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9,
    heq10, heq11, heq12, heq13, heq14, heq15, heq16, heq17, heq18, heq19,
    heq20, heq21, heq22, heq23, heq24, heq25,
    heq26, heq27, heq28, heq29, heq30, heq31] using hcoreOriginal

theorem compactBinaryNatStreamStepWitnessTableCurrentBounded_iff_canonicalRow_core
    (tokenTable width tokenCount tableWidth table rowIndex : Nat) :
    CompactBinaryNatStreamStepWitnessTableCurrentBounded
        tokenTable width tokenCount tableWidth table (2 ^ tableWidth) rowIndex ↔
      CompactBinaryNatStreamStepWitnessTableRowCore
        tokenTable width tokenCount tableWidth table rowIndex
        (compactBinaryNatStreamStepWitnessTableCanonicalRow
          tableWidth table rowIndex) :=
  ⟨compactBinaryNatStreamStepWitnessTableCurrentBounded_canonicalRow_core
      tokenTable width tokenCount tableWidth table rowIndex,
    compactBinaryNatStreamStepWitnessTableCanonicalRow_currentBounded
      tokenTable width tokenCount tableWidth table rowIndex⟩

theorem compactBinaryNatStreamStepWitnessTableBoundedGraph_iff_tableGraph
    (tokenTable width tokenCount tableWidth table rowCount valueBound : Nat) :
    CompactBinaryNatStreamStepWitnessTableBoundedGraph
        tokenTable width tokenCount tableWidth table rowCount valueBound ↔
      valueBound = 2 ^ tableWidth ∧
      CompactBinaryNatStreamStepWitnessTableGraph
        tokenTable width tokenCount tableWidth table rowCount := by
  constructor
  · rintro ⟨hvalueBound, hrows⟩
    refine ⟨hvalueBound, ?_⟩
    intro rowIndex hrowIndex
    have hbounded := hrows rowIndex hrowIndex
    rw [hvalueBound] at hbounded
    exact (compactBinaryNatStreamStepWitnessTableCanonicalRow_core_iff
      tokenTable width tokenCount tableWidth table rowIndex).mp
        ((compactBinaryNatStreamStepWitnessTableCurrentBounded_iff_canonicalRow_core
          tokenTable width tokenCount tableWidth table rowIndex).mp hbounded)
  · rintro ⟨hvalueBound, hgraph⟩
    refine ⟨hvalueBound, ?_⟩
    intro rowIndex hrowIndex
    rw [hvalueBound]
    apply (compactBinaryNatStreamStepWitnessTableCurrentBounded_iff_canonicalRow_core
      tokenTable width tokenCount tableWidth table rowIndex).mpr
    apply (compactBinaryNatStreamStepWitnessTableCanonicalRow_core_iff
      tokenTable width tokenCount tableWidth table rowIndex).mpr
    exact hgraph rowIndex hrowIndex

theorem compactBinaryNatStreamStepWitnessTableBoundedGraph_pow_iff_tableGraph
    (tokenTable width tokenCount tableWidth table rowCount : Nat) :
    CompactBinaryNatStreamStepWitnessTableBoundedGraph
        tokenTable width tokenCount tableWidth table rowCount (2 ^ tableWidth) ↔
      CompactBinaryNatStreamStepWitnessTableGraph
        tokenTable width tokenCount tableWidth table rowCount := by
  simpa using
    compactBinaryNatStreamStepWitnessTableBoundedGraph_iff_tableGraph
      tokenTable width tokenCount tableWidth table rowCount (2 ^ tableWidth)

theorem compactBinaryNatStreamStepWitnessTableBoundedGraphDef_eval_iff_tableGraph
    (tokenTable width tokenCount tableWidth table rowCount : Nat) :
    compactBinaryNatStreamStepWitnessTableBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount,
          tableWidth, table, rowCount, 2 ^ tableWidth] ↔
      CompactBinaryNatStreamStepWitnessTableGraph
        tokenTable width tokenCount tableWidth table rowCount := by
  rw [compactBinaryNatStreamStepWitnessTableBoundedGraphDef_spec]
  exact compactBinaryNatStreamStepWitnessTableBoundedGraph_pow_iff_tableGraph
    tokenTable width tokenCount tableWidth table rowCount

#print axioms compactBinaryNatStreamStepWitnessTableCanonicalRow_core_iff
#print axioms compactBinaryNatStreamStepWitnessTableCurrentBounded_iff_canonicalRow_core
#print axioms compactBinaryNatStreamStepWitnessTableBoundedGraph_iff_tableGraph
#print axioms compactBinaryNatStreamStepWitnessTableBoundedGraphDef_eval_iff_tableGraph

end FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormulaBridge
