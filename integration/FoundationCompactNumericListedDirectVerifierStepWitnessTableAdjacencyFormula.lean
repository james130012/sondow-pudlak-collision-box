import integration.FoundationCompactNumericListedDirectVerifierStepWitnessTableFormula
import integration.FoundationCompactNumericListedDirectCrossTableSliceEquality

/-!
# Bounded adjacency formula for complete verifier-step witness rows

Only ten columns are read: the table triple and next-state endpoints of row
`i`, followed by the table triple and current-state endpoints of row `i+1`.
The decoded slices are then joined by exact cross-table bit equality.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierStepWitnessTableAdjacencyFormula

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectVerifierStepWitnessTable

def CompactNumericVerifierStepWitnessTableAdjacentRow
    (tableWidth table valueBound rowIndex : Nat) : Prop :=
  ∃ sourceTable, sourceTable ≤ valueBound ∧
  ∃ sourceWidth, sourceWidth ≤ valueBound ∧
  ∃ sourceTokenCount, sourceTokenCount ≤ valueBound ∧
  ∃ sourceStart, sourceStart ≤ valueBound ∧
  ∃ sourceFinish, sourceFinish ≤ valueBound ∧
  ∃ targetTable, targetTable ≤ valueBound ∧
  ∃ targetWidth, targetWidth ≤ valueBound ∧
  ∃ targetTokenCount, targetTokenCount ≤ valueBound ∧
  ∃ targetStart, targetStart ≤ valueBound ∧
  ∃ targetFinish, targetFinish ≤ valueBound ∧
    CompactFixedWidthEntry table tableWidth
        (rowIndex * compactNumericVerifierStepWitnessColumnCount + 0)
        sourceTable ∧
      CompactFixedWidthEntry table tableWidth
        (rowIndex * compactNumericVerifierStepWitnessColumnCount + 1)
        sourceWidth ∧
      CompactFixedWidthEntry table tableWidth
        (rowIndex * compactNumericVerifierStepWitnessColumnCount + 2)
        sourceTokenCount ∧
      CompactFixedWidthEntry table tableWidth
        (rowIndex * compactNumericVerifierStepWitnessColumnCount + 24)
        sourceStart ∧
      CompactFixedWidthEntry table tableWidth
        (rowIndex * compactNumericVerifierStepWitnessColumnCount + 25)
        sourceFinish ∧
      CompactFixedWidthEntry table tableWidth
        ((rowIndex + 1) * compactNumericVerifierStepWitnessColumnCount + 0)
        targetTable ∧
      CompactFixedWidthEntry table tableWidth
        ((rowIndex + 1) * compactNumericVerifierStepWitnessColumnCount + 1)
        targetWidth ∧
      CompactFixedWidthEntry table tableWidth
        ((rowIndex + 1) * compactNumericVerifierStepWitnessColumnCount + 2)
        targetTokenCount ∧
      CompactFixedWidthEntry table tableWidth
        ((rowIndex + 1) * compactNumericVerifierStepWitnessColumnCount + 3)
        targetStart ∧
      CompactFixedWidthEntry table tableWidth
        ((rowIndex + 1) * compactNumericVerifierStepWitnessColumnCount + 4)
        targetFinish ∧
      CompactFixedWidthCrossTableSlicesEq
        sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
        targetTable targetWidth targetTokenCount targetStart targetFinish

def compactNumericVerifierStepWitnessTableAdjacentRowDef :
    𝚺₀.Semisentence 4 := .mkSigma
  “tableWidth table valueBound rowIndex.
    ∃ sourceTable <⁺ valueBound,
    ∃ sourceWidth <⁺ valueBound,
    ∃ sourceTokenCount <⁺ valueBound,
    ∃ sourceStart <⁺ valueBound,
    ∃ sourceFinish <⁺ valueBound,
    ∃ targetTable <⁺ valueBound,
    ∃ targetWidth <⁺ valueBound,
    ∃ targetTokenCount <⁺ valueBound,
    ∃ targetStart <⁺ valueBound,
    ∃ targetFinish <⁺ valueBound,
      !(compactFixedWidthEntryDef)
        table tableWidth (rowIndex * 429 + 0) sourceTable ∧
      !(compactFixedWidthEntryDef)
        table tableWidth (rowIndex * 429 + 1) sourceWidth ∧
      !(compactFixedWidthEntryDef)
        table tableWidth (rowIndex * 429 + 2) sourceTokenCount ∧
      !(compactFixedWidthEntryDef)
        table tableWidth (rowIndex * 429 + 24) sourceStart ∧
      !(compactFixedWidthEntryDef)
        table tableWidth (rowIndex * 429 + 25) sourceFinish ∧
      !(compactFixedWidthEntryDef)
        table tableWidth ((rowIndex + 1) * 429 + 0) targetTable ∧
      !(compactFixedWidthEntryDef)
        table tableWidth ((rowIndex + 1) * 429 + 1) targetWidth ∧
      !(compactFixedWidthEntryDef)
        table tableWidth ((rowIndex + 1) * 429 + 2) targetTokenCount ∧
      !(compactFixedWidthEntryDef)
        table tableWidth ((rowIndex + 1) * 429 + 3) targetStart ∧
      !(compactFixedWidthEntryDef)
        table tableWidth ((rowIndex + 1) * 429 + 4) targetFinish ∧
      !(compactFixedWidthCrossTableSlicesEqDef)
        sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
        targetTable targetWidth targetTokenCount targetStart targetFinish”

private theorem compactFixedWidthCrossTableSlicesEqDef_eval_env
    (env : Fin 10 -> Nat) :
    compactFixedWidthCrossTableSlicesEqDef.val.Evalb env ↔
      CompactFixedWidthCrossTableSlicesEq
        (env 0) (env 1) (env 2) (env 3) (env 4)
        (env 5) (env 6) (env 7) (env 8) (env 9) := by
  let sourceTable := env 0
  let sourceWidth := env 1
  let sourceTokenCount := env 2
  let sourceStart := env 3
  let sourceFinish := env 4
  let targetTable := env 5
  let targetWidth := env 6
  let targetTokenCount := env 7
  let targetStart := env 8
  let targetFinish := env 9
  have henv : env =
      ![sourceTable, sourceWidth, sourceTokenCount, sourceStart, sourceFinish,
        targetTable, targetWidth, targetTokenCount, targetStart,
        targetFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  rw [henv]
  exact compactFixedWidthCrossTableSlicesEqDef_spec
    sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
    targetTable targetWidth targetTokenCount targetStart targetFinish

@[simp] theorem compactNumericVerifierStepWitnessTableAdjacentRowDef_spec
    (tableWidth table valueBound rowIndex : Nat) :
    compactNumericVerifierStepWitnessTableAdjacentRowDef.val.Evalb
        ![tableWidth, table, valueBound, rowIndex] ↔
      CompactNumericVerifierStepWitnessTableAdjacentRow
        tableWidth table valueBound rowIndex := by
  simp [compactNumericVerifierStepWitnessTableAdjacentRowDef,
    CompactNumericVerifierStepWitnessTableAdjacentRow,
    compactNumericVerifierStepWitnessColumnCount,
    compactFixedWidthCrossTableSlicesEqDef_eval_env]
  rfl

theorem compactNumericVerifierStepWitnessTableAdjacentRowDef_sigmaZero :
    Hierarchy Polarity.sigma 0
      compactNumericVerifierStepWitnessTableAdjacentRowDef.val := by
  simp [compactNumericVerifierStepWitnessTableAdjacentRowDef]

def CompactNumericVerifierStepWitnessTableRowsAdjacent
    (tableWidth table rowCount valueBound : Nat) : Prop :=
  ∀ rowIndex < rowCount,
    rowIndex + 1 < rowCount →
      CompactNumericVerifierStepWitnessTableAdjacentRow
        tableWidth table valueBound rowIndex

def compactNumericVerifierStepWitnessTableRowsAdjacentDef :
    𝚺₀.Semisentence 4 := .mkSigma
  “tableWidth table rowCount valueBound.
    ∀ rowIndex < rowCount,
      rowIndex + 1 < rowCount →
        !(compactNumericVerifierStepWitnessTableAdjacentRowDef)
          tableWidth table valueBound rowIndex”

@[simp] theorem compactNumericVerifierStepWitnessTableRowsAdjacentDef_spec
    (tableWidth table rowCount valueBound : Nat) :
    compactNumericVerifierStepWitnessTableRowsAdjacentDef.val.Evalb
        ![tableWidth, table, rowCount, valueBound] ↔
      CompactNumericVerifierStepWitnessTableRowsAdjacent
        tableWidth table rowCount valueBound := by
  simp [compactNumericVerifierStepWitnessTableRowsAdjacentDef,
    CompactNumericVerifierStepWitnessTableRowsAdjacent]

theorem compactNumericVerifierStepWitnessTableRowsAdjacentDef_sigmaZero :
    Hierarchy Polarity.sigma 0
      compactNumericVerifierStepWitnessTableRowsAdjacentDef.val := by
  simp [compactNumericVerifierStepWitnessTableRowsAdjacentDef]

#print axioms compactNumericVerifierStepWitnessTableAdjacentRowDef_spec
#print axioms compactNumericVerifierStepWitnessTableAdjacentRowDef_sigmaZero
#print axioms compactNumericVerifierStepWitnessTableRowsAdjacentDef_spec
#print axioms compactNumericVerifierStepWitnessTableRowsAdjacentDef_sigmaZero

end FoundationCompactNumericListedDirectVerifierStepWitnessTableAdjacencyFormula
