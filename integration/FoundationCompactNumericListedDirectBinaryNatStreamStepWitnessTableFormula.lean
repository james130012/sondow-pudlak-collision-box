import integration.FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTable

/-!
# Bounded arithmetic formula for a complete stream-step witness table

One explicit power-of-two bound controls all 32 values read from a row.  Each
value is tied to its fixed-width table entry before the 35-variable step formula
is evaluated.  Hence the complete row-universal relation remains Delta-zero.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormula

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectBinaryNatStreamStepRows
open FoundationCompactNumericListedDirectBinaryNatStreamStepFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStateFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStepRealization
open FoundationCompactNumericListedDirectBinaryNatStreamStepStateFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTable

def compactBinaryNatStreamStepStateRowOfValues
    (currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      nextBitsBoundarySize nextDecodedBoundarySize
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) : CompactBinaryNatStreamStepStateRow :=
  { currentCoordinates :=
      { start := currentStart
        finish := currentFinish
        bitsFinish := currentBitsFinish
        decodedFinish := currentDecodedFinish
        bitsBoundary := currentBitsBoundary
        bitsCount := currentBitsCount
        decodedBoundary := currentDecodedBoundary
        decodedCount := currentDecodedCount }
    currentSize :=
      { bitsBoundarySize := currentBitsBoundarySize
        decodedBoundarySize := currentDecodedBoundarySize }
    nextCoordinates :=
      { start := nextStart
        finish := nextFinish
        bitsFinish := nextBitsFinish
        decodedFinish := nextDecodedFinish
        bitsBoundary := nextBitsBoundary
        bitsCount := nextBitsCount
        decodedBoundary := nextDecodedBoundary
        decodedCount := nextDecodedCount }
    nextSize :=
      { bitsBoundarySize := nextBitsBoundarySize
        decodedBoundarySize := nextDecodedBoundarySize }
    witness :=
      { branch := branch
        payload := payload
        digitCount := digitCount
        token := token
        consumed := consumed
        sourceOutputStart := sourceOutputStart
        sourceOutputBoundary := sourceOutputBoundary
        sourceOutputBoundarySize := sourceOutputBoundarySize
        targetOutputStart := targetOutputStart
        targetOutputBoundary := targetOutputBoundary
        targetOutputBoundarySize := targetOutputBoundarySize
        outputCount := outputCount } }

def CompactBinaryNatStreamStepWitnessTableCurrentEntries
    (tableWidth table rowIndex : Nat)
    (currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize : Nat) : Prop :=
  CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 0)
      currentStart ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 1)
      currentFinish ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 2)
      currentBitsFinish ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 3)
      currentDecodedFinish ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 4)
      currentBitsBoundary ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 5)
      currentBitsCount ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 6)
      currentDecodedBoundary ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 7)
      currentDecodedCount ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 8)
      currentBitsBoundarySize ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 9)
      currentDecodedBoundarySize

def CompactBinaryNatStreamStepWitnessTableNextEntries
    (tableWidth table rowIndex : Nat)
    (nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      nextBitsBoundarySize nextDecodedBoundarySize : Nat) : Prop :=
  CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 10)
      nextStart ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 11)
      nextFinish ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 12)
      nextBitsFinish ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 13)
      nextDecodedFinish ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 14)
      nextBitsBoundary ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 15)
      nextBitsCount ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 16)
      nextDecodedBoundary ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 17)
      nextDecodedCount ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 18)
      nextBitsBoundarySize ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 19)
      nextDecodedBoundarySize

def CompactBinaryNatStreamStepWitnessTableWitnessHeadEntries
    (tableWidth table rowIndex : Nat)
    (branch payload digitCount token consumed sourceOutputStart : Nat) : Prop :=
  CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 20)
      branch ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 21)
      payload ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 22)
      digitCount ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 23)
      token ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 24)
      consumed ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 25)
      sourceOutputStart

def CompactBinaryNatStreamStepWitnessTableWitnessTailEntries
    (tableWidth table rowIndex : Nat)
    (sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) : Prop :=
  CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 26)
      sourceOutputBoundary ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 27)
      sourceOutputBoundarySize ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 28)
      targetOutputStart ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 29)
      targetOutputBoundary ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 30)
      targetOutputBoundarySize ∧
    CompactFixedWidthEntry table tableWidth (rowIndex * 32 + 31)
      outputCount

def CompactBinaryNatStreamStepWitnessTableRowCore
    (tokenTable width tokenCount tableWidth table rowIndex : Nat)
    (row : CompactBinaryNatStreamStepStateRow) : Prop :=
  CompactBinaryNatStreamStepWitnessTableCurrentEntries
      tableWidth table rowIndex
      row.currentCoordinates.start row.currentCoordinates.finish
      row.currentCoordinates.bitsFinish row.currentCoordinates.decodedFinish
      row.currentCoordinates.bitsBoundary row.currentCoordinates.bitsCount
      row.currentCoordinates.decodedBoundary row.currentCoordinates.decodedCount
      row.currentSize.bitsBoundarySize row.currentSize.decodedBoundarySize ∧
    CompactBinaryNatStreamStepWitnessTableNextEntries
      tableWidth table rowIndex
      row.nextCoordinates.start row.nextCoordinates.finish
      row.nextCoordinates.bitsFinish row.nextCoordinates.decodedFinish
      row.nextCoordinates.bitsBoundary row.nextCoordinates.bitsCount
      row.nextCoordinates.decodedBoundary row.nextCoordinates.decodedCount
      row.nextSize.bitsBoundarySize row.nextSize.decodedBoundarySize ∧
    CompactBinaryNatStreamStepWitnessTableWitnessHeadEntries
      tableWidth table rowIndex
      row.witness.branch row.witness.payload row.witness.digitCount
      row.witness.token row.witness.consumed row.witness.sourceOutputStart ∧
    CompactBinaryNatStreamStepWitnessTableWitnessTailEntries
      tableWidth table rowIndex
      row.witness.sourceOutputBoundary row.witness.sourceOutputBoundarySize
      row.witness.targetOutputStart row.witness.targetOutputBoundary
      row.witness.targetOutputBoundarySize row.witness.outputCount ∧
    CompactBinaryNatStreamStepStateGraph tokenTable width tokenCount
      row.currentCoordinates row.nextCoordinates
      row.currentSize row.nextSize row.witness

def CompactBinaryNatStreamStepWitnessTableBoundedRow
    (tokenTable width tokenCount tableWidth table valueBound rowIndex : Nat)
    (row : CompactBinaryNatStreamStepStateRow) : Prop :=
  row.currentCoordinates.start ≤ valueBound ∧
  row.currentCoordinates.finish ≤ valueBound ∧
  row.currentCoordinates.bitsFinish ≤ valueBound ∧
  row.currentCoordinates.decodedFinish ≤ valueBound ∧
  row.currentCoordinates.bitsBoundary ≤ valueBound ∧
  row.currentCoordinates.bitsCount ≤ valueBound ∧
  row.currentCoordinates.decodedBoundary ≤ valueBound ∧
  row.currentCoordinates.decodedCount ≤ valueBound ∧
  row.currentSize.bitsBoundarySize ≤ valueBound ∧
  row.currentSize.decodedBoundarySize ≤ valueBound ∧
  row.nextCoordinates.start ≤ valueBound ∧
  row.nextCoordinates.finish ≤ valueBound ∧
  row.nextCoordinates.bitsFinish ≤ valueBound ∧
  row.nextCoordinates.decodedFinish ≤ valueBound ∧
  row.nextCoordinates.bitsBoundary ≤ valueBound ∧
  row.nextCoordinates.bitsCount ≤ valueBound ∧
  row.nextCoordinates.decodedBoundary ≤ valueBound ∧
  row.nextCoordinates.decodedCount ≤ valueBound ∧
  row.nextSize.bitsBoundarySize ≤ valueBound ∧
  row.nextSize.decodedBoundarySize ≤ valueBound ∧
  row.witness.branch ≤ valueBound ∧
  row.witness.payload ≤ valueBound ∧
  row.witness.digitCount ≤ valueBound ∧
  row.witness.token ≤ valueBound ∧
  row.witness.consumed ≤ valueBound ∧
  row.witness.sourceOutputStart ≤ valueBound ∧
  row.witness.sourceOutputBoundary ≤ valueBound ∧
  row.witness.sourceOutputBoundarySize ≤ valueBound ∧
  row.witness.targetOutputStart ≤ valueBound ∧
  row.witness.targetOutputBoundary ≤ valueBound ∧
  row.witness.targetOutputBoundarySize ≤ valueBound ∧
  row.witness.outputCount ≤ valueBound ∧
  CompactBinaryNatStreamStepWitnessTableRowCore
    tokenTable width tokenCount tableWidth table rowIndex row

def CompactBinaryNatStreamStepWitnessTableTailBounded
    (tokenTable width tokenCount tableWidth table valueBound rowIndex
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      nextBitsBoundarySize nextDecodedBoundarySize
      branch payload digitCount token consumed sourceOutputStart : Nat) : Prop :=
  ∃ sourceOutputBoundary, sourceOutputBoundary ≤ valueBound ∧
  ∃ sourceOutputBoundarySize, sourceOutputBoundarySize ≤ valueBound ∧
  ∃ targetOutputStart, targetOutputStart ≤ valueBound ∧
  ∃ targetOutputBoundary, targetOutputBoundary ≤ valueBound ∧
  ∃ targetOutputBoundarySize, targetOutputBoundarySize ≤ valueBound ∧
  ∃ outputCount, outputCount ≤ valueBound ∧
    CompactBinaryNatStreamStepWitnessTableRowCore
      tokenTable width tokenCount tableWidth table rowIndex
      (compactBinaryNatStreamStepStateRowOfValues
        currentStart currentFinish currentBitsFinish currentDecodedFinish
        currentBitsBoundary currentBitsCount
        currentDecodedBoundary currentDecodedCount
        currentBitsBoundarySize currentDecodedBoundarySize
        nextStart nextFinish nextBitsFinish nextDecodedFinish
        nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
        nextBitsBoundarySize nextDecodedBoundarySize
        branch payload digitCount token consumed
        sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
        targetOutputStart targetOutputBoundary targetOutputBoundarySize
        outputCount)

def CompactBinaryNatStreamStepWitnessTableHeadBounded
    (tokenTable width tokenCount tableWidth table valueBound rowIndex
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      nextBitsBoundarySize nextDecodedBoundarySize : Nat) : Prop :=
  ∃ branch, branch ≤ valueBound ∧
  ∃ payload, payload ≤ valueBound ∧
  ∃ digitCount, digitCount ≤ valueBound ∧
  ∃ token, token ≤ valueBound ∧
  ∃ consumed, consumed ≤ valueBound ∧
  ∃ sourceOutputStart, sourceOutputStart ≤ valueBound ∧
    CompactBinaryNatStreamStepWitnessTableTailBounded
      tokenTable width tokenCount tableWidth table valueBound rowIndex
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      nextBitsBoundarySize nextDecodedBoundarySize
      branch payload digitCount token consumed sourceOutputStart

def CompactBinaryNatStreamStepWitnessTableNextBounded
    (tokenTable width tokenCount tableWidth table valueBound rowIndex
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize : Nat) : Prop :=
  ∃ nextStart, nextStart ≤ valueBound ∧
  ∃ nextFinish, nextFinish ≤ valueBound ∧
  ∃ nextBitsFinish, nextBitsFinish ≤ valueBound ∧
  ∃ nextDecodedFinish, nextDecodedFinish ≤ valueBound ∧
  ∃ nextBitsBoundary, nextBitsBoundary ≤ valueBound ∧
  ∃ nextBitsCount, nextBitsCount ≤ valueBound ∧
  ∃ nextDecodedBoundary, nextDecodedBoundary ≤ valueBound ∧
  ∃ nextDecodedCount, nextDecodedCount ≤ valueBound ∧
  ∃ nextBitsBoundarySize, nextBitsBoundarySize ≤ valueBound ∧
  ∃ nextDecodedBoundarySize, nextDecodedBoundarySize ≤ valueBound ∧
    CompactBinaryNatStreamStepWitnessTableHeadBounded
      tokenTable width tokenCount tableWidth table valueBound rowIndex
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      nextBitsBoundarySize nextDecodedBoundarySize

def CompactBinaryNatStreamStepWitnessTableCurrentBounded
    (tokenTable width tokenCount tableWidth table valueBound rowIndex : Nat) :
    Prop :=
  ∃ currentStart, currentStart ≤ valueBound ∧
  ∃ currentFinish, currentFinish ≤ valueBound ∧
  ∃ currentBitsFinish, currentBitsFinish ≤ valueBound ∧
  ∃ currentDecodedFinish, currentDecodedFinish ≤ valueBound ∧
  ∃ currentBitsBoundary, currentBitsBoundary ≤ valueBound ∧
  ∃ currentBitsCount, currentBitsCount ≤ valueBound ∧
  ∃ currentDecodedBoundary, currentDecodedBoundary ≤ valueBound ∧
  ∃ currentDecodedCount, currentDecodedCount ≤ valueBound ∧
  ∃ currentBitsBoundarySize, currentBitsBoundarySize ≤ valueBound ∧
  ∃ currentDecodedBoundarySize, currentDecodedBoundarySize ≤ valueBound ∧
    CompactBinaryNatStreamStepWitnessTableNextBounded
      tokenTable width tokenCount tableWidth table valueBound rowIndex
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize

def CompactBinaryNatStreamStepWitnessTableBoundedGraph
    (tokenTable width tokenCount tableWidth table rowCount valueBound : Nat) :
    Prop :=
  valueBound = 2 ^ tableWidth ∧
  ∀ rowIndex < rowCount,
    CompactBinaryNatStreamStepWitnessTableCurrentBounded
      tokenTable width tokenCount tableWidth table valueBound rowIndex

def compactBinaryNatStreamStepWitnessTableCurrentEntriesDef :
    𝚺₀.Semisentence 13 := .mkSigma
  “tableWidth table rowIndex
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize.
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 0) currentStart ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 1) currentFinish ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 2) currentBitsFinish ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 3) currentDecodedFinish ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 4) currentBitsBoundary ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 5) currentBitsCount ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 6) currentDecodedBoundary ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 7) currentDecodedCount ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 8) currentBitsBoundarySize ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 9) currentDecodedBoundarySize”

def compactBinaryNatStreamStepWitnessTableNextEntriesDef :
    𝚺₀.Semisentence 13 := .mkSigma
  “tableWidth table rowIndex
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      nextBitsBoundarySize nextDecodedBoundarySize.
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 10) nextStart ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 11) nextFinish ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 12) nextBitsFinish ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 13) nextDecodedFinish ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 14) nextBitsBoundary ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 15) nextBitsCount ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 16) nextDecodedBoundary ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 17) nextDecodedCount ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 18) nextBitsBoundarySize ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 19) nextDecodedBoundarySize”

def compactBinaryNatStreamStepWitnessTableWitnessHeadEntriesDef :
    𝚺₀.Semisentence 9 := .mkSigma
  “tableWidth table rowIndex
      branch payload digitCount token consumed sourceOutputStart.
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 20) branch ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 21) payload ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 22) digitCount ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 23) token ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 24) consumed ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 25) sourceOutputStart”

def compactBinaryNatStreamStepWitnessTableWitnessTailEntriesDef :
    𝚺₀.Semisentence 9 := .mkSigma
  “tableWidth table rowIndex
      sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount.
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 26) sourceOutputBoundary ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 27) sourceOutputBoundarySize ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 28) targetOutputStart ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 29) targetOutputBoundary ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 30) targetOutputBoundarySize ∧
    !(compactFixedWidthEntryDef)
      table tableWidth (rowIndex * 32 + 31) outputCount”

def compactBinaryNatStreamStepWitnessTableRowCoreDef :
    𝚺₀.Semisentence 38 := .mkSigma
  “tokenTable width tokenCount tableWidth table rowIndex
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      nextBitsBoundarySize nextDecodedBoundarySize
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount.
    !(compactBinaryNatStreamStepWitnessTableCurrentEntriesDef)
      tableWidth table rowIndex
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize ∧
    !(compactBinaryNatStreamStepWitnessTableNextEntriesDef)
      tableWidth table rowIndex
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      nextBitsBoundarySize nextDecodedBoundarySize ∧
    !(compactBinaryNatStreamStepWitnessTableWitnessHeadEntriesDef)
      tableWidth table rowIndex
      branch payload digitCount token consumed sourceOutputStart ∧
    !(compactBinaryNatStreamStepWitnessTableWitnessTailEntriesDef)
      tableWidth table rowIndex
      sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount ∧
    !(compactBinaryNatStreamStepStateGraphDef)
      tokenTable width tokenCount
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      nextBitsBoundarySize nextDecodedBoundarySize
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount”

private def rowCoreFormulaEnvironment
    (tokenTable width tokenCount tableWidth table rowIndex
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      nextBitsBoundarySize nextDecodedBoundarySize
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) (coordinate : Fin 38) : Nat :=
  match coordinate.val with
  | 0 => tokenTable
  | 1 => width
  | 2 => tokenCount
  | 3 => tableWidth
  | 4 => table
  | 5 => rowIndex
  | 6 => currentStart
  | 7 => currentFinish
  | 8 => currentBitsFinish
  | 9 => currentDecodedFinish
  | 10 => currentBitsBoundary
  | 11 => currentBitsCount
  | 12 => currentDecodedBoundary
  | 13 => currentDecodedCount
  | 14 => currentBitsBoundarySize
  | 15 => currentDecodedBoundarySize
  | 16 => nextStart
  | 17 => nextFinish
  | 18 => nextBitsFinish
  | 19 => nextDecodedFinish
  | 20 => nextBitsBoundary
  | 21 => nextBitsCount
  | 22 => nextDecodedBoundary
  | 23 => nextDecodedCount
  | 24 => nextBitsBoundarySize
  | 25 => nextDecodedBoundarySize
  | 26 => branch
  | 27 => payload
  | 28 => digitCount
  | 29 => token
  | 30 => consumed
  | 31 => sourceOutputStart
  | 32 => sourceOutputBoundary
  | 33 => sourceOutputBoundarySize
  | 34 => targetOutputStart
  | 35 => targetOutputBoundary
  | 36 => targetOutputBoundarySize
  | 37 => outputCount
  | _ => 0

private theorem compactFixedWidthEntryDef_eval_env
    (env : Fin 4 → Nat) :
    compactFixedWidthEntryDef.val.Evalb env ↔
      CompactFixedWidthEntry (env 0) (env 1) (env 2) (env 3) := by
  let table := env 0
  let width := env 1
  let index := env 2
  let value := env 3
  have henv : env = ![table, width, index, value] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  rw [henv]
  exact compactFixedWidthEntryDef_spec table width index value

@[simp] theorem compactBinaryNatStreamStepWitnessTableCurrentEntriesDef_spec
    (tableWidth table rowIndex
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize : Nat) :
    compactBinaryNatStreamStepWitnessTableCurrentEntriesDef.val.Evalb
        ![tableWidth, table, rowIndex,
          currentStart, currentFinish, currentBitsFinish, currentDecodedFinish,
          currentBitsBoundary, currentBitsCount,
          currentDecodedBoundary, currentDecodedCount,
          currentBitsBoundarySize, currentDecodedBoundarySize] ↔
      CompactBinaryNatStreamStepWitnessTableCurrentEntries
        tableWidth table rowIndex
        currentStart currentFinish currentBitsFinish currentDecodedFinish
        currentBitsBoundary currentBitsCount
        currentDecodedBoundary currentDecodedCount
        currentBitsBoundarySize currentDecodedBoundarySize := by
  simp [compactBinaryNatStreamStepWitnessTableCurrentEntriesDef,
    CompactBinaryNatStreamStepWitnessTableCurrentEntries,
    compactFixedWidthEntryDef_eval_env]
  tauto

@[simp] theorem compactBinaryNatStreamStepWitnessTableNextEntriesDef_spec
    (tableWidth table rowIndex
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      nextBitsBoundarySize nextDecodedBoundarySize : Nat) :
    compactBinaryNatStreamStepWitnessTableNextEntriesDef.val.Evalb
        ![tableWidth, table, rowIndex,
          nextStart, nextFinish, nextBitsFinish, nextDecodedFinish,
          nextBitsBoundary, nextBitsCount, nextDecodedBoundary, nextDecodedCount,
          nextBitsBoundarySize, nextDecodedBoundarySize] ↔
      CompactBinaryNatStreamStepWitnessTableNextEntries
        tableWidth table rowIndex
        nextStart nextFinish nextBitsFinish nextDecodedFinish
        nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
        nextBitsBoundarySize nextDecodedBoundarySize := by
  simp [compactBinaryNatStreamStepWitnessTableNextEntriesDef,
    CompactBinaryNatStreamStepWitnessTableNextEntries,
    compactFixedWidthEntryDef_eval_env]

@[simp] theorem compactBinaryNatStreamStepWitnessTableWitnessHeadEntriesDef_spec
    (tableWidth table rowIndex branch payload digitCount token consumed
      sourceOutputStart : Nat) :
    compactBinaryNatStreamStepWitnessTableWitnessHeadEntriesDef.val.Evalb
        ![tableWidth, table, rowIndex,
          branch, payload, digitCount, token, consumed, sourceOutputStart] ↔
      CompactBinaryNatStreamStepWitnessTableWitnessHeadEntries
        tableWidth table rowIndex
        branch payload digitCount token consumed sourceOutputStart := by
  simp [compactBinaryNatStreamStepWitnessTableWitnessHeadEntriesDef,
    CompactBinaryNatStreamStepWitnessTableWitnessHeadEntries,
    compactFixedWidthEntryDef_eval_env]

@[simp] theorem compactBinaryNatStreamStepWitnessTableWitnessTailEntriesDef_spec
    (tableWidth table rowIndex sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) :
    compactBinaryNatStreamStepWitnessTableWitnessTailEntriesDef.val.Evalb
        ![tableWidth, table, rowIndex,
          sourceOutputBoundary, sourceOutputBoundarySize,
          targetOutputStart, targetOutputBoundary, targetOutputBoundarySize,
          outputCount] ↔
      CompactBinaryNatStreamStepWitnessTableWitnessTailEntries
        tableWidth table rowIndex
        sourceOutputBoundary sourceOutputBoundarySize
        targetOutputStart targetOutputBoundary targetOutputBoundarySize
        outputCount := by
  simp [compactBinaryNatStreamStepWitnessTableWitnessTailEntriesDef,
    CompactBinaryNatStreamStepWitnessTableWitnessTailEntries,
    compactFixedWidthEntryDef_eval_env]

private def rowCoreGraphOfEnvironment (env : Fin 38 → Nat) : Prop :=
  CompactBinaryNatStreamStepWitnessTableRowCore
    (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)
    (compactBinaryNatStreamStepStateRowOfValues
      (env 6) (env 7) (env 8) (env 9)
      (env 10) (env 11) (env 12) (env 13)
      (env 14) (env 15)
      (env 16) (env 17) (env 18) (env 19)
      (env 20) (env 21) (env 22) (env 23)
      (env 24) (env 25)
      (env 26) (env 27) (env 28) (env 29) (env 30)
      (env 31) (env 32) (env 33)
      (env 34) (env 35) (env 36) (env 37))

private theorem compactBinaryNatStreamStepWitnessTableRowCoreDef_eval_env
    (env : Fin 38 → Nat) :
    compactBinaryNatStreamStepWitnessTableRowCoreDef.val.Evalb env ↔
      rowCoreGraphOfEnvironment env := by
  have hcurrentEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#3 : Semiterm ℒₒᵣ Empty 38), #4, #5,
          #6, #7, #8, #9, #10, #11, #12, #13, #14, #15]) =
        ![env 3, env 4, env 5,
          env 6, env 7, env 8, env 9, env 10, env 11, env 12, env 13,
          env 14, env 15] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hnextEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#3 : Semiterm ℒₒᵣ Empty 38), #4, #5,
          #16, #17, #18, #19, #20, #21, #22, #23, #24, #25]) =
        ![env 3, env 4, env 5,
          env 16, env 17, env 18, env 19, env 20, env 21, env 22, env 23,
          env 24, env 25] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hwitnessHeadEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#3 : Semiterm ℒₒᵣ Empty 38), #4, #5,
          #26, #27, #28, #29, #30, #31]) =
        ![env 3, env 4, env 5,
          env 26, env 27, env 28, env 29, env 30, env 31] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hwitnessTailEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#3 : Semiterm ℒₒᵣ Empty 38), #4, #5,
          #32, #33, #34, #35, #36, #37]) =
        ![env 3, env 4, env 5,
          env 32, env 33, env 34, env 35, env 36, env 37] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hstepEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
          #6, #7, #8, #9, #10, #11, #12, #13, #14, #15,
          #16, #17, #18, #19, #20, #21, #22, #23, #24, #25,
          #26, #27, #28, #29, #30, #31, #32, #33, #34,
          #35, #36, #37]) =
        ![env 0, env 1, env 2,
          env 6, env 7, env 8, env 9, env 10, env 11, env 12, env 13,
          env 14, env 15,
          env 16, env 17, env 18, env 19,
          env 20, env 21, env 22, env 23,
          env 24, env 25,
          env 26, env 27, env 28, env 29, env 30,
          env 31, env 32, env 33,
          env 34, env 35, env 36, env 37] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcurrentEval :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 38), #4, #5,
              #6, #7, #8, #9, #10, #11, #12, #13, #14, #15])
          Empty.elim)
          compactBinaryNatStreamStepWitnessTableCurrentEntriesDef.val ↔
        CompactBinaryNatStreamStepWitnessTableCurrentEntries
          (env 3) (env 4) (env 5)
          (env 6) (env 7) (env 8) (env 9)
          (env 10) (env 11) (env 12) (env 13)
          (env 14) (env 15) := by
    rw [hcurrentEnv]
    exact compactBinaryNatStreamStepWitnessTableCurrentEntriesDef_spec
      (env 3) (env 4) (env 5)
      (env 6) (env 7) (env 8) (env 9)
      (env 10) (env 11) (env 12) (env 13)
      (env 14) (env 15)
  have hnextEval :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 38), #4, #5,
              #16, #17, #18, #19, #20, #21, #22, #23, #24, #25])
          Empty.elim)
          compactBinaryNatStreamStepWitnessTableNextEntriesDef.val ↔
        CompactBinaryNatStreamStepWitnessTableNextEntries
          (env 3) (env 4) (env 5)
          (env 16) (env 17) (env 18) (env 19)
          (env 20) (env 21) (env 22) (env 23)
          (env 24) (env 25) := by
    rw [hnextEnv]
    exact compactBinaryNatStreamStepWitnessTableNextEntriesDef_spec
      (env 3) (env 4) (env 5)
      (env 16) (env 17) (env 18) (env 19)
      (env 20) (env 21) (env 22) (env 23)
      (env 24) (env 25)
  have hwitnessHeadEval :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 38), #4, #5,
              #26, #27, #28, #29, #30, #31]) Empty.elim)
          compactBinaryNatStreamStepWitnessTableWitnessHeadEntriesDef.val ↔
        CompactBinaryNatStreamStepWitnessTableWitnessHeadEntries
          (env 3) (env 4) (env 5)
          (env 26) (env 27) (env 28) (env 29) (env 30) (env 31) := by
    rw [hwitnessHeadEnv]
    exact compactBinaryNatStreamStepWitnessTableWitnessHeadEntriesDef_spec
      (env 3) (env 4) (env 5)
      (env 26) (env 27) (env 28) (env 29) (env 30) (env 31)
  have hwitnessTailEval :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 38), #4, #5,
              #32, #33, #34, #35, #36, #37]) Empty.elim)
          compactBinaryNatStreamStepWitnessTableWitnessTailEntriesDef.val ↔
        CompactBinaryNatStreamStepWitnessTableWitnessTailEntries
          (env 3) (env 4) (env 5)
          (env 32) (env 33) (env 34) (env 35) (env 36) (env 37) := by
    rw [hwitnessTailEnv]
    exact compactBinaryNatStreamStepWitnessTableWitnessTailEntriesDef_spec
      (env 3) (env 4) (env 5)
      (env 32) (env 33) (env 34) (env 35) (env 36) (env 37)
  have hstepSpec :
      compactBinaryNatStreamStepStateGraphDef.val.Evalb
          ![env 0, env 1, env 2,
            env 6, env 7, env 8, env 9, env 10, env 11, env 12, env 13,
            env 14, env 15,
            env 16, env 17, env 18, env 19,
            env 20, env 21, env 22, env 23,
            env 24, env 25,
            env 26, env 27, env 28, env 29, env 30,
            env 31, env 32, env 33,
            env 34, env 35, env 36, env 37] ↔
        CompactBinaryNatStreamStepStateGraph (env 0) (env 1) (env 2)
          (compactBinaryNatStreamStateRowCoordinatesOf
            (env 6) (env 7) (env 8) (env 9)
            (env 10) (env 11) (env 12) (env 13))
          (compactBinaryNatStreamStateRowCoordinatesOf
            (env 16) (env 17) (env 18) (env 19)
            (env 20) (env 21) (env 22) (env 23))
          { bitsBoundarySize := env 14
            decodedBoundarySize := env 15 }
          { bitsBoundarySize := env 24
            decodedBoundarySize := env 25 }
          (compactBinaryNatStreamStepWitnessCoordinatesOf
            (env 26) (env 27) (env 28) (env 29) (env 30)
            (env 31) (env 32) (env 33)
            (env 34) (env 35) (env 36) (env 37)) := by
    simpa only [compactBinaryNatStreamStepStateFormulaEnvironment] using
      compactBinaryNatStreamStepStateGraphDef_spec
        (env 0) (env 1) (env 2)
        (env 6) (env 7) (env 8) (env 9)
        (env 10) (env 11) (env 12) (env 13)
        (env 14) (env 15)
        (env 16) (env 17) (env 18) (env 19)
        (env 20) (env 21) (env 22) (env 23)
        (env 24) (env 25)
        (env 26) (env 27) (env 28) (env 29) (env 30)
        (env 31) (env 32) (env 33)
        (env 34) (env 35) (env 36) (env 37)
  have hstepEval :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
              #6, #7, #8, #9, #10, #11, #12, #13, #14, #15,
              #16, #17, #18, #19, #20, #21, #22, #23, #24, #25,
              #26, #27, #28, #29, #30, #31, #32, #33, #34,
              #35, #36, #37]) Empty.elim)
          compactBinaryNatStreamStepStateGraphDef.val ↔
        CompactBinaryNatStreamStepStateGraph (env 0) (env 1) (env 2)
          (compactBinaryNatStreamStateRowCoordinatesOf
            (env 6) (env 7) (env 8) (env 9)
            (env 10) (env 11) (env 12) (env 13))
          (compactBinaryNatStreamStateRowCoordinatesOf
            (env 16) (env 17) (env 18) (env 19)
            (env 20) (env 21) (env 22) (env 23))
          { bitsBoundarySize := env 14
            decodedBoundarySize := env 15 }
          { bitsBoundarySize := env 24
            decodedBoundarySize := env 25 }
          (compactBinaryNatStreamStepWitnessCoordinatesOf
            (env 26) (env 27) (env 28) (env 29) (env 30)
            (env 31) (env 32) (env 33)
            (env 34) (env 35) (env 36) (env 37)) := by
    rw [hstepEnv]
    exact hstepSpec
  simp [compactBinaryNatStreamStepWitnessTableRowCoreDef,
    rowCoreGraphOfEnvironment,
    CompactBinaryNatStreamStepWitnessTableRowCore,
    compactBinaryNatStreamStepStateRowOfValues,
    compactBinaryNatStreamStateRowCoordinatesOf,
    compactBinaryNatStreamStepWitnessCoordinatesOf,
    hcurrentEval, hnextEval, hwitnessHeadEval, hwitnessTailEval,
    hstepEval]

@[simp] theorem compactBinaryNatStreamStepWitnessTableRowCoreDef_spec
    (tokenTable width tokenCount tableWidth table rowIndex
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      nextBitsBoundarySize nextDecodedBoundarySize
      branch payload digitCount token consumed
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) :
    compactBinaryNatStreamStepWitnessTableRowCoreDef.val.Evalb
        (rowCoreFormulaEnvironment
          tokenTable width tokenCount tableWidth table rowIndex
          currentStart currentFinish currentBitsFinish currentDecodedFinish
          currentBitsBoundary currentBitsCount
          currentDecodedBoundary currentDecodedCount
          currentBitsBoundarySize currentDecodedBoundarySize
          nextStart nextFinish nextBitsFinish nextDecodedFinish
          nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
          nextBitsBoundarySize nextDecodedBoundarySize
          branch payload digitCount token consumed
          sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
          targetOutputStart targetOutputBoundary targetOutputBoundarySize
          outputCount) ↔
      CompactBinaryNatStreamStepWitnessTableRowCore
        tokenTable width tokenCount tableWidth table rowIndex
        (compactBinaryNatStreamStepStateRowOfValues
          currentStart currentFinish currentBitsFinish currentDecodedFinish
          currentBitsBoundary currentBitsCount
          currentDecodedBoundary currentDecodedCount
          currentBitsBoundarySize currentDecodedBoundarySize
          nextStart nextFinish nextBitsFinish nextDecodedFinish
          nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
          nextBitsBoundarySize nextDecodedBoundarySize
          branch payload digitCount token consumed
          sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
          targetOutputStart targetOutputBoundary targetOutputBoundarySize
          outputCount) := by
  simpa [rowCoreGraphOfEnvironment, rowCoreFormulaEnvironment] using
    compactBinaryNatStreamStepWitnessTableRowCoreDef_eval_env
      (rowCoreFormulaEnvironment
        tokenTable width tokenCount tableWidth table rowIndex
        currentStart currentFinish currentBitsFinish currentDecodedFinish
        currentBitsBoundary currentBitsCount
        currentDecodedBoundary currentDecodedCount
        currentBitsBoundarySize currentDecodedBoundarySize
        nextStart nextFinish nextBitsFinish nextDecodedFinish
        nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
        nextBitsBoundarySize nextDecodedBoundarySize
        branch payload digitCount token consumed
        sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
        targetOutputStart targetOutputBoundary targetOutputBoundarySize
        outputCount)

def compactBinaryNatStreamStepWitnessTableTailBoundedDef :
    𝚺₀.Semisentence 33 := .mkSigma
  “tokenTable width tokenCount tableWidth table valueBound rowIndex
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      nextBitsBoundarySize nextDecodedBoundarySize
      branch payload digitCount token consumed sourceOutputStart.
    ∃ sourceOutputBoundary <⁺ valueBound,
    ∃ sourceOutputBoundarySize <⁺ valueBound,
    ∃ targetOutputStart <⁺ valueBound,
    ∃ targetOutputBoundary <⁺ valueBound,
    ∃ targetOutputBoundarySize <⁺ valueBound,
    ∃ outputCount <⁺ valueBound,
      !(compactBinaryNatStreamStepWitnessTableRowCoreDef)
        tokenTable width tokenCount tableWidth table rowIndex
        currentStart currentFinish currentBitsFinish currentDecodedFinish
        currentBitsBoundary currentBitsCount
        currentDecodedBoundary currentDecodedCount
        currentBitsBoundarySize currentDecodedBoundarySize
        nextStart nextFinish nextBitsFinish nextDecodedFinish
        nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
        nextBitsBoundarySize nextDecodedBoundarySize
        branch payload digitCount token consumed
        sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
        targetOutputStart targetOutputBoundary targetOutputBoundarySize
        outputCount”

def compactBinaryNatStreamStepWitnessTableHeadBoundedDef :
    𝚺₀.Semisentence 27 := .mkSigma
  “tokenTable width tokenCount tableWidth table valueBound rowIndex
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize
      nextStart nextFinish nextBitsFinish nextDecodedFinish
      nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
      nextBitsBoundarySize nextDecodedBoundarySize.
    ∃ branch <⁺ valueBound,
    ∃ payload <⁺ valueBound,
    ∃ digitCount <⁺ valueBound,
    ∃ token <⁺ valueBound,
    ∃ consumed <⁺ valueBound,
    ∃ sourceOutputStart <⁺ valueBound,
      !(compactBinaryNatStreamStepWitnessTableTailBoundedDef)
        tokenTable width tokenCount tableWidth table valueBound rowIndex
        currentStart currentFinish currentBitsFinish currentDecodedFinish
        currentBitsBoundary currentBitsCount
        currentDecodedBoundary currentDecodedCount
        currentBitsBoundarySize currentDecodedBoundarySize
        nextStart nextFinish nextBitsFinish nextDecodedFinish
        nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
        nextBitsBoundarySize nextDecodedBoundarySize
        branch payload digitCount token consumed sourceOutputStart”

def compactBinaryNatStreamStepWitnessTableNextBoundedDef :
    𝚺₀.Semisentence 17 := .mkSigma
  “tokenTable width tokenCount tableWidth table valueBound rowIndex
      currentStart currentFinish currentBitsFinish currentDecodedFinish
      currentBitsBoundary currentBitsCount
      currentDecodedBoundary currentDecodedCount
      currentBitsBoundarySize currentDecodedBoundarySize.
    ∃ nextStart <⁺ valueBound,
    ∃ nextFinish <⁺ valueBound,
    ∃ nextBitsFinish <⁺ valueBound,
    ∃ nextDecodedFinish <⁺ valueBound,
    ∃ nextBitsBoundary <⁺ valueBound,
    ∃ nextBitsCount <⁺ valueBound,
    ∃ nextDecodedBoundary <⁺ valueBound,
    ∃ nextDecodedCount <⁺ valueBound,
    ∃ nextBitsBoundarySize <⁺ valueBound,
    ∃ nextDecodedBoundarySize <⁺ valueBound,
      !(compactBinaryNatStreamStepWitnessTableHeadBoundedDef)
        tokenTable width tokenCount tableWidth table valueBound rowIndex
        currentStart currentFinish currentBitsFinish currentDecodedFinish
        currentBitsBoundary currentBitsCount
        currentDecodedBoundary currentDecodedCount
        currentBitsBoundarySize currentDecodedBoundarySize
        nextStart nextFinish nextBitsFinish nextDecodedFinish
        nextBitsBoundary nextBitsCount nextDecodedBoundary nextDecodedCount
        nextBitsBoundarySize nextDecodedBoundarySize”

def compactBinaryNatStreamStepWitnessTableCurrentBoundedDef :
    𝚺₀.Semisentence 7 := .mkSigma
  “tokenTable width tokenCount tableWidth table valueBound rowIndex.
    ∃ currentStart <⁺ valueBound,
    ∃ currentFinish <⁺ valueBound,
    ∃ currentBitsFinish <⁺ valueBound,
    ∃ currentDecodedFinish <⁺ valueBound,
    ∃ currentBitsBoundary <⁺ valueBound,
    ∃ currentBitsCount <⁺ valueBound,
    ∃ currentDecodedBoundary <⁺ valueBound,
    ∃ currentDecodedCount <⁺ valueBound,
    ∃ currentBitsBoundarySize <⁺ valueBound,
    ∃ currentDecodedBoundarySize <⁺ valueBound,
      !(compactBinaryNatStreamStepWitnessTableNextBoundedDef)
        tokenTable width tokenCount tableWidth table valueBound rowIndex
        currentStart currentFinish currentBitsFinish currentDecodedFinish
        currentBitsBoundary currentBitsCount
        currentDecodedBoundary currentDecodedCount
        currentBitsBoundarySize currentDecodedBoundarySize”

def compactBinaryNatStreamStepWitnessTableBoundedGraphDef :
    𝚺₀.Semisentence 7 := .mkSigma
  “tokenTable width tokenCount tableWidth table rowCount valueBound.
    !expDef valueBound tableWidth ∧
    ∀ rowIndex < rowCount,
      !(compactBinaryNatStreamStepWitnessTableCurrentBoundedDef)
        tokenTable width tokenCount tableWidth table valueBound rowIndex”

private def tailBoundedGraphOfEnvironment (env : Fin 33 → Nat) : Prop :=
  CompactBinaryNatStreamStepWitnessTableTailBounded
    (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6)
    (env 7) (env 8) (env 9) (env 10)
    (env 11) (env 12) (env 13) (env 14) (env 15) (env 16)
    (env 17) (env 18) (env 19) (env 20)
    (env 21) (env 22) (env 23) (env 24) (env 25) (env 26)
    (env 27) (env 28) (env 29) (env 30) (env 31) (env 32)

private theorem compactBinaryNatStreamStepWitnessTableTailBoundedDef_eval_env
    (env : Fin 33 → Nat) :
    compactBinaryNatStreamStepWitnessTableTailBoundedDef.val.Evalb env ↔
      tailBoundedGraphOfEnvironment env := by
  simp [compactBinaryNatStreamStepWitnessTableTailBoundedDef,
    tailBoundedGraphOfEnvironment,
    CompactBinaryNatStreamStepWitnessTableTailBounded,
    compactBinaryNatStreamStepWitnessTableRowCoreDef_eval_env,
    rowCoreGraphOfEnvironment]

private def headBoundedGraphOfEnvironment (env : Fin 27 → Nat) : Prop :=
  CompactBinaryNatStreamStepWitnessTableHeadBounded
    (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6)
    (env 7) (env 8) (env 9) (env 10)
    (env 11) (env 12) (env 13) (env 14) (env 15) (env 16)
    (env 17) (env 18) (env 19) (env 20)
    (env 21) (env 22) (env 23) (env 24) (env 25) (env 26)

private theorem compactBinaryNatStreamStepWitnessTableHeadBoundedDef_eval_env
    (env : Fin 27 → Nat) :
    compactBinaryNatStreamStepWitnessTableHeadBoundedDef.val.Evalb env ↔
      headBoundedGraphOfEnvironment env := by
  simp [compactBinaryNatStreamStepWitnessTableHeadBoundedDef,
    headBoundedGraphOfEnvironment,
    CompactBinaryNatStreamStepWitnessTableHeadBounded,
    compactBinaryNatStreamStepWitnessTableTailBoundedDef_eval_env,
    tailBoundedGraphOfEnvironment]

private def nextBoundedGraphOfEnvironment (env : Fin 17 → Nat) : Prop :=
  CompactBinaryNatStreamStepWitnessTableNextBounded
    (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6)
    (env 7) (env 8) (env 9) (env 10)
    (env 11) (env 12) (env 13) (env 14) (env 15) (env 16)

private theorem compactBinaryNatStreamStepWitnessTableNextBoundedDef_eval_env
    (env : Fin 17 → Nat) :
    compactBinaryNatStreamStepWitnessTableNextBoundedDef.val.Evalb env ↔
      nextBoundedGraphOfEnvironment env := by
  simp [compactBinaryNatStreamStepWitnessTableNextBoundedDef,
    nextBoundedGraphOfEnvironment,
    CompactBinaryNatStreamStepWitnessTableNextBounded,
    compactBinaryNatStreamStepWitnessTableHeadBoundedDef_eval_env,
    headBoundedGraphOfEnvironment]

private def currentBoundedGraphOfEnvironment (env : Fin 7 → Nat) : Prop :=
  CompactBinaryNatStreamStepWitnessTableCurrentBounded
    (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6)

private theorem compactBinaryNatStreamStepWitnessTableCurrentBoundedDef_eval_env
    (env : Fin 7 → Nat) :
    compactBinaryNatStreamStepWitnessTableCurrentBoundedDef.val.Evalb env ↔
      currentBoundedGraphOfEnvironment env := by
  simp [compactBinaryNatStreamStepWitnessTableCurrentBoundedDef,
    currentBoundedGraphOfEnvironment,
    CompactBinaryNatStreamStepWitnessTableCurrentBounded,
    compactBinaryNatStreamStepWitnessTableNextBoundedDef_eval_env,
    nextBoundedGraphOfEnvironment]

@[simp] theorem compactBinaryNatStreamStepWitnessTableBoundedGraphDef_spec
    (tokenTable width tokenCount tableWidth table rowCount valueBound : Nat) :
    compactBinaryNatStreamStepWitnessTableBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount,
          tableWidth, table, rowCount, valueBound] ↔
      CompactBinaryNatStreamStepWitnessTableBoundedGraph
        tokenTable width tokenCount tableWidth table rowCount valueBound := by
  simp [compactBinaryNatStreamStepWitnessTableBoundedGraphDef,
    CompactBinaryNatStreamStepWitnessTableBoundedGraph,
    compactBinaryNatStreamStepWitnessTableCurrentBoundedDef_eval_env,
    currentBoundedGraphOfEnvironment]

theorem compactBinaryNatStreamStepWitnessTableBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactBinaryNatStreamStepWitnessTableBoundedGraphDef.val := by
  simp [compactBinaryNatStreamStepWitnessTableBoundedGraphDef]

#print axioms compactBinaryNatStreamStepWitnessTableBoundedGraphDef_sigmaZero
#print axioms compactBinaryNatStreamStepWitnessTableBoundedGraphDef_spec

end FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormula
