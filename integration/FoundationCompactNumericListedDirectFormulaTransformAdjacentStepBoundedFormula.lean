import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidity

/-!
# Bounded formula for all adjacent formula-transform steps

The thirty-seven row witnesses are split into current-state, next-state, and
step-witness blocks.  Every quantifier is bounded by one explicit value bound;
the final row predicate is the exact adjacent-step formula, including both
state-boundary lookups.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula

open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

def compactFormulaTransformAdjacentStepRowOfValues
    (currentStart currentFinish currentParserFinish
      currentParserTokensFinish currentParserTasksFinish
      currentParserTokensBoundary currentParserTokensCount
      currentParserTasksBoundary currentParserTasksCount
      currentOutputBoundary currentOutputCount
      currentParserTokensBoundarySize currentParserTasksBoundarySize
      currentOutputBoundarySize
      nextStart nextFinish nextParserFinish
      nextParserTokensFinish nextParserTasksFinish
      nextParserTokensBoundary nextParserTokensCount
      nextParserTasksBoundary nextParserTasksCount
      nextOutputBoundary nextOutputCount
      nextParserTokensBoundarySize nextParserTasksBoundarySize
      nextOutputBoundarySize
      slot0 slot1 slot2 slot3 slot4 slot5 slot6
      consumedCount mappedHead : Nat) :
    CompactFormulaTransformAdjacentStepRow :=
  { currentCoordinates :=
      compactFormulaTransformStateRowCoordinatesOf
        currentStart currentFinish currentParserFinish
        currentParserTokensFinish currentParserTasksFinish
        currentParserTokensBoundary currentParserTokensCount
        currentParserTasksBoundary currentParserTasksCount
        currentOutputBoundary currentOutputCount
    currentSize :=
      { parserTokensBoundarySize := currentParserTokensBoundarySize
        parserTasksBoundarySize := currentParserTasksBoundarySize
        outputBoundarySize := currentOutputBoundarySize }
    nextCoordinates :=
      compactFormulaTransformStateRowCoordinatesOf
        nextStart nextFinish nextParserFinish
        nextParserTokensFinish nextParserTasksFinish
        nextParserTokensBoundary nextParserTokensCount
        nextParserTasksBoundary nextParserTasksCount
        nextOutputBoundary nextOutputCount
    nextSize :=
      { parserTokensBoundarySize := nextParserTokensBoundarySize
        parserTasksBoundarySize := nextParserTasksBoundarySize
        outputBoundarySize := nextOutputBoundarySize }
    stepWitness :=
      { slot0 := slot0
        slot1 := slot1
        slot2 := slot2
        slot3 := slot3
        slot4 := slot4
        slot5 := slot5
        slot6 := slot6 }
    consumedCount := consumedCount
    mappedHead := mappedHead }

def CompactFormulaTransformAdjacentStepWitnessBounded
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness) : Prop :=
  ∃ slot0, slot0 ≤ valueBound ∧
  ∃ slot1, slot1 ≤ valueBound ∧
  ∃ slot2, slot2 ≤ valueBound ∧
  ∃ slot3, slot3 ≤ valueBound ∧
  ∃ slot4, slot4 ≤ valueBound ∧
  ∃ slot5, slot5 ≤ valueBound ∧
  ∃ slot6, slot6 ≤ valueBound ∧
  ∃ consumedCount, consumedCount ≤ valueBound ∧
  ∃ mappedHead, mappedHead ≤ valueBound ∧
    CompactFormulaTransformAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount
        { currentCoordinates := currentCoordinates
          currentSize := currentSize
          nextCoordinates := nextCoordinates
          nextSize := nextSize
          stepWitness :=
            { slot0 := slot0
              slot1 := slot1
              slot2 := slot2
              slot3 := slot3
              slot4 := slot4
              slot5 := slot5
              slot6 := slot6 }
          consumedCount := consumedCount
          mappedHead := mappedHead } ∧
    CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount currentCoordinates.parserTasksFinish
        currentCoordinates.parserFinish valueBound ∧
    CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount nextCoordinates.parserTasksFinish
        nextCoordinates.parserFinish valueBound

def CompactFormulaTransformAdjacentNextBounded
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness) : Prop :=
  ∃ nextStart, nextStart ≤ valueBound ∧
  ∃ nextFinish, nextFinish ≤ valueBound ∧
  ∃ nextParserFinish, nextParserFinish ≤ valueBound ∧
  ∃ nextParserTokensFinish, nextParserTokensFinish ≤ valueBound ∧
  ∃ nextParserTasksFinish, nextParserTasksFinish ≤ valueBound ∧
  ∃ nextParserTokensBoundary, nextParserTokensBoundary ≤ valueBound ∧
  ∃ nextParserTokensCount, nextParserTokensCount ≤ valueBound ∧
  ∃ nextParserTasksBoundary, nextParserTasksBoundary ≤ valueBound ∧
  ∃ nextParserTasksCount, nextParserTasksCount ≤ valueBound ∧
  ∃ nextOutputBoundary, nextOutputBoundary ≤ valueBound ∧
  ∃ nextOutputCount, nextOutputCount ≤ valueBound ∧
  ∃ nextParserTokensBoundarySize,
      nextParserTokensBoundarySize ≤ valueBound ∧
  ∃ nextParserTasksBoundarySize,
      nextParserTasksBoundarySize ≤ valueBound ∧
  ∃ nextOutputBoundarySize, nextOutputBoundarySize ≤ valueBound ∧
    CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound
        currentCoordinates currentSize
        (compactFormulaTransformStateRowCoordinatesOf
          nextStart nextFinish nextParserFinish
          nextParserTokensFinish nextParserTasksFinish
          nextParserTokensBoundary nextParserTokensCount
          nextParserTasksBoundary nextParserTasksCount
          nextOutputBoundary nextOutputCount)
        { parserTokensBoundarySize := nextParserTokensBoundarySize
          parserTasksBoundarySize := nextParserTasksBoundarySize
          outputBoundarySize := nextOutputBoundarySize }

def CompactFormulaTransformAdjacentCurrentBounded
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat) : Prop :=
  ∃ currentStart, currentStart ≤ valueBound ∧
  ∃ currentFinish, currentFinish ≤ valueBound ∧
  ∃ currentParserFinish, currentParserFinish ≤ valueBound ∧
  ∃ currentParserTokensFinish, currentParserTokensFinish ≤ valueBound ∧
  ∃ currentParserTasksFinish, currentParserTasksFinish ≤ valueBound ∧
  ∃ currentParserTokensBoundary, currentParserTokensBoundary ≤ valueBound ∧
  ∃ currentParserTokensCount, currentParserTokensCount ≤ valueBound ∧
  ∃ currentParserTasksBoundary, currentParserTasksBoundary ≤ valueBound ∧
  ∃ currentParserTasksCount, currentParserTasksCount ≤ valueBound ∧
  ∃ currentOutputBoundary, currentOutputBoundary ≤ valueBound ∧
  ∃ currentOutputCount, currentOutputCount ≤ valueBound ∧
  ∃ currentParserTokensBoundarySize,
      currentParserTokensBoundarySize ≤ valueBound ∧
  ∃ currentParserTasksBoundarySize,
      currentParserTasksBoundarySize ≤ valueBound ∧
  ∃ currentOutputBoundarySize, currentOutputBoundarySize ≤ valueBound ∧
    CompactFormulaTransformAdjacentNextBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound
        (compactFormulaTransformStateRowCoordinatesOf
          currentStart currentFinish currentParserFinish
          currentParserTokensFinish currentParserTasksFinish
          currentParserTokensBoundary currentParserTokensCount
          currentParserTasksBoundary currentParserTasksCount
          currentOutputBoundary currentOutputCount)
        { parserTokensBoundarySize := currentParserTokensBoundarySize
          parserTasksBoundarySize := currentParserTasksBoundarySize
          outputBoundarySize := currentOutputBoundarySize }

def CompactFormulaTransformAdjacentRowsBoundedGraph
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound : Nat) :
    Prop :=
  valueBound = 2 ^ tableWidth ∧
    ∀ rowIndex < rowCount,
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound

def compactFormulaTransformAdjacentStepWitnessBoundedDef :
    𝚺₀.Semisentence 39 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound
      currentStart currentFinish currentParserFinish
      currentParserTokensFinish currentParserTasksFinish
      currentParserTokensBoundary currentParserTokensCount
      currentParserTasksBoundary currentParserTasksCount
      currentOutputBoundary currentOutputCount
      currentParserTokensBoundarySize currentParserTasksBoundarySize
      currentOutputBoundarySize
      nextStart nextFinish nextParserFinish
      nextParserTokensFinish nextParserTasksFinish
      nextParserTokensBoundary nextParserTokensCount
      nextParserTasksBoundary nextParserTasksCount
      nextOutputBoundary nextOutputCount
      nextParserTokensBoundarySize nextParserTasksBoundarySize
      nextOutputBoundarySize.
    ∃ slot0 <⁺ valueBound,
    ∃ slot1 <⁺ valueBound,
    ∃ slot2 <⁺ valueBound,
    ∃ slot3 <⁺ valueBound,
    ∃ slot4 <⁺ valueBound,
    ∃ slot5 <⁺ valueBound,
    ∃ slot6 <⁺ valueBound,
    ∃ consumedCount <⁺ valueBound,
    ∃ mappedHead <⁺ valueBound,
      (!(compactFormulaTransformAdjacentStepRowDef)
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount
        currentStart currentFinish currentParserFinish
        currentParserTokensFinish currentParserTasksFinish
        currentParserTokensBoundary currentParserTokensCount
        currentParserTasksBoundary currentParserTasksCount
        currentOutputBoundary currentOutputCount
        currentParserTokensBoundarySize currentParserTasksBoundarySize
        currentOutputBoundarySize
        nextStart nextFinish nextParserFinish
        nextParserTokensFinish nextParserTasksFinish
        nextParserTokensBoundary nextParserTokensCount
        nextParserTasksBoundary nextParserTasksCount
        nextOutputBoundary nextOutputCount
        nextParserTokensBoundarySize nextParserTasksBoundarySize
        nextOutputBoundarySize
        slot0 slot1 slot2 slot3 slot4 slot5 slot6
        consumedCount mappedHead ∧
       !(compactBinaryNatStatusValidBoundedDef)
        tokenTable width tokenCount currentParserTasksFinish
          currentParserFinish valueBound ∧
       !(compactBinaryNatStatusValidBoundedDef)
        tokenTable width tokenCount nextParserTasksFinish
          nextParserFinish valueBound)”

def compactFormulaTransformAdjacentNextBoundedDef :
    𝚺₀.Semisentence 25 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound
      currentStart currentFinish currentParserFinish
      currentParserTokensFinish currentParserTasksFinish
      currentParserTokensBoundary currentParserTokensCount
      currentParserTasksBoundary currentParserTasksCount
      currentOutputBoundary currentOutputCount
      currentParserTokensBoundarySize currentParserTasksBoundarySize
      currentOutputBoundarySize.
    ∃ nextStart <⁺ valueBound,
    ∃ nextFinish <⁺ valueBound,
    ∃ nextParserFinish <⁺ valueBound,
    ∃ nextParserTokensFinish <⁺ valueBound,
    ∃ nextParserTasksFinish <⁺ valueBound,
    ∃ nextParserTokensBoundary <⁺ valueBound,
    ∃ nextParserTokensCount <⁺ valueBound,
    ∃ nextParserTasksBoundary <⁺ valueBound,
    ∃ nextParserTasksCount <⁺ valueBound,
    ∃ nextOutputBoundary <⁺ valueBound,
    ∃ nextOutputCount <⁺ valueBound,
    ∃ nextParserTokensBoundarySize <⁺ valueBound,
    ∃ nextParserTasksBoundarySize <⁺ valueBound,
    ∃ nextOutputBoundarySize <⁺ valueBound,
      !(compactFormulaTransformAdjacentStepWitnessBoundedDef)
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound
        currentStart currentFinish currentParserFinish
        currentParserTokensFinish currentParserTasksFinish
        currentParserTokensBoundary currentParserTokensCount
        currentParserTasksBoundary currentParserTasksCount
        currentOutputBoundary currentOutputCount
        currentParserTokensBoundarySize currentParserTasksBoundarySize
        currentOutputBoundarySize
        nextStart nextFinish nextParserFinish
        nextParserTokensFinish nextParserTasksFinish
        nextParserTokensBoundary nextParserTokensCount
        nextParserTasksBoundary nextParserTasksCount
        nextOutputBoundary nextOutputCount
        nextParserTokensBoundarySize nextParserTasksBoundarySize
        nextOutputBoundarySize”

def compactFormulaTransformAdjacentCurrentBoundedDef :
    𝚺₀.Semisentence 11 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound.
    ∃ currentStart <⁺ valueBound,
    ∃ currentFinish <⁺ valueBound,
    ∃ currentParserFinish <⁺ valueBound,
    ∃ currentParserTokensFinish <⁺ valueBound,
    ∃ currentParserTasksFinish <⁺ valueBound,
    ∃ currentParserTokensBoundary <⁺ valueBound,
    ∃ currentParserTokensCount <⁺ valueBound,
    ∃ currentParserTasksBoundary <⁺ valueBound,
    ∃ currentParserTasksCount <⁺ valueBound,
    ∃ currentOutputBoundary <⁺ valueBound,
    ∃ currentOutputCount <⁺ valueBound,
    ∃ currentParserTokensBoundarySize <⁺ valueBound,
    ∃ currentParserTasksBoundarySize <⁺ valueBound,
    ∃ currentOutputBoundarySize <⁺ valueBound,
      !(compactFormulaTransformAdjacentNextBoundedDef)
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound
        currentStart currentFinish currentParserFinish
        currentParserTokensFinish currentParserTasksFinish
        currentParserTokensBoundary currentParserTokensCount
        currentParserTasksBoundary currentParserTasksCount
        currentOutputBoundary currentOutputCount
        currentParserTokensBoundarySize currentParserTasksBoundarySize
        currentOutputBoundarySize”

def compactFormulaTransformAdjacentRowsBoundedGraphDef :
    𝚺₀.Semisentence 12 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound.
    !expDef valueBound tableWidth ∧
    ∀ rowIndex < rowCount,
      !(compactFormulaTransformAdjacentCurrentBoundedDef)
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound”

set_option maxRecDepth 2048 in
@[simp] theorem compactFormulaTransformAdjacentStepWitnessBoundedDef_spec
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness) :
    compactFormulaTransformAdjacentStepWitnessBoundedDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, rowIndex,
          mode, witnessStart, witnessFinish, witnessCount, valueBound,
          currentCoordinates.start, currentCoordinates.finish,
          currentCoordinates.parserFinish,
          currentCoordinates.parserTokensFinish,
          currentCoordinates.parserTasksFinish,
          currentCoordinates.parserTokensBoundary,
          currentCoordinates.parserTokensCount,
          currentCoordinates.parserTasksBoundary,
          currentCoordinates.parserTasksCount,
          currentCoordinates.outputBoundary, currentCoordinates.outputCount,
          currentSize.parserTokensBoundarySize,
          currentSize.parserTasksBoundarySize,
          currentSize.outputBoundarySize,
          nextCoordinates.start, nextCoordinates.finish,
          nextCoordinates.parserFinish,
          nextCoordinates.parserTokensFinish,
          nextCoordinates.parserTasksFinish,
          nextCoordinates.parserTokensBoundary,
          nextCoordinates.parserTokensCount,
          nextCoordinates.parserTasksBoundary,
          nextCoordinates.parserTasksCount,
          nextCoordinates.outputBoundary, nextCoordinates.outputCount,
          nextSize.parserTokensBoundarySize,
          nextSize.parserTasksBoundarySize,
          nextSize.outputBoundarySize] ↔
      CompactFormulaTransformAdjacentStepWitnessBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound
          currentCoordinates currentSize nextCoordinates nextSize := by
  have hrow
      (mappedHead consumedCount slot6 slot5 slot4 slot3 slot2 slot1 slot0 :
        Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![mappedHead, consumedCount, slot6, slot5, slot4, slot3,
                slot2, slot1, slot0,
                tokenTable, width, tokenCount, stateBoundary, stateCount,
                rowIndex, mode, witnessStart, witnessFinish, witnessCount,
                valueBound,
                currentCoordinates.start, currentCoordinates.finish,
                currentCoordinates.parserFinish,
                currentCoordinates.parserTokensFinish,
                currentCoordinates.parserTasksFinish,
                currentCoordinates.parserTokensBoundary,
                currentCoordinates.parserTokensCount,
                currentCoordinates.parserTasksBoundary,
                currentCoordinates.parserTasksCount,
                currentCoordinates.outputBoundary,
                currentCoordinates.outputCount,
                currentSize.parserTokensBoundarySize,
                currentSize.parserTasksBoundarySize,
                currentSize.outputBoundarySize,
                nextCoordinates.start, nextCoordinates.finish,
                nextCoordinates.parserFinish,
                nextCoordinates.parserTokensFinish,
                nextCoordinates.parserTasksFinish,
                nextCoordinates.parserTokensBoundary,
                nextCoordinates.parserTokensCount,
                nextCoordinates.parserTasksBoundary,
                nextCoordinates.parserTasksCount,
                nextCoordinates.outputBoundary,
                nextCoordinates.outputCount,
                nextSize.parserTokensBoundarySize,
                nextSize.parserTasksBoundarySize,
                nextSize.outputBoundarySize]
              Empty.elim ∘
            ![(#9 : Semiterm ℒₒᵣ Empty 48), #10, #11, #12, #13, #14,
              #15, #16, #17, #18,
              #20, #21, #22, #23, #24, #25, #26, #27, #28, #29, #30,
              #31, #32, #33,
              #34, #35, #36, #37, #38, #39, #40, #41, #42, #43, #44,
              #45, #46, #47,
              #8, #7, #6, #5, #4, #3, #2, #1, #0])
          Empty.elim)
        compactFormulaTransformAdjacentStepRowDef.val ↔
      CompactFormulaTransformAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount
          { currentCoordinates := currentCoordinates
            currentSize := currentSize
            nextCoordinates := nextCoordinates
            nextSize := nextSize
            stepWitness :=
              { slot0 := slot0
                slot1 := slot1
                slot2 := slot2
                slot3 := slot3
                slot4 := slot4
                slot5 := slot5
                slot6 := slot6 }
            consumedCount := consumedCount
            mappedHead := mappedHead } := by
    have henv :
        (Semiterm.val
            ![mappedHead, consumedCount, slot6, slot5, slot4, slot3,
              slot2, slot1, slot0,
              tokenTable, width, tokenCount, stateBoundary, stateCount,
              rowIndex, mode, witnessStart, witnessFinish, witnessCount,
              valueBound,
              currentCoordinates.start, currentCoordinates.finish,
              currentCoordinates.parserFinish,
              currentCoordinates.parserTokensFinish,
              currentCoordinates.parserTasksFinish,
              currentCoordinates.parserTokensBoundary,
              currentCoordinates.parserTokensCount,
              currentCoordinates.parserTasksBoundary,
              currentCoordinates.parserTasksCount,
              currentCoordinates.outputBoundary,
              currentCoordinates.outputCount,
              currentSize.parserTokensBoundarySize,
              currentSize.parserTasksBoundarySize,
              currentSize.outputBoundarySize,
              nextCoordinates.start, nextCoordinates.finish,
              nextCoordinates.parserFinish,
              nextCoordinates.parserTokensFinish,
              nextCoordinates.parserTasksFinish,
              nextCoordinates.parserTokensBoundary,
              nextCoordinates.parserTokensCount,
              nextCoordinates.parserTasksBoundary,
              nextCoordinates.parserTasksCount,
              nextCoordinates.outputBoundary,
              nextCoordinates.outputCount,
              nextSize.parserTokensBoundarySize,
              nextSize.parserTasksBoundarySize,
              nextSize.outputBoundarySize]
            Empty.elim ∘
          ![(#9 : Semiterm ℒₒᵣ Empty 48), #10, #11, #12, #13, #14,
            #15, #16, #17, #18,
            #20, #21, #22, #23, #24, #25, #26, #27, #28, #29, #30,
            #31, #32, #33,
            #34, #35, #36, #37, #38, #39, #40, #41, #42, #43, #44,
            #45, #46, #47,
            #8, #7, #6, #5, #4, #3, #2, #1, #0]) =
          compactFormulaTransformAdjacentStepRowEnvironment
            tokenTable width tokenCount stateBoundary stateCount rowIndex mode
              witnessStart witnessFinish witnessCount
              { currentCoordinates := currentCoordinates
                currentSize := currentSize
                nextCoordinates := nextCoordinates
                nextSize := nextSize
                stepWitness :=
                  { slot0 := slot0
                    slot1 := slot1
                    slot2 := slot2
                    slot3 := slot3
                    slot4 := slot4
                    slot5 := slot5
                    slot6 := slot6 }
                consumedCount := consumedCount
                mappedHead := mappedHead } := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactFormulaTransformAdjacentStepRowDef_spec
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount _
  have hcurrentStatus
      (mappedHead consumedCount slot6 slot5 slot4 slot3 slot2 slot1 slot0 :
        Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![mappedHead, consumedCount, slot6, slot5, slot4, slot3,
                slot2, slot1, slot0,
                tokenTable, width, tokenCount, stateBoundary, stateCount,
                rowIndex, mode, witnessStart, witnessFinish, witnessCount,
                valueBound,
                currentCoordinates.start, currentCoordinates.finish,
                currentCoordinates.parserFinish,
                currentCoordinates.parserTokensFinish,
                currentCoordinates.parserTasksFinish,
                currentCoordinates.parserTokensBoundary,
                currentCoordinates.parserTokensCount,
                currentCoordinates.parserTasksBoundary,
                currentCoordinates.parserTasksCount,
                currentCoordinates.outputBoundary,
                currentCoordinates.outputCount,
                currentSize.parserTokensBoundarySize,
                currentSize.parserTasksBoundarySize,
                currentSize.outputBoundarySize,
                nextCoordinates.start, nextCoordinates.finish,
                nextCoordinates.parserFinish,
                nextCoordinates.parserTokensFinish,
                nextCoordinates.parserTasksFinish,
                nextCoordinates.parserTokensBoundary,
                nextCoordinates.parserTokensCount,
                nextCoordinates.parserTasksBoundary,
                nextCoordinates.parserTasksCount,
                nextCoordinates.outputBoundary,
                nextCoordinates.outputCount,
                nextSize.parserTokensBoundarySize,
                nextSize.parserTasksBoundarySize,
                nextSize.outputBoundarySize]
              Empty.elim ∘
            ![(#9 : Semiterm ℒₒᵣ Empty 48), #10, #11, #24, #22, #19])
          Empty.elim)
        compactBinaryNatStatusValidBoundedDef.val ↔
      CompactBinaryNatStatusValidBounded
        tokenTable width tokenCount currentCoordinates.parserTasksFinish
          currentCoordinates.parserFinish valueBound := by
    have henv :
        (Semiterm.val
            ![mappedHead, consumedCount, slot6, slot5, slot4, slot3,
              slot2, slot1, slot0,
              tokenTable, width, tokenCount, stateBoundary, stateCount,
              rowIndex, mode, witnessStart, witnessFinish, witnessCount,
              valueBound,
              currentCoordinates.start, currentCoordinates.finish,
              currentCoordinates.parserFinish,
              currentCoordinates.parserTokensFinish,
              currentCoordinates.parserTasksFinish,
              currentCoordinates.parserTokensBoundary,
              currentCoordinates.parserTokensCount,
              currentCoordinates.parserTasksBoundary,
              currentCoordinates.parserTasksCount,
              currentCoordinates.outputBoundary,
              currentCoordinates.outputCount,
              currentSize.parserTokensBoundarySize,
              currentSize.parserTasksBoundarySize,
              currentSize.outputBoundarySize,
              nextCoordinates.start, nextCoordinates.finish,
              nextCoordinates.parserFinish,
              nextCoordinates.parserTokensFinish,
              nextCoordinates.parserTasksFinish,
              nextCoordinates.parserTokensBoundary,
              nextCoordinates.parserTokensCount,
              nextCoordinates.parserTasksBoundary,
              nextCoordinates.parserTasksCount,
              nextCoordinates.outputBoundary,
              nextCoordinates.outputCount,
              nextSize.parserTokensBoundarySize,
              nextSize.parserTasksBoundarySize,
              nextSize.outputBoundarySize]
            Empty.elim ∘
          ![(#9 : Semiterm ℒₒᵣ Empty 48), #10, #11, #24, #22, #19]) =
        ![tokenTable, width, tokenCount,
          currentCoordinates.parserTasksFinish,
          currentCoordinates.parserFinish, valueBound] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactBinaryNatStatusValidBoundedDef_spec
      tokenTable width tokenCount currentCoordinates.parserTasksFinish
        currentCoordinates.parserFinish valueBound
  have hnextStatus
      (mappedHead consumedCount slot6 slot5 slot4 slot3 slot2 slot1 slot0 :
        Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![mappedHead, consumedCount, slot6, slot5, slot4, slot3,
                slot2, slot1, slot0,
                tokenTable, width, tokenCount, stateBoundary, stateCount,
                rowIndex, mode, witnessStart, witnessFinish, witnessCount,
                valueBound,
                currentCoordinates.start, currentCoordinates.finish,
                currentCoordinates.parserFinish,
                currentCoordinates.parserTokensFinish,
                currentCoordinates.parserTasksFinish,
                currentCoordinates.parserTokensBoundary,
                currentCoordinates.parserTokensCount,
                currentCoordinates.parserTasksBoundary,
                currentCoordinates.parserTasksCount,
                currentCoordinates.outputBoundary,
                currentCoordinates.outputCount,
                currentSize.parserTokensBoundarySize,
                currentSize.parserTasksBoundarySize,
                currentSize.outputBoundarySize,
                nextCoordinates.start, nextCoordinates.finish,
                nextCoordinates.parserFinish,
                nextCoordinates.parserTokensFinish,
                nextCoordinates.parserTasksFinish,
                nextCoordinates.parserTokensBoundary,
                nextCoordinates.parserTokensCount,
                nextCoordinates.parserTasksBoundary,
                nextCoordinates.parserTasksCount,
                nextCoordinates.outputBoundary,
                nextCoordinates.outputCount,
                nextSize.parserTokensBoundarySize,
                nextSize.parserTasksBoundarySize,
                nextSize.outputBoundarySize]
              Empty.elim ∘
            ![(#9 : Semiterm ℒₒᵣ Empty 48), #10, #11, #38, #36, #19])
          Empty.elim)
        compactBinaryNatStatusValidBoundedDef.val ↔
      CompactBinaryNatStatusValidBounded
        tokenTable width tokenCount nextCoordinates.parserTasksFinish
          nextCoordinates.parserFinish valueBound := by
    have henv :
        (Semiterm.val
            ![mappedHead, consumedCount, slot6, slot5, slot4, slot3,
              slot2, slot1, slot0,
              tokenTable, width, tokenCount, stateBoundary, stateCount,
              rowIndex, mode, witnessStart, witnessFinish, witnessCount,
              valueBound,
              currentCoordinates.start, currentCoordinates.finish,
              currentCoordinates.parserFinish,
              currentCoordinates.parserTokensFinish,
              currentCoordinates.parserTasksFinish,
              currentCoordinates.parserTokensBoundary,
              currentCoordinates.parserTokensCount,
              currentCoordinates.parserTasksBoundary,
              currentCoordinates.parserTasksCount,
              currentCoordinates.outputBoundary,
              currentCoordinates.outputCount,
              currentSize.parserTokensBoundarySize,
              currentSize.parserTasksBoundarySize,
              currentSize.outputBoundarySize,
              nextCoordinates.start, nextCoordinates.finish,
              nextCoordinates.parserFinish,
              nextCoordinates.parserTokensFinish,
              nextCoordinates.parserTasksFinish,
              nextCoordinates.parserTokensBoundary,
              nextCoordinates.parserTokensCount,
              nextCoordinates.parserTasksBoundary,
              nextCoordinates.parserTasksCount,
              nextCoordinates.outputBoundary,
              nextCoordinates.outputCount,
              nextSize.parserTokensBoundarySize,
              nextSize.parserTasksBoundarySize,
              nextSize.outputBoundarySize]
            Empty.elim ∘
          ![(#9 : Semiterm ℒₒᵣ Empty 48), #10, #11, #38, #36, #19]) =
        ![tokenTable, width, tokenCount,
          nextCoordinates.parserTasksFinish,
          nextCoordinates.parserFinish, valueBound] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactBinaryNatStatusValidBoundedDef_spec
      tokenTable width tokenCount nextCoordinates.parserTasksFinish
        nextCoordinates.parserFinish valueBound
  simp [compactFormulaTransformAdjacentStepWitnessBoundedDef,
    CompactFormulaTransformAdjacentStepWitnessBounded,
    hrow, hcurrentStatus, hnextStatus]

theorem compactFormulaTransformAdjacentStepWitnessBoundedDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformAdjacentStepWitnessBoundedDef.val := by
  simp [compactFormulaTransformAdjacentStepWitnessBoundedDef]

set_option maxRecDepth 2048 in
@[simp] theorem compactFormulaTransformAdjacentNextBoundedDef_spec
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness) :
    compactFormulaTransformAdjacentNextBoundedDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, rowIndex,
          mode, witnessStart, witnessFinish, witnessCount, valueBound,
          currentCoordinates.start, currentCoordinates.finish,
          currentCoordinates.parserFinish,
          currentCoordinates.parserTokensFinish,
          currentCoordinates.parserTasksFinish,
          currentCoordinates.parserTokensBoundary,
          currentCoordinates.parserTokensCount,
          currentCoordinates.parserTasksBoundary,
          currentCoordinates.parserTasksCount,
          currentCoordinates.outputBoundary, currentCoordinates.outputCount,
          currentSize.parserTokensBoundarySize,
          currentSize.parserTasksBoundarySize,
          currentSize.outputBoundarySize] ↔
      CompactFormulaTransformAdjacentNextBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound
          currentCoordinates currentSize := by
  have hnext
      (nextOutputBoundarySize nextParserTasksBoundarySize
        nextParserTokensBoundarySize nextOutputCount nextOutputBoundary
        nextParserTasksCount nextParserTasksBoundary
        nextParserTokensCount nextParserTokensBoundary
        nextParserTasksFinish nextParserTokensFinish nextParserFinish
        nextFinish nextStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![nextOutputBoundarySize, nextParserTasksBoundarySize,
                nextParserTokensBoundarySize, nextOutputCount,
                nextOutputBoundary, nextParserTasksCount,
                nextParserTasksBoundary, nextParserTokensCount,
                nextParserTokensBoundary, nextParserTasksFinish,
                nextParserTokensFinish, nextParserFinish,
                nextFinish, nextStart,
                tokenTable, width, tokenCount, stateBoundary, stateCount,
                rowIndex, mode, witnessStart, witnessFinish, witnessCount,
                valueBound,
                currentCoordinates.start, currentCoordinates.finish,
                currentCoordinates.parserFinish,
                currentCoordinates.parserTokensFinish,
                currentCoordinates.parserTasksFinish,
                currentCoordinates.parserTokensBoundary,
                currentCoordinates.parserTokensCount,
                currentCoordinates.parserTasksBoundary,
                currentCoordinates.parserTasksCount,
                currentCoordinates.outputBoundary,
                currentCoordinates.outputCount,
                currentSize.parserTokensBoundarySize,
                currentSize.parserTasksBoundarySize,
                currentSize.outputBoundarySize]
              Empty.elim ∘
            ![(#14 : Semiterm ℒₒᵣ Empty 39), #15, #16, #17, #18, #19,
              #20, #21, #22, #23, #24,
              #25, #26, #27, #28, #29, #30, #31, #32, #33, #34, #35,
              #36, #37, #38,
              #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3,
              #2, #1, #0])
          Empty.elim)
        compactFormulaTransformAdjacentStepWitnessBoundedDef.val ↔
      CompactFormulaTransformAdjacentStepWitnessBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound
          currentCoordinates currentSize
          (compactFormulaTransformStateRowCoordinatesOf
            nextStart nextFinish nextParserFinish
            nextParserTokensFinish nextParserTasksFinish
            nextParserTokensBoundary nextParserTokensCount
            nextParserTasksBoundary nextParserTasksCount
            nextOutputBoundary nextOutputCount)
          { parserTokensBoundarySize := nextParserTokensBoundarySize
            parserTasksBoundarySize := nextParserTasksBoundarySize
            outputBoundarySize := nextOutputBoundarySize } := by
    have henv :
        (Semiterm.val
            ![nextOutputBoundarySize, nextParserTasksBoundarySize,
              nextParserTokensBoundarySize, nextOutputCount,
              nextOutputBoundary, nextParserTasksCount,
              nextParserTasksBoundary, nextParserTokensCount,
              nextParserTokensBoundary, nextParserTasksFinish,
              nextParserTokensFinish, nextParserFinish,
              nextFinish, nextStart,
              tokenTable, width, tokenCount, stateBoundary, stateCount,
              rowIndex, mode, witnessStart, witnessFinish, witnessCount,
              valueBound,
              currentCoordinates.start, currentCoordinates.finish,
              currentCoordinates.parserFinish,
              currentCoordinates.parserTokensFinish,
              currentCoordinates.parserTasksFinish,
              currentCoordinates.parserTokensBoundary,
              currentCoordinates.parserTokensCount,
              currentCoordinates.parserTasksBoundary,
              currentCoordinates.parserTasksCount,
              currentCoordinates.outputBoundary,
              currentCoordinates.outputCount,
              currentSize.parserTokensBoundarySize,
              currentSize.parserTasksBoundarySize,
              currentSize.outputBoundarySize]
            Empty.elim ∘
          ![(#14 : Semiterm ℒₒᵣ Empty 39), #15, #16, #17, #18, #19,
            #20, #21, #22, #23, #24,
            #25, #26, #27, #28, #29, #30, #31, #32, #33, #34, #35,
            #36, #37, #38,
            #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3,
            #2, #1, #0]) =
          ![tokenTable, width, tokenCount, stateBoundary, stateCount,
            rowIndex, mode, witnessStart, witnessFinish, witnessCount,
            valueBound,
            currentCoordinates.start, currentCoordinates.finish,
            currentCoordinates.parserFinish,
            currentCoordinates.parserTokensFinish,
            currentCoordinates.parserTasksFinish,
            currentCoordinates.parserTokensBoundary,
            currentCoordinates.parserTokensCount,
            currentCoordinates.parserTasksBoundary,
            currentCoordinates.parserTasksCount,
            currentCoordinates.outputBoundary,
            currentCoordinates.outputCount,
            currentSize.parserTokensBoundarySize,
            currentSize.parserTasksBoundarySize,
            currentSize.outputBoundarySize,
            nextStart, nextFinish, nextParserFinish,
            nextParserTokensFinish, nextParserTasksFinish,
            nextParserTokensBoundary, nextParserTokensCount,
            nextParserTasksBoundary, nextParserTasksCount,
            nextOutputBoundary, nextOutputCount,
            nextParserTokensBoundarySize, nextParserTasksBoundarySize,
            nextOutputBoundarySize] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactFormulaTransformAdjacentStepWitnessBoundedDef_spec
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound
        currentCoordinates currentSize
        (compactFormulaTransformStateRowCoordinatesOf
          nextStart nextFinish nextParserFinish
          nextParserTokensFinish nextParserTasksFinish
          nextParserTokensBoundary nextParserTokensCount
          nextParserTasksBoundary nextParserTasksCount
          nextOutputBoundary nextOutputCount)
        { parserTokensBoundarySize := nextParserTokensBoundarySize
          parserTasksBoundarySize := nextParserTasksBoundarySize
          outputBoundarySize := nextOutputBoundarySize }
  simp [compactFormulaTransformAdjacentNextBoundedDef,
    CompactFormulaTransformAdjacentNextBounded, hnext]

set_option maxRecDepth 2048 in
@[simp] theorem compactFormulaTransformAdjacentCurrentBoundedDef_spec
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat) :
    compactFormulaTransformAdjacentCurrentBoundedDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, rowIndex,
          mode, witnessStart, witnessFinish, witnessCount, valueBound] ↔
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound := by
  have hcurrent
      (currentOutputBoundarySize currentParserTasksBoundarySize
        currentParserTokensBoundarySize currentOutputCount
        currentOutputBoundary currentParserTasksCount
        currentParserTasksBoundary currentParserTokensCount
        currentParserTokensBoundary currentParserTasksFinish
        currentParserTokensFinish currentParserFinish
        currentFinish currentStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![currentOutputBoundarySize, currentParserTasksBoundarySize,
                currentParserTokensBoundarySize, currentOutputCount,
                currentOutputBoundary, currentParserTasksCount,
                currentParserTasksBoundary, currentParserTokensCount,
                currentParserTokensBoundary, currentParserTasksFinish,
                currentParserTokensFinish, currentParserFinish,
                currentFinish, currentStart,
                tokenTable, width, tokenCount, stateBoundary, stateCount,
                rowIndex, mode, witnessStart, witnessFinish, witnessCount,
                valueBound]
              Empty.elim ∘
            ![(#14 : Semiterm ℒₒᵣ Empty 25), #15, #16, #17, #18, #19,
              #20, #21, #22, #23, #24,
              #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3,
              #2, #1, #0])
          Empty.elim)
        compactFormulaTransformAdjacentNextBoundedDef.val ↔
      CompactFormulaTransformAdjacentNextBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound
          (compactFormulaTransformStateRowCoordinatesOf
            currentStart currentFinish currentParserFinish
            currentParserTokensFinish currentParserTasksFinish
            currentParserTokensBoundary currentParserTokensCount
            currentParserTasksBoundary currentParserTasksCount
            currentOutputBoundary currentOutputCount)
          { parserTokensBoundarySize := currentParserTokensBoundarySize
            parserTasksBoundarySize := currentParserTasksBoundarySize
            outputBoundarySize := currentOutputBoundarySize } := by
    have henv :
        (Semiterm.val
            ![currentOutputBoundarySize, currentParserTasksBoundarySize,
              currentParserTokensBoundarySize, currentOutputCount,
              currentOutputBoundary, currentParserTasksCount,
              currentParserTasksBoundary, currentParserTokensCount,
              currentParserTokensBoundary, currentParserTasksFinish,
              currentParserTokensFinish, currentParserFinish,
              currentFinish, currentStart,
              tokenTable, width, tokenCount, stateBoundary, stateCount,
              rowIndex, mode, witnessStart, witnessFinish, witnessCount,
              valueBound]
            Empty.elim ∘
          ![(#14 : Semiterm ℒₒᵣ Empty 25), #15, #16, #17, #18, #19,
            #20, #21, #22, #23, #24,
            #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3,
            #2, #1, #0]) =
          ![tokenTable, width, tokenCount, stateBoundary, stateCount,
            rowIndex, mode, witnessStart, witnessFinish, witnessCount,
            valueBound,
            currentStart, currentFinish, currentParserFinish,
            currentParserTokensFinish, currentParserTasksFinish,
            currentParserTokensBoundary, currentParserTokensCount,
            currentParserTasksBoundary, currentParserTasksCount,
            currentOutputBoundary, currentOutputCount,
            currentParserTokensBoundarySize,
            currentParserTasksBoundarySize,
            currentOutputBoundarySize] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactFormulaTransformAdjacentNextBoundedDef_spec
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound
        (compactFormulaTransformStateRowCoordinatesOf
          currentStart currentFinish currentParserFinish
          currentParserTokensFinish currentParserTasksFinish
          currentParserTokensBoundary currentParserTokensCount
          currentParserTasksBoundary currentParserTasksCount
          currentOutputBoundary currentOutputCount)
        { parserTokensBoundarySize := currentParserTokensBoundarySize
          parserTasksBoundarySize := currentParserTasksBoundarySize
          outputBoundarySize := currentOutputBoundarySize }
  simp [compactFormulaTransformAdjacentCurrentBoundedDef,
    CompactFormulaTransformAdjacentCurrentBounded, hcurrent]

@[simp] theorem compactFormulaTransformAdjacentRowsBoundedGraphDef_spec
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound : Nat) :
    compactFormulaTransformAdjacentRowsBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, rowCount,
          mode, witnessStart, witnessFinish, witnessCount,
          tableWidth, valueBound] ↔
      CompactFormulaTransformAdjacentRowsBoundedGraph
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
          witnessStart witnessFinish witnessCount tableWidth valueBound := by
  have hrow (rowIndex : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![rowIndex, tokenTable, width, tokenCount, stateBoundary,
                stateCount, rowCount, mode, witnessStart, witnessFinish,
                witnessCount, tableWidth, valueBound]
              Empty.elim ∘
            ![(#1 : Semiterm ℒₒᵣ Empty 13), #2, #3, #4, #5, #0,
              #7, #8, #9, #10, #12])
          Empty.elim)
        compactFormulaTransformAdjacentCurrentBoundedDef.val ↔
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound := by
    have henv :
        (Semiterm.val
            ![rowIndex, tokenTable, width, tokenCount, stateBoundary,
              stateCount, rowCount, mode, witnessStart, witnessFinish,
              witnessCount, tableWidth, valueBound]
            Empty.elim ∘
          ![(#1 : Semiterm ℒₒᵣ Empty 13), #2, #3, #4, #5, #0,
            #7, #8, #9, #10, #12]) =
          ![tokenTable, width, tokenCount, stateBoundary, stateCount,
            rowIndex, mode, witnessStart, witnessFinish, witnessCount,
            valueBound] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactFormulaTransformAdjacentCurrentBoundedDef_spec
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound
  simp [compactFormulaTransformAdjacentRowsBoundedGraphDef,
    CompactFormulaTransformAdjacentRowsBoundedGraph, hrow]

theorem compactFormulaTransformAdjacentNextBoundedDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformAdjacentNextBoundedDef.val := by
  simp [compactFormulaTransformAdjacentNextBoundedDef]

theorem compactFormulaTransformAdjacentCurrentBoundedDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformAdjacentCurrentBoundedDef.val := by
  simp [compactFormulaTransformAdjacentCurrentBoundedDef]

theorem compactFormulaTransformAdjacentRowsBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformAdjacentRowsBoundedGraphDef.val := by
  simp [compactFormulaTransformAdjacentRowsBoundedGraphDef]

#print axioms compactFormulaTransformAdjacentStepWitnessBoundedDef_spec
#print axioms compactFormulaTransformAdjacentStepWitnessBoundedDef_sigmaZero
#print axioms compactFormulaTransformAdjacentNextBoundedDef_spec
#print axioms compactFormulaTransformAdjacentCurrentBoundedDef_spec
#print axioms compactFormulaTransformAdjacentRowsBoundedGraphDef_spec
#print axioms compactFormulaTransformAdjacentNextBoundedDef_sigmaZero
#print axioms compactFormulaTransformAdjacentCurrentBoundedDef_sigmaZero
#print axioms compactFormulaTransformAdjacentRowsBoundedGraphDef_sigmaZero

end FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
