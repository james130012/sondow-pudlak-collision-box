import integration.FoundationCompactNumericListedDirectParserClosedAdjacentStepFormula
import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidity

/-!
# Bounded universal formula for all adjacent closed-parser steps

Twenty-seven local row values are explicitly bounded by one power-of-two value
bound.  The row predicate contains both consecutive state lookups, the complete
closed-parser step graph, and exact bounded realizability of both nested statuses.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserClosedAdjacentStepBoundedFormula

open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserClosedAdjacentStepFormula
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

def compactParserClosedAdjacentStepRowOfValues
    (currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      currentTokensBoundarySize currentTasksBoundarySize
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      nextTokensBoundarySize nextTasksBoundarySize
      slot0 slot1 slot2 slot3 slot4 slot5 slot6 : Nat) :
    CompactParserSyntaxAdjacentStepRow :=
  { currentCoordinates := compactUnifiedParserStateRowCoordinatesOf
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
    currentSize :=
      { tokensBoundarySize := currentTokensBoundarySize
        tasksBoundarySize := currentTasksBoundarySize }
    nextCoordinates := compactUnifiedParserStateRowCoordinatesOf
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
    nextSize :=
      { tokensBoundarySize := nextTokensBoundarySize
        tasksBoundarySize := nextTasksBoundarySize }
    stepWitness :=
      { slot0 := slot0
        slot1 := slot1
        slot2 := slot2
        slot3 := slot3
        slot4 := slot4
        slot5 := slot5
        slot6 := slot6 } }

def CompactParserClosedAdjacentRowBounded
    (tokenTable width tokenCount stateBoundary stateCount rowIndex
      valueBound : Nat) : Prop :=
  ∃ currentStart, currentStart ≤ valueBound ∧
  ∃ currentFinish, currentFinish ≤ valueBound ∧
  ∃ currentTokensFinish, currentTokensFinish ≤ valueBound ∧
  ∃ currentTasksFinish, currentTasksFinish ≤ valueBound ∧
  ∃ currentTokensBoundary, currentTokensBoundary ≤ valueBound ∧
  ∃ currentTokensCount, currentTokensCount ≤ valueBound ∧
  ∃ currentTasksBoundary, currentTasksBoundary ≤ valueBound ∧
  ∃ currentTasksCount, currentTasksCount ≤ valueBound ∧
  ∃ currentTokensBoundarySize, currentTokensBoundarySize ≤ valueBound ∧
  ∃ currentTasksBoundarySize, currentTasksBoundarySize ≤ valueBound ∧
  ∃ nextStart, nextStart ≤ valueBound ∧
  ∃ nextFinish, nextFinish ≤ valueBound ∧
  ∃ nextTokensFinish, nextTokensFinish ≤ valueBound ∧
  ∃ nextTasksFinish, nextTasksFinish ≤ valueBound ∧
  ∃ nextTokensBoundary, nextTokensBoundary ≤ valueBound ∧
  ∃ nextTokensCount, nextTokensCount ≤ valueBound ∧
  ∃ nextTasksBoundary, nextTasksBoundary ≤ valueBound ∧
  ∃ nextTasksCount, nextTasksCount ≤ valueBound ∧
  ∃ nextTokensBoundarySize, nextTokensBoundarySize ≤ valueBound ∧
  ∃ nextTasksBoundarySize, nextTasksBoundarySize ≤ valueBound ∧
  ∃ slot0, slot0 ≤ valueBound ∧
  ∃ slot1, slot1 ≤ valueBound ∧
  ∃ slot2, slot2 ≤ valueBound ∧
  ∃ slot3, slot3 ≤ valueBound ∧
  ∃ slot4, slot4 ≤ valueBound ∧
  ∃ slot5, slot5 ≤ valueBound ∧
  ∃ slot6, slot6 ≤ valueBound ∧
    let row := compactParserClosedAdjacentStepRowOfValues
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      currentTokensBoundarySize currentTasksBoundarySize
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      nextTokensBoundarySize nextTasksBoundarySize
      slot0 slot1 slot2 slot3 slot4 slot5 slot6
    CompactParserClosedAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary stateCount rowIndex row ∧
      CompactBinaryNatStatusValidBounded
        tokenTable width tokenCount currentTasksFinish currentFinish valueBound ∧
      CompactBinaryNatStatusValidBounded
        tokenTable width tokenCount nextTasksFinish nextFinish valueBound

def CompactParserClosedAdjacentRowsBoundedGraph
    (tokenTable width tokenCount stateBoundary stateCount rowCount
      tableWidth valueBound : Nat) : Prop :=
  valueBound = 2 ^ tableWidth ∧
    ∀ rowIndex < rowCount,
      CompactParserClosedAdjacentRowBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex valueBound

def compactParserClosedAdjacentRowBoundedDef : 𝚺₀.Semisentence 7 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount rowIndex valueBound.
    ∃ currentStart <⁺ valueBound,
    ∃ currentFinish <⁺ valueBound,
    ∃ currentTokensFinish <⁺ valueBound,
    ∃ currentTasksFinish <⁺ valueBound,
    ∃ currentTokensBoundary <⁺ valueBound,
    ∃ currentTokensCount <⁺ valueBound,
    ∃ currentTasksBoundary <⁺ valueBound,
    ∃ currentTasksCount <⁺ valueBound,
    ∃ currentTokensBoundarySize <⁺ valueBound,
    ∃ currentTasksBoundarySize <⁺ valueBound,
    ∃ nextStart <⁺ valueBound,
    ∃ nextFinish <⁺ valueBound,
    ∃ nextTokensFinish <⁺ valueBound,
    ∃ nextTasksFinish <⁺ valueBound,
    ∃ nextTokensBoundary <⁺ valueBound,
    ∃ nextTokensCount <⁺ valueBound,
    ∃ nextTasksBoundary <⁺ valueBound,
    ∃ nextTasksCount <⁺ valueBound,
    ∃ nextTokensBoundarySize <⁺ valueBound,
    ∃ nextTasksBoundarySize <⁺ valueBound,
    ∃ slot0 <⁺ valueBound,
    ∃ slot1 <⁺ valueBound,
    ∃ slot2 <⁺ valueBound,
    ∃ slot3 <⁺ valueBound,
    ∃ slot4 <⁺ valueBound,
    ∃ slot5 <⁺ valueBound,
    ∃ slot6 <⁺ valueBound,
      (!(compactParserClosedAdjacentStepRowDef)
        tokenTable width tokenCount stateBoundary stateCount rowIndex
        currentStart currentFinish currentTokensFinish currentTasksFinish
        currentTokensBoundary currentTokensCount
        currentTasksBoundary currentTasksCount
        currentTokensBoundarySize currentTasksBoundarySize
        nextStart nextFinish nextTokensFinish nextTasksFinish
        nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
        nextTokensBoundarySize nextTasksBoundarySize
        slot0 slot1 slot2 slot3 slot4 slot5 slot6 ∧
       !(compactBinaryNatStatusValidBoundedDef)
        tokenTable width tokenCount currentTasksFinish currentFinish valueBound ∧
       !(compactBinaryNatStatusValidBoundedDef)
        tokenTable width tokenCount nextTasksFinish nextFinish valueBound)”

def compactParserClosedAdjacentRowsBoundedGraphDef :
    𝚺₀.Semisentence 8 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount rowCount
      tableWidth valueBound.
    !expDef valueBound tableWidth ∧
    ∀ rowIndex < rowCount,
      !(compactParserClosedAdjacentRowBoundedDef)
        tokenTable width tokenCount stateBoundary stateCount rowIndex valueBound”

set_option maxRecDepth 4096 in
@[simp] theorem compactParserClosedAdjacentRowBoundedDef_spec
    (tokenTable width tokenCount stateBoundary stateCount rowIndex
      valueBound : Nat) :
    compactParserClosedAdjacentRowBoundedDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, rowIndex,
          valueBound] ↔
      CompactParserClosedAdjacentRowBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex
          valueBound := by
  have hrow
      (slot6 slot5 slot4 slot3 slot2 slot1 slot0
        nextTasksBoundarySize nextTokensBoundarySize
        nextTasksCount nextTasksBoundary nextTokensCount nextTokensBoundary
        nextTasksFinish nextTokensFinish nextFinish nextStart
        currentTasksBoundarySize currentTokensBoundarySize
        currentTasksCount currentTasksBoundary currentTokensCount
        currentTokensBoundary currentTasksFinish currentTokensFinish
        currentFinish currentStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![slot6, slot5, slot4, slot3, slot2, slot1, slot0,
                nextTasksBoundarySize, nextTokensBoundarySize,
                nextTasksCount, nextTasksBoundary, nextTokensCount,
                nextTokensBoundary, nextTasksFinish, nextTokensFinish,
                nextFinish, nextStart,
                currentTasksBoundarySize, currentTokensBoundarySize,
                currentTasksCount, currentTasksBoundary, currentTokensCount,
                currentTokensBoundary, currentTasksFinish,
                currentTokensFinish, currentFinish, currentStart,
                tokenTable, width, tokenCount, stateBoundary, stateCount,
                rowIndex, valueBound]
              Empty.elim ∘
            ![(#27 : Semiterm ℒₒᵣ Empty 34), #28, #29, #30, #31, #32,
              #26, #25, #24, #23, #22, #21, #20, #19, #18, #17,
              #16, #15, #14, #13, #12, #11, #10, #9, #8, #7,
              #6, #5, #4, #3, #2, #1, #0])
          Empty.elim)
        compactParserClosedAdjacentStepRowDef.val ↔
      CompactParserClosedAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary stateCount rowIndex
          (compactParserClosedAdjacentStepRowOfValues
            currentStart currentFinish currentTokensFinish currentTasksFinish
            currentTokensBoundary currentTokensCount
            currentTasksBoundary currentTasksCount
            currentTokensBoundarySize currentTasksBoundarySize
            nextStart nextFinish nextTokensFinish nextTasksFinish
            nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
            nextTokensBoundarySize nextTasksBoundarySize
            slot0 slot1 slot2 slot3 slot4 slot5 slot6) := by
    have henv :
        (Semiterm.val
            ![slot6, slot5, slot4, slot3, slot2, slot1, slot0,
              nextTasksBoundarySize, nextTokensBoundarySize,
              nextTasksCount, nextTasksBoundary, nextTokensCount,
              nextTokensBoundary, nextTasksFinish, nextTokensFinish,
              nextFinish, nextStart,
              currentTasksBoundarySize, currentTokensBoundarySize,
              currentTasksCount, currentTasksBoundary, currentTokensCount,
              currentTokensBoundary, currentTasksFinish,
              currentTokensFinish, currentFinish, currentStart,
              tokenTable, width, tokenCount, stateBoundary, stateCount,
              rowIndex, valueBound]
            Empty.elim ∘
          ![(#27 : Semiterm ℒₒᵣ Empty 34), #28, #29, #30, #31, #32,
            #26, #25, #24, #23, #22, #21, #20, #19, #18, #17,
            #16, #15, #14, #13, #12, #11, #10, #9, #8, #7,
            #6, #5, #4, #3, #2, #1, #0]) =
          compactParserSyntaxAdjacentStepRowEnvironment
            tokenTable width tokenCount stateBoundary stateCount rowIndex
              (compactParserClosedAdjacentStepRowOfValues
                currentStart currentFinish currentTokensFinish
                currentTasksFinish currentTokensBoundary currentTokensCount
                currentTasksBoundary currentTasksCount
                currentTokensBoundarySize currentTasksBoundarySize
                nextStart nextFinish nextTokensFinish nextTasksFinish
                nextTokensBoundary nextTokensCount nextTasksBoundary
                nextTasksCount nextTokensBoundarySize nextTasksBoundarySize
                slot0 slot1 slot2 slot3 slot4 slot5 slot6) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactParserClosedAdjacentStepRowDef_spec
      tokenTable width tokenCount stateBoundary stateCount rowIndex _
  have hcurrentStatus
      (slot6 slot5 slot4 slot3 slot2 slot1 slot0
        nextTasksBoundarySize nextTokensBoundarySize
        nextTasksCount nextTasksBoundary nextTokensCount nextTokensBoundary
        nextTasksFinish nextTokensFinish nextFinish nextStart
        currentTasksBoundarySize currentTokensBoundarySize
        currentTasksCount currentTasksBoundary currentTokensCount
        currentTokensBoundary currentTasksFinish currentTokensFinish
        currentFinish currentStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![slot6, slot5, slot4, slot3, slot2, slot1, slot0,
                nextTasksBoundarySize, nextTokensBoundarySize,
                nextTasksCount, nextTasksBoundary, nextTokensCount,
                nextTokensBoundary, nextTasksFinish, nextTokensFinish,
                nextFinish, nextStart,
                currentTasksBoundarySize, currentTokensBoundarySize,
                currentTasksCount, currentTasksBoundary, currentTokensCount,
                currentTokensBoundary, currentTasksFinish,
                currentTokensFinish, currentFinish, currentStart,
                tokenTable, width, tokenCount, stateBoundary, stateCount,
                rowIndex, valueBound]
              Empty.elim ∘
            ![(#27 : Semiterm ℒₒᵣ Empty 34), #28, #29, #23, #25, #33])
          Empty.elim)
        compactBinaryNatStatusValidBoundedDef.val ↔
      CompactBinaryNatStatusValidBounded
        tokenTable width tokenCount currentTasksFinish currentFinish
          valueBound := by
    have henv :
        (Semiterm.val
            ![slot6, slot5, slot4, slot3, slot2, slot1, slot0,
              nextTasksBoundarySize, nextTokensBoundarySize,
              nextTasksCount, nextTasksBoundary, nextTokensCount,
              nextTokensBoundary, nextTasksFinish, nextTokensFinish,
              nextFinish, nextStart,
              currentTasksBoundarySize, currentTokensBoundarySize,
              currentTasksCount, currentTasksBoundary, currentTokensCount,
              currentTokensBoundary, currentTasksFinish,
              currentTokensFinish, currentFinish, currentStart,
              tokenTable, width, tokenCount, stateBoundary, stateCount,
              rowIndex, valueBound]
            Empty.elim ∘
          ![(#27 : Semiterm ℒₒᵣ Empty 34), #28, #29, #23, #25, #33]) =
        ![tokenTable, width, tokenCount, currentTasksFinish, currentFinish,
          valueBound] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactBinaryNatStatusValidBoundedDef_spec
      tokenTable width tokenCount currentTasksFinish currentFinish valueBound
  have hnextStatus
      (slot6 slot5 slot4 slot3 slot2 slot1 slot0
        nextTasksBoundarySize nextTokensBoundarySize
        nextTasksCount nextTasksBoundary nextTokensCount nextTokensBoundary
        nextTasksFinish nextTokensFinish nextFinish nextStart
        currentTasksBoundarySize currentTokensBoundarySize
        currentTasksCount currentTasksBoundary currentTokensCount
        currentTokensBoundary currentTasksFinish currentTokensFinish
        currentFinish currentStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![slot6, slot5, slot4, slot3, slot2, slot1, slot0,
                nextTasksBoundarySize, nextTokensBoundarySize,
                nextTasksCount, nextTasksBoundary, nextTokensCount,
                nextTokensBoundary, nextTasksFinish, nextTokensFinish,
                nextFinish, nextStart,
                currentTasksBoundarySize, currentTokensBoundarySize,
                currentTasksCount, currentTasksBoundary, currentTokensCount,
                currentTokensBoundary, currentTasksFinish,
                currentTokensFinish, currentFinish, currentStart,
                tokenTable, width, tokenCount, stateBoundary, stateCount,
                rowIndex, valueBound]
              Empty.elim ∘
            ![(#27 : Semiterm ℒₒᵣ Empty 34), #28, #29, #13, #15, #33])
          Empty.elim)
        compactBinaryNatStatusValidBoundedDef.val ↔
      CompactBinaryNatStatusValidBounded
        tokenTable width tokenCount nextTasksFinish nextFinish valueBound := by
    have henv :
        (Semiterm.val
            ![slot6, slot5, slot4, slot3, slot2, slot1, slot0,
              nextTasksBoundarySize, nextTokensBoundarySize,
              nextTasksCount, nextTasksBoundary, nextTokensCount,
              nextTokensBoundary, nextTasksFinish, nextTokensFinish,
              nextFinish, nextStart,
              currentTasksBoundarySize, currentTokensBoundarySize,
              currentTasksCount, currentTasksBoundary, currentTokensCount,
              currentTokensBoundary, currentTasksFinish,
              currentTokensFinish, currentFinish, currentStart,
              tokenTable, width, tokenCount, stateBoundary, stateCount,
              rowIndex, valueBound]
            Empty.elim ∘
          ![(#27 : Semiterm ℒₒᵣ Empty 34), #28, #29, #13, #15, #33]) =
        ![tokenTable, width, tokenCount, nextTasksFinish, nextFinish,
          valueBound] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactBinaryNatStatusValidBoundedDef_spec
      tokenTable width tokenCount nextTasksFinish nextFinish valueBound
  simp [compactParserClosedAdjacentRowBoundedDef,
    CompactParserClosedAdjacentRowBounded, hrow, hcurrentStatus, hnextStatus]

@[simp] theorem compactParserClosedAdjacentRowsBoundedGraphDef_spec
    (tokenTable width tokenCount stateBoundary stateCount rowCount
      tableWidth valueBound : Nat) :
    compactParserClosedAdjacentRowsBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, rowCount,
          tableWidth, valueBound] ↔
      CompactParserClosedAdjacentRowsBoundedGraph
        tokenTable width tokenCount stateBoundary stateCount rowCount
          tableWidth valueBound := by
  have hrow (rowIndex : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![rowIndex, tokenTable, width, tokenCount, stateBoundary,
                stateCount, rowCount, tableWidth, valueBound]
              Empty.elim ∘
            ![(#1 : Semiterm ℒₒᵣ Empty 9), #2, #3, #4, #5, #0, #8])
          Empty.elim)
        compactParserClosedAdjacentRowBoundedDef.val ↔
      CompactParserClosedAdjacentRowBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex
          valueBound := by
    have henv :
        (Semiterm.val
            ![rowIndex, tokenTable, width, tokenCount, stateBoundary,
              stateCount, rowCount, tableWidth, valueBound]
            Empty.elim ∘
          ![(#1 : Semiterm ℒₒᵣ Empty 9), #2, #3, #4, #5, #0, #8]) =
        ![tokenTable, width, tokenCount, stateBoundary, stateCount,
          rowIndex, valueBound] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactParserClosedAdjacentRowBoundedDef_spec
      tokenTable width tokenCount stateBoundary stateCount rowIndex valueBound
  simp [compactParserClosedAdjacentRowsBoundedGraphDef,
    CompactParserClosedAdjacentRowsBoundedGraph, hrow]

theorem compactParserClosedAdjacentRowBoundedDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserClosedAdjacentRowBoundedDef.val := by
  simp [compactParserClosedAdjacentRowBoundedDef]

theorem compactParserClosedAdjacentRowsBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserClosedAdjacentRowsBoundedGraphDef.val := by
  simp [compactParserClosedAdjacentRowsBoundedGraphDef]

#print axioms compactParserClosedAdjacentRowBoundedDef_spec
#print axioms compactParserClosedAdjacentRowsBoundedGraphDef_spec
#print axioms compactParserClosedAdjacentRowBoundedDef_sigmaZero
#print axioms compactParserClosedAdjacentRowsBoundedGraphDef_sigmaZero

end FoundationCompactNumericListedDirectParserClosedAdjacentStepBoundedFormula
