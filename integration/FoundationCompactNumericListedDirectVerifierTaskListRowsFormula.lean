import integration.FoundationCompactNumericListedDirectVerifierTaskFormula

/-!
# Bounded row formula for verifier task lists

Every task row receives fourteen bounded coordinates.  Two coordinates are
fixed by the public task-boundary table; the remaining coordinates describe
the exact task core.  A shared `valueBound = 2 ^ tableWidth` keeps every
quantifier bounded without introducing a hidden per-row witness code.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTaskListRowsFormula

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectVerifierTaskFormula

def CompactNumericVerifierTaskBoundedRow
    (tokenTable width tokenCount taskBoundary valueBound rowIndex : Nat) :
    Prop :=
  ∃ start, start ≤ valueBound ∧
  ∃ finish, finish ≤ valueBound ∧
  ∃ tag, tag ≤ valueBound ∧
  ∃ gammaFinish, gammaFinish ≤ valueBound ∧
  ∃ gammaCount, gammaCount ≤ valueBound ∧
  ∃ gammaBoundary, gammaBoundary ≤ valueBound ∧
  ∃ firstFinish, firstFinish ≤ valueBound ∧
  ∃ firstCount, firstCount ≤ valueBound ∧
  ∃ secondFinish, secondFinish ≤ valueBound ∧
  ∃ secondCount, secondCount ≤ valueBound ∧
  ∃ witnessFinish, witnessFinish ≤ valueBound ∧
  ∃ witnessCount, witnessCount ≤ valueBound ∧
  ∃ suffixCount, suffixCount ≤ valueBound ∧
  ∃ gammaBoundarySize, gammaBoundarySize ≤ valueBound ∧
    CompactFixedWidthEntry taskBoundary tokenCount rowIndex start ∧
    CompactFixedWidthEntry taskBoundary tokenCount (rowIndex + 1) finish ∧
    CompactNumericVerifierTaskCoreGraph tokenTable width tokenCount
      (compactNumericVerifierTaskRowCoordinatesOf
        start finish tag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish secondCount
        witnessFinish witnessCount suffixCount)
      { gammaBoundarySize := gammaBoundarySize }

def CompactNumericVerifierTaskListRowsGraph
    (tokenTable width tokenCount taskBoundary taskCount
      tableWidth valueBound : Nat) : Prop :=
  valueBound = 2 ^ tableWidth ∧
    ∀ rowIndex < taskCount,
      CompactNumericVerifierTaskBoundedRow
        tokenTable width tokenCount taskBoundary valueBound rowIndex

def compactNumericVerifierTaskBoundedRowDef :
    𝚺₀.Semisentence 6 := .mkSigma
  “tokenTable width tokenCount taskBoundary valueBound rowIndex.
    ∃ start <⁺ valueBound,
    ∃ finish <⁺ valueBound,
    ∃ tag <⁺ valueBound,
    ∃ gammaFinish <⁺ valueBound,
    ∃ gammaCount <⁺ valueBound,
    ∃ gammaBoundary <⁺ valueBound,
    ∃ firstFinish <⁺ valueBound,
    ∃ firstCount <⁺ valueBound,
    ∃ secondFinish <⁺ valueBound,
    ∃ secondCount <⁺ valueBound,
    ∃ witnessFinish <⁺ valueBound,
    ∃ witnessCount <⁺ valueBound,
    ∃ suffixCount <⁺ valueBound,
    ∃ gammaBoundarySize <⁺ valueBound,
      !(compactFixedWidthEntryDef)
        taskBoundary tokenCount rowIndex start ∧
      !(compactFixedWidthEntryDef)
        taskBoundary tokenCount (rowIndex + 1) finish ∧
      !(compactNumericVerifierTaskCoreGraphDef)
        tokenTable width tokenCount
        start finish tag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish secondCount
        witnessFinish witnessCount suffixCount gammaBoundarySize”

@[simp] theorem compactNumericVerifierTaskBoundedRowDef_spec
    (tokenTable width tokenCount taskBoundary valueBound rowIndex : Nat) :
    compactNumericVerifierTaskBoundedRowDef.val.Evalb
        ![tokenTable, width, tokenCount, taskBoundary,
          valueBound, rowIndex] ↔
      CompactNumericVerifierTaskBoundedRow
        tokenTable width tokenCount taskBoundary valueBound rowIndex := by
  have hcore
      (gammaBoundarySize suffixCount witnessCount witnessFinish
        secondCount secondFinish firstCount firstFinish
        gammaBoundary gammaCount gammaFinish tag finish start : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![gammaBoundarySize, suffixCount, witnessCount, witnessFinish,
                secondCount, secondFinish, firstCount, firstFinish,
                gammaBoundary, gammaCount, gammaFinish, tag, finish, start,
                tokenTable, width, tokenCount, taskBoundary,
                valueBound, rowIndex]
              Empty.elim ∘
            ![(#14 : Semiterm ℒₒᵣ Empty 20), #15, #16,
              #13, #12, #11, #10, #9, #8, #7, #6, #5, #4,
              #3, #2, #1, #0])
          Empty.elim)
        compactNumericVerifierTaskCoreGraphDef.val ↔
      CompactNumericVerifierTaskCoreGraph tokenTable width tokenCount
        (compactNumericVerifierTaskRowCoordinatesOf
          start finish tag gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish secondCount
          witnessFinish witnessCount suffixCount)
        { gammaBoundarySize := gammaBoundarySize } := by
    have henv :
        (Semiterm.val
            ![gammaBoundarySize, suffixCount, witnessCount, witnessFinish,
              secondCount, secondFinish, firstCount, firstFinish,
              gammaBoundary, gammaCount, gammaFinish, tag, finish, start,
              tokenTable, width, tokenCount, taskBoundary,
              valueBound, rowIndex]
            Empty.elim ∘
          ![(#14 : Semiterm ℒₒᵣ Empty 20), #15, #16,
            #13, #12, #11, #10, #9, #8, #7, #6, #5, #4,
            #3, #2, #1, #0]) =
          compactNumericVerifierTaskCoreFormulaEnvironment
            tokenTable width tokenCount
            start finish tag gammaFinish gammaCount gammaBoundary
            firstFinish firstCount secondFinish secondCount
            witnessFinish witnessCount suffixCount gammaBoundarySize := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactNumericVerifierTaskCoreGraphDef_spec
      tokenTable width tokenCount
      start finish tag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount gammaBoundarySize
  simp [compactNumericVerifierTaskBoundedRowDef,
    CompactNumericVerifierTaskBoundedRow, hcore]

def compactNumericVerifierTaskListRowsGraphDef :
    𝚺₀.Semisentence 7 := .mkSigma
  “tokenTable width tokenCount taskBoundary taskCount tableWidth valueBound.
    !expDef valueBound tableWidth ∧
    ∀ rowIndex < taskCount,
      !(compactNumericVerifierTaskBoundedRowDef)
        tokenTable width tokenCount taskBoundary valueBound rowIndex”

@[simp] theorem compactNumericVerifierTaskListRowsGraphDef_spec
    (tokenTable width tokenCount taskBoundary taskCount
      tableWidth valueBound : Nat) :
    compactNumericVerifierTaskListRowsGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, taskBoundary,
          taskCount, tableWidth, valueBound] ↔
      CompactNumericVerifierTaskListRowsGraph
        tokenTable width tokenCount taskBoundary taskCount
        tableWidth valueBound := by
  have hrow (rowIndex : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![rowIndex, tokenTable, width, tokenCount, taskBoundary,
                taskCount, tableWidth, valueBound]
              Empty.elim ∘
            ![(#1 : Semiterm ℒₒᵣ Empty 8), #2, #3, #4, #7, #0])
          Empty.elim)
        compactNumericVerifierTaskBoundedRowDef.val ↔
      CompactNumericVerifierTaskBoundedRow
        tokenTable width tokenCount taskBoundary valueBound rowIndex := by
    have henv :
        (Semiterm.val
            ![rowIndex, tokenTable, width, tokenCount, taskBoundary,
              taskCount, tableWidth, valueBound]
            Empty.elim ∘
          ![(#1 : Semiterm ℒₒᵣ Empty 8), #2, #3, #4, #7, #0]) =
          ![tokenTable, width, tokenCount, taskBoundary,
            valueBound, rowIndex] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactNumericVerifierTaskBoundedRowDef_spec
      tokenTable width tokenCount taskBoundary valueBound rowIndex
  simp [compactNumericVerifierTaskListRowsGraphDef,
    CompactNumericVerifierTaskListRowsGraph, hrow]

theorem compactNumericVerifierTaskBoundedRowDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierTaskBoundedRowDef.val := by
  simp [compactNumericVerifierTaskBoundedRowDef]

theorem compactNumericVerifierTaskListRowsGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierTaskListRowsGraphDef.val := by
  simp [compactNumericVerifierTaskListRowsGraphDef]

def compactNumericVerifierTaskRowTableWidth
    (width tokenCount : Nat) : Nat :=
  (tokenCount + 1) * tokenCount + width + tokenCount + 3

theorem CompactAdditiveStructuredListElementRowLayouts.taskListRowsGraph
    {tokenTable width tokenCount taskBoundary : Nat}
    {tasks : List CompactNumericVerifierTask}
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
      taskBoundary tasks) :
    CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount taskBoundary tasks.length
      (compactNumericVerifierTaskRowTableWidth width tokenCount)
      (2 ^ compactNumericVerifierTaskRowTableWidth width tokenCount) := by
  let tableWidth :=
    compactNumericVerifierTaskRowTableWidth width tokenCount
  refine ⟨rfl, ?_⟩
  intro rowIndex hrowIndex
  rcases hrows rowIndex hrowIndex with
    ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, hlayout⟩
  rcases CompactNumericVerifierTaskDirectLayout.toCoreGraph hlayout with
    ⟨coordinates, sizeWitness,
      hstart, hfinish, _htag, hcore⟩
  have hbounds := CompactNumericVerifierTaskCoreGraph.bounds hcore
  have htokenWidth : tokenCount ≤ tableWidth := by
    dsimp only [tableWidth, compactNumericVerifierTaskRowTableWidth]
    omega
  have hpublicWidth : width ≤ tableWidth := by
    dsimp only [tableWidth, compactNumericVerifierTaskRowTableWidth]
    omega
  have hareaWidth : (tokenCount + 1) * tokenCount ≤ tableWidth := by
    dsimp only [tableWidth, compactNumericVerifierTaskRowTableWidth]
    omega
  have hwidthPower : tableWidth ≤ 2 ^ tableWidth :=
    Nat.le_of_lt tableWidth.lt_two_pow_self
  have hsmall {value : Nat} (hvalue : value ≤ tokenCount) :
      value ≤ 2 ^ tableWidth :=
    (hvalue.trans htokenWidth).trans hwidthPower
  have htagSize : Nat.size coordinates.tag ≤ tableWidth :=
    hbounds.tag_size_le.trans hpublicWidth
  have htagBound : coordinates.tag ≤ 2 ^ tableWidth :=
    (Nat.size_le.mp htagSize).le
  have hgammaArea :
      (coordinates.gammaCount + 1) * tokenCount ≤
        (tokenCount + 1) * tokenCount :=
    Nat.mul_le_mul_right tokenCount
      (Nat.add_le_add_right hbounds.gammaCount_le 1)
  have hgammaBoundarySize :
      Nat.size coordinates.gammaBoundary ≤ tableWidth :=
    hbounds.gammaBoundary_size_le.trans
      (hgammaArea.trans hareaWidth)
  have hgammaBoundaryBound :
      coordinates.gammaBoundary ≤ 2 ^ tableWidth :=
    (Nat.size_le.mp hgammaBoundarySize).le
  have hgammaSizeBound :
      sizeWitness.gammaBoundarySize ≤ 2 ^ tableWidth :=
    (hbounds.gammaBoundarySize_le.trans
      (hgammaArea.trans hareaWidth)).trans hwidthPower
  refine ⟨coordinates.start, hsmall hbounds.start_le,
    coordinates.finish, hsmall hbounds.finish_le,
    coordinates.tag, htagBound,
    coordinates.gammaFinish, hsmall hbounds.gammaFinish_le,
    coordinates.gammaCount, hsmall hbounds.gammaCount_le,
    coordinates.gammaBoundary, hgammaBoundaryBound,
    coordinates.firstFinish, hsmall hbounds.firstFinish_le,
    coordinates.firstCount, hsmall hbounds.firstCount_le,
    coordinates.secondFinish, hsmall hbounds.secondFinish_le,
    coordinates.secondCount, hsmall hbounds.secondCount_le,
    coordinates.witnessFinish, hsmall hbounds.witnessFinish_le,
    coordinates.witnessCount, hsmall hbounds.witnessCount_le,
    coordinates.suffixCount, hsmall hbounds.suffixCount_le,
    sizeWitness.gammaBoundarySize, hgammaSizeBound, ?_, ?_, hcore⟩
  · simpa only [hstart] using hleftEntry
  · simpa only [hfinish] using hrightEntry

#print axioms compactNumericVerifierTaskBoundedRowDef_spec
#print axioms compactNumericVerifierTaskListRowsGraphDef_spec
#print axioms compactNumericVerifierTaskBoundedRowDef_sigmaZero
#print axioms compactNumericVerifierTaskListRowsGraphDef_sigmaZero
#print axioms CompactAdditiveStructuredListElementRowLayouts.taskListRowsGraph

end FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
