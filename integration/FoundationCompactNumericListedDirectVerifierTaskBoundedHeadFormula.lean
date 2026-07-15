import integration.FoundationCompactNumericListedDirectVerifierTaskFieldRealization

/-!
# Explicit bounded head graph for verifier-task lists

The list-row graph existentially binds fourteen coordinates for each task.
This module exposes those coordinates for row zero, while retaining the exact
fixed-width boundary entries and the complete task-core graph.  Under the real
typed row layouts, the exposed row is proved to be the actual task-list head.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization

def CompactNumericVerifierTaskBoundedHead
    (tokenTable width tokenCount taskBoundary valueBound : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness) : Prop :=
  coordinates.start ≤ valueBound ∧
    coordinates.finish ≤ valueBound ∧
    coordinates.tag ≤ valueBound ∧
    coordinates.gammaFinish ≤ valueBound ∧
    coordinates.gammaCount ≤ valueBound ∧
    coordinates.gammaBoundary ≤ valueBound ∧
    coordinates.firstFinish ≤ valueBound ∧
    coordinates.firstCount ≤ valueBound ∧
    coordinates.secondFinish ≤ valueBound ∧
    coordinates.secondCount ≤ valueBound ∧
    coordinates.witnessFinish ≤ valueBound ∧
    coordinates.witnessCount ≤ valueBound ∧
    coordinates.suffixCount ≤ valueBound ∧
    sizeWitness.gammaBoundarySize ≤ valueBound ∧
    CompactFixedWidthEntry taskBoundary tokenCount 0 coordinates.start ∧
    CompactFixedWidthEntry taskBoundary tokenCount 1 coordinates.finish ∧
    CompactNumericVerifierTaskCoreGraph tokenTable width tokenCount
      coordinates sizeWitness

def compactNumericVerifierTaskBoundedHeadDef :
    𝚺₀.Semisentence 19 := .mkSigma
  “tokenTable width tokenCount taskBoundary valueBound
      start finish tag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount gammaBoundarySize.
    start ≤ valueBound ∧
    finish ≤ valueBound ∧
    tag ≤ valueBound ∧
    gammaFinish ≤ valueBound ∧
    gammaCount ≤ valueBound ∧
    gammaBoundary ≤ valueBound ∧
    firstFinish ≤ valueBound ∧
    firstCount ≤ valueBound ∧
    secondFinish ≤ valueBound ∧
    secondCount ≤ valueBound ∧
    witnessFinish ≤ valueBound ∧
    witnessCount ≤ valueBound ∧
    suffixCount ≤ valueBound ∧
    gammaBoundarySize ≤ valueBound ∧
    !(compactFixedWidthEntryDef) taskBoundary tokenCount 0 start ∧
    !(compactFixedWidthEntryDef) taskBoundary tokenCount 1 finish ∧
    !(compactNumericVerifierTaskCoreGraphDef)
      tokenTable width tokenCount
      start finish tag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount gammaBoundarySize”

def compactNumericVerifierTaskBoundedHeadEnvironment
    (tokenTable width tokenCount taskBoundary valueBound
      start finish tag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount gammaBoundarySize : Nat) :
    Fin 19 → Nat :=
  ![tokenTable, width, tokenCount, taskBoundary, valueBound,
    start, finish, tag, gammaFinish, gammaCount, gammaBoundary,
    firstFinish, firstCount, secondFinish, secondCount,
    witnessFinish, witnessCount, suffixCount, gammaBoundarySize]

@[simp] theorem compactNumericVerifierTaskBoundedHeadDef_spec
    (tokenTable width tokenCount taskBoundary valueBound
      start finish tag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount gammaBoundarySize : Nat) :
    compactNumericVerifierTaskBoundedHeadDef.val.Evalb
        (compactNumericVerifierTaskBoundedHeadEnvironment
          tokenTable width tokenCount taskBoundary valueBound
          start finish tag gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish secondCount
          witnessFinish witnessCount suffixCount gammaBoundarySize) ↔
      CompactNumericVerifierTaskBoundedHead
        tokenTable width tokenCount taskBoundary valueBound
        (compactNumericVerifierTaskRowCoordinatesOf
          start finish tag gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish secondCount
          witnessFinish witnessCount suffixCount)
        { gammaBoundarySize := gammaBoundarySize } := by
  let env := compactNumericVerifierTaskBoundedHeadEnvironment
    tokenTable width tokenCount taskBoundary valueBound
    start finish tag gammaFinish gammaCount gammaBoundary
    firstFinish firstCount secondFinish secondCount
    witnessFinish witnessCount suffixCount gammaBoundarySize
  change compactNumericVerifierTaskBoundedHeadDef.val.Evalb env ↔ _
  have hcore :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2,
              #5, #6, #7, #8, #9, #10, #11, #12, #13, #14,
              #15, #16, #17, #18])
          Empty.elim) compactNumericVerifierTaskCoreGraphDef.val ↔
        CompactNumericVerifierTaskCoreGraph tokenTable width tokenCount
          (compactNumericVerifierTaskRowCoordinatesOf
            start finish tag gammaFinish gammaCount gammaBoundary
            firstFinish firstCount secondFinish secondCount
            witnessFinish witnessCount suffixCount)
          { gammaBoundarySize := gammaBoundarySize } := by
    have henv :
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2,
            #5, #6, #7, #8, #9, #10, #11, #12, #13, #14,
            #15, #16, #17, #18]) =
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
  have hcoreExplicit :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount, taskBoundary, valueBound,
                start, finish, tag, gammaFinish, gammaCount, gammaBoundary,
                firstFinish, firstCount, secondFinish, secondCount,
                witnessFinish, witnessCount, suffixCount, gammaBoundarySize]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2,
              #5, #6, #7, #8, #9, #10, #11, #12, #13, #14,
              #15, #16, #17, #18])
          Empty.elim) compactNumericVerifierTaskCoreGraphDef.val ↔
        CompactNumericVerifierTaskCoreGraph tokenTable width tokenCount
          { start := start
            finish := finish
            tag := tag
            gammaFinish := gammaFinish
            gammaCount := gammaCount
            gammaBoundary := gammaBoundary
            firstFinish := firstFinish
            firstCount := firstCount
            secondFinish := secondFinish
            secondCount := secondCount
            witnessFinish := witnessFinish
            witnessCount := witnessCount
            suffixCount := suffixCount }
          { gammaBoundarySize := gammaBoundarySize } := by
    simpa [env, compactNumericVerifierTaskBoundedHeadEnvironment,
      compactNumericVerifierTaskRowCoordinatesOf] using hcore
  simp [compactNumericVerifierTaskBoundedHeadDef,
    CompactNumericVerifierTaskBoundedHead,
    compactNumericVerifierTaskBoundedHeadEnvironment, env, hcoreExplicit,
    compactNumericVerifierTaskRowCoordinatesOf]

theorem compactNumericVerifierTaskBoundedHeadDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierTaskBoundedHeadDef.val := by
  simp [compactNumericVerifierTaskBoundedHeadDef]

theorem CompactNumericVerifierTaskBoundedRow.exists_boundedHead
    {tokenTable width tokenCount taskBoundary valueBound : Nat}
    (hrow : CompactNumericVerifierTaskBoundedRow
      tokenTable width tokenCount taskBoundary valueBound 0) :
    ∃ coordinates : CompactNumericVerifierTaskRowCoordinates,
    ∃ sizeWitness : CompactNumericVerifierTaskSizeWitness,
      CompactNumericVerifierTaskBoundedHead
        tokenTable width tokenCount taskBoundary valueBound
        coordinates sizeWitness := by
  rcases hrow with
    ⟨start, hstart, finish, hfinish, tag, htag,
      gammaFinish, hgammaFinish, gammaCount, hgammaCount,
      gammaBoundary, hgammaBoundary,
      firstFinish, hfirstFinish, firstCount, hfirstCount,
      secondFinish, hsecondFinish, secondCount, hsecondCount,
      witnessFinish, hwitnessFinish, witnessCount, hwitnessCount,
      suffixCount, hsuffixCount,
      gammaBoundarySize, hgammaBoundarySize,
      hstartEntry, hfinishEntry, hcore⟩
  refine ⟨compactNumericVerifierTaskRowCoordinatesOf
      start finish tag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount,
    { gammaBoundarySize := gammaBoundarySize }, ?_⟩
  exact ⟨hstart, hfinish, htag, hgammaFinish, hgammaCount,
    hgammaBoundary, hfirstFinish, hfirstCount,
    hsecondFinish, hsecondCount, hwitnessFinish, hwitnessCount,
    hsuffixCount, hgammaBoundarySize,
    hstartEntry,
    by simpa [compactNumericVerifierTaskRowCoordinatesOf] using hfinishEntry,
    hcore⟩

theorem CompactNumericVerifierTaskBoundedHead.to_boundedRow
    {tokenTable width tokenCount taskBoundary valueBound : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    (hhead : CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount taskBoundary valueBound
      coordinates sizeWitness) :
    CompactNumericVerifierTaskBoundedRow
      tokenTable width tokenCount taskBoundary valueBound 0 := by
  rcases hhead with
    ⟨hstart, hfinish, htag, hgammaFinish, hgammaCount,
      hgammaBoundary, hfirstFinish, hfirstCount,
      hsecondFinish, hsecondCount, hwitnessFinish, hwitnessCount,
      hsuffixCount, hgammaBoundarySize,
      hstartEntry, hfinishEntry, hcore⟩
  exact ⟨coordinates.start, hstart,
    coordinates.finish, hfinish,
    coordinates.tag, htag,
    coordinates.gammaFinish, hgammaFinish,
    coordinates.gammaCount, hgammaCount,
    coordinates.gammaBoundary, hgammaBoundary,
    coordinates.firstFinish, hfirstFinish,
    coordinates.firstCount, hfirstCount,
    coordinates.secondFinish, hsecondFinish,
    coordinates.secondCount, hsecondCount,
    coordinates.witnessFinish, hwitnessFinish,
    coordinates.witnessCount, hwitnessCount,
    coordinates.suffixCount, hsuffixCount,
    sizeWitness.gammaBoundarySize, hgammaBoundarySize,
    hstartEntry, by simpa using hfinishEntry, hcore⟩

theorem CompactNumericVerifierTaskBoundedHead.core
    {tokenTable width tokenCount taskBoundary valueBound : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    (hhead : CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount taskBoundary valueBound
      coordinates sizeWitness) :
    CompactNumericVerifierTaskCoreGraph
      tokenTable width tokenCount coordinates sizeWitness := by
  rcases hhead with
    ⟨_hstart, _hfinish, _htag, _hgammaFinish, _hgammaCount,
      _hgammaBoundary, _hfirstFinish, _hfirstCount,
      _hsecondFinish, _hsecondCount, _hwitnessFinish, _hwitnessCount,
      _hsuffixCount, _hgammaBoundarySize,
      _hstartEntry, _hfinishEntry, hcore⟩
  exact hcore

theorem CompactNumericVerifierTaskBoundedHead.realize_actualHeadWithFields
    {tokenTable width tokenCount taskBoundary valueBound : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    {tasks : List CompactNumericVerifierTask}
    (hhead : CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount taskBoundary valueBound
      coordinates sizeWitness)
    (hnonempty : 0 < tasks.length)
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        taskBoundary tasks) :
    ∃ task : CompactNumericVerifierTask,
      task = tasks.getI 0 ∧
      task.1 = coordinates.tag ∧
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        coordinates.start coordinates.finish task ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        coordinates.gammaBoundary task.2.1 ∧
      task.2.1.length = coordinates.gammaCount ∧
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        coordinates.gammaFinish coordinates.firstFinish task.2.2.1 ∧
      task.2.2.1.length = coordinates.firstCount ∧
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        coordinates.firstFinish coordinates.secondFinish task.2.2.2.1 ∧
      task.2.2.2.1.length = coordinates.secondCount ∧
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        coordinates.secondFinish coordinates.witnessFinish
          task.2.2.2.2.1 ∧
      task.2.2.2.2.1.length = coordinates.witnessCount ∧
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        coordinates.witnessFinish coordinates.finish
          task.2.2.2.2.2 ∧
      task.2.2.2.2.2.length = coordinates.suffixCount := by
  rcases hhead with
    ⟨_hstartBound, _hfinishBound, _htagBound,
      _hgammaFinishBound, _hgammaCountBound, _hgammaBoundaryBound,
      _hfirstFinishBound, _hfirstCountBound,
      _hsecondFinishBound, _hsecondCountBound,
      _hwitnessFinishBound, _hwitnessCountBound,
      _hsuffixCountBound, _hgammaBoundarySizeBound,
      hstartEntry, hfinishEntry, hcore⟩
  rcases hrows 0 hnonempty with
    ⟨actualStart, _hactualStartBound,
      actualFinish, _hactualFinishBound,
      hactualStartEntry, hactualFinishEntry, hactualLayout⟩
  have hstart : coordinates.start = actualStart :=
    (CompactFixedWidthEntry.value_eq_tableValue hstartEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue hactualStartEntry).symm
  have hfinish : coordinates.finish = actualFinish :=
    (CompactFixedWidthEntry.value_eq_tableValue hfinishEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue hactualFinishEntry).symm
  subst actualStart
  subst actualFinish
  rcases CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
      hcore with
    ⟨task, htaskLayout, htag,
      hgammaRows, hgammaLength,
      hfirstLayout, hfirstLength,
      hsecondLayout, hsecondLength,
      hwitnessLayout, hwitnessLength,
      hsuffixLayout, hsuffixLength⟩
  have htask : task = tasks.getI 0 :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hcore hactualLayout htaskLayout
  exact ⟨task, htask, htag, htaskLayout,
    hgammaRows, hgammaLength,
    hfirstLayout, hfirstLength,
    hsecondLayout, hsecondLength,
    hwitnessLayout, hwitnessLength,
    hsuffixLayout, hsuffixLength⟩

#print axioms compactNumericVerifierTaskBoundedHeadDef_spec
#print axioms compactNumericVerifierTaskBoundedHeadDef_sigmaZero
#print axioms CompactNumericVerifierTaskBoundedRow.exists_boundedHead
#print axioms CompactNumericVerifierTaskBoundedHead.to_boundedRow
#print axioms CompactNumericVerifierTaskBoundedHead.core
#print axioms CompactNumericVerifierTaskBoundedHead.realize_actualHeadWithFields

end FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
