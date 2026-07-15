import integration.FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula

/-!
# Explicit bounded verifier-task row at an arbitrary index

The verifier task-list graph hides each row's fourteen local coordinates.
This relation exposes the coordinates at a public row index.  It is the
indexed counterpart of the existing head relation and is used to check the
short task prefixes produced by a parse transition.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTaskBoundedAtFormula

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization

def CompactNumericVerifierTaskBoundedAt
    (tokenTable width tokenCount taskBoundary valueBound rowIndex : Nat)
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
    CompactFixedWidthEntry taskBoundary tokenCount
      rowIndex coordinates.start ∧
    CompactFixedWidthEntry taskBoundary tokenCount
      (rowIndex + 1) coordinates.finish ∧
    CompactNumericVerifierTaskCoreGraph tokenTable width tokenCount
      coordinates sizeWitness

def compactNumericVerifierTaskBoundedAtDef :
    𝚺₀.Semisentence 20 := .mkSigma
  “tokenTable width tokenCount taskBoundary valueBound rowIndex
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
    !(compactFixedWidthEntryDef) taskBoundary tokenCount rowIndex start ∧
    !(compactFixedWidthEntryDef)
      taskBoundary tokenCount (rowIndex + 1) finish ∧
    !(compactNumericVerifierTaskCoreGraphDef)
      tokenTable width tokenCount
      start finish tag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount gammaBoundarySize”

def compactNumericVerifierTaskBoundedAtEnvironment
    (tokenTable width tokenCount taskBoundary valueBound rowIndex
      start finish tag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount gammaBoundarySize : Nat) :
    Fin 20 → Nat :=
  ![tokenTable, width, tokenCount, taskBoundary, valueBound, rowIndex,
    start, finish, tag, gammaFinish, gammaCount, gammaBoundary,
    firstFinish, firstCount, secondFinish, secondCount,
    witnessFinish, witnessCount, suffixCount, gammaBoundarySize]

@[simp] theorem compactNumericVerifierTaskBoundedAtDef_spec
    (tokenTable width tokenCount taskBoundary valueBound rowIndex
      start finish tag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount gammaBoundarySize : Nat) :
    compactNumericVerifierTaskBoundedAtDef.val.Evalb
        (compactNumericVerifierTaskBoundedAtEnvironment
          tokenTable width tokenCount taskBoundary valueBound rowIndex
          start finish tag gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish secondCount
          witnessFinish witnessCount suffixCount gammaBoundarySize) ↔
      CompactNumericVerifierTaskBoundedAt
        tokenTable width tokenCount taskBoundary valueBound rowIndex
        (compactNumericVerifierTaskRowCoordinatesOf
          start finish tag gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish secondCount
          witnessFinish witnessCount suffixCount)
        { gammaBoundarySize := gammaBoundarySize } := by
  let env := compactNumericVerifierTaskBoundedAtEnvironment
    tokenTable width tokenCount taskBoundary valueBound rowIndex
    start finish tag gammaFinish gammaCount gammaBoundary
    firstFinish firstCount secondFinish secondCount
    witnessFinish witnessCount suffixCount gammaBoundarySize
  change compactNumericVerifierTaskBoundedAtDef.val.Evalb env ↔ _
  have hstartEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#3 : Semiterm ℒₒᵣ Empty 20), #2, #5, #6]) =
        ![taskBoundary, tokenCount, rowIndex, start] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hfinishEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#3 : Semiterm ℒₒᵣ Empty 20), #2, ‘(#5 + 1)’, #7]) =
        ![taskBoundary, tokenCount, rowIndex + 1, finish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcoreEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 20), #1, #2,
          #6, #7, #8, #9, #10, #11, #12, #13, #14, #15,
          #16, #17, #18, #19]) =
        compactNumericVerifierTaskCoreFormulaEnvironment
          tokenTable width tokenCount
          start finish tag gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish secondCount
          witnessFinish witnessCount suffixCount gammaBoundarySize := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcoreSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 20), #1, #2,
              #6, #7, #8, #9, #10, #11, #12, #13, #14, #15,
              #16, #17, #18, #19])
          Empty.elim) compactNumericVerifierTaskCoreGraphDef.val ↔
        CompactNumericVerifierTaskCoreGraph tokenTable width tokenCount
          (compactNumericVerifierTaskRowCoordinatesOf
            start finish tag gammaFinish gammaCount gammaBoundary
            firstFinish firstCount secondFinish secondCount
            witnessFinish witnessCount suffixCount)
          { gammaBoundarySize := gammaBoundarySize } := by
    rw [hcoreEnv]
    exact compactNumericVerifierTaskCoreGraphDef_spec
      tokenTable width tokenCount
      start finish tag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount gammaBoundarySize
  have hcoreExplicit :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount, taskBoundary, valueBound,
                rowIndex, start, finish, tag, gammaFinish, gammaCount,
                gammaBoundary, firstFinish, firstCount, secondFinish,
                secondCount, witnessFinish, witnessCount, suffixCount,
                gammaBoundarySize]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 20), #1, #2,
              #6, #7, #8, #9, #10, #11, #12, #13, #14, #15,
              #16, #17, #18, #19])
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
    simpa [env, compactNumericVerifierTaskBoundedAtEnvironment,
      compactNumericVerifierTaskRowCoordinatesOf] using hcoreSpec
  simp [compactNumericVerifierTaskBoundedAtDef,
    CompactNumericVerifierTaskBoundedAt,
    compactNumericVerifierTaskBoundedAtEnvironment, env,
    compactNumericVerifierTaskRowCoordinatesOf, hcoreExplicit]

theorem compactNumericVerifierTaskBoundedAtDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierTaskBoundedAtDef.val := by
  simp [compactNumericVerifierTaskBoundedAtDef]

theorem CompactNumericVerifierTaskBoundedRow.exists_boundedAt
    {tokenTable width tokenCount taskBoundary valueBound rowIndex : Nat}
    (hrow : CompactNumericVerifierTaskBoundedRow
      tokenTable width tokenCount taskBoundary valueBound rowIndex) :
    ∃ coordinates : CompactNumericVerifierTaskRowCoordinates,
    ∃ sizeWitness : CompactNumericVerifierTaskSizeWitness,
      CompactNumericVerifierTaskBoundedAt
        tokenTable width tokenCount taskBoundary valueBound rowIndex
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

theorem CompactNumericVerifierTaskBoundedAt.to_boundedRow
    {tokenTable width tokenCount taskBoundary valueBound rowIndex : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    (hat : CompactNumericVerifierTaskBoundedAt
      tokenTable width tokenCount taskBoundary valueBound rowIndex
      coordinates sizeWitness) :
    CompactNumericVerifierTaskBoundedRow
      tokenTable width tokenCount taskBoundary valueBound rowIndex := by
  rcases hat with
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

theorem CompactNumericVerifierTaskBoundedAt.core
    {tokenTable width tokenCount taskBoundary valueBound rowIndex : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    (hat : CompactNumericVerifierTaskBoundedAt
      tokenTable width tokenCount taskBoundary valueBound rowIndex
      coordinates sizeWitness) :
    CompactNumericVerifierTaskCoreGraph
      tokenTable width tokenCount coordinates sizeWitness :=
  hat.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem CompactNumericVerifierTaskBoundedAt.realize_actualAtWithFields
    {tokenTable width tokenCount taskBoundary valueBound rowIndex : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    {tasks : List CompactNumericVerifierTask}
    (hat : CompactNumericVerifierTaskBoundedAt
      tokenTable width tokenCount taskBoundary valueBound rowIndex
      coordinates sizeWitness)
    (hindex : rowIndex < tasks.length)
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        taskBoundary tasks) :
    ∃ task : CompactNumericVerifierTask,
      task = tasks.getI rowIndex ∧
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
  rcases hat with
    ⟨_hstartBound, _hfinishBound, _htagBound,
      _hgammaFinishBound, _hgammaCountBound, _hgammaBoundaryBound,
      _hfirstFinishBound, _hfirstCountBound,
      _hsecondFinishBound, _hsecondCountBound,
      _hwitnessFinishBound, _hwitnessCountBound,
      _hsuffixCountBound, _hgammaBoundarySizeBound,
      hstartEntry, hfinishEntry, hcore⟩
  rcases hrows rowIndex hindex with
    ⟨actualStart, _hactualStartBound,
      actualFinish, _hactualFinishBound,
      hactualStartEntry, hactualFinishEntry, hactualLayout⟩
  have hstart : coordinates.start = actualStart :=
    (CompactFixedWidthEntry.value_eq_tableValue hstartEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualStartEntry).symm
  have hfinish : coordinates.finish = actualFinish :=
    (CompactFixedWidthEntry.value_eq_tableValue hfinishEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualFinishEntry).symm
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
  have htask : task = tasks.getI rowIndex :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hcore hactualLayout htaskLayout
  exact ⟨task, htask, htag, htaskLayout,
    hgammaRows, hgammaLength,
    hfirstLayout, hfirstLength,
    hsecondLayout, hsecondLength,
    hwitnessLayout, hwitnessLength,
    hsuffixLayout, hsuffixLength⟩

#print axioms compactNumericVerifierTaskBoundedAtDef_spec
#print axioms compactNumericVerifierTaskBoundedAtDef_sigmaZero
#print axioms CompactNumericVerifierTaskBoundedRow.exists_boundedAt
#print axioms CompactNumericVerifierTaskBoundedAt.to_boundedRow
#print axioms CompactNumericVerifierTaskBoundedAt.realize_actualAtWithFields

end FoundationCompactNumericListedDirectVerifierTaskBoundedAtFormula
