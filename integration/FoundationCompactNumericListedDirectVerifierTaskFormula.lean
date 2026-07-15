import integration.FoundationCompactNumericListedDirectVerifierTaskLayout
import integration.FoundationCompactNumericListedDirectNatListListRowsFormula

/-!
# Bounded arithmetic core for one verifier task

The formula exposes the task tag, the nested context list, and the four flat
formula/term/suffix lists.  It is independent of the typed task decoder and
uses only the common token table, bounded cursor witnesses, and direct list
graphs.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTaskFormula

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectNatListListRowsFormula

structure CompactNumericVerifierTaskRowCoordinates where
  start : Nat
  finish : Nat
  tag : Nat
  gammaFinish : Nat
  gammaCount : Nat
  gammaBoundary : Nat
  firstFinish : Nat
  firstCount : Nat
  secondFinish : Nat
  secondCount : Nat
  witnessFinish : Nat
  witnessCount : Nat
  suffixCount : Nat

structure CompactNumericVerifierTaskSizeWitness where
  gammaBoundarySize : Nat

def compactNumericVerifierTaskRowCoordinatesOf
    (start finish tag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount : Nat) :
    CompactNumericVerifierTaskRowCoordinates where
  start := start
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
  suffixCount := suffixCount

def CompactNumericVerifierTaskCoreGraph
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness) : Prop :=
  CompactAdditiveTokenCell tokenTable width tokenCount
      coordinates.start coordinates.tag (coordinates.start + 1) ∧
    CompactAdditiveStructuredListLayout tokenTable width tokenCount
      (coordinates.start + 1) coordinates.gammaCount
      coordinates.gammaFinish coordinates.gammaBoundary ∧
    CompactAdditiveNatListListRowsWellFormed tokenTable width tokenCount
      coordinates.gammaBoundary coordinates.gammaCount ∧
    sizeWitness.gammaBoundarySize = Nat.size coordinates.gammaBoundary ∧
    sizeWitness.gammaBoundarySize ≤
      (coordinates.gammaCount + 1) * tokenCount ∧
    CompactAdditiveNatListSlice tokenTable width tokenCount
      coordinates.gammaFinish coordinates.firstCount
      coordinates.firstFinish ∧
    CompactAdditiveNatListSlice tokenTable width tokenCount
      coordinates.firstFinish coordinates.secondCount
      coordinates.secondFinish ∧
    CompactAdditiveNatListSlice tokenTable width tokenCount
      coordinates.secondFinish coordinates.witnessCount
      coordinates.witnessFinish ∧
    CompactAdditiveNatListSlice tokenTable width tokenCount
      coordinates.witnessFinish coordinates.suffixCount
      coordinates.finish

def compactNumericVerifierTaskCoreGraphDef :
    𝚺₀.Semisentence 17 := .mkSigma
  “tokenTable width tokenCount
      start finish tag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount gammaBoundarySize.
    !(compactAdditiveTokenCellDef)
      tokenTable width tokenCount start tag (start + 1) ∧
    !(compactAdditiveStructuredListLayoutDef)
      tokenTable width tokenCount (start + 1) gammaCount
        gammaFinish gammaBoundary ∧
    !(compactAdditiveNatListListRowsWellFormedDef)
      tokenTable width tokenCount gammaBoundary gammaCount ∧
    !(compactNatSizeDef) gammaBoundarySize gammaBoundary ∧
    gammaBoundarySize ≤ (gammaCount + 1) * tokenCount ∧
    !(compactAdditiveNatListSliceDef)
      tokenTable width tokenCount gammaFinish firstCount firstFinish ∧
    !(compactAdditiveNatListSliceDef)
      tokenTable width tokenCount firstFinish secondCount secondFinish ∧
    !(compactAdditiveNatListSliceDef)
      tokenTable width tokenCount secondFinish witnessCount witnessFinish ∧
    !(compactAdditiveNatListSliceDef)
      tokenTable width tokenCount witnessFinish suffixCount finish”

def compactNumericVerifierTaskCoreFormulaEnvironment
    (tokenTable width tokenCount start finish tag
      gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount gammaBoundarySize : Nat) :
    Fin 17 → Nat :=
  ![tokenTable, width, tokenCount,
    start, finish, tag, gammaFinish, gammaCount, gammaBoundary,
    firstFinish, firstCount, secondFinish, secondCount,
    witnessFinish, witnessCount, suffixCount, gammaBoundarySize]

@[simp] theorem compactNumericVerifierTaskCoreGraphDef_spec
    (tokenTable width tokenCount start finish tag
      gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount gammaBoundarySize : Nat) :
    compactNumericVerifierTaskCoreGraphDef.val.Evalb
        (compactNumericVerifierTaskCoreFormulaEnvironment
          tokenTable width tokenCount start finish tag
          gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish secondCount
          witnessFinish witnessCount suffixCount gammaBoundarySize) ↔
      CompactNumericVerifierTaskCoreGraph tokenTable width tokenCount
        (compactNumericVerifierTaskRowCoordinatesOf
          start finish tag gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish secondCount
          witnessFinish witnessCount suffixCount)
        { gammaBoundarySize := gammaBoundarySize } := by
  let env := compactNumericVerifierTaskCoreFormulaEnvironment
    tokenTable width tokenCount start finish tag
    gammaFinish gammaCount gammaBoundary
    firstFinish firstCount secondFinish secondCount
    witnessFinish witnessCount suffixCount gammaBoundarySize
  change compactNumericVerifierTaskCoreGraphDef.val.Evalb env ↔ _
  have htokenEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2, #3, #5,
          ‘(#3 + 1)’]) =
        ![tokenTable, width, tokenCount, start, tag, start + 1] := by
    funext index
    fin_cases index <;> simp [env,
      compactNumericVerifierTaskCoreFormulaEnvironment]
  have hgammaLayoutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2,
          ‘(#3 + 1)’, #7, #6, #8]) =
        ![tokenTable, width, tokenCount, start + 1,
          gammaCount, gammaFinish, gammaBoundary] := by
    funext index
    fin_cases index <;> simp [env,
      compactNumericVerifierTaskCoreFormulaEnvironment]
  have hgammaRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2, #8, #7]) =
        ![tokenTable, width, tokenCount, gammaBoundary, gammaCount] := by
    funext index
    fin_cases index <;> rfl
  have hsizeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#16 : Semiterm ℒₒᵣ Empty 17), #8]) =
        ![gammaBoundarySize, gammaBoundary] := by
    funext index
    fin_cases index <;> rfl
  have hfirstEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2, #6, #10, #9]) =
        ![tokenTable, width, tokenCount,
          gammaFinish, firstCount, firstFinish] := by
    funext index
    fin_cases index <;> rfl
  have hsecondEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2, #9, #12, #11]) =
        ![tokenTable, width, tokenCount,
          firstFinish, secondCount, secondFinish] := by
    funext index
    fin_cases index <;> rfl
  have hwitnessEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2, #11, #14, #13]) =
        ![tokenTable, width, tokenCount,
          secondFinish, witnessCount, witnessFinish] := by
    funext index
    fin_cases index <;> rfl
  have hsuffixEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2, #13, #15, #4]) =
        ![tokenTable, width, tokenCount,
          witnessFinish, suffixCount, finish] := by
    funext index
    fin_cases index <;> rfl
  have htokenCountValue : env 2 = tokenCount := rfl
  have hgammaCountValue : env 7 = gammaCount := rfl
  have hgammaBoundarySizeValue : env 16 = gammaBoundarySize := rfl
  simp [compactNumericVerifierTaskCoreGraphDef,
    compactNumericVerifierTaskRowCoordinatesOf,
    CompactNumericVerifierTaskCoreGraph,
    htokenEnv, hgammaLayoutEnv, hgammaRowsEnv, hsizeEnv,
    hfirstEnv, hsecondEnv, hwitnessEnv, hsuffixEnv,
    htokenCountValue, hgammaCountValue, hgammaBoundarySizeValue]

theorem compactNumericVerifierTaskCoreGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierTaskCoreGraphDef.val := by
  simp [compactNumericVerifierTaskCoreGraphDef]

theorem CompactNumericVerifierTaskDirectLayout.toCoreGraph
    {tokenTable width tokenCount start finish : Nat}
    {task : CompactNumericVerifierTask}
    (hlayout : CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount start finish task) :
    ∃ coordinates sizeWitness,
      coordinates.start = start ∧
      coordinates.finish = finish ∧
      coordinates.tag = task.1 ∧
      CompactNumericVerifierTaskCoreGraph
        tokenTable width tokenCount coordinates sizeWitness := by
  rcases hlayout with ⟨fieldsStart, htag, hfields⟩
  rcases hfields with
    ⟨gammaFinish, firstFinish, secondFinish, witnessFinish,
      hgamma, hfirst, hsecond, hwitness, hsuffix⟩
  rcases hgamma with
    ⟨gammaBoundary, hgammaLayout, hgammaRows, hgammaSize⟩
  have hfieldsStart : fieldsStart = start + 1 := htag.2.1
  subst fieldsStart
  let coordinates : CompactNumericVerifierTaskRowCoordinates :=
    { start := start
      finish := finish
      tag := task.1
      gammaFinish := gammaFinish
      gammaCount := task.2.1.length
      gammaBoundary := gammaBoundary
      firstFinish := firstFinish
      firstCount := task.2.2.1.length
      secondFinish := secondFinish
      secondCount := task.2.2.2.1.length
      witnessFinish := witnessFinish
      witnessCount := task.2.2.2.2.1.length
      suffixCount := task.2.2.2.2.2.length }
  let sizeWitness : CompactNumericVerifierTaskSizeWitness :=
    { gammaBoundarySize := Nat.size gammaBoundary }
  refine ⟨coordinates, sizeWitness, rfl, rfl, rfl, ?_⟩
  exact ⟨htag, hgammaLayout,
    CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
      hgammaRows,
    rfl, hgammaSize,
    CompactAdditiveNatListDirectLayout.toSlice hfirst,
    CompactAdditiveNatListDirectLayout.toSlice hsecond,
    CompactAdditiveNatListDirectLayout.toSlice hwitness,
    CompactAdditiveNatListDirectLayout.toSlice hsuffix⟩

structure CompactNumericVerifierTaskCoreBounds
    (width tokenCount : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness) : Prop where
  start_le : coordinates.start ≤ tokenCount
  finish_le : coordinates.finish ≤ tokenCount
  tag_size_le : Nat.size coordinates.tag ≤ width
  gammaFinish_le : coordinates.gammaFinish ≤ tokenCount
  gammaCount_le : coordinates.gammaCount ≤ tokenCount
  gammaBoundary_size_le :
    Nat.size coordinates.gammaBoundary ≤
      (coordinates.gammaCount + 1) * tokenCount
  gammaBoundarySize_le :
    sizeWitness.gammaBoundarySize ≤
      (coordinates.gammaCount + 1) * tokenCount
  firstFinish_le : coordinates.firstFinish ≤ tokenCount
  firstCount_le : coordinates.firstCount ≤ tokenCount
  secondFinish_le : coordinates.secondFinish ≤ tokenCount
  secondCount_le : coordinates.secondCount ≤ tokenCount
  witnessFinish_le : coordinates.witnessFinish ≤ tokenCount
  witnessCount_le : coordinates.witnessCount ≤ tokenCount
  suffixCount_le : coordinates.suffixCount ≤ tokenCount

theorem CompactNumericVerifierTaskCoreGraph.bounds
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    (hgraph : CompactNumericVerifierTaskCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    CompactNumericVerifierTaskCoreBounds
      width tokenCount coordinates sizeWitness := by
  rcases hgraph with
    ⟨htag, hgamma, _hgammaRows, hgammaSizeEq, hgammaSize,
      hfirst, hsecond, hwitness, hsuffix⟩
  rcases hgamma with
    ⟨gammaBodyStart, _hgammaBodyStart, hgammaHeader,
      hgammaBoundary⟩
  rcases hfirst with
    ⟨firstBodyStart, _hfirstBodyStart, hfirstHeader, hfirstFinish⟩
  rcases hsecond with
    ⟨secondBodyStart, _hsecondBodyStart, hsecondHeader, hsecondFinish⟩
  rcases hwitness with
    ⟨witnessBodyStart, _hwitnessBodyStart,
      hwitnessHeader, hwitnessFinish⟩
  rcases hsuffix with
    ⟨suffixBodyStart, _hsuffixBodyStart, hsuffixHeader, hsuffixFinish⟩
  have htagSize : Nat.size coordinates.tag ≤ width := htag.2.2.1
  have hstartLt : coordinates.start < tokenCount := htag.1
  have hgammaCountBound :
      gammaBodyStart + coordinates.gammaCount ≤ tokenCount :=
    hgammaHeader.2
  have hfirstBound :
      firstBodyStart + coordinates.firstCount ≤ tokenCount :=
    hfirstHeader.2
  have hsecondBound :
      secondBodyStart + coordinates.secondCount ≤ tokenCount :=
    hsecondHeader.2
  have hwitnessBound :
      witnessBodyStart + coordinates.witnessCount ≤ tokenCount :=
    hwitnessHeader.2
  have hsuffixBound :
      suffixBodyStart + coordinates.suffixCount ≤ tokenCount :=
    hsuffixHeader.2
  have hstart : coordinates.start ≤ tokenCount := by omega
  have hgammaFinish : coordinates.gammaFinish ≤ tokenCount :=
    hgammaBoundary.2.1
  have hgammaCount : coordinates.gammaCount ≤ tokenCount := by
    omega
  have hfirstFinishLe : coordinates.firstFinish ≤ tokenCount := by
    omega
  have hfirstCount : coordinates.firstCount ≤ tokenCount := by
    omega
  have hsecondFinishLe : coordinates.secondFinish ≤ tokenCount := by
    omega
  have hsecondCount : coordinates.secondCount ≤ tokenCount := by
    omega
  have hwitnessFinishLe : coordinates.witnessFinish ≤ tokenCount := by
    omega
  have hwitnessCount : coordinates.witnessCount ≤ tokenCount := by
    omega
  have hfinish : coordinates.finish ≤ tokenCount := by
    omega
  have hsuffixCount : coordinates.suffixCount ≤ tokenCount := by
    omega
  exact
    { start_le := hstart
      finish_le := hfinish
      tag_size_le := htagSize
      gammaFinish_le := hgammaFinish
      gammaCount_le := hgammaCount
      gammaBoundary_size_le := by
        rw [← hgammaSizeEq]
        exact hgammaSize
      gammaBoundarySize_le := hgammaSize
      firstFinish_le := hfirstFinishLe
      firstCount_le := hfirstCount
      secondFinish_le := hsecondFinishLe
      secondCount_le := hsecondCount
      witnessFinish_le := hwitnessFinishLe
      witnessCount_le := hwitnessCount
      suffixCount_le := hsuffixCount }

#print axioms compactNumericVerifierTaskCoreGraphDef_spec
#print axioms compactNumericVerifierTaskCoreGraphDef_sigmaZero
#print axioms CompactNumericVerifierTaskDirectLayout.toCoreGraph
#print axioms CompactNumericVerifierTaskCoreGraph.bounds

end FoundationCompactNumericListedDirectVerifierTaskFormula
