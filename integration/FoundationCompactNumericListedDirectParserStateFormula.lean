import integration.FoundationCompactNumericListedDirectParserStateLayout
import integration.FoundationCompactNumericListedDirectSyntaxTaskRowRealization

/-!
# Pure numeric core formula for one compact parser state

The state row is split into its remaining-token list, three-cell syntax-task
list, and status interval using only numeric coordinates.  The status payload
is left to the parser-step formulas; this module realizes both list fields and
all structural boundaries without taking a typed parser state as input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserStateFormula

open FoundationCompactParserDirectTrace
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectParserStateLayout

structure CompactUnifiedParserStateRowCoordinates where
  start : Nat
  finish : Nat
  tokensFinish : Nat
  tasksFinish : Nat
  tokensBoundary : Nat
  tokensCount : Nat
  tasksBoundary : Nat
  tasksCount : Nat

structure CompactUnifiedParserStateCoreSizeWitness where
  tokensBoundarySize : Nat
  tasksBoundarySize : Nat

def compactUnifiedParserStateRowCoordinatesOf
    (start finish tokensFinish tasksFinish tokensBoundary tokensCount
      tasksBoundary tasksCount : Nat) :
    CompactUnifiedParserStateRowCoordinates where
  start := start
  finish := finish
  tokensFinish := tokensFinish
  tasksFinish := tasksFinish
  tokensBoundary := tokensBoundary
  tokensCount := tokensCount
  tasksBoundary := tasksBoundary
  tasksCount := tasksCount

def CompactUnifiedParserStateCoreGraph
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness) : Prop :=
  CompactAdditiveProductSplit
      tokenCount coordinates.start coordinates.tokensFinish
        coordinates.finish ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount coordinates.start coordinates.tokensCount
        coordinates.tokensFinish coordinates.tokensBoundary ∧
    CompactAdditiveUnitBoundaryRows
      tokenCount coordinates.tokensCount coordinates.tokensBoundary ∧
    CompactAdditiveProductSplit
      tokenCount coordinates.tokensFinish coordinates.tasksFinish
        coordinates.finish ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount coordinates.tokensFinish
        coordinates.tasksCount coordinates.tasksFinish
        coordinates.tasksBoundary ∧
    CompactAdditiveTripleBoundaryRows
      tokenCount coordinates.tasksCount coordinates.tasksBoundary ∧
    sizeWitness.tokensBoundarySize = Nat.size coordinates.tokensBoundary ∧
    sizeWitness.tokensBoundarySize ≤
      (coordinates.tokensCount + 1) * tokenCount ∧
    sizeWitness.tasksBoundarySize = Nat.size coordinates.tasksBoundary ∧
    sizeWitness.tasksBoundarySize ≤
      (coordinates.tasksCount + 1) * tokenCount

def compactUnifiedParserStateCoreGraphDef :
    𝚺₀.Semisentence 13 := .mkSigma
  “tokenTable width tokenCount
      start finish tokensFinish tasksFinish
      tokensBoundary tokensCount tasksBoundary tasksCount
      tokensBoundarySize tasksBoundarySize.
    !(compactAdditiveProductSplitDef)
      tokenCount start tokensFinish finish ∧
    !(compactAdditiveStructuredListLayoutDef)
      tokenTable width tokenCount start tokensCount
        tokensFinish tokensBoundary ∧
    !(compactAdditiveUnitBoundaryRowsDef)
      tokenCount tokensCount tokensBoundary ∧
    !(compactAdditiveProductSplitDef)
      tokenCount tokensFinish tasksFinish finish ∧
    !(compactAdditiveStructuredListLayoutDef)
      tokenTable width tokenCount tokensFinish tasksCount
        tasksFinish tasksBoundary ∧
    !(compactAdditiveTripleBoundaryRowsDef)
      tokenCount tasksCount tasksBoundary ∧
    !(compactNatSizeDef) tokensBoundarySize tokensBoundary ∧
    tokensBoundarySize ≤ (tokensCount + 1) * tokenCount ∧
    !(compactNatSizeDef) tasksBoundarySize tasksBoundary ∧
    tasksBoundarySize ≤ (tasksCount + 1) * tokenCount”

def compactUnifiedParserStateCoreFormulaEnvironment
    (tokenTable width tokenCount
      start finish tokensFinish tasksFinish
      tokensBoundary tokensCount tasksBoundary tasksCount
      tokensBoundarySize tasksBoundarySize : Nat) : Fin 13 → Nat :=
  ![tokenTable, width, tokenCount,
    start, finish, tokensFinish, tasksFinish,
    tokensBoundary, tokensCount, tasksBoundary, tasksCount,
    tokensBoundarySize, tasksBoundarySize]

@[simp] theorem compactUnifiedParserStateCoreGraphDef_spec
    (tokenTable width tokenCount
      start finish tokensFinish tasksFinish
      tokensBoundary tokensCount tasksBoundary tasksCount
      tokensBoundarySize tasksBoundarySize : Nat) :
    compactUnifiedParserStateCoreGraphDef.val.Evalb
        (compactUnifiedParserStateCoreFormulaEnvironment
          tokenTable width tokenCount
          start finish tokensFinish tasksFinish
          tokensBoundary tokensCount tasksBoundary tasksCount
          tokensBoundarySize tasksBoundarySize) ↔
      CompactUnifiedParserStateCoreGraph tokenTable width tokenCount
        (compactUnifiedParserStateRowCoordinatesOf
          start finish tokensFinish tasksFinish
          tokensBoundary tokensCount tasksBoundary tasksCount)
        { tokensBoundarySize := tokensBoundarySize
          tasksBoundarySize := tasksBoundarySize } := by
  let env := compactUnifiedParserStateCoreFormulaEnvironment
    tokenTable width tokenCount
    start finish tokensFinish tasksFinish
    tokensBoundary tokensCount tasksBoundary tasksCount
    tokensBoundarySize tasksBoundarySize
  change compactUnifiedParserStateCoreGraphDef.val.Evalb env ↔ _
  have houterEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#2 : Semiterm ℒₒᵣ Empty 13), #3, #5, #4]) =
        ![tokenCount, start, tokensFinish, finish] := by
    funext index
    fin_cases index <;> rfl
  have htokensLayoutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2, #3, #8, #5, #7]) =
        ![tokenTable, width, tokenCount,
          start, tokensCount, tokensFinish, tokensBoundary] := by
    funext index
    fin_cases index <;> rfl
  have htokensRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#2 : Semiterm ℒₒᵣ Empty 13), #8, #7]) =
        ![tokenCount, tokensCount, tokensBoundary] := by
    funext index
    fin_cases index <;> rfl
  have hinnerEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#2 : Semiterm ℒₒᵣ Empty 13), #5, #6, #4]) =
        ![tokenCount, tokensFinish, tasksFinish, finish] := by
    funext index
    fin_cases index <;> rfl
  have htasksLayoutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2, #5, #10, #6, #9]) =
        ![tokenTable, width, tokenCount,
          tokensFinish, tasksCount, tasksFinish, tasksBoundary] := by
    funext index
    fin_cases index <;> rfl
  have htasksRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#2 : Semiterm ℒₒᵣ Empty 13), #10, #9]) =
        ![tokenCount, tasksCount, tasksBoundary] := by
    funext index
    fin_cases index <;> rfl
  have htokensSizeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#11 : Semiterm ℒₒᵣ Empty 13), #7]) =
        ![tokensBoundarySize, tokensBoundary] := by
    funext index
    fin_cases index <;> rfl
  have htasksSizeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#12 : Semiterm ℒₒᵣ Empty 13), #9]) =
        ![tasksBoundarySize, tasksBoundary] := by
    funext index
    fin_cases index <;> rfl
  have htokenCountValue : env 2 = tokenCount := rfl
  have htokensCountValue : env 8 = tokensCount := rfl
  have htasksCountValue : env 10 = tasksCount := rfl
  have htokensBoundarySizeValue : env 11 = tokensBoundarySize := rfl
  have htasksBoundarySizeValue : env 12 = tasksBoundarySize := rfl
  simp [compactUnifiedParserStateCoreGraphDef,
    compactUnifiedParserStateRowCoordinatesOf,
    CompactUnifiedParserStateCoreGraph,
    houterEnv, htokensLayoutEnv, htokensRowsEnv,
    hinnerEnv, htasksLayoutEnv, htasksRowsEnv,
    htokensSizeEnv, htasksSizeEnv,
    htokenCountValue, htokensCountValue, htasksCountValue,
    htokensBoundarySizeValue, htasksBoundarySizeValue]

theorem compactUnifiedParserStateCoreGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserStateCoreGraphDef.val := by
  simp [compactUnifiedParserStateCoreGraphDef]

structure CompactUnifiedParserStateCoreFixedLayout
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (tokens : List Nat) (tasks : List CompactSyntaxTask) : Prop where
  tokensCount_eq : coordinates.tokensCount = tokens.length
  tasksCount_eq : coordinates.tasksCount = tasks.length
  outerSplit : CompactAdditiveProductSplit
    tokenCount coordinates.start coordinates.tokensFinish coordinates.finish
  tokensLayout : CompactAdditiveStructuredListLayout
    tokenTable width tokenCount coordinates.start coordinates.tokensCount
      coordinates.tokensFinish coordinates.tokensBoundary
  tokensRows : CompactAdditiveStructuredListElementRowLayouts
    CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      coordinates.tokensBoundary tokens
  innerSplit : CompactAdditiveProductSplit
    tokenCount coordinates.tokensFinish coordinates.tasksFinish
      coordinates.finish
  tasksLayout : CompactAdditiveStructuredListLayout
    tokenTable width tokenCount coordinates.tokensFinish
      coordinates.tasksCount coordinates.tasksFinish
      coordinates.tasksBoundary
  tasksRows : CompactAdditiveStructuredListElementRowLayouts
    CompactSyntaxTaskDirectLayout tokenTable width tokenCount
      coordinates.tasksBoundary tasks
  tokensBoundarySize : Nat.size coordinates.tokensBoundary ≤
    (coordinates.tokensCount + 1) * tokenCount
  tasksBoundarySize : Nat.size coordinates.tasksBoundary ≤
    (coordinates.tasksCount + 1) * tokenCount

theorem CompactUnifiedParserStateDirectLayout.toCoreGraph
    {tokenTable width tokenCount start finish : Nat}
    {state : CompactUnifiedParserState}
    (hlayout : CompactUnifiedParserStateDirectLayout
      tokenTable width tokenCount start finish state) :
    ∃ coordinates sizeWitness,
      coordinates.start = start ∧
      coordinates.finish = finish ∧
      CompactUnifiedParserStateCoreGraph
        tokenTable width tokenCount coordinates sizeWitness ∧
      CompactBinaryNatStreamStatusDirectLayout
        tokenTable width tokenCount coordinates.tasksFinish
          coordinates.finish state.2.2 := by
  rcases hlayout with
    ⟨tokensFinish, tasksFinish, tokensBoundary, tasksBoundary,
      houter, htokensLayout, htokensRows,
      hinner, htasksLayout, htasksRows, hstatus,
      htokensSize, htasksSize⟩
  let coordinates : CompactUnifiedParserStateRowCoordinates :=
    { start := start
      finish := finish
      tokensFinish := tokensFinish
      tasksFinish := tasksFinish
      tokensBoundary := tokensBoundary
      tokensCount := state.1.length
      tasksBoundary := tasksBoundary
      tasksCount := state.2.1.length }
  let sizeWitness : CompactUnifiedParserStateCoreSizeWitness :=
    { tokensBoundarySize := Nat.size tokensBoundary
      tasksBoundarySize := Nat.size tasksBoundary }
  refine ⟨coordinates, sizeWitness, rfl, rfl, ?_, hstatus⟩
  exact ⟨houter, htokensLayout,
    CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
      htokensRows,
    hinner, htasksLayout,
    CompactAdditiveStructuredListElementRowLayouts.tripleBoundaryRows
      htasksRows,
    rfl, htokensSize, rfl, htasksSize⟩

theorem CompactUnifiedParserStateCoreGraph.realize
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactUnifiedParserStateRowCoordinates}
    {sizeWitness : CompactUnifiedParserStateCoreSizeWitness}
    (hgraph : CompactUnifiedParserStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    ∃ tokens tasks,
      CompactUnifiedParserStateCoreFixedLayout
        tokenTable width tokenCount coordinates tokens tasks := by
  let tokens := compactAdditiveNatListRowValues
    tokenTable width tokenCount
      coordinates.tokensBoundary coordinates.tokensCount
  let tasks := compactAdditiveSyntaxTaskListRowValues
    tokenTable width tokenCount
      coordinates.tasksBoundary coordinates.tasksCount
  rcases hgraph with
    ⟨houter, htokensLayout, htokensRows,
      hinner, htasksLayout, htasksRows,
      htokensSizeEq, htokensSize,
      htasksSizeEq, htasksSize⟩
  refine ⟨tokens, tasks,
    { tokensCount_eq := by simp [tokens]
      tasksCount_eq := by simp [tasks]
      outerSplit := houter
      tokensLayout := htokensLayout
      tokensRows := ?_
      innerSplit := hinner
      tasksLayout := htasksLayout
      tasksRows := ?_
      tokensBoundarySize := ?_
      tasksBoundarySize := ?_ }⟩
  · exact CompactAdditiveUnitBoundaryRows.realizedNatRows htokensRows
  · exact CompactAdditiveTripleBoundaryRows.realizedTaskRows htasksRows
  · rw [← htokensSizeEq]
    exact htokensSize
  · rw [← htasksSizeEq]
    exact htasksSize

theorem CompactUnifiedParserStateCoreFixedLayout.withStatus
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactUnifiedParserStateRowCoordinates}
    {tokens : List Nat} {tasks : List CompactSyntaxTask}
    {status : Option (Option (List Nat))}
    (hcore : CompactUnifiedParserStateCoreFixedLayout
      tokenTable width tokenCount coordinates tokens tasks)
    (hstatus : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount coordinates.tasksFinish
        coordinates.finish status) :
    CompactUnifiedParserStateDirectLayout
      tokenTable width tokenCount coordinates.start coordinates.finish
        (tokens, tasks, status) := by
  have htokensLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount coordinates.start tokens.length
        coordinates.tokensFinish coordinates.tokensBoundary := by
    simpa only [hcore.tokensCount_eq] using hcore.tokensLayout
  have htasksLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount coordinates.tokensFinish tasks.length
        coordinates.tasksFinish coordinates.tasksBoundary := by
    simpa only [hcore.tasksCount_eq] using hcore.tasksLayout
  have htokensSize : Nat.size coordinates.tokensBoundary ≤
      (tokens.length + 1) * tokenCount := by
    simpa only [hcore.tokensCount_eq] using hcore.tokensBoundarySize
  have htasksSize : Nat.size coordinates.tasksBoundary ≤
      (tasks.length + 1) * tokenCount := by
    simpa only [hcore.tasksCount_eq] using hcore.tasksBoundarySize
  exact ⟨coordinates.tokensFinish, coordinates.tasksFinish,
    coordinates.tokensBoundary, coordinates.tasksBoundary,
    hcore.outerSplit, htokensLayout, hcore.tokensRows,
    hcore.innerSplit, htasksLayout, hcore.tasksRows,
    hstatus, htokensSize, htasksSize⟩

def compactUnifiedParserStateCoreFormulaEnvironmentOf
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness) : Fin 13 → Nat :=
  compactUnifiedParserStateCoreFormulaEnvironment
    tokenTable width tokenCount
    coordinates.start coordinates.finish
    coordinates.tokensFinish coordinates.tasksFinish
    coordinates.tokensBoundary coordinates.tokensCount
    coordinates.tasksBoundary coordinates.tasksCount
    sizeWitness.tokensBoundarySize sizeWitness.tasksBoundarySize

@[simp] theorem compactUnifiedParserStateCoreGraphDef_environmentOf_iff
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness) :
    compactUnifiedParserStateCoreGraphDef.val.Evalb
        (compactUnifiedParserStateCoreFormulaEnvironmentOf
          tokenTable width tokenCount coordinates sizeWitness) ↔
      CompactUnifiedParserStateCoreGraph
        tokenTable width tokenCount coordinates sizeWitness := by
  simpa [compactUnifiedParserStateCoreFormulaEnvironmentOf,
    compactUnifiedParserStateRowCoordinatesOf] using
    compactUnifiedParserStateCoreGraphDef_spec
      tokenTable width tokenCount
      coordinates.start coordinates.finish
      coordinates.tokensFinish coordinates.tasksFinish
      coordinates.tokensBoundary coordinates.tokensCount
      coordinates.tasksBoundary coordinates.tasksCount
      sizeWitness.tokensBoundarySize sizeWitness.tasksBoundarySize

#print axioms compactUnifiedParserStateCoreGraphDef_spec
#print axioms compactUnifiedParserStateCoreGraphDef_sigmaZero
#print axioms CompactUnifiedParserStateDirectLayout.toCoreGraph
#print axioms CompactUnifiedParserStateCoreGraph.realize
#print axioms CompactUnifiedParserStateCoreFixedLayout.withStatus
#print axioms compactUnifiedParserStateCoreGraphDef_environmentOf_iff

end FoundationCompactNumericListedDirectParserStateFormula
