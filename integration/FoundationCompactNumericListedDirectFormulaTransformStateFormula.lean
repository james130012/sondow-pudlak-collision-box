import integration.FoundationCompactNumericListedDirectFormulaTransformStateLayout
import integration.FoundationCompactNumericListedDirectParserStateFormula
import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidity

/-!
# Bounded core formula for one formula-transform state row

The row is split into the real parser-state interval and the emitted-output
list.  All boundaries and their bit sizes are explicit natural witnesses.
The formula is Delta-zero and contains no appeal to the executable transform
as an opaque predicate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformStateFormula

open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectParserStateLayout
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateLayout

structure CompactFormulaTransformStateRowCoordinates where
  start : Nat
  finish : Nat
  parserFinish : Nat
  parserTokensFinish : Nat
  parserTasksFinish : Nat
  parserTokensBoundary : Nat
  parserTokensCount : Nat
  parserTasksBoundary : Nat
  parserTasksCount : Nat
  outputBoundary : Nat
  outputCount : Nat

structure CompactFormulaTransformStateCoreSizeWitness where
  parserTokensBoundarySize : Nat
  parserTasksBoundarySize : Nat
  outputBoundarySize : Nat

def CompactFormulaTransformStateRowCoordinates.parser
    (coordinates : CompactFormulaTransformStateRowCoordinates) :
    CompactUnifiedParserStateRowCoordinates :=
  { start := coordinates.start
    finish := coordinates.parserFinish
    tokensFinish := coordinates.parserTokensFinish
    tasksFinish := coordinates.parserTasksFinish
    tokensBoundary := coordinates.parserTokensBoundary
    tokensCount := coordinates.parserTokensCount
    tasksBoundary := coordinates.parserTasksBoundary
    tasksCount := coordinates.parserTasksCount }

def CompactFormulaTransformStateCoreSizeWitness.parser
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    CompactUnifiedParserStateCoreSizeWitness :=
  { tokensBoundarySize := sizeWitness.parserTokensBoundarySize
    tasksBoundarySize := sizeWitness.parserTasksBoundarySize }

def compactFormulaTransformStateRowCoordinatesOf
    (start finish parserFinish parserTokensFinish parserTasksFinish
      parserTokensBoundary parserTokensCount parserTasksBoundary
      parserTasksCount outputBoundary outputCount : Nat) :
    CompactFormulaTransformStateRowCoordinates :=
  { start := start
    finish := finish
    parserFinish := parserFinish
    parserTokensFinish := parserTokensFinish
    parserTasksFinish := parserTasksFinish
    parserTokensBoundary := parserTokensBoundary
    parserTokensCount := parserTokensCount
    parserTasksBoundary := parserTasksBoundary
    parserTasksCount := parserTasksCount
    outputBoundary := outputBoundary
    outputCount := outputCount }

def CompactFormulaTransformStateCoreGraph
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) : Prop :=
  CompactAdditiveProductSplit
      tokenCount coordinates.start coordinates.parserFinish
        coordinates.finish ∧
    CompactUnifiedParserStateCoreGraph
      tokenTable width tokenCount coordinates.parser sizeWitness.parser ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount coordinates.parserFinish
        coordinates.outputCount coordinates.finish
        coordinates.outputBoundary ∧
    CompactAdditiveUnitBoundaryRows
      tokenCount coordinates.outputCount coordinates.outputBoundary ∧
    sizeWitness.outputBoundarySize = Nat.size coordinates.outputBoundary ∧
    sizeWitness.outputBoundarySize ≤
      (coordinates.outputCount + 1) * tokenCount

def compactFormulaTransformStateCoreGraphDef :
    𝚺₀.Semisentence 17 := .mkSigma
  “tokenTable width tokenCount
      start finish parserFinish
      parserTokensFinish parserTasksFinish
      parserTokensBoundary parserTokensCount
      parserTasksBoundary parserTasksCount
      outputBoundary outputCount
      parserTokensBoundarySize parserTasksBoundarySize outputBoundarySize.
    !(compactAdditiveProductSplitDef)
      tokenCount start parserFinish finish ∧
    !(compactUnifiedParserStateCoreGraphDef)
      tokenTable width tokenCount
      start parserFinish parserTokensFinish parserTasksFinish
      parserTokensBoundary parserTokensCount
      parserTasksBoundary parserTasksCount
      parserTokensBoundarySize parserTasksBoundarySize ∧
    !(compactAdditiveStructuredListLayoutDef)
      tokenTable width tokenCount parserFinish outputCount finish
        outputBoundary ∧
    !(compactAdditiveUnitBoundaryRowsDef)
      tokenCount outputCount outputBoundary ∧
    !(compactNatSizeDef) outputBoundarySize outputBoundary ∧
    outputBoundarySize ≤ (outputCount + 1) * tokenCount”

def compactFormulaTransformStateCoreFormulaEnvironment
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    Fin 17 → Nat :=
  ![tokenTable, width, tokenCount,
    coordinates.start, coordinates.finish, coordinates.parserFinish,
    coordinates.parserTokensFinish, coordinates.parserTasksFinish,
    coordinates.parserTokensBoundary, coordinates.parserTokensCount,
    coordinates.parserTasksBoundary, coordinates.parserTasksCount,
    coordinates.outputBoundary, coordinates.outputCount,
    sizeWitness.parserTokensBoundarySize,
    sizeWitness.parserTasksBoundarySize,
    sizeWitness.outputBoundarySize]

@[simp] theorem compactFormulaTransformStateCoreGraphDef_spec
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    compactFormulaTransformStateCoreGraphDef.val.Evalb
        (compactFormulaTransformStateCoreFormulaEnvironment
          tokenTable width tokenCount coordinates sizeWitness) ↔
      CompactFormulaTransformStateCoreGraph
        tokenTable width tokenCount coordinates sizeWitness := by
  let env := compactFormulaTransformStateCoreFormulaEnvironment
    tokenTable width tokenCount coordinates sizeWitness
  change compactFormulaTransformStateCoreGraphDef.val.Evalb env ↔ _
  have houterEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#2 : Semiterm ℒₒᵣ Empty 17), #3, #5, #4]) =
        ![tokenCount, coordinates.start,
          coordinates.parserFinish, coordinates.finish] := by
    funext index
    fin_cases index <;> rfl
  have hparserEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2,
          #3, #5, #6, #7, #8, #9, #10, #11, #14, #15]) =
        compactUnifiedParserStateCoreFormulaEnvironmentOf
          tokenTable width tokenCount coordinates.parser
            sizeWitness.parser := by
    funext index
    fin_cases index <;> rfl
  have houtputLayoutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2,
          #5, #13, #4, #12]) =
        ![tokenTable, width, tokenCount, coordinates.parserFinish,
          coordinates.outputCount, coordinates.finish,
          coordinates.outputBoundary] := by
    funext index
    fin_cases index <;> rfl
  have houtputRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#2 : Semiterm ℒₒᵣ Empty 17), #13, #12]) =
        ![tokenCount, coordinates.outputCount,
          coordinates.outputBoundary] := by
    funext index
    fin_cases index <;> rfl
  have houtputSizeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#16 : Semiterm ℒₒᵣ Empty 17), #12]) =
        ![sizeWitness.outputBoundarySize,
          coordinates.outputBoundary] := by
    funext index
    fin_cases index <;> rfl
  have htokenCountValue : env 2 = tokenCount := rfl
  have houtputCountValue : env 13 = coordinates.outputCount := rfl
  have houtputSizeValue : env 16 =
      sizeWitness.outputBoundarySize := rfl
  simp [compactFormulaTransformStateCoreGraphDef,
    CompactFormulaTransformStateCoreGraph,
    houterEnv, hparserEnv, houtputLayoutEnv,
    houtputRowsEnv, houtputSizeEnv,
    htokenCountValue, houtputCountValue, houtputSizeValue]

theorem compactFormulaTransformStateCoreGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformStateCoreGraphDef.val := by
  simp [compactFormulaTransformStateCoreGraphDef]

structure CompactFormulaTransformStateFixedLayout
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (state : CompactFormulaTransformState) : Prop where
  outerSplit : CompactAdditiveProductSplit
    tokenCount coordinates.start coordinates.parserFinish coordinates.finish
  parserLayout : CompactUnifiedParserStateFixedLayout
    tokenTable width tokenCount coordinates.parser state.1
  outputCount_eq : coordinates.outputCount = state.2.length
  outputLayout : CompactAdditiveStructuredListLayout
    tokenTable width tokenCount coordinates.parserFinish
      coordinates.outputCount coordinates.finish coordinates.outputBoundary
  outputRows : CompactAdditiveStructuredListElementRowLayouts
    CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      coordinates.outputBoundary state.2
  outputBoundarySize : Nat.size coordinates.outputBoundary ≤
    (coordinates.outputCount + 1) * tokenCount

theorem compactFormulaTransformStateDirectLayout_iff_fixedCoordinates
    (tokenTable width tokenCount start finish : Nat)
    (state : CompactFormulaTransformState) :
    CompactFormulaTransformStateDirectLayout
        tokenTable width tokenCount start finish state ↔
      ∃ coordinates : CompactFormulaTransformStateRowCoordinates,
        coordinates.start = start ∧
        coordinates.finish = finish ∧
        CompactFormulaTransformStateFixedLayout
          tokenTable width tokenCount coordinates state := by
  constructor
  · rintro ⟨parserFinish, houter, hparser, houtput⟩
    rcases (compactUnifiedParserStateDirectLayout_iff_fixedCoordinates
      tokenTable width tokenCount start parserFinish state.1).mp hparser with
      ⟨parserCoordinates, hparserStart, hparserFinish, hparserFixed⟩
    rcases houtput with
      ⟨outputBoundary, houtputLayout, houtputRows, houtputSize⟩
    let coordinates : CompactFormulaTransformStateRowCoordinates :=
      { start := start
        finish := finish
        parserFinish := parserFinish
        parserTokensFinish := parserCoordinates.tokensFinish
        parserTasksFinish := parserCoordinates.tasksFinish
        parserTokensBoundary := parserCoordinates.tokensBoundary
        parserTokensCount := parserCoordinates.tokensCount
        parserTasksBoundary := parserCoordinates.tasksBoundary
        parserTasksCount := parserCoordinates.tasksCount
        outputBoundary := outputBoundary
        outputCount := state.2.length }
    have hparserCoordinates : coordinates.parser = parserCoordinates := by
      cases parserCoordinates
      simp_all [coordinates,
        CompactFormulaTransformStateRowCoordinates.parser]
    refine ⟨coordinates, rfl, rfl,
      { outerSplit := houter
        parserLayout := ?_
        outputCount_eq := rfl
        outputLayout := houtputLayout
        outputRows := houtputRows
        outputBoundarySize := houtputSize }⟩
    simpa only [hparserCoordinates] using hparserFixed
  · rintro ⟨coordinates, hstart, hfinish, hlayout⟩
    rw [← hstart, ← hfinish]
    refine ⟨coordinates.parserFinish, hlayout.outerSplit, ?_, ?_⟩
    · exact (compactUnifiedParserStateDirectLayout_iff_fixedCoordinates
        tokenTable width tokenCount coordinates.start
          coordinates.parserFinish state.1).mpr
        ⟨coordinates.parser, rfl, rfl, hlayout.parserLayout⟩
    · refine ⟨coordinates.outputBoundary, ?_, hlayout.outputRows, ?_⟩
      · simpa only [hlayout.outputCount_eq] using hlayout.outputLayout
      · simpa only [hlayout.outputCount_eq] using
          hlayout.outputBoundarySize

theorem CompactFormulaTransformStateFixedLayout.toCoreGraph
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactFormulaTransformStateRowCoordinates}
    {state : CompactFormulaTransformState}
    (hlayout : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount coordinates state) :
    ∃ sizeWitness,
      CompactFormulaTransformStateCoreGraph
        tokenTable width tokenCount coordinates sizeWitness := by
  let sizeWitness : CompactFormulaTransformStateCoreSizeWitness :=
    { parserTokensBoundarySize :=
        Nat.size coordinates.parserTokensBoundary
      parserTasksBoundarySize :=
        Nat.size coordinates.parserTasksBoundary
      outputBoundarySize := Nat.size coordinates.outputBoundary }
  have hparserTokenRows : CompactAdditiveUnitBoundaryRows
      tokenCount coordinates.parser.tokensCount
        coordinates.parser.tokensBoundary := by
    rw [hlayout.parserLayout.tokensCount_eq]
    exact CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
      hlayout.parserLayout.tokensRows
  have hparserTaskRows : CompactAdditiveTripleBoundaryRows
      tokenCount coordinates.parser.tasksCount
        coordinates.parser.tasksBoundary := by
    rw [hlayout.parserLayout.tasksCount_eq]
    exact CompactAdditiveStructuredListElementRowLayouts.tripleBoundaryRows
      hlayout.parserLayout.tasksRows
  have hparserCore : CompactUnifiedParserStateCoreGraph
      tokenTable width tokenCount coordinates.parser sizeWitness.parser := by
    exact ⟨hlayout.parserLayout.outerSplit,
      hlayout.parserLayout.tokensLayout,
      hparserTokenRows,
      hlayout.parserLayout.innerSplit,
      hlayout.parserLayout.tasksLayout,
      hparserTaskRows,
      rfl, hlayout.parserLayout.tokensBoundarySize,
      rfl, hlayout.parserLayout.tasksBoundarySize⟩
  have houtputRows : CompactAdditiveUnitBoundaryRows
      tokenCount coordinates.outputCount coordinates.outputBoundary := by
    rw [hlayout.outputCount_eq]
    exact CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
      hlayout.outputRows
  refine ⟨sizeWitness, hlayout.outerSplit, hparserCore,
    hlayout.outputLayout, houtputRows, rfl, hlayout.outputBoundarySize⟩

theorem CompactFormulaTransformStateDirectLayout.toCoreGraph
    {tokenTable width tokenCount start finish : Nat}
    {state : CompactFormulaTransformState}
    (hlayout : CompactFormulaTransformStateDirectLayout
      tokenTable width tokenCount start finish state) :
    ∃ coordinates sizeWitness,
      coordinates.start = start ∧ coordinates.finish = finish ∧
      CompactFormulaTransformStateCoreGraph
        tokenTable width tokenCount coordinates sizeWitness := by
  rcases (compactFormulaTransformStateDirectLayout_iff_fixedCoordinates
      tokenTable width tokenCount start finish state).mp hlayout with
    ⟨coordinates, hstart, hfinish, hfixed⟩
  rcases hfixed.toCoreGraph with ⟨sizeWitness, hcore⟩
  exact ⟨coordinates, sizeWitness, hstart, hfinish, hcore⟩

structure CompactFormulaTransformStateCoreFixedLayout
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (parserTokens : List Nat) (parserTasks : List CompactSyntaxTask)
    (output : List Nat) : Prop where
  outerSplit : CompactAdditiveProductSplit
    tokenCount coordinates.start coordinates.parserFinish coordinates.finish
  parserCore : CompactUnifiedParserStateCoreFixedLayout
    tokenTable width tokenCount coordinates.parser parserTokens parserTasks
  outputCount_eq : coordinates.outputCount = output.length
  outputLayout : CompactAdditiveStructuredListLayout
    tokenTable width tokenCount coordinates.parserFinish
      coordinates.outputCount coordinates.finish coordinates.outputBoundary
  outputRows : CompactAdditiveStructuredListElementRowLayouts
    CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      coordinates.outputBoundary output
  outputBoundarySize : Nat.size coordinates.outputBoundary ≤
    (coordinates.outputCount + 1) * tokenCount

theorem CompactFormulaTransformStateCoreGraph.realize
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactFormulaTransformStateRowCoordinates}
    {sizeWitness : CompactFormulaTransformStateCoreSizeWitness}
    (hgraph : CompactFormulaTransformStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    ∃ parserTokens parserTasks output,
      CompactFormulaTransformStateCoreFixedLayout
        tokenTable width tokenCount coordinates
          parserTokens parserTasks output := by
  rcases hgraph with
    ⟨houter, hparser, houtputLayout, houtputUnit,
      houtputSizeEq, houtputSize⟩
  rcases hparser.realize with
    ⟨parserTokens, parserTasks, hparserCore⟩
  let output := compactAdditiveNatListRowValues
    tokenTable width tokenCount coordinates.outputBoundary
      coordinates.outputCount
  have houtputRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        coordinates.outputBoundary output :=
    CompactAdditiveUnitBoundaryRows.realizedNatRows houtputUnit
  have houtputCount : coordinates.outputCount = output.length := by
    simp [output]
  have hboundarySize : Nat.size coordinates.outputBoundary ≤
      (coordinates.outputCount + 1) * tokenCount := by
    rw [← houtputSizeEq]
    exact houtputSize
  exact ⟨parserTokens, parserTasks, output,
    { outerSplit := houter
      parserCore := hparserCore
      outputCount_eq := houtputCount
      outputLayout := houtputLayout
      outputRows := houtputRows
      outputBoundarySize := hboundarySize }⟩

theorem CompactFormulaTransformStateCoreFixedLayout.withStatus
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactFormulaTransformStateRowCoordinates}
    {parserTokens : List Nat} {parserTasks : List CompactSyntaxTask}
    {output : List Nat} {status : Option (Option (List Nat))}
    (hcore : CompactFormulaTransformStateCoreFixedLayout
      tokenTable width tokenCount coordinates parserTokens parserTasks output)
    (hstatus : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount coordinates.parserTasksFinish
        coordinates.parserFinish status) :
    CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount coordinates
        ((parserTokens, parserTasks, status), output) := by
  have hparser : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount coordinates.parser
        (parserTokens, parserTasks, status) :=
    { tokensCount_eq := hcore.parserCore.tokensCount_eq
      tasksCount_eq := hcore.parserCore.tasksCount_eq
      outerSplit := hcore.parserCore.outerSplit
      tokensLayout := hcore.parserCore.tokensLayout
      tokensRows := hcore.parserCore.tokensRows
      innerSplit := hcore.parserCore.innerSplit
      tasksLayout := hcore.parserCore.tasksLayout
      tasksRows := hcore.parserCore.tasksRows
      statusLayout := hstatus
      tokensBoundarySize := hcore.parserCore.tokensBoundarySize
      tasksBoundarySize := hcore.parserCore.tasksBoundarySize }
  exact
    { outerSplit := hcore.outerSplit
      parserLayout := hparser
      outputCount_eq := hcore.outputCount_eq
      outputLayout := hcore.outputLayout
      outputRows := hcore.outputRows
      outputBoundarySize := hcore.outputBoundarySize }

theorem CompactFormulaTransformStateCoreGraph.realizeWithStatus
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactFormulaTransformStateRowCoordinates}
    {sizeWitness : CompactFormulaTransformStateCoreSizeWitness}
    {statusWitness : CompactBinaryNatStatusValidityWitness}
    (hgraph : CompactFormulaTransformStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (hstatus : CompactBinaryNatStatusValidRows
      tokenTable width tokenCount coordinates.parserTasksFinish
        coordinates.parserFinish statusWitness) :
    ∃ state : CompactFormulaTransformState,
      CompactFormulaTransformStateFixedLayout
        tokenTable width tokenCount coordinates state := by
  rcases hgraph.realize with
    ⟨parserTokens, parserTasks, output, hcore⟩
  rcases hstatus.realize with ⟨status, hstatusLayout⟩
  exact ⟨((parserTokens, parserTasks, status), output),
    hcore.withStatus hstatusLayout⟩

theorem CompactFormulaTransformStateCoreGraph.realizeWithStatusBounded
    {tokenTable width tokenCount valueBound : Nat}
    {coordinates : CompactFormulaTransformStateRowCoordinates}
    {sizeWitness : CompactFormulaTransformStateCoreSizeWitness}
    (hgraph : CompactFormulaTransformStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (hstatus : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount coordinates.parserTasksFinish
        coordinates.parserFinish valueBound) :
    ∃ state : CompactFormulaTransformState,
      CompactFormulaTransformStateFixedLayout
        tokenTable width tokenCount coordinates state := by
  rcases hstatus with
    ⟨outputStart, _houtputStart, outputBoundary, _houtputBoundary,
      outputBoundarySize, _houtputBoundarySize, outputCount, _houtputCount,
      hvalid⟩
  exact CompactFormulaTransformStateCoreGraph.realizeWithStatus hgraph hvalid

#print axioms compactFormulaTransformStateCoreGraphDef_spec
#print axioms compactFormulaTransformStateCoreGraphDef_sigmaZero
#print axioms compactFormulaTransformStateDirectLayout_iff_fixedCoordinates
#print axioms CompactFormulaTransformStateFixedLayout.toCoreGraph
#print axioms CompactFormulaTransformStateDirectLayout.toCoreGraph
#print axioms CompactFormulaTransformStateCoreGraph.realize
#print axioms CompactFormulaTransformStateCoreFixedLayout.withStatus
#print axioms CompactFormulaTransformStateCoreGraph.realizeWithStatus
#print axioms CompactFormulaTransformStateCoreGraph.realizeWithStatusBounded

end FoundationCompactNumericListedDirectFormulaTransformStateFormula
