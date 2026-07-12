import integration.FoundationCompactNumericListedDirectParserStateFormula
import integration.FoundationCompactNumericListedDirectParserStateListLayout
import integration.FoundationCompactNumericListedDirectSyntaxTaskBoundaryRigidity

/-!
# Direct bounded lookup of one parser-state row

The state-list boundary table fixes the selected row's start and finish.  The
existing thirteen-variable state core then exposes both list fields and all
internal cursors without taking a typed state as a formula input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserStateAtRows

open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskBoundaryRigidity
open FoundationCompactNumericListedDirectParserStateLayout
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserStateFormula

def CompactUnifiedParserStateAtRows
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness) : Prop :=
  index < stateCount ∧
    CompactFixedWidthEntry
      stateBoundary tokenCount index coordinates.start ∧
    CompactFixedWidthEntry
      stateBoundary tokenCount (index + 1) coordinates.finish ∧
    CompactUnifiedParserStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness

def compactUnifiedParserStateAtRowsDef : 𝚺₀.Semisentence 16 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount index
      start finish tokensFinish tasksFinish
      tokensBoundary tokensCount tasksBoundary tasksCount
      tokensBoundarySize tasksBoundarySize.
    index < stateCount ∧
    !(compactFixedWidthEntryDef)
      stateBoundary tokenCount index start ∧
    !(compactFixedWidthEntryDef)
      stateBoundary tokenCount (index + 1) finish ∧
    !(compactUnifiedParserStateCoreGraphDef)
      tokenTable width tokenCount
      start finish tokensFinish tasksFinish
      tokensBoundary tokensCount tasksBoundary tasksCount
      tokensBoundarySize tasksBoundarySize”

def compactUnifiedParserStateAtRowsEnvironment
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness) : Fin 16 → Nat :=
  ![tokenTable, width, tokenCount, stateBoundary, stateCount, index,
    coordinates.start, coordinates.finish,
    coordinates.tokensFinish, coordinates.tasksFinish,
    coordinates.tokensBoundary, coordinates.tokensCount,
    coordinates.tasksBoundary, coordinates.tasksCount,
    sizeWitness.tokensBoundarySize, sizeWitness.tasksBoundarySize]

@[simp] theorem compactUnifiedParserStateAtRowsDef_spec
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness) :
    compactUnifiedParserStateAtRowsDef.val.Evalb
        (compactUnifiedParserStateAtRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount index
            coordinates sizeWitness) ↔
      CompactUnifiedParserStateAtRows
        tokenTable width tokenCount stateBoundary stateCount index
          coordinates sizeWitness := by
  let env := compactUnifiedParserStateAtRowsEnvironment
    tokenTable width tokenCount stateBoundary stateCount index
      coordinates sizeWitness
  change compactUnifiedParserStateAtRowsDef.val.Evalb env ↔ _
  have hleftEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#3 : Semiterm ℒₒᵣ Empty 16), #2, #5, #6]) =
        ![stateBoundary, tokenCount, index, coordinates.start] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hrightEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#3 : Semiterm ℒₒᵣ Empty 16), #2,
          (‘(#5 + 1)’ : Semiterm ℒₒᵣ Empty 16), #7]) =
        ![stateBoundary, tokenCount, index + 1, coordinates.finish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcoreEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 16), #1, #2,
          #6, #7, #8, #9, #10, #11, #12, #13, #14, #15]) =
        compactUnifiedParserStateCoreFormulaEnvironmentOf
          tokenTable width tokenCount coordinates sizeWitness := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hindexValue : env 5 = index := rfl
  have hstateCountValue : env 4 = stateCount := rfl
  simp [compactUnifiedParserStateAtRowsDef,
    CompactUnifiedParserStateAtRows,
    hleftEnv, hrightEnv, hcoreEnv,
    hindexValue, hstateCountValue]

theorem compactUnifiedParserStateAtRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserStateAtRowsDef.val := by
  simp [compactUnifiedParserStateAtRowsDef]

private theorem structuredList_count_eq_of_same_start
    {tokenTable width tokenCount start
      leftCount leftFinish leftBoundary
      rightCount rightFinish rightBoundary : Nat}
    (hleft : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start leftCount leftFinish leftBoundary)
    (hright : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start rightCount rightFinish rightBoundary) :
    leftCount = rightCount := by
  rcases hleft with ⟨leftBody, _hleftBody, hleftHeader, _hleftBoundary⟩
  rcases hright with
    ⟨rightBody, _hrightBody, hrightHeader, _hrightBoundary⟩
  exact (CompactAdditiveTokenCell.value_eq_tableValue hleftHeader.1).trans
    (CompactAdditiveTokenCell.value_eq_tableValue hrightHeader.1).symm

theorem exists_compactUnifiedParserStateAtRows_with_fixed_layout
    {tokenTable width tokenCount stateBoundary index : Nat}
    {states : List CompactUnifiedParserState}
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hindex : index < states.length) :
    ∃ coordinates sizeWitness,
      CompactUnifiedParserStateAtRows
        tokenTable width tokenCount stateBoundary states.length index
          coordinates sizeWitness ∧
      CompactUnifiedParserStateFixedLayout
        tokenTable width tokenCount coordinates (states.getI index) := by
  rcases hrows index hindex with
    ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, hlayout⟩
  rcases (compactUnifiedParserStateDirectLayout_iff_fixedCoordinates
      tokenTable width tokenCount left right (states.getI index)).mp hlayout with
    ⟨coordinates, hstart, hfinish, hfixed⟩
  let sizeWitness : CompactUnifiedParserStateCoreSizeWitness :=
    { tokensBoundarySize := Nat.size coordinates.tokensBoundary
      tasksBoundarySize := Nat.size coordinates.tasksBoundary }
  have hgraph : CompactUnifiedParserStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness :=
    ⟨hfixed.outerSplit, hfixed.tokensLayout,
      (by
        simpa only [hfixed.tokensCount_eq] using
          (CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
            hfixed.tokensRows)),
      hfixed.innerSplit, hfixed.tasksLayout,
      (by
        simpa only [hfixed.tasksCount_eq] using
          (CompactAdditiveStructuredListElementRowLayouts.tripleBoundaryRows
            hfixed.tasksRows)),
      rfl,
      (by simpa only [hfixed.tokensCount_eq] using
        hfixed.tokensBoundarySize),
      rfl,
      (by simpa only [hfixed.tasksCount_eq] using
        hfixed.tasksBoundarySize)⟩
  refine ⟨coordinates, sizeWitness,
    ⟨hindex, ?_, ?_, hgraph⟩, hfixed⟩
  · simpa only [hstart] using hleftEntry
  · simpa only [hfinish] using hrightEntry

theorem CompactUnifiedParserStateAtRows.fixedLayout_of_rows
    {tokenTable width tokenCount stateBoundary stateCount index : Nat}
    {states : List CompactUnifiedParserState}
    {coordinates : CompactUnifiedParserStateRowCoordinates}
    {sizeWitness : CompactUnifiedParserStateCoreSizeWitness}
    (hcount : states.length = stateCount)
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hat : CompactUnifiedParserStateAtRows
      tokenTable width tokenCount stateBoundary stateCount index
        coordinates sizeWitness) :
    CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount coordinates (states.getI index) := by
  rcases hat with ⟨hindexCoordinates, hstartEntry, hfinishEntry, hgraph⟩
  have hindex : index < states.length := by
    simpa only [hcount] using hindexCoordinates
  rcases hrows index hindex with
    ⟨actualStart, _hactualStart, actualFinish, _hactualFinish,
      hactualStartEntry, hactualFinishEntry, hactualDirect⟩
  have hstartEq : coordinates.start = actualStart :=
    (CompactFixedWidthEntry.value_eq_tableValue hstartEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue hactualStartEntry).symm
  have hfinishEq : coordinates.finish = actualFinish :=
    (CompactFixedWidthEntry.value_eq_tableValue hfinishEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue hactualFinishEntry).symm
  rcases (compactUnifiedParserStateDirectLayout_iff_fixedCoordinates
      tokenTable width tokenCount actualStart actualFinish
        (states.getI index)).mp hactualDirect with
    ⟨actualCoordinates, hactualStartEq, hactualFinishEq, hactual⟩
  have hstartCoordinates :
      coordinates.start = actualCoordinates.start :=
    hstartEq.trans hactualStartEq.symm
  have hfinishCoordinates :
      coordinates.finish = actualCoordinates.finish :=
    hfinishEq.trans hactualFinishEq.symm
  rcases hgraph with
    ⟨houter, htokensLayout, htokensUnit,
      hinner, htasksLayout, htasksTriple,
      htokensSizeEq, htokensSize,
      htasksSizeEq, htasksSize⟩
  have hactualTokensLayoutAtStart : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount coordinates.start
        actualCoordinates.tokensCount actualCoordinates.tokensFinish
        actualCoordinates.tokensBoundary := by
    simpa only [hstartCoordinates] using hactual.tokensLayout
  have htokensCountEq :
      coordinates.tokensCount = actualCoordinates.tokensCount :=
    structuredList_count_eq_of_same_start
      htokensLayout hactualTokensLayoutAtStart
  have hactualTokensUnit : CompactAdditiveUnitBoundaryRows
      tokenCount actualCoordinates.tokensCount
        actualCoordinates.tokensBoundary := by
    simpa only [hactual.tokensCount_eq] using
      (CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hactual.tokensRows)
  have htokensFinishFormula :=
    CompactAdditiveStructuredListLayout.finish_eq_start_add_count
      htokensLayout htokensUnit
  have htokensFinishActual :=
    CompactAdditiveStructuredListLayout.finish_eq_start_add_count
      hactualTokensLayoutAtStart hactualTokensUnit
  have htokensFinishEq :
      coordinates.tokensFinish = actualCoordinates.tokensFinish := by
    omega
  have htokensCountState :
      coordinates.tokensCount = (states.getI index).1.length :=
    htokensCountEq.trans hactual.tokensCount_eq
  have hactualTokensLayoutTyped : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount coordinates.start
        (states.getI index).1.length coordinates.tokensFinish
        actualCoordinates.tokensBoundary := by
    simpa only [hactual.tokensCount_eq, htokensFinishEq] using
      hactualTokensLayoutAtStart
  have htokensRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        coordinates.tokensBoundary (states.getI index).1 :=
    CompactAdditiveStructuredListElementRowLayouts.natRows_on_unitBoundary
      hactualTokensLayoutTyped hactual.tokensRows
      (by simpa only [htokensCountState] using htokensLayout)
      (by simpa only [htokensCountState] using htokensUnit)
  have hactualTasksLayoutAtStart : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount coordinates.tokensFinish
        actualCoordinates.tasksCount actualCoordinates.tasksFinish
        actualCoordinates.tasksBoundary := by
    simpa only [htokensFinishEq] using hactual.tasksLayout
  have htasksCountEq :
      coordinates.tasksCount = actualCoordinates.tasksCount :=
    structuredList_count_eq_of_same_start
      htasksLayout hactualTasksLayoutAtStart
  have hactualTasksTriple : CompactAdditiveTripleBoundaryRows
      tokenCount actualCoordinates.tasksCount actualCoordinates.tasksBoundary := by
    simpa only [hactual.tasksCount_eq] using
      (CompactAdditiveStructuredListElementRowLayouts.tripleBoundaryRows
        hactual.tasksRows)
  have htasksFinishFormula :=
    CompactAdditiveStructuredListLayout.taskFinish_eq_start_add_count
      htasksLayout htasksTriple
  have htasksFinishActual :=
    CompactAdditiveStructuredListLayout.taskFinish_eq_start_add_count
      hactualTasksLayoutAtStart hactualTasksTriple
  have htasksFinishEq :
      coordinates.tasksFinish = actualCoordinates.tasksFinish := by
    omega
  have htasksCountState :
      coordinates.tasksCount = (states.getI index).2.1.length :=
    htasksCountEq.trans hactual.tasksCount_eq
  have hactualTasksLayoutTyped : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount coordinates.tokensFinish
        (states.getI index).2.1.length coordinates.tasksFinish
        actualCoordinates.tasksBoundary := by
    simpa only [hactual.tasksCount_eq, htasksFinishEq] using
      hactualTasksLayoutAtStart
  have htasksRows : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        coordinates.tasksBoundary (states.getI index).2.1 :=
    CompactAdditiveStructuredListElementRowLayouts.taskRows_on_tripleBoundary
      hactualTasksLayoutTyped hactual.tasksRows
      (by simpa only [htasksCountState] using htasksLayout)
      (by simpa only [htasksCountState] using htasksTriple)
  have hstatus : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount coordinates.tasksFinish coordinates.finish
        (states.getI index).2.2 := by
    simpa only [htasksFinishEq, hfinishCoordinates] using hactual.statusLayout
  have htokensBoundarySize : Nat.size coordinates.tokensBoundary ≤
      (coordinates.tokensCount + 1) * tokenCount := by
    rw [← htokensSizeEq]
    exact htokensSize
  have htasksBoundarySize : Nat.size coordinates.tasksBoundary ≤
      (coordinates.tasksCount + 1) * tokenCount := by
    rw [← htasksSizeEq]
    exact htasksSize
  exact
    { tokensCount_eq := htokensCountState
      tasksCount_eq := htasksCountState
      outerSplit := houter
      tokensLayout := htokensLayout
      tokensRows := htokensRows
      innerSplit := hinner
      tasksLayout := htasksLayout
      tasksRows := htasksRows
      statusLayout := hstatus
      tokensBoundarySize := htokensBoundarySize
      tasksBoundarySize := htasksBoundarySize }

theorem exists_compactUnifiedParserStateAtRows_with_status
    {tokenTable width tokenCount stateBoundary index : Nat}
    {states : List CompactUnifiedParserState}
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hindex : index < states.length) :
    ∃ coordinates sizeWitness,
      CompactUnifiedParserStateAtRows
        tokenTable width tokenCount stateBoundary states.length index
          coordinates sizeWitness ∧
      CompactBinaryNatStreamStatusDirectLayout
        tokenTable width tokenCount coordinates.tasksFinish
          coordinates.finish (states.getI index).2.2 := by
  rcases exists_compactUnifiedParserStateAtRows_with_fixed_layout
      hrows hindex with
    ⟨coordinates, sizeWitness, hat, hfixed⟩
  exact ⟨coordinates, sizeWitness, hat, hfixed.statusLayout⟩

theorem exists_compactUnifiedParserStateAtRows_iff
    {tokenTable width tokenCount stateBoundary stateCount index : Nat}
    {states : List CompactUnifiedParserState}
    (hcount : states.length = stateCount)
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states) :
    (∃ coordinates sizeWitness,
        CompactUnifiedParserStateAtRows
          tokenTable width tokenCount stateBoundary stateCount index
            coordinates sizeWitness) ↔
      index < states.length := by
  constructor
  · rintro ⟨coordinates, sizeWitness, hindex, _hleft, _hright, _hcore⟩
    simpa only [hcount] using hindex
  · intro hindex
    rcases exists_compactUnifiedParserStateAtRows_with_status hrows hindex with
      ⟨coordinates, sizeWitness, hat, _hstatus⟩
    refine ⟨coordinates, sizeWitness, ?_⟩
    simpa only [hcount] using hat

#print axioms compactUnifiedParserStateAtRowsDef_spec
#print axioms compactUnifiedParserStateAtRowsDef_sigmaZero
#print axioms exists_compactUnifiedParserStateAtRows_with_fixed_layout
#print axioms CompactUnifiedParserStateAtRows.fixedLayout_of_rows
#print axioms exists_compactUnifiedParserStateAtRows_with_status
#print axioms exists_compactUnifiedParserStateAtRows_iff

end FoundationCompactNumericListedDirectParserStateAtRows
