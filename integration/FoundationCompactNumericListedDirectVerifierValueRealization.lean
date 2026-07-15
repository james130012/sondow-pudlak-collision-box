import integration.FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
import integration.FoundationCompactNumericListedDirectAtomicListRowRealization

/-!
# Realization of verifier value graphs

This module reverses the arithmetic value graphs.  A valid flat natural-list
slice is realized by a typed list with an explicit consecutive boundary table;
the same construction is lifted to nested natural lists and child results.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierValueRealization

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula

def compactAdditiveConsecutiveBoundaryRows
    (bodyStart count : Nat) : List Nat :=
  (List.range (count + 1)).map fun index => bodyStart + index

@[simp] theorem compactAdditiveConsecutiveBoundaryRows_length
    (bodyStart count : Nat) :
    (compactAdditiveConsecutiveBoundaryRows bodyStart count).length =
      count + 1 := by
  simp [compactAdditiveConsecutiveBoundaryRows]

theorem compactAdditiveConsecutiveBoundaryRows_getI
    (bodyStart count index : Nat) (hindex : index ≤ count) :
    (compactAdditiveConsecutiveBoundaryRows bodyStart count).getI index =
      bodyStart + index := by
  rw [List.getI_eq_getElem _ (by simp; omega)]
  simp [compactAdditiveConsecutiveBoundaryRows]

theorem CompactAdditiveBoundaryTable.start_le_finish
    {tokenCount partCount start finish boundaryTable : Nat}
    (hboundary : CompactAdditiveBoundaryTable
      tokenCount partCount start finish boundaryTable) :
    start ≤ finish := by
  have hentry : ∀ index ≤ partCount,
      ∃ cursor,
        CompactFixedWidthEntry boundaryTable tokenCount index cursor ∧
        start ≤ cursor := by
    intro index hindex
    induction index with
    | zero =>
        exact ⟨start, hboundary.2.2.1, Nat.le_refl start⟩
    | succ index ih =>
        have hindexLt : index < partCount := by omega
        rcases ih (by omega) with ⟨cursor, hcursorEntry, hcursor⟩
        rcases hboundary.2.2.2.2 index hindexLt with
          ⟨left, _hleft, right, _hright,
            hleftEntry, hrightEntry, hstrict⟩
        have hleft : cursor = left :=
          (CompactFixedWidthEntry.value_eq_tableValue hcursorEntry).trans
            (CompactFixedWidthEntry.value_eq_tableValue hleftEntry).symm
        exact ⟨right, hrightEntry, by omega⟩
  rcases hentry partCount (by rfl) with
    ⟨cursor, hcursorEntry, hcursor⟩
  have hfinishEntry := hboundary.2.2.2.1
  have hcursorFinish : cursor = finish :=
    (CompactFixedWidthEntry.value_eq_tableValue hcursorEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue hfinishEntry).symm
  omega

theorem CompactAdditiveBoundaryTable.entry_mono
    {tokenCount partCount start finish boundaryTable
      leftIndex rightIndex left right : Nat}
    (hboundary : CompactAdditiveBoundaryTable
      tokenCount partCount start finish boundaryTable)
    (hindices : leftIndex ≤ rightIndex)
    (hrightIndex : rightIndex ≤ partCount)
    (hleftEntry : CompactFixedWidthEntry
      boundaryTable tokenCount leftIndex left)
    (hrightEntry : CompactFixedWidthEntry
      boundaryTable tokenCount rightIndex right) :
    left ≤ right := by
  induction rightIndex generalizing leftIndex left right with
  | zero =>
      have hleftIndex : leftIndex = 0 := by omega
      subst leftIndex
      exact Nat.le_of_eq <|
        (CompactFixedWidthEntry.value_eq_tableValue hleftEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue hrightEntry).symm
  | succ rightIndex ih =>
      by_cases hsame : leftIndex = rightIndex + 1
      · subst leftIndex
        exact Nat.le_of_eq <|
          (CompactFixedWidthEntry.value_eq_tableValue hleftEntry).trans
            (CompactFixedWidthEntry.value_eq_tableValue hrightEntry).symm
      · have hleftPrevious : leftIndex ≤ rightIndex := by omega
        have hrightPrevious : rightIndex < partCount := by omega
        rcases hboundary.2.2.2.2 rightIndex hrightPrevious with
          ⟨middle, _hmiddle, next, _hnext,
            hmiddleEntry, hnextEntry, _hstrict⟩
        have hnext : next = right :=
          (CompactFixedWidthEntry.value_eq_tableValue hnextEntry).trans
            (CompactFixedWidthEntry.value_eq_tableValue hrightEntry).symm
        have hleftMiddle := ih hleftPrevious (by omega)
          hleftEntry hmiddleEntry
        omega

theorem CompactAdditiveBoundaryTable.entry_lt_finish
    {tokenCount partCount start finish boundaryTable index value : Nat}
    (hboundary : CompactAdditiveBoundaryTable
      tokenCount partCount start finish boundaryTable)
    (hindex : index < partCount)
    (hentry : CompactFixedWidthEntry boundaryTable tokenCount index value) :
    value < finish := by
  rcases hboundary.2.2.2.2 index hindex with
    ⟨left, _hleft, right, _hright,
      hleftEntry, hrightEntry, hstrict⟩
  have hvalueLeft : value = left :=
    (CompactFixedWidthEntry.value_eq_tableValue hentry).trans
      (CompactFixedWidthEntry.value_eq_tableValue hleftEntry).symm
  have hrightFinish := CompactAdditiveBoundaryTable.entry_mono
    hboundary (by omega) (by rfl) hrightEntry hboundary.2.2.2.1
  omega

theorem CompactAdditiveNatListSlice.realizeDirectLayout
    {tokenTable width tokenCount start count finish : Nat}
    (hslice : CompactAdditiveNatListSlice
      tokenTable width tokenCount start count finish)
    (hfinishBound : finish ≤ tokenCount) :
    ∃ values : List Nat,
      values.length = count ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount start finish values := by
  rcases hslice with
    ⟨bodyStart, hbodyStart, hheader, hfinish⟩
  let boundaries :=
    compactAdditiveConsecutiveBoundaryRows bodyStart count
  let boundaryTable :=
    compactFixedWidthTableCode tokenCount boundaries
  let values := compactAdditiveNatListRowValues
    tokenTable width tokenCount boundaryTable count
  have hboundariesLength : boundaries.length = count + 1 := by
    simp [boundaries]
  have hboundaryGet (index : Nat) (hindex : index ≤ count) :
      boundaries.getI index = bodyStart + index := by
    exact compactAdditiveConsecutiveBoundaryRows_getI
      bodyStart count index hindex
  have hboundaryBounded : ∀ cursor ∈ boundaries,
      cursor ≤ tokenCount := by
    intro cursor hcursor
    rcases List.mem_map.mp hcursor with ⟨index, hindex, rfl⟩
    have hindexLt : index < count + 1 := by
      simpa using (List.mem_range.mp hindex)
    have hfinishEq : finish = bodyStart + count := hfinish
    omega
  have hboundaryStrict : ∀ index < count,
      boundaries.getI index < boundaries.getI (index + 1) := by
    intro index hindex
    rw [hboundaryGet index (by omega),
      hboundaryGet (index + 1) (by omega)]
    omega
  have hboundary : CompactAdditiveBoundaryTable
      tokenCount count bodyStart finish boundaryTable := by
    apply compactAdditiveBoundaryTable_of_rows
      tokenCount count bodyStart finish boundaries
    · exact hboundariesLength
    · simpa using hboundaryGet 0 (by omega)
    · rw [hboundaryGet count (by rfl)]
      exact hfinish.symm
    · exact hboundaryBounded
    · exact hboundaryStrict
  have hentryBound : ∀ cursor ∈ boundaries,
      Nat.size cursor ≤ tokenCount := by
    intro cursor hcursor
    exact natSize_le_of_le (hboundaryBounded cursor hcursor)
  have hentry (index : Nat) (hindex : index ≤ count) :
      CompactFixedWidthEntry boundaryTable tokenCount index
        (bodyStart + index) := by
    have hlistIndex : index < boundaries.length := by
      rw [hboundariesLength]
      omega
    simpa [boundaryTable, hboundaryGet index hindex] using
      compactFixedWidthTableCode_entry
        tokenCount boundaries index hlistIndex hentryBound
  have hunit : CompactAdditiveUnitBoundaryRows
      tokenCount count boundaryTable := by
    intro index hindex
    refine ⟨bodyStart + index, ?_, bodyStart + (index + 1), ?_,
      hentry index (by omega), hentry (index + 1) (by omega), by omega⟩
    · have hfinishEq : finish = bodyStart + count := hfinish
      omega
    · have hfinishEq : finish = bodyStart + count := hfinish
      omega
  have hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      boundaryTable values :=
    CompactAdditiveUnitBoundaryRows.realizedNatRows hunit
  have hsize : Nat.size boundaryTable ≤
      (count + 1) * tokenCount := by
    simpa [boundaryTable, hboundariesLength] using
      compactAdditiveBoundaryTable_code_size_le tokenCount boundaries
  have hstructure : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable :=
    ⟨bodyStart, hbodyStart, hheader, hboundary⟩
  refine ⟨values, by simp [values], boundaryTable, ?_, hrows, ?_⟩
  · simpa [values] using hstructure
  · simpa [values] using hsize

theorem CompactAdditiveNatListListRowsWellFormed.realizeDirectLayout
    {tokenTable width tokenCount start count finish boundaryTable : Nat}
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable)
    (hrows : CompactAdditiveNatListListRowsWellFormed
      tokenTable width tokenCount boundaryTable count)
    (hsize : Nat.size boundaryTable ≤ (count + 1) * tokenCount) :
    ∃ values : List (List Nat),
      values.length = count ∧
      CompactAdditiveNatListListDirectLayout
        tokenTable width tokenCount start finish values ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        boundaryTable values := by
  classical
  have hexists (index : Nat) (hindex : index < count) :
      ∃ value : List Nat,
      ∃ left, left ≤ tokenCount ∧
      ∃ right, right ≤ tokenCount ∧
        CompactFixedWidthEntry boundaryTable tokenCount index left ∧
        CompactFixedWidthEntry boundaryTable tokenCount (index + 1) right ∧
        CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount left right value := by
    rcases hrows index hindex with
      ⟨left, hleft, right, hright, innerCount, _hinnerCount,
        hleftEntry, hrightEntry, hslice⟩
    rcases CompactAdditiveNatListSlice.realizeDirectLayout
        hslice hright with
      ⟨value, _hvalueLength, hvalue⟩
    exact ⟨value, left, hleft, right, hright,
      hleftEntry, hrightEntry, hvalue⟩
  let valueAt (index : Fin count) : List Nat :=
    Classical.choose (hexists index index.isLt)
  let values : List (List Nat) := List.ofFn valueAt
  have hvaluesLength : values.length = count := by
    simp [values]
  have hvalueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      boundaryTable values := by
    intro index hindex
    have hcount : index < count := by
      simpa [hvaluesLength] using hindex
    have hspec := Classical.choose_spec (hexists index hcount)
    rcases hspec with
      ⟨left, hleft, right, hright,
        hleftEntry, hrightEntry, hvalue⟩
    refine ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, ?_⟩
    have hget : values.getI index = valueAt ⟨index, hcount⟩ := by
      rw [List.getI_eq_getElem _ (by simpa [hvaluesLength] using hcount)]
      simp [values]
    rw [hget]
    exact hvalue
  refine ⟨values, hvaluesLength, ⟨boundaryTable, ?_, hvalueRows, ?_⟩,
    hvalueRows⟩
  · simpa [hvaluesLength] using hlayout
  · simpa [hvaluesLength] using hsize

theorem CompactNumericChildResultCoreGraph.realizeDirectLayout
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactNumericChildResultRowCoordinates}
    {sizeWitness : CompactNumericChildResultSizeWitness}
    (hgraph : CompactNumericChildResultCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    ∃ value : CompactNumericChildResult,
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        coordinates.start coordinates.finish value ∧
      compactAdditiveBoolTag value.2 = coordinates.boolValue := by
  rcases hgraph with
    ⟨hgammaLayout, hgammaRows, hgammaSizeEq,
      hgammaSize, hbool⟩
  have hgammaBoundarySize :
      Nat.size coordinates.gammaBoundary ≤
        (coordinates.gammaCount + 1) * tokenCount := by
    rw [← hgammaSizeEq]
    exact hgammaSize
  rcases CompactAdditiveNatListListRowsWellFormed.realizeDirectLayout
      hgammaLayout hgammaRows hgammaBoundarySize with
    ⟨gamma, hgammaLength, _hgamma, hgammaValueRows⟩
  rcases hbool.exists_bool with ⟨result, hresult⟩
  have hresultTag :
      coordinates.boolValue = compactAdditiveBoolTag result := by
    simpa [compactAdditiveBoolTag] using hresult
  have hstartGamma : coordinates.start < coordinates.gammaFinish := by
    rcases hgammaLayout with
      ⟨bodyStart, _hbodyStart, hheader, hboundary⟩
    have hbodyStart : bodyStart = coordinates.start + 1 :=
      hheader.1.2.1
    have hbodyFinish : bodyStart ≤ coordinates.gammaFinish :=
      CompactAdditiveBoundaryTable.start_le_finish hboundary
    omega
  have hproduct : CompactAdditiveProductSplit tokenCount
      coordinates.start coordinates.gammaFinish coordinates.finish := by
    have hfinishEq :
        coordinates.finish = coordinates.gammaFinish + 1 :=
      hbool.1.2.1
    have hmiddleBound : coordinates.gammaFinish < tokenCount :=
      hbool.1.1
    have hmiddleFinish :
        coordinates.gammaFinish < coordinates.finish := by
      omega
    have hfinishBound : coordinates.finish ≤ tokenCount := by
      omega
    exact ⟨hstartGamma, hmiddleFinish, hfinishBound⟩
  let value : CompactNumericChildResult := (gamma, result)
  refine ⟨value, ?_, ?_⟩
  · refine ⟨coordinates.gammaFinish, coordinates.gammaBoundary,
      coordinates.boolValue, hproduct, ?_, ?_, hresultTag,
      hbool, ?_⟩
    · simpa [value, hgammaLength] using hgammaLayout
    · simpa [value] using hgammaValueRows
    · simpa [value, hgammaLength, hgammaSizeEq] using hgammaSize
  · exact hresultTag.symm

theorem CompactNumericChildResultBoundedRow.realizeDirectLayout
    {tokenTable width tokenCount valueBoundary valueBound rowIndex : Nat}
    (hrow : CompactNumericChildResultBoundedRow
      tokenTable width tokenCount valueBoundary valueBound rowIndex) :
    ∃ start,
    ∃ finish,
    ∃ value : CompactNumericChildResult,
      CompactFixedWidthEntry valueBoundary tokenCount rowIndex start ∧
      CompactFixedWidthEntry valueBoundary tokenCount (rowIndex + 1) finish ∧
      CompactNumericChildResultDirectLayout
        tokenTable width tokenCount start finish value := by
  rcases hrow with
    ⟨start, _hstartBound, finish, _hfinishBound,
      gammaFinish, _hgammaFinishBound, gammaCount, _hgammaCountBound,
      gammaBoundary, _hgammaBoundaryBound, boolValue, _hboolBound,
      gammaBoundarySize, _hgammaBoundarySizeBound,
      hstartEntry, hfinishEntry, hcore⟩
  rcases CompactNumericChildResultCoreGraph.realizeDirectLayout hcore with
    ⟨value, hvalue, _hbool⟩
  exact ⟨start, finish, value,
    hstartEntry, hfinishEntry, hvalue⟩

theorem CompactNumericChildResultBoundedRowWithBool.realizeDirectLayout
    {tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool : Nat}
    (hrow : CompactNumericChildResultBoundedRowWithBool
      tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool) :
    ∃ start,
    ∃ finish,
    ∃ value : CompactNumericChildResult,
      CompactFixedWidthEntry valueBoundary tokenCount rowIndex start ∧
      CompactFixedWidthEntry valueBoundary tokenCount (rowIndex + 1) finish ∧
      CompactNumericChildResultDirectLayout
        tokenTable width tokenCount start finish value ∧
      compactAdditiveBoolTag value.2 = expectedBool := by
  rcases hrow with
    ⟨start, _hstartBound, finish, _hfinishBound,
      gammaFinish, _hgammaFinishBound, gammaCount, _hgammaCountBound,
      gammaBoundary, _hgammaBoundaryBound,
      gammaBoundarySize, _hgammaBoundarySizeBound, _hexpectedBound,
      hstartEntry, hfinishEntry, hcore⟩
  rcases CompactNumericChildResultCoreGraph.realizeDirectLayout hcore with
    ⟨value, hvalue, hbool⟩
  exact ⟨start, finish, value,
    hstartEntry, hfinishEntry, hvalue, hbool⟩

theorem CompactNumericChildResultListRowsGraph.realizeDirectRows
    {tokenTable width tokenCount start finish valueBoundary valueCount
      tableWidth valueBound : Nat}
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start valueCount finish valueBoundary)
    (hrows : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount valueBoundary valueCount
      tableWidth valueBound) :
    ∃ values : List CompactNumericChildResult,
      values.length = valueCount ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactNumericChildResultDirectLayout tokenTable width tokenCount
        valueBoundary values := by
  classical
  rcases hlayout with
    ⟨bodyStart, _hbodyStart, _hheader, hboundary⟩
  have hexists (index : Nat) (hindex : index < valueCount) :
      ∃ value : CompactNumericChildResult,
      ∃ left, left ≤ tokenCount ∧
      ∃ right, right ≤ tokenCount ∧
        CompactFixedWidthEntry valueBoundary tokenCount index left ∧
        CompactFixedWidthEntry valueBoundary tokenCount (index + 1) right ∧
        CompactNumericChildResultDirectLayout
          tokenTable width tokenCount left right value := by
    rcases CompactNumericChildResultBoundedRow.realizeDirectLayout
        (hrows.2 index hindex) with
      ⟨rowLeft, rowRight, value,
        hrowLeftEntry, hrowRightEntry, hvalue⟩
    rcases hboundary.2.2.2.2 index hindex with
      ⟨left, hleft, right, hright,
        hleftEntry, hrightEntry, _hstrict⟩
    have hleftEq : rowLeft = left :=
      (CompactFixedWidthEntry.value_eq_tableValue hrowLeftEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue hleftEntry).symm
    have hrightEq : rowRight = right :=
      (CompactFixedWidthEntry.value_eq_tableValue hrowRightEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue hrightEntry).symm
    subst rowLeft
    subst rowRight
    exact ⟨value, left, hleft, right, hright,
      hleftEntry, hrightEntry, hvalue⟩
  let valueAt (index : Fin valueCount) : CompactNumericChildResult :=
    Classical.choose (hexists index index.isLt)
  let values : List CompactNumericChildResult := List.ofFn valueAt
  have hvaluesLength : values.length = valueCount := by
    simp [values]
  have hvalueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
      valueBoundary values := by
    intro index hindex
    have hcount : index < valueCount := by
      simpa [hvaluesLength] using hindex
    have hspec := Classical.choose_spec (hexists index hcount)
    rcases hspec with
      ⟨left, hleft, right, hright,
        hleftEntry, hrightEntry, hvalue⟩
    refine ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, ?_⟩
    have hget : values.getI index = valueAt ⟨index, hcount⟩ := by
      rw [List.getI_eq_getElem _ (by simpa [hvaluesLength] using hcount)]
      simp [values]
    rw [hget]
    exact hvalue
  exact ⟨values, hvaluesLength, hvalueRows⟩

theorem CompactNumericChildResultDirectLayout.boolTag_eq_of_same_slice
    {tokenTable width tokenCount start finish : Nat}
    {leftValue rightValue : CompactNumericChildResult}
    (hleft : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount start finish leftValue)
    (hright : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount start finish rightValue) :
    compactAdditiveBoolTag leftValue.2 =
      compactAdditiveBoolTag rightValue.2 := by
  rcases hleft with
    ⟨leftGammaFinish, _leftGammaBoundary, leftBoolValue,
      _hleftProduct, _hleftGammaLayout, _hleftGammaRows,
      hleftBoolValue, hleftBool, _hleftGammaSize⟩
  rcases hright with
    ⟨rightGammaFinish, _rightGammaBoundary, rightBoolValue,
      _hrightProduct, _hrightGammaLayout, _hrightGammaRows,
      hrightBoolValue, hrightBool, _hrightGammaSize⟩
  have hgammaFinish : leftGammaFinish = rightGammaFinish := by
    have hleftFinish : finish = leftGammaFinish + 1 :=
      hleftBool.1.2.1
    have hrightFinish : finish = rightGammaFinish + 1 :=
      hrightBool.1.2.1
    omega
  have hboolValue : leftBoolValue = rightBoolValue := by
    subst rightGammaFinish
    exact (CompactFixedWidthEntry.value_eq_tableValue
      hleftBool.1.2.2).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          hrightBool.1.2.2).symm
  omega

theorem CompactNumericChildResultBoundedRowWithBool.matchesDirectRows
    {tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool : Nat}
    {values : List CompactNumericChildResult}
    (hindex : rowIndex < values.length)
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
      valueBoundary values)
    (hrow : CompactNumericChildResultBoundedRowWithBool
      tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool) :
    compactAdditiveBoolTag (values.getI rowIndex).2 = expectedBool := by
  rcases hrows rowIndex hindex with
    ⟨left, _hleft, right, _hright,
      hleftEntry, hrightEntry, hlayout⟩
  rcases CompactNumericChildResultBoundedRowWithBool.realizeDirectLayout
      hrow with
    ⟨rowLeft, rowRight, rowValue,
      hrowLeftEntry, hrowRightEntry, hrowLayout, hrowBool⟩
  have hleftEq : rowLeft = left :=
    (CompactFixedWidthEntry.value_eq_tableValue hrowLeftEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue hleftEntry).symm
  have hrightEq : rowRight = right :=
    (CompactFixedWidthEntry.value_eq_tableValue hrowRightEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue hrightEntry).symm
  subst rowLeft
  subst rowRight
  exact (CompactNumericChildResultDirectLayout.boolTag_eq_of_same_slice
    hlayout hrowLayout).trans hrowBool

#print axioms compactAdditiveConsecutiveBoundaryRows_getI
#print axioms CompactAdditiveBoundaryTable.entry_mono
#print axioms CompactAdditiveBoundaryTable.entry_lt_finish
#print axioms CompactAdditiveNatListSlice.realizeDirectLayout
#print axioms CompactAdditiveNatListListRowsWellFormed.realizeDirectLayout
#print axioms CompactNumericChildResultCoreGraph.realizeDirectLayout
#print axioms CompactNumericChildResultBoundedRow.realizeDirectLayout
#print axioms CompactNumericChildResultBoundedRowWithBool.realizeDirectLayout
#print axioms CompactNumericChildResultListRowsGraph.realizeDirectRows
#print axioms CompactNumericChildResultDirectLayout.boolTag_eq_of_same_slice
#print axioms CompactNumericChildResultBoundedRowWithBool.matchesDirectRows

end FoundationCompactNumericListedDirectVerifierValueRealization
