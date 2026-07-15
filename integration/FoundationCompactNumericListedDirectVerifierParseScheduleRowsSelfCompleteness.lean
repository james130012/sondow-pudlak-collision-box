import integration.FoundationCompactNumericListedDirectVerifierParseScheduleRowsCompleteness

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseScheduleRowsCompleteness

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedAtFormula
open FoundationCompactNumericListedDirectVerifierTaskListReplaceHeadRows
open FoundationCompactNumericListedDirectVerifierTaskSliceEquality
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierParseScheduleRows

private theorem compactNumericParseTaskShape_of_boundedAt
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
        taskBoundary tasks)
    (htask : tasks.getI rowIndex = compactNumericParseTask) :
    CompactNumericParseTaskShape coordinates := by
  rcases hat.realize_actualAtWithFields hindex hrows with
    ⟨task, hactual, htag, _htaskLayout,
      _hgammaRows, hgammaLength,
      _hfirstLayout, hfirstLength,
      _hsecondLayout, hsecondLength,
      _hwitnessLayout, hwitnessLength,
      _hsuffixLayout, hsuffixLength⟩
  have htaskValue : task = compactNumericParseTask := hactual.trans htask
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [htaskValue, compactNumericParseTask] using htag.symm
  · simpa [htaskValue, compactNumericParseTask,
      compactNumericEmptyNodeFields] using hgammaLength.symm
  · simpa [htaskValue, compactNumericParseTask,
      compactNumericEmptyNodeFields] using hfirstLength.symm
  · simpa [htaskValue, compactNumericParseTask,
      compactNumericEmptyNodeFields] using hsecondLength.symm
  · simpa [htaskValue, compactNumericParseTask,
      compactNumericEmptyNodeFields] using hwitnessLength.symm
  · simpa [htaskValue, compactNumericParseTask,
      compactNumericEmptyNodeFields] using hsuffixLength.symm

theorem CompactNumericVerifierOneParseScheduleRows.of_components_self_root
    {tokenTable width tokenCount sourceBoundary targetBoundary
      tableWidth valueBound : Nat}
    {source target : List CompactNumericVerifierTask}
    {root : CompactNumericVerifierTask}
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hsourceGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount sourceBoundary source.length
        tableWidth valueBound)
    (htargetGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound)
    (hrootTag : root.1 = 4 ∨ root.1 = 5 ∨ root.1 = 6 ∨
      root.1 = 7 ∨ root.1 = 8)
    (hsourceNonempty : source ≠ [])
    (htarget : target = compactNumericParseTask :: root :: source.drop 1) :
    ∃ parseCoordinates : CompactNumericVerifierTaskRowCoordinates,
    ∃ combineCoordinates : CompactNumericVerifierTaskRowCoordinates,
    ∃ parseSize : CompactNumericVerifierTaskSizeWitness,
    ∃ combineSize : CompactNumericVerifierTaskSizeWitness,
      CompactNumericVerifierOneParseScheduleRows
        tokenTable width tokenCount
        sourceBoundary source.length targetBoundary target.length valueBound
        combineCoordinates.start combineCoordinates.finish root.1
        parseCoordinates combineCoordinates parseSize combineSize := by
  have hsourceLength : 1 ≤ source.length := by
    cases source with
    | nil => simp at hsourceNonempty
    | cons => simp
  have htargetTwo : 2 ≤ target.length := by
    rw [htarget]
    simp
  have htail : target.drop 2 = source.drop 1 := by
    rw [htarget]
    simp
  have hreplace :=
    CompactAdditiveStructuredListElementRowLayouts.verifierTaskReplaceHeadRows
      hsourceRows htargetRows hsourceGraph htargetGraph hsourceLength htargetTwo htail
  rcases CompactNumericVerifierTaskBoundedRow.exists_boundedAt
      (htargetGraph.2 0 (by omega)) with
    ⟨parseCoordinates, parseSize, hparseAt⟩
  rcases CompactNumericVerifierTaskBoundedRow.exists_boundedAt
      (htargetGraph.2 1 (by omega)) with
    ⟨combineCoordinates, combineSize, hcombineAt⟩
  have hparseValue : target.getI 0 = compactNumericParseTask := by
    rw [htarget]
    rfl
  have hcombineValue : target.getI 1 = root := by
    rw [htarget]
    rfl
  have hparseShape := compactNumericParseTaskShape_of_boundedAt
    hparseAt (by omega) htargetRows hparseValue
  rcases hcombineAt.realize_actualAtWithFields (by omega) htargetRows with
    ⟨combineTask, hcombineActual, _hcombineTag, hcombineLayout,
      _hcombineGammaRows, _hcombineGammaLength,
      _hcombineFirstLayout, _hcombineFirstLength,
      _hcombineSecondLayout, _hcombineSecondLength,
      _hcombineWitnessLayout, _hcombineWitnessLength,
      _hcombineSuffixLayout, _hcombineSuffixLength⟩
  have hcombineTask : combineTask = root :=
    hcombineActual.trans hcombineValue
  have hcombineSlices : CompactFixedWidthTokenSlicesEq
      tokenTable width tokenCount
        combineCoordinates.start combineCoordinates.finish
        combineCoordinates.start combineCoordinates.finish :=
    CompactNumericVerifierTaskDirectLayout.slicesEq_of_eq
      hcombineLayout hcombineLayout rfl
  exact ⟨parseCoordinates, combineCoordinates, parseSize, combineSize,
    hrootTag, hreplace, hparseAt, hparseShape, hcombineAt, hcombineSlices⟩

theorem CompactNumericVerifierTwoParseScheduleRows.of_components_self_root
    {tokenTable width tokenCount sourceBoundary targetBoundary
      tableWidth valueBound : Nat}
    {source target : List CompactNumericVerifierTask}
    {root : CompactNumericVerifierTask}
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hsourceGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount sourceBoundary source.length
        tableWidth valueBound)
    (htargetGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound)
    (hrootTag : root.1 = 3 ∨ root.1 = 9)
    (hsourceNonempty : source ≠ [])
    (htarget : target = compactNumericParseTask :: compactNumericParseTask ::
      root :: source.drop 1) :
    ∃ firstParseCoordinates : CompactNumericVerifierTaskRowCoordinates,
    ∃ secondParseCoordinates : CompactNumericVerifierTaskRowCoordinates,
    ∃ combineCoordinates : CompactNumericVerifierTaskRowCoordinates,
    ∃ firstParseSize : CompactNumericVerifierTaskSizeWitness,
    ∃ secondParseSize : CompactNumericVerifierTaskSizeWitness,
    ∃ combineSize : CompactNumericVerifierTaskSizeWitness,
      CompactNumericVerifierTwoParseScheduleRows
        tokenTable width tokenCount
        sourceBoundary source.length targetBoundary target.length valueBound
        combineCoordinates.start combineCoordinates.finish root.1
        firstParseCoordinates secondParseCoordinates combineCoordinates
        firstParseSize secondParseSize combineSize := by
  have hsourceLength : 1 ≤ source.length := by
    cases source with
    | nil => simp at hsourceNonempty
    | cons => simp
  have htargetThree : 3 ≤ target.length := by
    rw [htarget]
    simp
  have htail : target.drop 3 = source.drop 1 := by
    rw [htarget]
    simp
  have hreplace :=
    CompactAdditiveStructuredListElementRowLayouts.verifierTaskReplaceHeadRows
      hsourceRows htargetRows hsourceGraph htargetGraph hsourceLength
        htargetThree htail
  rcases CompactNumericVerifierTaskBoundedRow.exists_boundedAt
      (htargetGraph.2 0 (by omega)) with
    ⟨firstParseCoordinates, firstParseSize, hfirstParseAt⟩
  rcases CompactNumericVerifierTaskBoundedRow.exists_boundedAt
      (htargetGraph.2 1 (by omega)) with
    ⟨secondParseCoordinates, secondParseSize, hsecondParseAt⟩
  rcases CompactNumericVerifierTaskBoundedRow.exists_boundedAt
      (htargetGraph.2 2 (by omega)) with
    ⟨combineCoordinates, combineSize, hcombineAt⟩
  have hfirstParseValue : target.getI 0 = compactNumericParseTask := by
    rw [htarget]
    rfl
  have hsecondParseValue : target.getI 1 = compactNumericParseTask := by
    rw [htarget]
    rfl
  have hcombineValue : target.getI 2 = root := by
    rw [htarget]
    rfl
  have hfirstParseShape := compactNumericParseTaskShape_of_boundedAt
    hfirstParseAt (by omega) htargetRows hfirstParseValue
  have hsecondParseShape := compactNumericParseTaskShape_of_boundedAt
    hsecondParseAt (by omega) htargetRows hsecondParseValue
  rcases hcombineAt.realize_actualAtWithFields (by omega) htargetRows with
    ⟨combineTask, hcombineActual, _hcombineTag, hcombineLayout,
      _hcombineGammaRows, _hcombineGammaLength,
      _hcombineFirstLayout, _hcombineFirstLength,
      _hcombineSecondLayout, _hcombineSecondLength,
      _hcombineWitnessLayout, _hcombineWitnessLength,
      _hcombineSuffixLayout, _hcombineSuffixLength⟩
  have hcombineTask : combineTask = root :=
    hcombineActual.trans hcombineValue
  have hcombineSlices : CompactFixedWidthTokenSlicesEq
      tokenTable width tokenCount
        combineCoordinates.start combineCoordinates.finish
        combineCoordinates.start combineCoordinates.finish :=
    CompactNumericVerifierTaskDirectLayout.slicesEq_of_eq
      hcombineLayout hcombineLayout rfl
  exact ⟨firstParseCoordinates, secondParseCoordinates, combineCoordinates,
    firstParseSize, secondParseSize, combineSize,
    hrootTag, hreplace, hfirstParseAt, hfirstParseShape,
    hsecondParseAt, hsecondParseShape, hcombineAt, hcombineSlices⟩

#print axioms CompactNumericVerifierOneParseScheduleRows.of_components_self_root
#print axioms CompactNumericVerifierTwoParseScheduleRows.of_components_self_root

end FoundationCompactNumericListedDirectVerifierParseScheduleRowsCompleteness
