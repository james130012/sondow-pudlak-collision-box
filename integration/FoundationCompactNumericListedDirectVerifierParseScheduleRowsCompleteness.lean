import integration.FoundationCompactNumericListedDirectVerifierParseScheduleRows
import integration.FoundationCompactNumericListedDirectVerifierParseScheduleFormula
import integration.FoundationCompactNumericListedDirectVerifierTaskSliceEquality

/-!
# Canonical converse for successful parse scheduling rows

The typed source and target task rows provide the public row coordinates.  A
successful parse schedule is therefore reconstructed from its actual short
target prefix, rather than assumed as an auxiliary graph premise.
-/

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
open FoundationCompactNumericListedDirectVerifierParseScheduleFormula

private theorem CompactNumericParseTaskShape.of_boundedAt
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

theorem CompactNumericVerifierOneParseScheduleRows.of_components
    {tokenTable width tokenCount sourceBoundary targetBoundary
      tableWidth valueBound rootStart rootFinish : Nat}
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
    (hroot : CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount rootStart rootFinish root)
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
        rootStart rootFinish root.1
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
  have hparseShape := CompactNumericParseTaskShape.of_boundedAt
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
      tokenTable width tokenCount rootStart rootFinish
        combineCoordinates.start combineCoordinates.finish :=
    CompactNumericVerifierTaskDirectLayout.slicesEq_of_eq
      hroot hcombineLayout hcombineTask.symm
  exact ⟨parseCoordinates, combineCoordinates, parseSize, combineSize,
    hrootTag, hreplace, hparseAt, hparseShape, hcombineAt, hcombineSlices⟩

theorem CompactNumericVerifierTwoParseScheduleRows.of_components
    {tokenTable width tokenCount sourceBoundary targetBoundary
      tableWidth valueBound rootStart rootFinish : Nat}
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
    (hroot : CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount rootStart rootFinish root)
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
        rootStart rootFinish root.1
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
  have hfirstParseShape := CompactNumericParseTaskShape.of_boundedAt
    hfirstParseAt (by omega) htargetRows hfirstParseValue
  have hsecondParseShape := CompactNumericParseTaskShape.of_boundedAt
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
      tokenTable width tokenCount rootStart rootFinish
        combineCoordinates.start combineCoordinates.finish :=
    CompactNumericVerifierTaskDirectLayout.slicesEq_of_eq
      hroot hcombineLayout hcombineTask.symm
  exact ⟨firstParseCoordinates, secondParseCoordinates, combineCoordinates,
    firstParseSize, secondParseSize, combineSize,
    hrootTag, hreplace, hfirstParseAt, hfirstParseShape,
    hsecondParseAt, hsecondParseShape, hcombineAt, hcombineSlices⟩

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
theorem exists_compactNumericVerifierOneParseScheduleRows_evalb_of_components
    {tokenTable width tokenCount sourceBoundary targetBoundary
      tableWidth valueBound rootStart rootFinish rootTag : Nat}
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
    (hroot : CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount rootStart rootFinish root)
    (hrootTag : root.1 = rootTag)
    (hrootTagCases : rootTag = 4 ∨ rootTag = 5 ∨ rootTag = 6 ∨
      rootTag = 7 ∨ rootTag = 8)
    (hsourceNonempty : source ≠ [])
    (htarget : target = compactNumericParseTask :: root :: source.drop 1) :
    ∃ parseCoordinates : CompactNumericVerifierTaskRowCoordinates,
    ∃ combineCoordinates : CompactNumericVerifierTaskRowCoordinates,
    ∃ parseSize : CompactNumericVerifierTaskSizeWitness,
    ∃ combineSize : CompactNumericVerifierTaskSizeWitness,
      compactNumericVerifierOneParseScheduleRowsDef.val.Evalb
        (compactNumericVerifierOneParseScheduleRowsEnvironment
          tokenTable width tokenCount
          sourceBoundary source.length targetBoundary target.length valueBound
          rootStart rootFinish rootTag
          parseCoordinates.start parseCoordinates.finish parseCoordinates.tag
          parseCoordinates.gammaFinish parseCoordinates.gammaCount
          parseCoordinates.gammaBoundary
          parseCoordinates.firstFinish parseCoordinates.firstCount
          parseCoordinates.secondFinish parseCoordinates.secondCount
          parseCoordinates.witnessFinish parseCoordinates.witnessCount
          parseCoordinates.suffixCount parseSize.gammaBoundarySize
          combineCoordinates.start combineCoordinates.finish combineCoordinates.tag
          combineCoordinates.gammaFinish combineCoordinates.gammaCount
          combineCoordinates.gammaBoundary
          combineCoordinates.firstFinish combineCoordinates.firstCount
          combineCoordinates.secondFinish combineCoordinates.secondCount
          combineCoordinates.witnessFinish combineCoordinates.witnessCount
          combineCoordinates.suffixCount combineSize.gammaBoundarySize) := by
  have hrootCases : root.1 = 4 ∨ root.1 = 5 ∨ root.1 = 6 ∨
      root.1 = 7 ∨ root.1 = 8 := by
    simpa only [hrootTag] using hrootTagCases
  rcases CompactNumericVerifierOneParseScheduleRows.of_components
      hsourceRows htargetRows hsourceGraph htargetGraph hroot hrootCases
        hsourceNonempty htarget with
    ⟨parseCoordinates, combineCoordinates, parseSize, combineSize, hrows⟩
  refine ⟨parseCoordinates, combineCoordinates, parseSize, combineSize, ?_⟩
  exact compactNumericVerifierOneParseScheduleRowsDef_spec
    tokenTable width tokenCount
    sourceBoundary source.length targetBoundary target.length valueBound
    rootStart rootFinish rootTag
    parseCoordinates.start parseCoordinates.finish parseCoordinates.tag
    parseCoordinates.gammaFinish parseCoordinates.gammaCount
    parseCoordinates.gammaBoundary
    parseCoordinates.firstFinish parseCoordinates.firstCount
    parseCoordinates.secondFinish parseCoordinates.secondCount
    parseCoordinates.witnessFinish parseCoordinates.witnessCount
    parseCoordinates.suffixCount parseSize.gammaBoundarySize
    combineCoordinates.start combineCoordinates.finish combineCoordinates.tag
    combineCoordinates.gammaFinish combineCoordinates.gammaCount
    combineCoordinates.gammaBoundary
    combineCoordinates.firstFinish combineCoordinates.firstCount
    combineCoordinates.secondFinish combineCoordinates.secondCount
    combineCoordinates.witnessFinish combineCoordinates.witnessCount
    combineCoordinates.suffixCount combineSize.gammaBoundarySize |>.mpr
      (by simpa only [hrootTag,
        compactNumericVerifierTaskRowCoordinatesOf] using hrows)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
theorem exists_compactNumericVerifierTwoParseScheduleRows_evalb_of_components
    {tokenTable width tokenCount sourceBoundary targetBoundary
      tableWidth valueBound rootStart rootFinish rootTag : Nat}
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
    (hroot : CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount rootStart rootFinish root)
    (hrootTag : root.1 = rootTag)
    (hrootTagCases : rootTag = 3 ∨ rootTag = 9)
    (hsourceNonempty : source ≠ [])
    (htarget : target = compactNumericParseTask :: compactNumericParseTask ::
      root :: source.drop 1) :
    ∃ firstParseCoordinates : CompactNumericVerifierTaskRowCoordinates,
    ∃ secondParseCoordinates : CompactNumericVerifierTaskRowCoordinates,
    ∃ combineCoordinates : CompactNumericVerifierTaskRowCoordinates,
    ∃ firstParseSize : CompactNumericVerifierTaskSizeWitness,
    ∃ secondParseSize : CompactNumericVerifierTaskSizeWitness,
    ∃ combineSize : CompactNumericVerifierTaskSizeWitness,
      compactNumericVerifierTwoParseScheduleRowsDef.val.Evalb
        (compactNumericVerifierTwoParseScheduleRowsEnvironment
          tokenTable width tokenCount
          sourceBoundary source.length targetBoundary target.length valueBound
          rootStart rootFinish rootTag
          firstParseCoordinates.start firstParseCoordinates.finish
          firstParseCoordinates.tag
          firstParseCoordinates.gammaFinish firstParseCoordinates.gammaCount
          firstParseCoordinates.gammaBoundary
          firstParseCoordinates.firstFinish firstParseCoordinates.firstCount
          firstParseCoordinates.secondFinish firstParseCoordinates.secondCount
          firstParseCoordinates.witnessFinish firstParseCoordinates.witnessCount
          firstParseCoordinates.suffixCount firstParseSize.gammaBoundarySize
          secondParseCoordinates.start secondParseCoordinates.finish
          secondParseCoordinates.tag
          secondParseCoordinates.gammaFinish secondParseCoordinates.gammaCount
          secondParseCoordinates.gammaBoundary
          secondParseCoordinates.firstFinish secondParseCoordinates.firstCount
          secondParseCoordinates.secondFinish secondParseCoordinates.secondCount
          secondParseCoordinates.witnessFinish secondParseCoordinates.witnessCount
          secondParseCoordinates.suffixCount secondParseSize.gammaBoundarySize
          combineCoordinates.start combineCoordinates.finish combineCoordinates.tag
          combineCoordinates.gammaFinish combineCoordinates.gammaCount
          combineCoordinates.gammaBoundary
          combineCoordinates.firstFinish combineCoordinates.firstCount
          combineCoordinates.secondFinish combineCoordinates.secondCount
          combineCoordinates.witnessFinish combineCoordinates.witnessCount
          combineCoordinates.suffixCount combineSize.gammaBoundarySize) := by
  have hrootCases : root.1 = 3 ∨ root.1 = 9 := by
    simpa only [hrootTag] using hrootTagCases
  rcases CompactNumericVerifierTwoParseScheduleRows.of_components
      hsourceRows htargetRows hsourceGraph htargetGraph hroot hrootCases
        hsourceNonempty htarget with
    ⟨firstParseCoordinates, secondParseCoordinates, combineCoordinates,
      firstParseSize, secondParseSize, combineSize, hrows⟩
  refine ⟨firstParseCoordinates, secondParseCoordinates, combineCoordinates,
    firstParseSize, secondParseSize, combineSize, ?_⟩
  exact compactNumericVerifierTwoParseScheduleRowsDef_spec
    tokenTable width tokenCount
    sourceBoundary source.length targetBoundary target.length valueBound
    rootStart rootFinish rootTag
    firstParseCoordinates.start firstParseCoordinates.finish
    firstParseCoordinates.tag
    firstParseCoordinates.gammaFinish firstParseCoordinates.gammaCount
    firstParseCoordinates.gammaBoundary
    firstParseCoordinates.firstFinish firstParseCoordinates.firstCount
    firstParseCoordinates.secondFinish firstParseCoordinates.secondCount
    firstParseCoordinates.witnessFinish firstParseCoordinates.witnessCount
    firstParseCoordinates.suffixCount firstParseSize.gammaBoundarySize
    secondParseCoordinates.start secondParseCoordinates.finish
    secondParseCoordinates.tag
    secondParseCoordinates.gammaFinish secondParseCoordinates.gammaCount
    secondParseCoordinates.gammaBoundary
    secondParseCoordinates.firstFinish secondParseCoordinates.firstCount
    secondParseCoordinates.secondFinish secondParseCoordinates.secondCount
    secondParseCoordinates.witnessFinish secondParseCoordinates.witnessCount
    secondParseCoordinates.suffixCount secondParseSize.gammaBoundarySize
    combineCoordinates.start combineCoordinates.finish combineCoordinates.tag
    combineCoordinates.gammaFinish combineCoordinates.gammaCount
    combineCoordinates.gammaBoundary
    combineCoordinates.firstFinish combineCoordinates.firstCount
    combineCoordinates.secondFinish combineCoordinates.secondCount
    combineCoordinates.witnessFinish combineCoordinates.witnessCount
    combineCoordinates.suffixCount combineSize.gammaBoundarySize |>.mpr
      (by simpa only [hrootTag,
        compactNumericVerifierTaskRowCoordinatesOf] using hrows)

#print axioms CompactNumericVerifierOneParseScheduleRows.of_components
#print axioms CompactNumericVerifierTwoParseScheduleRows.of_components
#print axioms exists_compactNumericVerifierOneParseScheduleRows_evalb_of_components
#print axioms exists_compactNumericVerifierTwoParseScheduleRows_evalb_of_components

end FoundationCompactNumericListedDirectVerifierParseScheduleRowsCompleteness
