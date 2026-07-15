import integration.FoundationCompactNumericListedDirectVerifierTaskBoundedAtFormula
import integration.FoundationCompactNumericListedDirectVerifierTaskListReplaceHeadRows

/-!
# Exact task scheduling rows for successful parse transitions

Non-leaf proof nodes replace the consumed parse-task head by either
`parse, combine` or `parse, parse, combine`.  The combine task is byte-for-byte
the proof root returned by the parser.  These relations expose and verify that
short prefix while the replace-head relation preserves the complete tail.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseScheduleRows

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierTaskBoundedAtFormula
open FoundationCompactNumericListedDirectVerifierTaskListReplaceHeadRows

def CompactNumericParseTaskShape
    (coordinates : CompactNumericVerifierTaskRowCoordinates) : Prop :=
  coordinates.tag = 10 ∧
    coordinates.gammaCount = 0 ∧
    coordinates.firstCount = 0 ∧
    coordinates.secondCount = 0 ∧
    coordinates.witnessCount = 0 ∧
    coordinates.suffixCount = 0

def CompactNumericVerifierOneParseScheduleRows
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount valueBound
      rootStart rootFinish rootTag : Nat)
    (parseCoordinates combineCoordinates :
      CompactNumericVerifierTaskRowCoordinates)
    (parseSize combineSize : CompactNumericVerifierTaskSizeWitness) : Prop :=
  (rootTag = 4 ∨ rootTag = 5 ∨ rootTag = 6 ∨
      rootTag = 7 ∨ rootTag = 8) ∧
    CompactNumericVerifierTaskListReplaceHeadRows
      tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount valueBound 2 ∧
    CompactNumericVerifierTaskBoundedAt
      tokenTable width tokenCount targetBoundary valueBound 0
        parseCoordinates parseSize ∧
    CompactNumericParseTaskShape parseCoordinates ∧
    CompactNumericVerifierTaskBoundedAt
      tokenTable width tokenCount targetBoundary valueBound 1
        combineCoordinates combineSize ∧
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      rootStart rootFinish combineCoordinates.start combineCoordinates.finish

def CompactNumericVerifierTwoParseScheduleRows
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount valueBound
      rootStart rootFinish rootTag : Nat)
    (firstParseCoordinates secondParseCoordinates combineCoordinates :
      CompactNumericVerifierTaskRowCoordinates)
    (firstParseSize secondParseSize combineSize :
      CompactNumericVerifierTaskSizeWitness) : Prop :=
  (rootTag = 3 ∨ rootTag = 9) ∧
    CompactNumericVerifierTaskListReplaceHeadRows
      tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount valueBound 3 ∧
    CompactNumericVerifierTaskBoundedAt
      tokenTable width tokenCount targetBoundary valueBound 0
        firstParseCoordinates firstParseSize ∧
    CompactNumericParseTaskShape firstParseCoordinates ∧
    CompactNumericVerifierTaskBoundedAt
      tokenTable width tokenCount targetBoundary valueBound 1
        secondParseCoordinates secondParseSize ∧
    CompactNumericParseTaskShape secondParseCoordinates ∧
    CompactNumericVerifierTaskBoundedAt
      tokenTable width tokenCount targetBoundary valueBound 2
        combineCoordinates combineSize ∧
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      rootStart rootFinish combineCoordinates.start combineCoordinates.finish

private theorem parseTask_eq_of_shape
    {tokenTable width tokenCount taskBoundary valueBound rowIndex : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    {tasks : List CompactNumericVerifierTask}
    (hat : CompactNumericVerifierTaskBoundedAt
      tokenTable width tokenCount taskBoundary valueBound rowIndex
        coordinates sizeWitness)
    (hshape : CompactNumericParseTaskShape coordinates)
    (hindex : rowIndex < tasks.length)
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        taskBoundary tasks) :
    tasks.getI rowIndex = compactNumericParseTask := by
  rcases hat.realize_actualAtWithFields hindex hrows with
    ⟨task, htask, htag, _htaskLayout,
      _hgammaRows, hgammaLength,
      _hfirstLayout, hfirstLength,
      _hsecondLayout, hsecondLength,
      _hwitnessLayout, hwitnessLength,
      _hsuffixLayout, hsuffixLength⟩
  rcases hshape with
    ⟨hshapeTag, hgammaZero, hfirstZero, hsecondZero,
      hwitnessZero, hsuffixZero⟩
  have htaskTag : task.1 = 10 := htag.trans hshapeTag
  have hgamma : task.2.1 = [] :=
    List.eq_nil_of_length_eq_zero (hgammaLength.trans hgammaZero)
  have hfirst : task.2.2.1 = [] :=
    List.eq_nil_of_length_eq_zero (hfirstLength.trans hfirstZero)
  have hsecond : task.2.2.2.1 = [] :=
    List.eq_nil_of_length_eq_zero (hsecondLength.trans hsecondZero)
  have hwitness : task.2.2.2.2.1 = [] :=
    List.eq_nil_of_length_eq_zero (hwitnessLength.trans hwitnessZero)
  have hsuffix : task.2.2.2.2.2 = [] :=
    List.eq_nil_of_length_eq_zero (hsuffixLength.trans hsuffixZero)
  have hfields : task.2 = compactNumericEmptyNodeFields := by
    apply Prod.ext hgamma
    apply Prod.ext hfirst
    apply Prod.ext hsecond
    exact Prod.ext hwitness hsuffix
  have htaskValue : task = compactNumericParseTask :=
    Prod.ext htaskTag hfields
  exact htask.symm.trans htaskValue

private theorem verifierTaskLayout_start_lt_finish
    {tokenTable width tokenCount start finish : Nat}
    {task : CompactNumericVerifierTask}
    (hlayout : CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount start finish task) :
    start < finish := by
  rcases hlayout with ⟨fieldsStart, htag, hfields⟩
  rcases hfields with
    ⟨gammaFinish, firstFinish, secondFinish, witnessFinish,
      hgamma, hfirst, hsecond, hwitness, hsuffix⟩
  rcases hgamma with
    ⟨_gammaBoundary, hgammaStructure, _hgammaRows, _hgammaSize⟩
  have hfieldsStart : fieldsStart = start + 1 := htag.2.1
  have hgammaLt := CompactAdditiveStructuredListLayout.start_lt_finish
    hgammaStructure
  have hfirstFinish := CompactAdditiveNatListDirectLayout.finish_eq hfirst
  have hsecondFinish := CompactAdditiveNatListDirectLayout.finish_eq hsecond
  have hwitnessFinish := CompactAdditiveNatListDirectLayout.finish_eq hwitness
  have hsuffixFinish := CompactAdditiveNatListDirectLayout.finish_eq hsuffix
  omega

private theorem combineTask_eq_of_slices
    {tokenTable width tokenCount taskBoundary valueBound rowIndex
      rootStart rootFinish : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    {tasks : List CompactNumericVerifierTask}
    {root : CompactNumericVerifierTask}
    (hat : CompactNumericVerifierTaskBoundedAt
      tokenTable width tokenCount taskBoundary valueBound rowIndex
        coordinates sizeWitness)
    (hindex : rowIndex < tasks.length)
    (htaskRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        taskBoundary tasks)
    (hroot : CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount rootStart rootFinish root)
    (hslices : CompactFixedWidthTokenSlicesEq
      tokenTable width tokenCount rootStart rootFinish
        coordinates.start coordinates.finish) :
    tasks.getI rowIndex = root := by
  rcases hat.realize_actualAtWithFields hindex htaskRows with
    ⟨task, htask, _htag, htaskLayout,
      _hgammaRows, _hgammaLength,
      _hfirstLayout, _hfirstLength,
      _hsecondLayout, _hsecondLength,
      _hwitnessLayout, _hwitnessLength,
      _hsuffixLayout, _hsuffixLength⟩
  have hrootLt := verifierTaskLayout_start_lt_finish hroot
  rcases CompactFixedWidthTokenSlicesEq.verifierTaskPrefix_eq
      (offset := 0) hslices rfl rfl (by omega)
      (le_refl rootFinish) (le_refl coordinates.finish)
      hroot htaskLayout with
    ⟨_finishOffset, _hrootFinish, _htaskFinish, htaskRoot⟩
  exact htask.symm.trans htaskRoot

theorem CompactNumericVerifierOneParseScheduleRows.sound
    {tokenTable width tokenCount
      sourceBoundary targetBoundary tableWidth valueBound
      rootStart rootFinish rootTag : Nat}
    {parseCoordinates combineCoordinates :
      CompactNumericVerifierTaskRowCoordinates}
    {parseSize combineSize : CompactNumericVerifierTaskSizeWitness}
    {source target : List CompactNumericVerifierTask}
    {root : CompactNumericVerifierTask}
    (hrows : CompactNumericVerifierOneParseScheduleRows
      tokenTable width tokenCount
      sourceBoundary source.length targetBoundary target.length valueBound
      rootStart rootFinish rootTag
      parseCoordinates combineCoordinates parseSize combineSize)
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
    (hrootTag : root.1 = rootTag) :
    (root.1 = 4 ∨ root.1 = 5 ∨ root.1 = 6 ∨
        root.1 = 7 ∨ root.1 = 8) ∧
      target = compactNumericParseTask :: root :: source.drop 1 := by
  rcases hrows with
    ⟨htagCases, hreplace, hparseAt, hparseShape,
      hcombineAt, hcombineSlices⟩
  have hsourceNonempty := hreplace.1
  have htargetTwo : 2 ≤ target.length := by
    have hcount := hreplace.2.1
    omega
  have hparse := parseTask_eq_of_shape hparseAt hparseShape
    (tasks := target) (by omega) htargetRows
  have hcombine := combineTask_eq_of_slices hcombineAt
    (tasks := target) (root := root) (by omega) htargetRows hroot
      hcombineSlices
  have htail := hreplace.eq_drop_of_rows hsourceRows htargetRows
  have htarget : target =
      compactNumericParseTask :: root :: source.drop 1 := by
    cases target with
    | nil => simp at htargetTwo
    | cons first rest =>
        cases rest with
        | nil => simp at htargetTwo
        | cons second tail =>
            have hfirst : first = compactNumericParseTask := by
              simpa using hparse
            have hsecond : second = root := by
              simpa using hcombine
            have hrest : tail = source.drop 1 := by
              simpa using htail
            simp [hfirst, hsecond, hrest]
  simpa only [hrootTag] using And.intro htagCases htarget

theorem CompactNumericVerifierTwoParseScheduleRows.sound
    {tokenTable width tokenCount
      sourceBoundary targetBoundary tableWidth valueBound
      rootStart rootFinish rootTag : Nat}
    {firstParseCoordinates secondParseCoordinates combineCoordinates :
      CompactNumericVerifierTaskRowCoordinates}
    {firstParseSize secondParseSize combineSize :
      CompactNumericVerifierTaskSizeWitness}
    {source target : List CompactNumericVerifierTask}
    {root : CompactNumericVerifierTask}
    (hrows : CompactNumericVerifierTwoParseScheduleRows
      tokenTable width tokenCount
      sourceBoundary source.length targetBoundary target.length valueBound
      rootStart rootFinish rootTag
      firstParseCoordinates secondParseCoordinates combineCoordinates
      firstParseSize secondParseSize combineSize)
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
    (hrootTag : root.1 = rootTag) :
    (root.1 = 3 ∨ root.1 = 9) ∧
      target = compactNumericParseTask :: compactNumericParseTask ::
        root :: source.drop 1 := by
  rcases hrows with
    ⟨htagCases, hreplace, hfirstAt, hfirstShape,
      hsecondAt, hsecondShape, hcombineAt, hcombineSlices⟩
  have hsourceNonempty := hreplace.1
  have htargetThree : 3 ≤ target.length := by
    have hcount := hreplace.2.1
    omega
  have hfirstParse := parseTask_eq_of_shape hfirstAt hfirstShape
    (tasks := target) (by omega) htargetRows
  have hsecondParse := parseTask_eq_of_shape hsecondAt hsecondShape
    (tasks := target) (by omega) htargetRows
  have hcombine := combineTask_eq_of_slices hcombineAt
    (tasks := target) (root := root) (by omega) htargetRows hroot
      hcombineSlices
  have htail := hreplace.eq_drop_of_rows hsourceRows htargetRows
  have htarget : target = compactNumericParseTask ::
      compactNumericParseTask :: root :: source.drop 1 := by
    cases target with
    | nil => simp at htargetThree
    | cons first rest =>
        cases rest with
        | nil => simp at htargetThree
        | cons second rest' =>
            cases rest' with
            | nil => simp at htargetThree
            | cons third tail =>
                have hfirst : first = compactNumericParseTask := by
                  simpa using hfirstParse
                have hsecond : second = compactNumericParseTask := by
                  simpa using hsecondParse
                have hthird : third = root := by
                  simpa using hcombine
                have hrest : tail = source.drop 1 := by
                  simpa using htail
                simp [hfirst, hsecond, hthird, hrest]
  simpa only [hrootTag] using And.intro htagCases htarget

#print axioms CompactNumericVerifierOneParseScheduleRows.sound
#print axioms CompactNumericVerifierTwoParseScheduleRows.sound

end FoundationCompactNumericListedDirectVerifierParseScheduleRows
