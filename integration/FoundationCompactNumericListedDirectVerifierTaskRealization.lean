import integration.FoundationCompactNumericListedDirectVerifierValueRealization
import integration.FoundationCompactNumericListedDirectVerifierTaskListRowsFormula

/-!
# Reverse realization of verifier tasks

The bounded task graph is decoded into the exact typed verifier task.  The
construction is then lifted row by row to an arbitrary task stack.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTaskRealization

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierValueRealization

theorem CompactNumericVerifierTaskCoreGraph.realizeDirectLayout
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    (hgraph : CompactNumericVerifierTaskCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    ∃ task : CompactNumericVerifierTask,
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        coordinates.start coordinates.finish task ∧
      task.1 = coordinates.tag := by
  have hbounds := CompactNumericVerifierTaskCoreGraph.bounds hgraph
  rcases hgraph with
    ⟨htag, hgammaLayout, hgammaRows, hgammaSizeEq, hgammaSize,
      hfirst, hsecond, hwitness, hsuffix⟩
  have hgammaBoundarySize : Nat.size coordinates.gammaBoundary ≤
      (coordinates.gammaCount + 1) * tokenCount := by
    rw [← hgammaSizeEq]
    exact hgammaSize
  rcases CompactAdditiveNatListListRowsWellFormed.realizeDirectLayout
      hgammaLayout hgammaRows hgammaBoundarySize with
    ⟨gamma, hgammaLength, hgammaDirect, _hgammaValueRows⟩
  rcases CompactAdditiveNatListSlice.realizeDirectLayout
      hfirst hbounds.firstFinish_le with
    ⟨firstFormula, hfirstLength, hfirstDirect⟩
  rcases CompactAdditiveNatListSlice.realizeDirectLayout
      hsecond hbounds.secondFinish_le with
    ⟨secondFormula, hsecondLength, hsecondDirect⟩
  rcases CompactAdditiveNatListSlice.realizeDirectLayout
      hwitness hbounds.witnessFinish_le with
    ⟨witness, hwitnessLength, hwitnessDirect⟩
  rcases CompactAdditiveNatListSlice.realizeDirectLayout
      hsuffix hbounds.finish_le with
    ⟨suffix, hsuffixLength, hsuffixDirect⟩
  let fields : CompactNumericNodeFields :=
    (gamma, (firstFormula, (secondFormula, (witness, suffix))))
  let task : CompactNumericVerifierTask := (coordinates.tag, fields)
  have hfields : CompactNumericNodeFieldsDirectLayout
      tokenTable width tokenCount (coordinates.start + 1)
        coordinates.finish fields := by
    refine ⟨coordinates.gammaFinish, coordinates.firstFinish,
      coordinates.secondFinish, coordinates.witnessFinish, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [fields, hgammaLength] using hgammaDirect
    · simpa [fields, hfirstLength] using hfirstDirect
    · simpa [fields, hsecondLength] using hsecondDirect
    · simpa [fields, hwitnessLength] using hwitnessDirect
    · simpa [fields, hsuffixLength] using hsuffixDirect
  refine ⟨task, ?_, rfl⟩
  exact ⟨coordinates.start + 1, by simpa [task] using htag,
    by simpa [task] using hfields⟩

theorem CompactNumericVerifierTaskBoundedRow.realizeDirectLayout
    {tokenTable width tokenCount taskBoundary valueBound rowIndex : Nat}
    (hrow : CompactNumericVerifierTaskBoundedRow
      tokenTable width tokenCount taskBoundary valueBound rowIndex) :
    ∃ start finish,
    ∃ task : CompactNumericVerifierTask,
      CompactFixedWidthEntry taskBoundary tokenCount rowIndex start ∧
      CompactFixedWidthEntry taskBoundary tokenCount (rowIndex + 1) finish ∧
      CompactNumericVerifierTaskDirectLayout
        tokenTable width tokenCount start finish task := by
  rcases hrow with
    ⟨start, _hstartBound, finish, _hfinishBound,
      tag, _htagBound, gammaFinish, _hgammaFinishBound,
      gammaCount, _hgammaCountBound, gammaBoundary, _hgammaBoundaryBound,
      firstFinish, _hfirstFinishBound, firstCount, _hfirstCountBound,
      secondFinish, _hsecondFinishBound, secondCount, _hsecondCountBound,
      witnessFinish, _hwitnessFinishBound, witnessCount, _hwitnessCountBound,
      suffixCount, _hsuffixCountBound,
      gammaBoundarySize, _hgammaBoundarySizeBound,
      hstartEntry, hfinishEntry, hcore⟩
  rcases CompactNumericVerifierTaskCoreGraph.realizeDirectLayout hcore with
    ⟨task, htask, _htag⟩
  exact ⟨start, finish, task, hstartEntry, hfinishEntry, htask⟩

theorem CompactNumericVerifierTaskListRowsGraph.realizeDirectRows
    {tokenTable width tokenCount start finish taskBoundary taskCount
      tableWidth valueBound : Nat}
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start taskCount finish taskBoundary)
    (hrows : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount taskBoundary taskCount
        tableWidth valueBound) :
    ∃ tasks : List CompactNumericVerifierTask,
      tasks.length = taskCount ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
          taskBoundary tasks := by
  classical
  rcases hlayout with
    ⟨_bodyStart, _hbodyStart, _hheader, hboundary⟩
  have hexists (index : Nat) (hindex : index < taskCount) :
      ∃ task : CompactNumericVerifierTask,
      ∃ left, left ≤ tokenCount ∧
      ∃ right, right ≤ tokenCount ∧
        CompactFixedWidthEntry taskBoundary tokenCount index left ∧
        CompactFixedWidthEntry taskBoundary tokenCount (index + 1) right ∧
        CompactNumericVerifierTaskDirectLayout
          tokenTable width tokenCount left right task := by
    rcases CompactNumericVerifierTaskBoundedRow.realizeDirectLayout
        (hrows.2 index hindex) with
      ⟨rowLeft, rowRight, task,
        hrowLeftEntry, hrowRightEntry, htask⟩
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
    exact ⟨task, left, hleft, right, hright,
      hleftEntry, hrightEntry, htask⟩
  let taskAt (index : Fin taskCount) : CompactNumericVerifierTask :=
    Classical.choose (hexists index index.isLt)
  let tasks : List CompactNumericVerifierTask := List.ofFn taskAt
  have htasksLength : tasks.length = taskCount := by
    simp [tasks]
  have htaskRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        taskBoundary tasks := by
    intro index hindex
    have hcount : index < taskCount := by
      simpa [htasksLength] using hindex
    have hspec := Classical.choose_spec (hexists index hcount)
    rcases hspec with
      ⟨left, hleft, right, hright,
        hleftEntry, hrightEntry, htask⟩
    refine ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, ?_⟩
    have hget : tasks.getI index = taskAt ⟨index, hcount⟩ := by
      rw [List.getI_eq_getElem _ (by simpa [htasksLength] using hcount)]
      simp [tasks]
    rw [hget]
    exact htask
  exact ⟨tasks, htasksLength, htaskRows⟩

#print axioms CompactNumericVerifierTaskCoreGraph.realizeDirectLayout
#print axioms CompactNumericVerifierTaskBoundedRow.realizeDirectLayout
#print axioms CompactNumericVerifierTaskListRowsGraph.realizeDirectRows

end FoundationCompactNumericListedDirectVerifierTaskRealization
