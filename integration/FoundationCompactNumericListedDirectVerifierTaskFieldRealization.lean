import integration.FoundationCompactNumericListedDirectChildResultListPushDropRows
import integration.FoundationCompactNumericListedDirectVerifierTaskRealization

/-!
# Field-preserving realization of one verifier task

The existing task realization returns the typed task.  This refinement also
retains the exact checked row layouts and lengths of Gamma, both formula
fields, the witness, and the suffix.  It lets rule graphs use the parsed task
coordinates without any coordinate-choice assumption.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTaskFieldRealization

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierValueRealization
open FoundationCompactNumericListedDirectVerifierPayloadEquality

theorem CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    (hgraph : CompactNumericVerifierTaskCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    ∃ task : CompactNumericVerifierTask,
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        coordinates.start coordinates.finish task ∧
      task.1 = coordinates.tag ∧
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
    ⟨gamma, hgammaLength, hgammaDirect, hgammaValueRows⟩
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
  have htask : CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount coordinates.start coordinates.finish task :=
    ⟨coordinates.start + 1, by simpa [task] using htag,
      by simpa [task] using hfields⟩
  refine ⟨task, htask, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [task, fields] using hgammaValueRows
  · simpa [task, fields] using hgammaLength
  · simpa [task, fields] using hfirstDirect
  · simpa [task, fields] using hfirstLength
  · simpa [task, fields] using hsecondDirect
  · simpa [task, fields] using hsecondLength
  · simpa [task, fields] using hwitnessDirect
  · simpa [task, fields] using hwitnessLength
  · simpa [task, fields] using hsuffixDirect
  · simpa [task, fields] using hsuffixLength

theorem CompactNumericVerifierTaskCoreGraph.realizedTask_eq
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    {actualTask realizedTask : CompactNumericVerifierTask}
    (hcore : CompactNumericVerifierTaskCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (hactual : CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount coordinates.start coordinates.finish
        actualTask)
    (hrealized : CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount coordinates.start coordinates.finish
        realizedTask) :
    realizedTask = actualTask := by
  have hbounds := hcore.bounds
  have hstartFinish : coordinates.start < coordinates.finish := by
    rcases hcore with
      ⟨_htag, hgamma, _hgammaRows, _hgammaSizeEq, _hgammaSize,
        hfirst, hsecond, hwitness, hsuffix⟩
    have hgammaStartFinish :=
      CompactAdditiveStructuredListLayout.start_lt_finish hgamma
    rcases hfirst with
      ⟨firstBodyStart, _hfirstBodyStart, hfirstHeader, hfirstFinish⟩
    rcases hsecond with
      ⟨secondBodyStart, _hsecondBodyStart, hsecondHeader, hsecondFinish⟩
    rcases hwitness with
      ⟨witnessBodyStart, _hwitnessBodyStart,
        hwitnessHeader, hwitnessFinish⟩
    rcases hsuffix with
      ⟨suffixBodyStart, _hsuffixBodyStart, hsuffixHeader, hsuffixFinish⟩
    have hfirstBody : firstBodyStart = coordinates.gammaFinish + 1 :=
      hfirstHeader.1.2.1
    have hsecondBody : secondBodyStart = coordinates.firstFinish + 1 :=
      hsecondHeader.1.2.1
    have hwitnessBody :
        witnessBodyStart = coordinates.secondFinish + 1 :=
      hwitnessHeader.1.2.1
    have hsuffixBody : suffixBodyStart = coordinates.witnessFinish + 1 :=
      hsuffixHeader.1.2.1
    omega
  have hslices := CompactFixedWidthTokenSlicesEq.refl
    (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
    (Nat.le_of_lt hstartFinish) hbounds.finish_le
  rcases CompactFixedWidthTokenSlicesEq.verifierTaskPrefix_eq
      (sourceBase := coordinates.start)
      (sourceLimit := coordinates.finish)
      (targetBase := coordinates.start)
      (targetLimit := coordinates.finish)
      (sourceStart := coordinates.start)
      (sourceFinish := coordinates.finish)
      (targetStart := coordinates.start)
      (targetFinish := coordinates.finish)
      (offset := 0)
      hslices rfl rfl (by omega)
      (le_refl coordinates.finish) (le_refl coordinates.finish)
      hactual hrealized with
    ⟨_finishOffset, _hactualFinish, _hrealizedFinish, htask⟩
  exact htask

#print axioms CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
#print axioms CompactNumericVerifierTaskCoreGraph.realizedTask_eq

end FoundationCompactNumericListedDirectVerifierTaskFieldRealization
