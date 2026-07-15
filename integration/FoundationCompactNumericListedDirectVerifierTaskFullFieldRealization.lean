import integration.FoundationCompactNumericListedDirectVerifierTaskFieldRealization

/-!
# Full-field realization of one verifier task

This companion exposes the complete direct layout of Gamma together with the
four remaining field layouts of the task recovered from a core graph.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTaskFullFieldRealization

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula

theorem CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithAllFields
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    (hgraph : CompactNumericVerifierTaskCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    ∃ task : CompactNumericVerifierTask,
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        coordinates.start coordinates.finish task ∧
      task.1 = coordinates.tag ∧
      CompactAdditiveNatListListDirectLayout tokenTable width tokenCount
        (coordinates.start + 1) coordinates.gammaFinish task.2.1 ∧
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        coordinates.gammaFinish coordinates.firstFinish task.2.2.1 ∧
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        coordinates.firstFinish coordinates.secondFinish task.2.2.2.1 ∧
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        coordinates.secondFinish coordinates.witnessFinish task.2.2.2.2.1 ∧
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        coordinates.witnessFinish coordinates.finish task.2.2.2.2.2 := by
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
        hgraph with
    ⟨task, htask, htag, hgammaRows, hgammaLength,
      hfirst, _hfirstLength, hsecond, _hsecondLength,
      hwitness, _hwitnessLength, hsuffix, _hsuffixLength⟩
  rcases hgraph with
    ⟨_htag, hgammaLayout, _hgammaWellFormed, hgammaSizeEq, hgammaSize,
      _hfirst, _hsecond, _hwitness, _hsuffix⟩
  have hgamma : CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount (coordinates.start + 1)
        coordinates.gammaFinish task.2.1 := by
    refine ⟨coordinates.gammaBoundary, ?_, hgammaRows, ?_⟩
    · simpa [hgammaLength] using hgammaLayout
    · simpa [hgammaLength, hgammaSizeEq] using hgammaSize
  exact ⟨task, htask, htag, hgamma, hfirst, hsecond, hwitness, hsuffix⟩

#print axioms CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithAllFields

end FoundationCompactNumericListedDirectVerifierTaskFullFieldRealization
