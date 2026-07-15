import integration.FoundationCompactNumericListedDirectPackedRouteTable
import integration.FoundationCompactNumericListedDirectSuccIndOuterAssemblyRoute

/-!
# Canonical completeness for the outer induction assembly
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSuccIndOuterAssemblyRouteCompleteness

open FoundationCompactNumericFormulaConstructors
open FoundationCompactNumericListedDirectFormulaConstructorSlices
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
open FoundationCompactNumericListedDirectSuccIndOuterAssemblyRoute
open FoundationCompactNumericListedDirectPackedRouteTable

theorem compactSuccIndOuterAssemblyRoute_of_constructor_outputs
    {tokenTable width tokenCount : Nat}
    {negatedBaseSlot negatedQuantifiedStepSlot quantifiedFinalSlot
      innerDisjunctionSlot sentenceSlot : CompactNatListRowSlot}
    {negatedBase negatedQuantifiedStep quantifiedFinal innerDisjunction
      sentence : List Nat}
    (hnegatedBaseSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount negatedBaseSlot negatedBase)
    (hnegatedQuantifiedStepSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount negatedQuantifiedStepSlot
        negatedQuantifiedStep)
    (hquantifiedFinalSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount quantifiedFinalSlot quantifiedFinal)
    (hinnerDisjunctionSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount innerDisjunctionSlot innerDisjunction)
    (hsentenceSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount sentenceSlot sentence)
    (hinnerDisjunction : innerDisjunction =
      tokenFormulaOr negatedQuantifiedStep quantifiedFinal)
    (hsentence : sentence = tokenFormulaOr negatedBase innerDisjunction) :
    CompactSuccIndOuterAssemblyRoute tokenTable width tokenCount
      negatedBaseSlot negatedQuantifiedStepSlot quantifiedFinalSlot
      innerDisjunctionSlot sentenceSlot := by
  have hinnerSlicesValue : CompactAdditiveBinaryFormulaConstructorSlices
      tokenTable width tokenCount 5
      negatedQuantifiedStepSlot.start negatedQuantifiedStepSlot.finish
        negatedQuantifiedStep.length
      quantifiedFinalSlot.start quantifiedFinalSlot.finish
        quantifiedFinal.length
      innerDisjunctionSlot.start innerDisjunctionSlot.finish
        innerDisjunction.length :=
    (compactAdditiveFormulaOrSlices_iff
      hnegatedQuantifiedStepSlot.layout hquantifiedFinalSlot.layout
      hinnerDisjunctionSlot.layout).2 hinnerDisjunction
  have hinnerSlices : CompactAdditiveBinaryFormulaConstructorSlices
      tokenTable width tokenCount 5
      negatedQuantifiedStepSlot.start negatedQuantifiedStepSlot.finish
        negatedQuantifiedStepSlot.count
      quantifiedFinalSlot.start quantifiedFinalSlot.finish
        quantifiedFinalSlot.count
      innerDisjunctionSlot.start innerDisjunctionSlot.finish
        innerDisjunctionSlot.count := by
    simpa only [hnegatedQuantifiedStepSlot.1, hquantifiedFinalSlot.1,
      hinnerDisjunctionSlot.1] using hinnerSlicesValue
  have hsentenceSlicesValue : CompactAdditiveBinaryFormulaConstructorSlices
      tokenTable width tokenCount 5
      negatedBaseSlot.start negatedBaseSlot.finish negatedBase.length
      innerDisjunctionSlot.start innerDisjunctionSlot.finish
        innerDisjunction.length
      sentenceSlot.start sentenceSlot.finish sentence.length :=
    (compactAdditiveFormulaOrSlices_iff hnegatedBaseSlot.layout
      hinnerDisjunctionSlot.layout hsentenceSlot.layout).2 hsentence
  have hsentenceSlices : CompactAdditiveBinaryFormulaConstructorSlices
      tokenTable width tokenCount 5
      negatedBaseSlot.start negatedBaseSlot.finish negatedBaseSlot.count
      innerDisjunctionSlot.start innerDisjunctionSlot.finish
        innerDisjunctionSlot.count
      sentenceSlot.start sentenceSlot.finish sentenceSlot.count := by
    simpa only [hnegatedBaseSlot.1, hinnerDisjunctionSlot.1,
      hsentenceSlot.1] using hsentenceSlicesValue
  exact ⟨hnegatedBaseSlot.2.1, hnegatedQuantifiedStepSlot.2.1,
    hquantifiedFinalSlot.2.1, hinnerDisjunctionSlot.2.1, hinnerSlices,
    hsentenceSlot.2.1, hsentenceSlices⟩

#print axioms compactSuccIndOuterAssemblyRoute_of_constructor_outputs

end FoundationCompactNumericListedDirectSuccIndOuterAssemblyRouteCompleteness
