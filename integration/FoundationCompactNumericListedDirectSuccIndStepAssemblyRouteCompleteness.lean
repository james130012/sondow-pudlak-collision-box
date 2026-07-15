import integration.FoundationCompactNumericListedDirectPackedRouteTable
import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpointCompleteness
import integration.FoundationCompactNumericListedDirectSuccIndStepAssemblyRoute

/-!
# Canonical completeness for the induction step assembly
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSuccIndStepAssemblyRouteCompleteness

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaConstructors
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaConstructorSlices
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
open FoundationCompactNumericListedDirectSuccIndStepAssemblyRoute
open FoundationCompactNumericListedDirectPackedRouteTable
open FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpointCompleteness

theorem exists_compactSuccIndStepAssemblyRoute_of_executable_outputs
    {tokenTable width tokenCount
      negatedStepZeroStateBoundary negatedQuantifiedStepStateBoundary : Nat}
    {stepZeroSlot stepSuccessorSlot negatedStepZeroSlot
      stepDisjunctionSlot quantifiedStepSlot negatedQuantifiedStepSlot
      quantifiedFinalSlot emptySlot : CompactNatListRowSlot}
    {stepZero stepSuccessor negatedStepZero stepDisjunction quantifiedStep
      negatedQuantifiedStep quantifiedFinal : List Nat}
    (hstepZeroSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount stepZeroSlot stepZero)
    (hstepSuccessorSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount stepSuccessorSlot stepSuccessor)
    (hnegatedStepZeroSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount negatedStepZeroSlot negatedStepZero)
    (hstepDisjunctionSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount stepDisjunctionSlot stepDisjunction)
    (hquantifiedStepSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount quantifiedStepSlot quantifiedStep)
    (hnegatedQuantifiedStepSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount negatedQuantifiedStepSlot
        negatedQuantifiedStep)
    (hquantifiedFinalSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount quantifiedFinalSlot quantifiedFinal)
    (hemptySlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount emptySlot [])
    (hnegatedStepZeroStateRows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount negatedStepZeroStateBoundary
        (compactFormulaTransformStateTrace (3, [])
          (compactSyntaxRunFuelBound stepZero)
          (compactFormulaTransformInitialState 1 stepZero)))
    (hnegatedQuantifiedStepStateRows :
      CompactFormulaTransformStateListRowLayouts
        tokenTable width tokenCount negatedQuantifiedStepStateBoundary
          (compactFormulaTransformStateTrace (3, [])
            (compactSyntaxRunFuelBound quantifiedStep)
            (compactFormulaTransformInitialState 0 quantifiedStep)))
    (hnegatedStepZero : negatedStepZero =
      (compactExactFormulaTransformResult
        (compactFormulaTransformResult
          (3, []) (1, stepZero))).getD [])
    (hstepDisjunction : stepDisjunction =
      tokenFormulaOr negatedStepZero stepSuccessor)
    (hquantifiedStep : quantifiedStep = tokenFormulaAll stepDisjunction)
    (hnegatedQuantifiedStep : negatedQuantifiedStep =
      (compactExactFormulaTransformResult
        (compactFormulaTransformResult
          (3, []) (0, quantifiedStep))).getD [])
    (hquantifiedFinal : quantifiedFinal = tokenFormulaAll stepZero) :
    ∃ coordinates : CompactSuccIndStepAssemblyRouteCoordinates,
      CompactSuccIndStepAssemblyRoute tokenTable width tokenCount
        stepZeroSlot stepSuccessorSlot negatedStepZeroSlot
        stepDisjunctionSlot quantifiedStepSlot negatedQuantifiedStepSlot
        quantifiedFinalSlot emptySlot coordinates := by
  rcases exists_compactFormulaTransformTotalExactEndpoint_of_canonical_trace
      hemptySlot.rows hstepZeroSlot.rows hnegatedStepZeroSlot.rows
      hemptySlot.rows hemptySlot.layout hstepZeroSlot.elements
      hnegatedStepZeroSlot.elements hemptySlot.elements
      hnegatedStepZeroStateRows hnegatedStepZero with
    ⟨negatedStepZeroTrace, hnegatedStepZeroEndpoint⟩
  have hstepDisjunctionSlicesValue :
      CompactAdditiveBinaryFormulaConstructorSlices
        tokenTable width tokenCount 5
        negatedStepZeroSlot.start negatedStepZeroSlot.finish
          negatedStepZero.length
        stepSuccessorSlot.start stepSuccessorSlot.finish stepSuccessor.length
        stepDisjunctionSlot.start stepDisjunctionSlot.finish
          stepDisjunction.length :=
    (compactAdditiveFormulaOrSlices_iff hnegatedStepZeroSlot.layout
      hstepSuccessorSlot.layout hstepDisjunctionSlot.layout).2
        hstepDisjunction
  have hstepDisjunctionSlices :
      CompactAdditiveBinaryFormulaConstructorSlices
        tokenTable width tokenCount 5
        negatedStepZeroSlot.start negatedStepZeroSlot.finish
          negatedStepZeroSlot.count
        stepSuccessorSlot.start stepSuccessorSlot.finish
          stepSuccessorSlot.count
        stepDisjunctionSlot.start stepDisjunctionSlot.finish
          stepDisjunctionSlot.count := by
    simpa only [hnegatedStepZeroSlot.1, hstepSuccessorSlot.1,
      hstepDisjunctionSlot.1] using hstepDisjunctionSlicesValue
  have hquantifiedStepSlicesValue :
      CompactAdditiveUnaryFormulaConstructorSlices
        tokenTable width tokenCount 6
        stepDisjunctionSlot.start stepDisjunctionSlot.finish
          stepDisjunction.length
        quantifiedStepSlot.start quantifiedStepSlot.finish
          quantifiedStep.length :=
    (compactAdditiveFormulaAllSlices_iff hstepDisjunctionSlot.layout
      hquantifiedStepSlot.layout).2 hquantifiedStep
  have hquantifiedStepSlices :
      CompactAdditiveUnaryFormulaConstructorSlices
        tokenTable width tokenCount 6
        stepDisjunctionSlot.start stepDisjunctionSlot.finish
          stepDisjunctionSlot.count
        quantifiedStepSlot.start quantifiedStepSlot.finish
          quantifiedStepSlot.count := by
    simpa only [hstepDisjunctionSlot.1, hquantifiedStepSlot.1]
      using hquantifiedStepSlicesValue
  rcases exists_compactFormulaTransformTotalExactEndpoint_of_canonical_trace
      hemptySlot.rows hquantifiedStepSlot.rows
      hnegatedQuantifiedStepSlot.rows hemptySlot.rows
      hemptySlot.layout hquantifiedStepSlot.elements
      hnegatedQuantifiedStepSlot.elements hemptySlot.elements
      hnegatedQuantifiedStepStateRows hnegatedQuantifiedStep with
    ⟨negatedQuantifiedStepTrace, hnegatedQuantifiedStepEndpoint⟩
  have hquantifiedFinalSlicesValue :
      CompactAdditiveUnaryFormulaConstructorSlices
        tokenTable width tokenCount 6
        stepZeroSlot.start stepZeroSlot.finish stepZero.length
        quantifiedFinalSlot.start quantifiedFinalSlot.finish
          quantifiedFinal.length :=
    (compactAdditiveFormulaAllSlices_iff hstepZeroSlot.layout
      hquantifiedFinalSlot.layout).2 hquantifiedFinal
  have hquantifiedFinalSlices :
      CompactAdditiveUnaryFormulaConstructorSlices
        tokenTable width tokenCount 6
        stepZeroSlot.start stepZeroSlot.finish stepZeroSlot.count
        quantifiedFinalSlot.start quantifiedFinalSlot.finish
          quantifiedFinalSlot.count := by
    simpa only [hstepZeroSlot.1, hquantifiedFinalSlot.1]
      using hquantifiedFinalSlicesValue
  let coordinates : CompactSuccIndStepAssemblyRouteCoordinates :=
    { negatedStepZeroTrace := negatedStepZeroTrace
      negatedQuantifiedStepTrace := negatedQuantifiedStepTrace }
  refine ⟨coordinates, by simpa using hemptySlot.1,
    hstepSuccessorSlot.2.1, ?_, hstepDisjunctionSlot.2.1,
    hstepDisjunctionSlices, hquantifiedStepSlices, ?_,
    hquantifiedFinalSlot.2.1, hquantifiedFinalSlices⟩
  · simpa [coordinates, hemptySlot.1, hstepZeroSlot.1,
      hnegatedStepZeroSlot.1] using hnegatedStepZeroEndpoint
  · simpa [coordinates, hemptySlot.1, hquantifiedStepSlot.1,
      hnegatedQuantifiedStepSlot.1] using hnegatedQuantifiedStepEndpoint

#print axioms
  exists_compactSuccIndStepAssemblyRoute_of_executable_outputs

end FoundationCompactNumericListedDirectSuccIndStepAssemblyRouteCompleteness
