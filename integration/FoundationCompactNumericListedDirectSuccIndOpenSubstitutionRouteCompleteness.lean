import integration.FoundationCompactNumericListedDirectPackedRouteTable
import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpointCompleteness

/-!
# Canonical completeness for the open substitution route

The shift, substitution, and one-variable fixitr executions use canonical
state traces and canonical slots in one shared token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRouteCompleteness

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
open FoundationCompactNumericListedDirectPackedRouteTable
open FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpointCompleteness

theorem exists_compactSuccIndOpenSubstitutionRoute_of_executable_outputs
    {tokenTable width tokenCount
      shiftStateBoundary substitutionStateBoundary fixitrStateBoundary : Nat}
    {bodySlot witnessSlot captureSlot resultSlot emptySlot
      shiftedSlot substitutedSlot : CompactNatListRowSlot}
    {body witness capture result shifted substituted : List Nat}
    (hbodySlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount bodySlot body)
    (hwitnessSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount witnessSlot witness)
    (hcaptureSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount captureSlot capture)
    (hresultSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount resultSlot result)
    (hemptySlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount emptySlot [])
    (hshiftedSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount shiftedSlot shifted)
    (hsubstitutedSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount substitutedSlot substituted)
    (hcaptureLength : capture.length = 1)
    (hshiftStateRows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount shiftStateBoundary
        (compactFormulaTransformStateTrace (1, [])
          (compactSyntaxRunFuelBound body)
          (compactFormulaTransformInitialState 1 body)))
    (hsubstitutionStateRows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount substitutionStateBoundary
        (compactFormulaTransformStateTrace (2, witness)
          (compactSyntaxRunFuelBound shifted)
          (compactFormulaTransformInitialState 1 shifted)))
    (hfixitrStateRows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount fixitrStateBoundary
        (compactFormulaTransformStateTrace (5, capture)
          (compactSyntaxRunFuelBound substituted)
          (compactFormulaTransformInitialState 0 substituted)))
    (hshifted : shifted =
      (compactExactFormulaTransformResult
        (compactFormulaTransformResult (1, []) (1, body))).getD [])
    (hsubstituted : substituted =
      (compactExactFormulaTransformResult
        (compactFormulaTransformResult
          (2, witness) (1, shifted))).getD [])
    (hresult : result =
      (compactExactFormulaTransformResult
        (compactFormulaTransformResult
          (5, capture) (0, substituted))).getD []) :
    ∃ coordinates : CompactSuccIndOpenSubstitutionRouteCoordinates,
      CompactSuccIndOpenSubstitutionRoute tokenTable width tokenCount
        bodySlot witnessSlot captureSlot resultSlot emptySlot coordinates := by
  rcases exists_compactFormulaTransformTotalExactEndpoint_of_canonical_trace
      hemptySlot.rows hbodySlot.rows hshiftedSlot.rows hemptySlot.rows
      hemptySlot.layout hbodySlot.elements hshiftedSlot.elements
      hemptySlot.elements hshiftStateRows hshifted with
    ⟨shiftTrace, hshiftEndpoint⟩
  rcases exists_compactFormulaTransformTotalExactEndpoint_of_canonical_trace
      hwitnessSlot.rows hshiftedSlot.rows hsubstitutedSlot.rows hemptySlot.rows
      hwitnessSlot.layout hshiftedSlot.elements hsubstitutedSlot.elements
      hemptySlot.elements hsubstitutionStateRows hsubstituted with
    ⟨substitutionTrace, hsubstitutionEndpoint⟩
  rcases exists_compactFormulaTransformTotalExactEndpoint_of_canonical_trace
      hcaptureSlot.rows hsubstitutedSlot.rows hresultSlot.rows hemptySlot.rows
      hcaptureSlot.layout hsubstitutedSlot.elements hresultSlot.elements
      hemptySlot.elements hfixitrStateRows hresult with
    ⟨fixitrTrace, hfixitrEndpoint⟩
  let coordinates : CompactSuccIndOpenSubstitutionRouteCoordinates :=
    { shifted := shiftedSlot
      substituted := substitutedSlot
      shiftTrace := shiftTrace
      substitutionTrace := substitutionTrace
      fixitrTrace := fixitrTrace }
  refine ⟨coordinates, ?_⟩
  refine ⟨by simpa using hemptySlot.1,
    hcaptureSlot.1.trans hcaptureLength, ?_, ?_, ?_⟩
  · simpa [coordinates, hemptySlot.1, hbodySlot.1, hshiftedSlot.1]
      using hshiftEndpoint
  · simpa [coordinates, hwitnessSlot.1, hshiftedSlot.1,
      hsubstitutedSlot.1] using hsubstitutionEndpoint
  · simpa [coordinates, hcaptureSlot.1, hsubstitutedSlot.1,
      hresultSlot.1] using hfixitrEndpoint

#print axioms
  exists_compactSuccIndOpenSubstitutionRoute_of_executable_outputs

end FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRouteCompleteness
