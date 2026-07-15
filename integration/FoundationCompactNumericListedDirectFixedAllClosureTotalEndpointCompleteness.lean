import integration.FoundationCompactNumericListedDirectPackedRouteTable
import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpointCompleteness
import integration.FoundationCompactNumericListedDirectFixedAllClosureTotalEndpoint

/-!
# Canonical completeness for the fixed universal-closure endpoint

The executable mode-five transform and the explicit closure constructor produce
the complete bounded endpoint in one shared token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFixedAllClosureTotalEndpointCompleteness

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericAllClosure
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
open FoundationCompactNumericListedDirectAllClosureSlices
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
open FoundationCompactNumericListedDirectFixedAllClosureTotalEndpoint
open FoundationCompactNumericListedDirectPackedRouteTable
open FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpointCompleteness

theorem exists_compactFixedAllClosureTotalEndpoint_of_executable_output
    {tokenTable width tokenCount depth stateBoundary : Nat}
    {emptySlot captureSlot inputSlot fixedSlot closureSlot :
      CompactNatListRowSlot}
    {capture input fixed closure : List Nat}
    (hemptySlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount emptySlot [])
    (hcaptureSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount captureSlot capture)
    (hinputSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount inputSlot input)
    (hfixedSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount fixedSlot fixed)
    (hclosureSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount closureSlot closure)
    (hstateRows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary
        (compactFormulaTransformStateTrace (5, capture)
          (compactSyntaxRunFuelBound input)
          (compactFormulaTransformInitialState 0 input)))
    (hcaptureLength : capture.length = depth)
    (hfixed : fixed =
      (compactExactFormulaTransformResult
        (compactFormulaTransformResult
          (5, capture) (0, input))).getD [])
    (hclosure : closure = compactAllClosureTokens depth fixed) :
    ∃ coordinates : CompactFixedAllClosureTotalEndpointCoordinates,
      CompactFixedAllClosureTotalEndpoint tokenTable width tokenCount depth
        emptySlot captureSlot inputSlot fixedSlot closureSlot coordinates := by
  rcases exists_compactFormulaTransformTotalExactEndpoint_of_canonical_trace
      hcaptureSlot.rows hinputSlot.rows hfixedSlot.rows hemptySlot.rows
      hcaptureSlot.layout hinputSlot.elements hfixedSlot.elements
      hemptySlot.elements hstateRows hfixed with
    ⟨trace, htransformEndpoint⟩
  have hcaptureCount : captureSlot.count = depth := by
    rw [hcaptureSlot.1, hcaptureLength]
  have hclosureSlicesValue : CompactAdditiveAllClosureSlices
      tokenTable width tokenCount depth
        fixedSlot.start fixedSlot.finish fixed.length
        closureSlot.start closureSlot.finish closure.length :=
    (compactAdditiveAllClosureSlices_iff
      hfixedSlot.layout hclosureSlot.layout).2 hclosure
  have hclosureSlices : CompactAdditiveAllClosureSlices
      tokenTable width tokenCount depth
        fixedSlot.start fixedSlot.finish fixedSlot.count
        closureSlot.start closureSlot.finish closureSlot.count := by
    simpa only [hfixedSlot.1, hclosureSlot.1] using hclosureSlicesValue
  let coordinates : CompactFixedAllClosureTotalEndpointCoordinates :=
    { trace := trace }
  refine ⟨coordinates, ?_, hcaptureCount, ?_, hclosureSlot.2.1,
    hclosureSlices⟩
  · simpa using hemptySlot.1
  · simpa [coordinates, hcaptureSlot.1, hinputSlot.1, hfixedSlot.1,
      hemptySlot.1] using htransformEndpoint

#print axioms
  exists_compactFixedAllClosureTotalEndpoint_of_executable_output

end FoundationCompactNumericListedDirectFixedAllClosureTotalEndpointCompleteness
