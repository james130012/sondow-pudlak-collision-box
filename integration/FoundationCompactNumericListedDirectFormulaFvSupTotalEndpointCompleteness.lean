import integration.FoundationCompactNumericListedDirectPackedRouteTable
import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpointCompleteness
import integration.FoundationCompactNumericListedDirectFormulaFvSupTotalEndpoint

/-!
# Canonical completeness for the free-variable supremum endpoint
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaFvSupTotalEndpointCompleteness

open FoundationCompactSyntaxTokenMachine
open FoundationCompactSyntaxTransformationTraceCore
open FoundationCompactNumericFormulaFvSup
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectListFvSupRows
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
open FoundationCompactNumericListedDirectFormulaFvSupTotalEndpoint
open FoundationCompactNumericListedDirectPackedRouteTable
open FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpointCompleteness

theorem exists_compactFormulaFvSupTotalEndpoint_of_executable_output
    {tokenTable width tokenCount stateBoundary binderArity maximum : Nat}
    {emptySlot inputSlot fvarListSlot : CompactNatListRowSlot}
    {input fvarList : List Nat}
    (hemptySlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount emptySlot [])
    (hinputSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount inputSlot input)
    (hfvarListSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount fvarListSlot fvarList)
    (hstateRows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary
        (compactFormulaTransformStateTrace (4, [])
          (compactSyntaxRunFuelBound input)
          (compactFormulaTransformInitialState binderArity input)))
    (hfvarList : fvarList =
      (compactExactFormulaTransformResult
        (compactFormulaTransformResult
          (4, []) (binderArity, input))).getD [])
    (hmaximum : maximum = listFvSup fvarList) :
    ∃ coordinates : CompactFormulaFvSupTotalEndpointCoordinates,
      CompactFormulaFvSupTotalEndpoint tokenTable width tokenCount
        binderArity maximum emptySlot inputSlot fvarListSlot coordinates := by
  rcases exists_compactFormulaTransformTotalExactEndpoint_of_canonical_trace
      hemptySlot.rows hinputSlot.rows hfvarListSlot.rows hemptySlot.rows
      hemptySlot.layout hinputSlot.elements hfvarListSlot.elements
      hemptySlot.elements hstateRows hfvarList with
    ⟨trace, htransformEndpoint⟩
  have hmaximumRowsValue : CompactAdditiveNatListFvSupRows
      tokenTable width tokenCount fvarListSlot.boundary fvarList.length
        maximum :=
    (compactAdditiveNatListFvSupRows_iff
      hfvarListSlot.elements maximum).2 hmaximum
  have hmaximumRows : CompactAdditiveNatListFvSupRows
      tokenTable width tokenCount fvarListSlot.boundary fvarListSlot.count
        maximum := by
    simpa only [hfvarListSlot.1] using hmaximumRowsValue
  let coordinates : CompactFormulaFvSupTotalEndpointCoordinates :=
    { trace := trace }
  refine ⟨coordinates, by simpa using hemptySlot.1, ?_, hmaximumRows⟩
  simpa [coordinates, hemptySlot.1, hinputSlot.1, hfvarListSlot.1]
    using htransformEndpoint

#print axioms
  exists_compactFormulaFvSupTotalEndpoint_of_executable_output

end FoundationCompactNumericListedDirectFormulaFvSupTotalEndpointCompleteness
