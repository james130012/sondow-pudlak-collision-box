import integration.FoundationCompactNumericListedDirectPackedRouteTable
import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpointCompleteness
import integration.FoundationCompactNumericListedDirectSuccIndBaseNegationRoute

/-!
# Canonical completeness for the induction base-negation route
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSuccIndBaseNegationRouteCompleteness

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectLiteralNatListFormula
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
open FoundationCompactNumericListedDirectSuccIndBaseNegationRoute
open FoundationCompactNumericListedDirectPackedRouteTable
open FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpointCompleteness

theorem exists_compactSuccIndBaseNegationRoute_of_executable_outputs
    {tokenTable width tokenCount baseStateBoundary negationStateBoundary : Nat}
    {bodySlot zeroWitnessSlot baseSlot negatedBaseSlot emptySlot :
      CompactNatListRowSlot}
    {bodyTokens zeroWitnessTokens baseTokens negatedBaseTokens : List Nat}
    (hbodySlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount bodySlot bodyTokens)
    (hzeroWitnessSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount zeroWitnessSlot zeroWitnessTokens)
    (hbaseSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount baseSlot baseTokens)
    (hnegatedBaseSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount negatedBaseSlot negatedBaseTokens)
    (hemptySlot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount emptySlot [])
    (hzeroWitness : zeroWitnessTokens = compactSuccIndZeroWitnessTokens)
    (hbaseStateRows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount baseStateBoundary
        (compactFormulaTransformStateTrace (2, zeroWitnessTokens)
          (compactSyntaxRunFuelBound bodyTokens)
          (compactFormulaTransformInitialState 1 bodyTokens)))
    (hnegationStateRows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount negationStateBoundary
        (compactFormulaTransformStateTrace (3, [])
          (compactSyntaxRunFuelBound baseTokens)
          (compactFormulaTransformInitialState 0 baseTokens)))
    (hbase : baseTokens =
      (compactExactFormulaTransformResult
        (compactFormulaTransformResult
          (2, zeroWitnessTokens) (1, bodyTokens))).getD [])
    (hnegatedBase : negatedBaseTokens =
      (compactExactFormulaTransformResult
        (compactFormulaTransformResult
          (3, []) (0, baseTokens))).getD []) :
    ∃ coordinates : CompactSuccIndBaseNegationRouteCoordinates,
      CompactSuccIndBaseNegationRoute tokenTable width tokenCount
        bodySlot zeroWitnessSlot baseSlot negatedBaseSlot emptySlot
        coordinates := by
  have hliteral : CompactAdditiveLiteralNatListRows
      tokenTable width tokenCount zeroWitnessSlot.start zeroWitnessSlot.count
        compactSuccIndZeroWitnessTokens := by
    apply (compactAdditiveLiteralNatListRows_iff_eq
      hzeroWitnessSlot.layout hzeroWitnessSlot.1).2
    exact hzeroWitness
  rcases exists_compactFormulaTransformTotalExactEndpoint_of_canonical_trace
      hzeroWitnessSlot.rows hbodySlot.rows hbaseSlot.rows hemptySlot.rows
      hzeroWitnessSlot.layout hbodySlot.elements hbaseSlot.elements
      hemptySlot.elements hbaseStateRows hbase with
    ⟨baseTrace, hbaseEndpoint⟩
  rcases exists_compactFormulaTransformTotalExactEndpoint_of_canonical_trace
      hemptySlot.rows hbaseSlot.rows hnegatedBaseSlot.rows hemptySlot.rows
      hemptySlot.layout hbaseSlot.elements hnegatedBaseSlot.elements
      hemptySlot.elements hnegationStateRows hnegatedBase with
    ⟨negationTrace, hnegationEndpoint⟩
  let coordinates : CompactSuccIndBaseNegationRouteCoordinates :=
    { baseTrace := baseTrace
      negationTrace := negationTrace }
  refine ⟨coordinates, by simpa using hemptySlot.1, hliteral, ?_, ?_⟩
  · simpa [coordinates, hzeroWitnessSlot.1, hbodySlot.1, hbaseSlot.1]
      using hbaseEndpoint
  · simpa [coordinates, hemptySlot.1, hbaseSlot.1, hnegatedBaseSlot.1]
      using hnegationEndpoint

#print axioms
  exists_compactSuccIndBaseNegationRoute_of_executable_outputs

end FoundationCompactNumericListedDirectSuccIndBaseNegationRouteCompleteness
