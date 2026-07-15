import integration.FoundationCompactNumericListedDirectSequentFormulaFailureSemantics
import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointFormula
import integration.FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointFormula

/-!
# Exact endpoint for a failed sequent formula parse

The endpoint shares one fixed-width table between the original count-prefixed
input, a successful parse of every formula before the first failure, and the
complete no-output trace of the failing formula parser call.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSequentFormulaFailureEndpoint

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectSequentFormulaEndpointFormula
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointFormula
open FoundationCompactNumericListedDirectSequentFormulaFailureSemantics

structure CompactSequentFormulaFailureEndpointCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  count : Nat
  prefixInputStart : Nat
  prefixInputFinish : Nat
  valueStart : Nat
  valueFinish : Nat
  failedStart : Nat
  failedFinish : Nat
  prefixEndpoint : CompactSequentFormulaEndpointCoordinates
  failureEndpoint : CompactParserSyntaxNoOutputExactEndpointCoordinates

def CompactSequentFormulaFailureEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactSequentFormulaFailureEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount inputFinish
        coordinates.inputBoundary coordinates.inputBoundarySize ∧
    CompactSequentFormulaEndpointGraph
      tokenTable width tokenCount
        coordinates.prefixInputStart coordinates.prefixInputFinish
        coordinates.valueStart coordinates.valueFinish
        coordinates.failedStart coordinates.failedFinish
        coordinates.prefixEndpoint ∧
    coordinates.prefixEndpoint.valueCount < coordinates.count ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount
        coordinates.prefixEndpoint.firstBoundary
        coordinates.prefixEndpoint.firstCount
        coordinates.inputBoundary coordinates.inputCount coordinates.count ∧
    CompactParserSyntaxNoOutputExactEndpointGraph
      tokenTable width tokenCount coordinates.failedStart
        coordinates.failedFinish 1 0 0 coordinates.failureEndpoint

theorem CompactSequentFormulaFailureEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish : Nat}
    {coordinates : CompactSequentFormulaFailureEndpointCoordinates}
    (hgraph : CompactSequentFormulaFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish coordinates) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactSequentTokenValueParser input = none := by
  rcases hgraph with
    ⟨hinputWitness, hprefix, hfailedIndex, hinputCons, hfailure⟩
  rcases hinputWitness.realize with
    ⟨input, hinputCount, hinputLayout, hinputRows⟩
  have hprefixRows := hprefix
  rcases hprefixRows with
    ⟨hprefixInputWitness, hfirstWitness, _hfinalWitness,
      _htrace, _hfirstStart, _hfirstFinish,
      _hfinalStart, _hfinalFinish, hprefixCons,
      _hvalueStructure, _hvalueSizeEq, _hvalueSize⟩
  rcases hprefixInputWitness.realize with
    ⟨prefixInputFromRows, hprefixInputCount,
      hprefixInputRowsLayout, hprefixInputRows⟩
  rcases hfirstWitness.realize with
    ⟨first, hfirstCount, hfirstLayout, hfirstRows⟩
  rcases hprefix.sound with
    ⟨prefixInput, values, failedTokens,
      hprefixInputLayout, _hvaluesLayout, hfailedLayout, hprefixParser⟩
  have hprefixInputEq : prefixInput = prefixInputFromRows :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hprefixInputRowsLayout hprefixInputLayout).1
  have hprefixCons' : CompactAdditiveNatListConsRows
      tokenTable width tokenCount coordinates.prefixEndpoint.firstBoundary
        first.length coordinates.prefixEndpoint.inputBoundary
        prefixInputFromRows.length coordinates.prefixEndpoint.valueCount := by
    simpa only [hfirstCount, hprefixInputCount] using hprefixCons
  have hprefixInputFromRowsEq :
      prefixInputFromRows = coordinates.prefixEndpoint.valueCount :: first :=
    hprefixCons'.eq_cons_of_rows hfirstRows hprefixInputRows
  have hinputCons' : CompactAdditiveNatListConsRows
      tokenTable width tokenCount coordinates.prefixEndpoint.firstBoundary
        first.length coordinates.inputBoundary input.length
        coordinates.count := by
    simpa only [hfirstCount, hinputCount] using hinputCons
  have hinputEq : input = coordinates.count :: first :=
    hinputCons'.eq_cons_of_rows hfirstRows hinputRows
  have hprefixParser' :
      compactFormulaTokenValuesRepeat
          coordinates.prefixEndpoint.valueCount first =
        some (values, failedTokens) := by
    rw [hprefixInputEq, hprefixInputFromRowsEq] at hprefixParser
    simpa [compactSequentTokenValueParser] using hprefixParser
  rcases hfailure.sound_formula with
    ⟨failureInput, hfailureLayout, hfailureParser⟩
  have hfailureInputEq : failureInput = failedTokens :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hfailedLayout hfailureLayout).1
  rw [hfailureInputEq] at hfailureParser
  have hfailureValueParser :
      compactFormulaTokenValueParser 0 failedTokens = none := by
    simp [compactFormulaTokenValueParser, hfailureParser]
  have hparser : compactSequentTokenValueParser
      (coordinates.count :: first) = none :=
    (compactSequentTokenValueParser_cons_eq_none_iff
      coordinates.count first).mpr
        ⟨coordinates.prefixEndpoint.valueCount, hfailedIndex,
          values, failedTokens, hprefixParser', hfailureValueParser⟩
  exact ⟨input, hinputLayout, by simpa only [hinputEq] using hparser⟩

#print axioms CompactSequentFormulaFailureEndpointGraph.sound

end FoundationCompactNumericListedDirectSequentFormulaFailureEndpoint
