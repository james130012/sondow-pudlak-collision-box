import integration.FoundationCompactNumericListedDirectSequentFormulaTraceFormula
import integration.FoundationCompactNumericListedDirectNatListConsRows
import integration.FoundationCompactNumericListedDirectVerifierValueRealization

/-!
# Endpoint installation for exact sequent parsing

The first suffix is connected to the count-prefixed parser input, and the last
suffix is connected to the public parser output.  All three semantic values
are reconstructed from direct numeric rows; none is supplied to soundness.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation

open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierValueRealization
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectSequentFormulaTraceFormula

structure CompactSequentFormulaEndpointCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  firstStart : Nat
  firstFinish : Nat
  firstBoundary : Nat
  firstCount : Nat
  firstBoundarySize : Nat
  suffixBoundary : Nat
  suffixCount : Nat
  valueBoundary : Nat
  valueCount : Nat
  valueBoundarySize : Nat
  finalBoundary : Nat
  finalCount : Nat
  finalBoundarySize : Nat
  traceTableWidth : Nat
  traceValueBound : Nat

def CompactSequentFormulaEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish
      valueStart valueFinish finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount
        inputFinish coordinates.inputBoundary coordinates.inputBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount coordinates.firstStart coordinates.firstCount
        coordinates.firstFinish coordinates.firstBoundary
        coordinates.firstBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount finalStart coordinates.finalCount
        finalFinish coordinates.finalBoundary coordinates.finalBoundarySize ∧
    CompactSequentFormulaTraceBoundedGraph
      tokenTable width tokenCount coordinates.suffixBoundary
        coordinates.suffixCount coordinates.valueBoundary
        coordinates.valueCount coordinates.traceTableWidth
        coordinates.traceValueBound ∧
    CompactFixedWidthEntry coordinates.suffixBoundary tokenCount 0
      coordinates.firstStart ∧
    CompactFixedWidthEntry coordinates.suffixBoundary tokenCount 1
      coordinates.firstFinish ∧
    CompactFixedWidthEntry coordinates.suffixBoundary tokenCount
      coordinates.valueCount finalStart ∧
    CompactFixedWidthEntry coordinates.suffixBoundary tokenCount
      (coordinates.valueCount + 1) finalFinish ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount coordinates.firstBoundary
        coordinates.firstCount coordinates.inputBoundary
        coordinates.inputCount coordinates.valueCount ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount valueStart coordinates.valueCount
        valueFinish coordinates.valueBoundary ∧
    coordinates.valueBoundarySize = Nat.size coordinates.valueBoundary ∧
    coordinates.valueBoundarySize ≤
      (coordinates.valueCount + 1) * tokenCount

theorem CompactSequentFormulaEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      valueStart valueFinish finalStart finalFinish : Nat}
    {coordinates : CompactSequentFormulaEndpointCoordinates}
    (hgraph : CompactSequentFormulaEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        valueStart valueFinish finalStart finalFinish coordinates) :
    ∃ input : List Nat,
    ∃ values : List (List Nat),
    ∃ suffix : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactAdditiveNatListListDirectLayout
        tokenTable width tokenCount valueStart valueFinish values ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount finalStart finalFinish suffix ∧
      compactSequentTokenValueParser input = some (values, suffix) := by
  rcases hgraph with
    ⟨hinputWitness, hfirstWitness, hfinalWitness, htrace,
      hfirstStartEntry, _hfirstFinishEntry,
      hfinalStartEntry, _hfinalFinishEntry,
      hcons, hvalueStructure, hvalueBoundarySizeEq,
      hvalueBoundarySize⟩
  have hsuffixCount := htrace.1
  rcases hinputWitness.realize with
    ⟨input, hinputLength, hinputLayout, hinputRows⟩
  rcases hfirstWitness.realize with
    ⟨first, hfirstLength, hfirstLayout, hfirstRows⟩
  rcases hfinalWitness.realize with
    ⟨suffix, hfinalLength, hfinalLayout, _hfinalRows⟩
  rcases htrace.sound_repeat with
    ⟨suffixes, values, hsuffixesLength, hvaluesLength,
      hsuffixRows, hvalueRows, hrepeat⟩
  have hfirstIndex : 0 < suffixes.length := by
    rw [hsuffixesLength, hsuffixCount]
    omega
  have hfinalIndex : coordinates.valueCount < suffixes.length := by
    rw [hsuffixesLength, hsuffixCount]
    omega
  rcases hsuffixRows 0 hfirstIndex with
    ⟨actualFirstStart, _hactualFirstStartBound,
      actualFirstFinish, _hactualFirstFinishBound,
      hactualFirstStartEntry, _hactualFirstFinishEntry,
      hactualFirstLayout⟩
  rcases hsuffixRows coordinates.valueCount hfinalIndex with
    ⟨actualFinalStart, _hactualFinalStartBound,
      actualFinalFinish, _hactualFinalFinishBound,
      hactualFinalStartEntry, _hactualFinalFinishEntry,
      hactualFinalLayout⟩
  have hfirstStartEq : coordinates.firstStart = actualFirstStart :=
    (CompactFixedWidthEntry.value_eq_tableValue
      hfirstStartEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          hactualFirstStartEntry).symm
  have hfinalStartEq : finalStart = actualFinalStart :=
    (CompactFixedWidthEntry.value_eq_tableValue
      hfinalStartEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          hactualFinalStartEntry).symm
  subst actualFirstStart
  subst actualFinalStart
  have hfirstEq : suffixes.getI 0 = first :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hfirstLayout hactualFirstLayout).1
  have hfinalEq : suffixes.getI coordinates.valueCount = suffix :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hfinalLayout hactualFinalLayout).1
  have hcons' : CompactAdditiveNatListConsRows
      tokenTable width tokenCount coordinates.firstBoundary first.length
        coordinates.inputBoundary input.length coordinates.valueCount := by
    simpa only [hfirstLength, hinputLength] using hcons
  have hinputEq : input = coordinates.valueCount :: first :=
    CompactAdditiveNatListConsRows.eq_cons_of_rows
      hcons' hfirstRows hinputRows
  have hvaluesLayout : CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount valueStart valueFinish values := by
    refine ⟨coordinates.valueBoundary, ?_, hvalueRows, ?_⟩
    · simpa only [hvaluesLength] using hvalueStructure
    · rw [hvaluesLength, ← hvalueBoundarySizeEq]
      exact hvalueBoundarySize
  rw [hfirstEq, hfinalEq] at hrepeat
  have hparser : compactSequentTokenValueParser input =
      some (values, suffix) := by
    rw [hinputEq]
    simpa [compactSequentTokenValueParser] using hrepeat
  exact ⟨input, values, suffix,
    hinputLayout, hvaluesLayout, hfinalLayout, hparser⟩

#print axioms CompactSequentFormulaEndpointGraph.sound

end FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
