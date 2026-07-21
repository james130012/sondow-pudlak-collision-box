import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointCompleteness
import integration.FoundationCompactNumericListedDirectSequentFormulaTracePublicBounds

/-!
# Public quantitative bounds for the sequent formula endpoint

The exact endpoint exposes eighteen coordinates: three flat-list witnesses,
two outer boundary tables, and the aggregate nested-parser width.  This module
retains explicit bit-size bounds for all eighteen coordinates while preserving
the exact parser result in the original shared token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointPublicBounds

open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
open FoundationCompactNumericListedDirectSequentFormulaTraceFormula
open FoundationCompactNumericListedDirectSequentFormulaTracePublicBounds
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation

def compactSequentFormulaEndpointCoordinateValues
    (coordinates : CompactSequentFormulaEndpointCoordinates) : List Nat :=
  [coordinates.inputBoundary,
    coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.firstStart,
    coordinates.firstFinish,
    coordinates.firstBoundary,
    coordinates.firstCount,
    coordinates.firstBoundarySize,
    coordinates.suffixBoundary,
    coordinates.suffixCount,
    coordinates.valueBoundary,
    coordinates.valueCount,
    coordinates.valueBoundarySize,
    coordinates.finalBoundary,
    coordinates.finalCount,
    coordinates.finalBoundarySize,
    coordinates.traceTableWidth,
    coordinates.traceValueBound]

def compactSequentFormulaEndpointPublicCoordinateSizeBound
    (width tokenCount : Nat) : Nat :=
  tokenCount + 1 +
    (tokenCount + 2) * tokenCount +
    compactSequentFormulaTracePublicTableWidthBound width tokenCount + 2

structure CompactSequentFormulaEndpointPublicBounds
    (finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates)
    (bound : Nat) : Prop where
  finalStart_size_le : Nat.size finalStart <= bound
  finalFinish_size_le : Nat.size finalFinish <= bound
  value_size_le :
    ∀ value ∈ compactSequentFormulaEndpointCoordinateValues coordinates,
      Nat.size value <= bound

theorem exists_compactSequentFormulaEndpointGraph_of_rows_with_publicBounds
    {tokenTable width tokenCount inputStart inputFinish
      valueStart valueFinish suffixBoundary valueBoundary : Nat}
    {input suffix : List Nat}
    {suffixes values : List (List Nat)}
    {parserTraces : List CompactFormulaTokenParserDirectTrace}
    (hinputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hsuffixRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        suffixBoundary suffixes)
    (hsuffixBoundarySize :
      Nat.size suffixBoundary <=
        (suffixes.length + 1) * tokenCount)
    (hvalueStructure : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount valueStart values.length valueFinish
        valueBoundary)
    (hvalueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        valueBoundary values)
    (hvalueBoundarySize :
      Nat.size valueBoundary <= (values.length + 1) * tokenCount)
    (hparserRows : ∀ index < values.length,
      ∃ parserStateBoundary,
        CompactUnifiedParserStateListRowLayouts
            tokenTable width tokenCount parserStateBoundary
              (parserTraces.getI index) ∧
          Nat.size parserStateBoundary <=
            ((parserTraces.getI index).length + 1) * tokenCount)
    (hsuffixCount : suffixes.length = values.length + 1)
    (hparserCount : parserTraces.length = values.length)
    (hsteps : ∀ index < values.length,
      CompactFormulaTokenParserDirectTraceValid
          0 (suffixes.getI index) (suffixes.getI (index + 1))
            (parserTraces.getI index) ∧
        suffixes.getI index =
          values.getI index ++ suffixes.getI (index + 1))
    (hinputEq : input = values.length :: suffixes.getI 0)
    (hfinalEq : suffixes.getI values.length = suffix) :
    ∃ finalStart finalFinish,
    ∃ coordinates : CompactSequentFormulaEndpointCoordinates,
      CompactSequentFormulaEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            valueStart valueFinish finalStart finalFinish coordinates ∧
        CompactSequentFormulaEndpointPublicBounds finalStart finalFinish
          coordinates
          (compactSequentFormulaEndpointPublicCoordinateSizeBound
            width tokenCount) := by
  have hvalueCount : values.length <= tokenCount :=
    structuredListLayout_count_le_tokenCount hvalueStructure
  rcases
      exists_compactSequentFormulaTraceBoundedGraph_of_directData_with_publicWidth
        hsuffixCount hparserCount hsuffixRows hvalueRows hvalueCount
        hparserRows hsteps with
    ⟨traceTableWidth, htraceTableWidth, htrace⟩
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputRows, hinputBoundarySize⟩
  have hinputWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart input.length inputFinish
        inputBoundary (Nat.size inputBoundary) :=
    ⟨hinputStructure,
      FoundationCompactNumericListedDirectNatListBoundaryRigidity.CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hinputRows,
      rfl, hinputBoundarySize⟩
  have hfirstIndex : 0 < suffixes.length := by
    rw [hsuffixCount]
    omega
  rcases hsuffixRows 0 hfirstIndex with
    ⟨firstStart, hfirstStartBound,
      firstFinish, hfirstFinishBound,
      hfirstStartEntry, hfirstFinishEntry, hfirstLayout⟩
  rcases hfirstLayout with
    ⟨firstBoundary, hfirstStructure, hfirstRows, hfirstBoundarySize⟩
  have hfirstWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount firstStart (suffixes.getI 0).length
        firstFinish firstBoundary (Nat.size firstBoundary) :=
    ⟨hfirstStructure,
      FoundationCompactNumericListedDirectNatListBoundaryRigidity.CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hfirstRows,
      rfl, hfirstBoundarySize⟩
  have hfinalIndex : values.length < suffixes.length := by
    rw [hsuffixCount]
    omega
  rcases hsuffixRows values.length hfinalIndex with
    ⟨finalStart, hfinalStartBound,
      finalFinish, hfinalFinishBound,
      hfinalStartEntry, hfinalFinishEntry, hfinalLayout⟩
  rw [hfinalEq] at hfinalLayout
  rcases hfinalLayout with
    ⟨finalBoundary, hfinalStructure, hfinalRows, hfinalBoundarySize⟩
  have hfinalWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount finalStart suffix.length finalFinish
        finalBoundary (Nat.size finalBoundary) :=
    ⟨hfinalStructure,
      FoundationCompactNumericListedDirectNatListBoundaryRigidity.CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hfinalRows,
      rfl, hfinalBoundarySize⟩
  have hcons : CompactAdditiveNatListConsRows
      tokenTable width tokenCount firstBoundary (suffixes.getI 0).length
        inputBoundary input.length values.length :=
    CompactAdditiveStructuredListElementRowLayouts.natConsRows
      hfirstRows hinputRows hinputEq
  let coordinates : CompactSequentFormulaEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      firstStart := firstStart
      firstFinish := firstFinish
      firstBoundary := firstBoundary
      firstCount := (suffixes.getI 0).length
      firstBoundarySize := Nat.size firstBoundary
      suffixBoundary := suffixBoundary
      suffixCount := suffixes.length
      valueBoundary := valueBoundary
      valueCount := values.length
      valueBoundarySize := Nat.size valueBoundary
      finalBoundary := finalBoundary
      finalCount := suffix.length
      finalBoundarySize := Nat.size finalBoundary
      traceTableWidth := traceTableWidth
      traceValueBound := 2 ^ traceTableWidth }
  have hgraph : CompactSequentFormulaEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        valueStart valueFinish finalStart finalFinish coordinates := by
    unfold CompactSequentFormulaEndpointGraph
    dsimp only [coordinates]
    exact ⟨hinputWitness, hfirstWitness, hfinalWitness, htrace,
      hfirstStartEntry, hfirstFinishEntry,
      hfinalStartEntry, hfinalFinishEntry, hcons,
      hvalueStructure, rfl, hvalueBoundarySize⟩
  have hinputCount : input.length <= tokenCount :=
    structuredListLayout_count_le_tokenCount hinputStructure
  have hfirstCount : (suffixes.getI 0).length <= tokenCount :=
    structuredListLayout_count_le_tokenCount hfirstStructure
  have hfinalCount : suffix.length <= tokenCount :=
    structuredListLayout_count_le_tokenCount hfinalStructure
  have hinputBoundary :
      Nat.size inputBoundary <= (tokenCount + 1) * tokenCount :=
    hinputBoundarySize.trans
      (Nat.mul_le_mul_right tokenCount (by omega))
  have hfirstBoundary :
      Nat.size firstBoundary <= (tokenCount + 1) * tokenCount :=
    hfirstBoundarySize.trans
      (Nat.mul_le_mul_right tokenCount (by omega))
  have hfinalBoundary :
      Nat.size finalBoundary <= (tokenCount + 1) * tokenCount :=
    hfinalBoundarySize.trans
      (Nat.mul_le_mul_right tokenCount (by omega))
  have hsuffixBoundary :
      Nat.size suffixBoundary <= (tokenCount + 2) * tokenCount := by
    exact hsuffixBoundarySize.trans
      (Nat.mul_le_mul_right tokenCount (by
        rw [hsuffixCount]
        omega))
  have hvalueBoundary :
      Nat.size valueBoundary <= (tokenCount + 1) * tokenCount :=
    hvalueBoundarySize.trans
      (Nat.mul_le_mul_right tokenCount (by omega))
  have hboundaryArea :
      (tokenCount + 1) * tokenCount <=
        (tokenCount + 2) * tokenCount :=
    Nat.mul_le_mul_right tokenCount (by omega)
  have hinputBoundaryPublic :
      Nat.size inputBoundary <= (tokenCount + 2) * tokenCount :=
    hinputBoundary.trans hboundaryArea
  have hfirstBoundaryPublic :
      Nat.size firstBoundary <= (tokenCount + 2) * tokenCount :=
    hfirstBoundary.trans hboundaryArea
  have hvalueBoundaryPublic :
      Nat.size valueBoundary <= (tokenCount + 2) * tokenCount :=
    hvalueBoundary.trans hboundaryArea
  have hfinalBoundaryPublic :
      Nat.size finalBoundary <= (tokenCount + 2) * tokenCount :=
    hfinalBoundary.trans hboundaryArea
  have hsuffixCountPublic : suffixes.length <= tokenCount + 1 := by
    rw [hsuffixCount]
    omega
  let coordinateBound :=
    compactSequentFormulaEndpointPublicCoordinateSizeBound width tokenCount
  have hpublic :
      CompactSequentFormulaEndpointPublicBounds finalStart finalFinish
        coordinates
        coordinateBound := by
    refine
      ⟨(natSize_le_of_le hfinalStartBound).trans (by
          dsimp only [coordinateBound]
          unfold compactSequentFormulaEndpointPublicCoordinateSizeBound
          omega),
        (natSize_le_of_le hfinalFinishBound).trans (by
          dsimp only [coordinateBound]
          unfold compactSequentFormulaEndpointPublicCoordinateSizeBound
          omega),
        ?_⟩
    intro coordinate hcoordinate
    simp only [compactSequentFormulaEndpointCoordinateValues,
      List.mem_cons, List.not_mem_nil, or_false] at hcoordinate
    rcases hcoordinate with
      h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h
    all_goals
      subst coordinate
      dsimp only [coordinates, coordinateBound,
        compactSequentFormulaEndpointPublicCoordinateSizeBound]
    · exact hinputBoundaryPublic.trans (by omega)
    · exact (natSize_le_of_le hinputCount).trans (by omega)
    · exact (natSize_le_of_le hinputBoundaryPublic).trans (by omega)
    · exact (natSize_le_of_le hfirstStartBound).trans (by omega)
    · exact (natSize_le_of_le hfirstFinishBound).trans (by omega)
    · exact hfirstBoundaryPublic.trans (by omega)
    · exact (natSize_le_of_le hfirstCount).trans (by omega)
    · exact (natSize_le_of_le hfirstBoundaryPublic).trans (by omega)
    · exact hsuffixBoundary.trans (by
        unfold compactSequentFormulaTracePublicTableWidthBound
        omega)
    · exact (natSize_le_of_le hsuffixCountPublic).trans (by omega)
    · exact hvalueBoundaryPublic.trans (by omega)
    · exact (natSize_le_of_le hvalueCount).trans (by omega)
    · exact (natSize_le_of_le hvalueBoundaryPublic).trans (by omega)
    · exact hfinalBoundaryPublic.trans (by omega)
    · exact (natSize_le_of_le hfinalCount).trans (by omega)
    · exact (natSize_le_of_le hfinalBoundaryPublic).trans (by omega)
    · exact (natSize_le_of_le htraceTableWidth).trans (by omega)
    · rw [Nat.size_pow]
      exact Nat.add_le_add_right htraceTableWidth 1 |>.trans (by omega)
  exact ⟨finalStart, finalFinish, coordinates, hgraph, hpublic⟩

#print axioms
  exists_compactSequentFormulaEndpointGraph_of_rows_with_publicBounds

end FoundationCompactNumericListedDirectSequentFormulaEndpointPublicBounds
