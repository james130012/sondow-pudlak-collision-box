import integration.FoundationCompactNumericListedDirectParserSyntaxExactEndpointFormula
import integration.FoundationCompactNumericListedDirectParserSyntaxTraceBounds
import integration.FoundationCompactNumericListedDirectSequentFormulaTracePublicBounds

/-!
# Public bounds for exact formula and term parser endpoints

The exact endpoint records two flat token lists and one complete ordinary
syntax-parser trace.  The older constructor retained a table width chosen from
the realized trace.  This module uses the public adjacent-row aggregation
theorem and proves that all ten endpoint coordinates have an explicit bound
depending only on the shared table width and token count.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxExactEndpointPublicBounds

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectParserSyntaxTraceBounds
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointFormula
open FoundationCompactNumericListedDirectSequentFormulaTracePublicBounds

def compactParserSyntaxExactEndpointCoordinateValues
    (coordinates : CompactParserSyntaxExactEndpointCoordinates) : List Nat :=
  [coordinates.inputBoundary,
    coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.expectedBoundary,
    coordinates.expectedCount,
    coordinates.expectedBoundarySize,
    coordinates.stateBoundary,
    coordinates.stateCount,
    coordinates.tableWidth,
    coordinates.valueBound]

def compactParserSyntaxExactEndpointPublicCoordinateSizeBound
    (width tokenCount : Nat) : Nat :=
  compactSequentFormulaStepPublicCoordinateSizeBound width tokenCount

structure CompactParserSyntaxExactEndpointPublicBounds
    (coordinates : CompactParserSyntaxExactEndpointCoordinates)
    (bound : Nat) : Prop where
  value_size_le :
    ∀ value ∈ compactParserSyntaxExactEndpointCoordinateValues coordinates,
      Nat.size value <= bound

private theorem compactSyntaxRunFuelBound_le_public
    {input : List Nat} {tokenCount : Nat}
    (hcount : input.length <= tokenCount) :
    compactSyntaxRunFuelBound input <=
      compactSequentFormulaPublicParserFuelBound tokenCount := by
  have hplus : input.length + 1 <= tokenCount + 1 := by omega
  have hsquare :
      (input.length + 1) * (input.length + 1) <=
        (tokenCount + 1) * (tokenCount + 1) :=
    Nat.mul_le_mul hplus hplus
  have hscaled :
      16 * (input.length + 1) * (input.length + 1) <=
        16 * (tokenCount + 1) * (tokenCount + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 16 hplus) hplus
  unfold compactSyntaxRunFuelBound
    compactSequentFormulaPublicParserFuelBound
  omega

private theorem compactParserSyntaxCanonicalTableWidthBound_mono_fuel
    {width tokenCount leftFuel rightFuel : Nat}
    (hfuel : leftFuel <= rightFuel) :
    compactParserSyntaxCanonicalTableWidthBound
        width tokenCount leftFuel <=
      compactParserSyntaxCanonicalTableWidthBound
        width tokenCount rightFuel := by
  have hcolumns :
      leftFuel * compactParserSyntaxAdjacentStepWitnessColumnCount <=
        rightFuel * compactParserSyntaxAdjacentStepWitnessColumnCount :=
    Nat.mul_le_mul_right
      compactParserSyntaxAdjacentStepWitnessColumnCount hfuel
  have hrows :=
    Nat.mul_le_mul_right
      (FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessBound.compactParserSyntaxAdjacentStepPublicWidth
        width tokenCount)
      hcolumns
  unfold compactParserSyntaxCanonicalTableWidthBound
  omega

/-- Install an already laid-out exact parser trace while retaining public
bounds for all ten endpoint coordinates. -/
theorem
    exists_compactParserSyntaxExactEndpointGraph_of_rows_with_publicBounds
    {tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish stateBoundary : Nat}
    {input expected : List Nat}
    {states : List CompactUnifiedParserState}
    {taskKind taskBinderArity taskRepeatCount : Nat}
    (hinputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hexpectedLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount expectedStart expectedFinish expected)
    (hstateRows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hstateBoundarySize :
      Nat.size stateBoundary <= (states.length + 1) * tokenCount)
    (hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(taskKind, taskBinderArity, taskRepeatCount)])
    (hvalid : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      (some expected) states) :
    ∃ coordinates : CompactParserSyntaxExactEndpointCoordinates,
      CompactParserSyntaxExactEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            expectedStart expectedFinish taskKind taskBinderArity
            taskRepeatCount coordinates ∧
        CompactParserSyntaxExactEndpointPublicBounds coordinates
          (compactParserSyntaxExactEndpointPublicCoordinateSizeBound
            width tokenCount) ∧
        coordinates.stateBoundary = stateBoundary := by
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputRows, hinputSize⟩
  rcases hexpectedLayout with
    ⟨expectedBoundary, hexpectedStructure, hexpectedRows, hexpectedSize⟩
  rcases
      localTrace_exists_compactParserSyntaxExactBoundedGraph_with_publicWidth
        hstateRows hinputRows hexpectedRows hstartWell hvalid with
    ⟨tableWidth, htableWidth, hexact⟩
  have hinputWitness :
      CompactAdditiveNatListWitnessRows
        tokenTable width tokenCount inputStart input.length inputFinish
          inputBoundary (Nat.size inputBoundary) :=
    ⟨hinputStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hinputRows,
      rfl, hinputSize⟩
  have hexpectedWitness :
      CompactAdditiveNatListWitnessRows
        tokenTable width tokenCount expectedStart expected.length
          expectedFinish expectedBoundary (Nat.size expectedBoundary) :=
    ⟨hexpectedStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hexpectedRows,
      rfl, hexpectedSize⟩
  let coordinates : CompactParserSyntaxExactEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      expectedBoundary := expectedBoundary
      expectedCount := expected.length
      expectedBoundarySize := Nat.size expectedBoundary
      stateBoundary := stateBoundary
      stateCount := states.length
      tableWidth := tableWidth
      valueBound := 2 ^ tableWidth }
  have hgraph :
      CompactParserSyntaxExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          expectedStart expectedFinish taskKind taskBinderArity
          taskRepeatCount coordinates := by
    unfold CompactParserSyntaxExactEndpointGraph
    dsimp only [coordinates]
    exact ⟨hinputWitness, hexpectedWitness, hexact⟩
  have hinputCount : input.length <= tokenCount :=
    structuredListLayout_count_le_tokenCount hinputStructure
  have hexpectedCount : expected.length <= tokenCount :=
    structuredListLayout_count_le_tokenCount hexpectedStructure
  have htokenCountPos : 0 < tokenCount :=
    Nat.lt_of_le_of_lt (Nat.zero_le inputStart)
      (FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound.structuredListLayout_start_lt_tokenCount
        hinputStructure)
  have hfuel :
      compactSyntaxRunFuelBound input <=
        compactSequentFormulaPublicParserFuelBound tokenCount :=
    compactSyntaxRunFuelBound_le_public hinputCount
  have hstateCount :
      states.length <=
        compactSequentFormulaPublicParserFuelBound tokenCount + 1 := by
    rw [hvalid.1.1]
    omega
  have hstateCountPublic :
      states.length <=
        (compactSequentFormulaPublicParserFuelBound tokenCount + 2) *
          tokenCount := by
    have hone : 1 <= tokenCount := Nat.succ_le_iff.mpr htokenCountPos
    have hscaled :
        (compactSequentFormulaPublicParserFuelBound tokenCount + 2) * 1 <=
          (compactSequentFormulaPublicParserFuelBound tokenCount + 2) *
            tokenCount :=
      Nat.mul_le_mul_left
        (compactSequentFormulaPublicParserFuelBound tokenCount + 2) hone
    exact hstateCount.trans (by
      exact (show
        compactSequentFormulaPublicParserFuelBound tokenCount + 1 <=
          (compactSequentFormulaPublicParserFuelBound tokenCount + 2) * 1
        by omega) |>.trans hscaled)
  have hinputBoundary :
      Nat.size inputBoundary <= (tokenCount + 1) * tokenCount :=
    hinputSize.trans
      (Nat.mul_le_mul_right tokenCount
        (Nat.add_le_add_right hinputCount 1))
  have hexpectedBoundary :
      Nat.size expectedBoundary <= (tokenCount + 1) * tokenCount :=
    hexpectedSize.trans
      (Nat.mul_le_mul_right tokenCount
        (Nat.add_le_add_right hexpectedCount 1))
  have hstateBoundary :
      Nat.size stateBoundary <=
        (compactSequentFormulaPublicParserFuelBound tokenCount + 2) *
          tokenCount :=
    hstateBoundarySize.trans
      (Nat.mul_le_mul_right tokenCount
        (Nat.add_le_add_right hstateCount 1))
  have htableWidthPublic :
      tableWidth <=
        compactParserSyntaxCanonicalTableWidthBound
          width tokenCount
            (compactSequentFormulaPublicParserFuelBound tokenCount) :=
    htableWidth.trans
      (compactParserSyntaxCanonicalTableWidthBound_mono_fuel hfuel)
  let coordinateBound :=
    compactParserSyntaxExactEndpointPublicCoordinateSizeBound
      width tokenCount
  have hpublic :
      CompactParserSyntaxExactEndpointPublicBounds
        coordinates coordinateBound := by
    refine ⟨?_⟩
    intro value hvalue
    simp only [compactParserSyntaxExactEndpointCoordinateValues,
      List.mem_cons, List.not_mem_nil, or_false] at hvalue
    rcases hvalue with
      h | h | h | h | h | h | h | h | h | h
    all_goals
      subst value
      dsimp only [coordinates, coordinateBound,
        compactParserSyntaxExactEndpointPublicCoordinateSizeBound,
        compactSequentFormulaStepPublicCoordinateSizeBound]
    · exact hinputBoundary.trans (by omega)
    · exact (natSize_le_of_le hinputCount).trans (by omega)
    · exact (natSize_le_of_le hinputBoundary).trans (by omega)
    · exact hexpectedBoundary.trans (by omega)
    · exact (natSize_le_of_le hexpectedCount).trans (by omega)
    · exact (natSize_le_of_le hexpectedBoundary).trans (by omega)
    · exact hstateBoundary.trans (by omega)
    · exact (natSize_le_of_le hstateCountPublic).trans (by omega)
    · exact (natSize_le_of_le htableWidthPublic).trans (by omega)
    · rw [Nat.size_pow]
      exact Nat.add_le_add_right htableWidthPublic 1 |>.trans (by omega)
  exact ⟨coordinates, hgraph, hpublic, rfl⟩

#print axioms
  exists_compactParserSyntaxExactEndpointGraph_of_rows_with_publicBounds

end FoundationCompactNumericListedDirectParserSyntaxExactEndpointPublicBounds
