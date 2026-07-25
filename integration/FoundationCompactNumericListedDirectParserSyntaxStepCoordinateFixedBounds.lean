import integration.FoundationCompactNumericListedDirectParserSyntaxStepFormulaSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectParserDoneFormulaSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatFormulaSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds

/-! # Uniform coordinate bounds for all SyntaxStep branches -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds

open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserDoneFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFormula
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepFormulaSyntaxFixedBounds

def compactUnifiedParserSyntaxStepWitnessCoordinateValues
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) : Fin 7 -> Nat :=
  ![witness.slot0, witness.slot1, witness.slot2, witness.slot3, witness.slot4,
    witness.slot5, witness.slot6]

def CompactUnifiedParserSyntaxStepWitnessCoordinateValueBound
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound : Nat) : Prop :=
  forall coordinate,
    compactUnifiedParserSyntaxStepWitnessCoordinateValues witness coordinate <=
      numericBound

def CompactUnifiedParserSyntaxStepWitnessCoordinateSizeBound
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (bitBound : Nat) : Prop :=
  forall coordinate,
    Nat.size
      (compactUnifiedParserSyntaxStepWitnessCoordinateValues witness
        coordinate) <= bitBound

theorem compactUnifiedParserSyntaxStepFormulaEnvironment_size_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (bitBound : Nat)
    (htokenTable : Nat.size tokenTable <= bitBound)
    (hwidth : Nat.size width <= bitBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hcurrent :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnext :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (hwitness :
      CompactUnifiedParserSyntaxStepWitnessCoordinateSizeBound witness
        bitBound) :
    forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxStepFormulaEnvironment tokenTable width
          tokenCount current next witness coordinate) <= bitBound := by
  intro coordinate
  fin_cases coordinate
  · exact htokenTable
  · exact hwidth
  · exact htokenCount
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (0 : Fin 8)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (1 : Fin 8)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (2 : Fin 8)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (3 : Fin 8)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (4 : Fin 8)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (5 : Fin 8)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (6 : Fin 8)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hcurrent (7 : Fin 8)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (0 : Fin 8)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (1 : Fin 8)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (2 : Fin 8)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (3 : Fin 8)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (4 : Fin 8)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (5 : Fin 8)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (6 : Fin 8)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserStateCoordinateValues] using hnext (7 : Fin 8)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      hwitness (0 : Fin 7)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      hwitness (1 : Fin 7)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      hwitness (2 : Fin 7)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      hwitness (3 : Fin 7)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      hwitness (4 : Fin 7)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      hwitness (5 : Fin 7)
  · simpa [compactUnifiedParserSyntaxStepFormulaEnvironment,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      hwitness (6 : Fin 7)

theorem compactUnifiedParserSyntaxStepDoneWitness_size_le
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (bitBound : Nat)
    (hsize :
      CompactUnifiedParserSyntaxStepWitnessCoordinateSizeBound witness
        bitBound) :
    CompactUnifiedParserDoneWitnessCoordinateSizeBound witness.done
      bitBound := by
  intro coordinate
  fin_cases coordinate <;>
    simp [CompactUnifiedParserSyntaxStepWitnessCoordinates.done,
      compactUnifiedParserDoneWitnessCoordinatesOf,
      compactUnifiedParserDoneWitnessCoordinateValues] at hsize ⊢
  all_goals first | exact hsize 0 | exact hsize 1 | exact hsize 2 |
    exact hsize 3 | exact hsize 4 | exact hsize 5 | exact hsize 6

theorem compactUnifiedParserSyntaxStepRepeatWitness_size_le
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (bitBound : Nat)
    (hsize :
      CompactUnifiedParserSyntaxStepWitnessCoordinateSizeBound witness
        bitBound) :
    CompactUnifiedParserSyntaxRepeatWitnessCoordinateSizeBound witness.repeat
      bitBound := by
  intro coordinate
  fin_cases coordinate
  · simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.repeat,
      compactSyntaxRepeatTaskWitnessCoordinatesOf,
      compactUnifiedParserSyntaxRepeatWitnessCoordinateValues,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      hsize (2 : Fin 7)
  · simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.repeat,
      compactSyntaxRepeatTaskWitnessCoordinatesOf,
      compactUnifiedParserSyntaxRepeatWitnessCoordinateValues,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      hsize (3 : Fin 7)
  · simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.repeat,
      compactSyntaxRepeatTaskWitnessCoordinatesOf,
      compactUnifiedParserSyntaxRepeatWitnessCoordinateValues,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      hsize (4 : Fin 7)
  · simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.repeat,
      compactSyntaxRepeatTaskWitnessCoordinatesOf,
      compactUnifiedParserSyntaxRepeatWitnessCoordinateValues,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      hsize (5 : Fin 7)

theorem compactUnifiedParserSyntaxStepTermWitness_size_le
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (bitBound : Nat)
    (hsize :
      CompactUnifiedParserSyntaxStepWitnessCoordinateSizeBound witness
        bitBound) :
    CompactUnifiedParserSyntaxTermWitnessCoordinateSizeBound witness.term
      bitBound := by
  intro coordinate
  fin_cases coordinate
  · simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.term,
      compactSyntaxTermTaskWitnessCoordinatesOf,
      compactUnifiedParserSyntaxTermWitnessCoordinateValues,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      hsize (1 : Fin 7)
  · simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.term,
      compactSyntaxTermTaskWitnessCoordinatesOf,
      compactUnifiedParserSyntaxTermWitnessCoordinateValues,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      hsize (2 : Fin 7)
  · simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.term,
      compactSyntaxTermTaskWitnessCoordinatesOf,
      compactUnifiedParserSyntaxTermWitnessCoordinateValues,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      hsize (3 : Fin 7)
  · simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.term,
      compactSyntaxTermTaskWitnessCoordinatesOf,
      compactUnifiedParserSyntaxTermWitnessCoordinateValues,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      hsize (4 : Fin 7)
  · simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.term,
      compactSyntaxTermTaskWitnessCoordinatesOf,
      compactUnifiedParserSyntaxTermWitnessCoordinateValues,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      hsize (5 : Fin 7)
  · simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.term,
      compactSyntaxTermTaskWitnessCoordinatesOf,
      compactUnifiedParserSyntaxTermWitnessCoordinateValues,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      hsize (6 : Fin 7)

end FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
