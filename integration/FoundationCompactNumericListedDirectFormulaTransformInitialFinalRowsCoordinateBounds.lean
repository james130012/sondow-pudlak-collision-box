import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
import integration.FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds

/-! # Coordinatewise public bounds for formula-transform endpoints -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsCoordinateBounds

open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula

def FormulaTransformInitialFinalRowsValueBound
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity numericBound : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) : Prop :=
  forall coordinate,
    compactFormulaTransformInitialFinalRowsEnvironment tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity witness coordinate <= numericBound

def FormulaTransformInitialFinalRowsSizeBound
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity bitBound : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) : Prop :=
  forall coordinate,
    Nat.size
      (compactFormulaTransformInitialFinalRowsEnvironment tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity witness coordinate) <= bitBound

theorem initialParserValueBound_of_transformInitialFinal
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity numericBound : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates)
    (hvalue : FormulaTransformInitialFinalRowsValueBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity numericBound witness) :
    CompactUnifiedParserStateCoordinateValueBound
      witness.initialCoordinates.parser numericBound := by
  intro coordinate
  fin_cases coordinate
  · simpa [FormulaTransformInitialFinalRowsValueBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 13
  · simpa [FormulaTransformInitialFinalRowsValueBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 15
  · simpa [FormulaTransformInitialFinalRowsValueBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 16
  · simpa [FormulaTransformInitialFinalRowsValueBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 17
  · simpa [FormulaTransformInitialFinalRowsValueBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 18
  · simpa [FormulaTransformInitialFinalRowsValueBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 19
  · simpa [FormulaTransformInitialFinalRowsValueBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 20
  · simpa [FormulaTransformInitialFinalRowsValueBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 21

theorem finalParserValueBound_of_transformInitialFinal
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity numericBound : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates)
    (hvalue : FormulaTransformInitialFinalRowsValueBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity numericBound witness) :
    CompactUnifiedParserStateCoordinateValueBound
      witness.finalCoordinates.parser numericBound := by
  intro coordinate
  fin_cases coordinate
  · simpa [FormulaTransformInitialFinalRowsValueBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 27
  · simpa [FormulaTransformInitialFinalRowsValueBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 29
  · simpa [FormulaTransformInitialFinalRowsValueBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 30
  · simpa [FormulaTransformInitialFinalRowsValueBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 31
  · simpa [FormulaTransformInitialFinalRowsValueBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 32
  · simpa [FormulaTransformInitialFinalRowsValueBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 33
  · simpa [FormulaTransformInitialFinalRowsValueBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 34
  · simpa [FormulaTransformInitialFinalRowsValueBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 35

theorem initialParserSizeBound_of_transformInitialFinal
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity bitBound : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates)
    (hsize : FormulaTransformInitialFinalRowsSizeBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity bitBound witness) :
    CompactUnifiedParserStateCoordinateSizeBound witness.initialCoordinates.parser
      bitBound := by
  intro coordinate
  fin_cases coordinate
  · simpa [FormulaTransformInitialFinalRowsSizeBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hsize 13
  · simpa [FormulaTransformInitialFinalRowsSizeBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hsize 15
  · simpa [FormulaTransformInitialFinalRowsSizeBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hsize 16
  · simpa [FormulaTransformInitialFinalRowsSizeBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hsize 17
  · simpa [FormulaTransformInitialFinalRowsSizeBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hsize 18
  · simpa [FormulaTransformInitialFinalRowsSizeBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hsize 19
  · simpa [FormulaTransformInitialFinalRowsSizeBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hsize 20
  · simpa [FormulaTransformInitialFinalRowsSizeBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hsize 21

theorem finalParserSizeBound_of_transformInitialFinal
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity bitBound : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates)
    (hsize : FormulaTransformInitialFinalRowsSizeBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity bitBound witness) :
    CompactUnifiedParserStateCoordinateSizeBound witness.finalCoordinates.parser
      bitBound := by
  intro coordinate
  fin_cases coordinate
  · simpa [FormulaTransformInitialFinalRowsSizeBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hsize 27
  · simpa [FormulaTransformInitialFinalRowsSizeBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hsize 29
  · simpa [FormulaTransformInitialFinalRowsSizeBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hsize 30
  · simpa [FormulaTransformInitialFinalRowsSizeBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hsize 31
  · simpa [FormulaTransformInitialFinalRowsSizeBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hsize 32
  · simpa [FormulaTransformInitialFinalRowsSizeBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hsize 33
  · simpa [FormulaTransformInitialFinalRowsSizeBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hsize 34
  · simpa [FormulaTransformInitialFinalRowsSizeBound,
      CompactFormulaTransformStateRowCoordinates.parser,
      compactUnifiedParserStateCoordinateValues,
      compactFormulaTransformInitialFinalRowsEnvironment] using hsize 35

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsCoordinateBounds
