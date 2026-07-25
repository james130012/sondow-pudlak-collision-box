import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds

/-! # Coordinatewise value and size bounds for the parser endpoints -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectParserInitialFinalRowsCoordinateBounds

open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserInitialFinalFormula

def ParserInitialFinalRowsValueBound
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount numericBound : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) : Prop :=
  forall coordinate,
    compactUnifiedParserInitialFinalRowsEnvironment tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount witness
        coordinate <= numericBound

def ParserInitialFinalRowsSizeBound
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount bitBound : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) : Prop :=
  forall coordinate,
    Nat.size
      (compactUnifiedParserInitialFinalRowsEnvironment tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness coordinate) <= bitBound

theorem initialCoordinatesValueBound_of_combined
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount numericBound : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates)
    (hvalue : ParserInitialFinalRowsValueBound tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount numericBound
      witness) :
    CompactUnifiedParserStateCoordinateValueBound witness.initialCoordinates
      numericBound := by
  intro coordinate
  fin_cases coordinate
  · simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 13
  · simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 14
  · simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 15
  · simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 16
  · simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 17
  · simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 18
  · simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 19
  · simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 20

theorem finalCoordinatesValueBound_of_combined
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount numericBound : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates)
    (hvalue : ParserInitialFinalRowsValueBound tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount numericBound
      witness) :
    CompactUnifiedParserStateCoordinateValueBound witness.finalCoordinates
      numericBound := by
  intro coordinate
  fin_cases coordinate
  · simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 23
  · simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 24
  · simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 25
  · simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 26
  · simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 27
  · simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 28
  · simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 29
  · simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 30

theorem initialCoordinatesSizeBound_of_combined
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount bitBound : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates)
    (hsize : ParserInitialFinalRowsSizeBound tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount bitBound
      witness) :
    CompactUnifiedParserStateCoordinateSizeBound witness.initialCoordinates
      bitBound := by
  intro coordinate
  fin_cases coordinate
  · simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 13
  · simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 14
  · simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 15
  · simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 16
  · simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 17
  · simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 18
  · simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 19
  · simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 20

theorem finalCoordinatesSizeBound_of_combined
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount bitBound : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates)
    (hsize : ParserInitialFinalRowsSizeBound tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount bitBound
      witness) :
    CompactUnifiedParserStateCoordinateSizeBound witness.finalCoordinates
      bitBound := by
  intro coordinate
  fin_cases coordinate
  · simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 23
  · simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 24
  · simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 25
  · simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 26
  · simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 27
  · simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 28
  · simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 29
  · simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserStateCoordinateValues,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 30

#print axioms initialCoordinatesValueBound_of_combined
#print axioms finalCoordinatesValueBound_of_combined
#print axioms initialCoordinatesSizeBound_of_combined
#print axioms finalCoordinatesSizeBound_of_combined

end FoundationCompactNumericListedDirectParserInitialFinalRowsCoordinateBounds
