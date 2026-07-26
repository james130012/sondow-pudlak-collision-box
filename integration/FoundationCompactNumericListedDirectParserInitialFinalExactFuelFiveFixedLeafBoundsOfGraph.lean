import integration.FoundationCompactNumericListedDirectParserInitialFinalExactFuelFiveFixedLeafBounds

/-! # Wiring the five fixed exact-fuel endpoint leaves -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 350000

namespace FoundationCompactNumericListedDirectParserInitialFinalExactFuelFiveFixedLeafBoundsOfGraph

open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalRowsCoordinateBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle
open FoundationCompactNumericListedDirectParserInitialFinalExactFuelFinalAtFixedBound
open FoundationCompactNumericListedDirectParserInitialFinalExactFuelFiveFixedLeafBounds
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality

noncomputable def parserInitialFinalExactFuelFiveFixedLeafBoundsOfGraph
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount numericBound bitBound : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates)
    (hgraph : CompactUnifiedParserInitialFinalRows tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
        taskBinderArity taskRepeatCount witness)
    (hvalue : ParserInitialFinalRowsValueBound tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
        taskBinderArity taskRepeatCount numericBound witness)
    (hsize : ParserInitialFinalRowsSizeBound tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
        taskBinderArity taskRepeatCount bitBound witness)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ParserInitialFinalExactFuelFiveFixedLeafBounds tokenTable width tokenCount
      stateBoundary stateCount inputCount inputBoundary expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount numericBound
      bitBound witness := by
  let oldLeaves := parserInitialFinalExactFuelFiveLeafBoundsOfGraph tokenTable
    width tokenCount stateBoundary stateCount inputBoundary inputCount
    expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
    numericBound bitBound witness hgraph hvalue hsize hnumericSize hbitPositive
  rcases hgraph with
    ⟨hcount, _hinitialAt, _hinitial, hfinalAt, _hfinal⟩
  have hinputCount : inputCount <= numericBound := by
    simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 7
  have hwidthValue : width <= numericBound := by
    simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 1
  have htokenCountValue : tokenCount <= numericBound := by
    simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 2
  have hstateCountValue : stateCount <= numericBound := by
    simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 4
  have hfinalCoordinatesValue :=
    finalCoordinatesValueBound_of_combined tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
      taskBinderArity taskRepeatCount numericBound witness hvalue
  have htokenTableSize : Nat.size tokenTable <= bitBound := by
    simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 0
  have hstateBoundarySize : Nat.size stateBoundary <= bitBound := by
    simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 3
  have hfinalCoordinatesSize :=
    finalCoordinatesSizeBound_of_combined tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
      taskBinderArity taskRepeatCount bitBound witness hsize
  let count := parserInitialFinalExactFuelCountFixedClosedDirectBound stateCount
    inputCount numericBound hcount hinputCount
  let finalAt :=
    parserInitialFinalExactFuelFinalAtFixedClosedDirectBoundOfGraph tokenTable
      width tokenCount stateBoundary stateCount inputCount numericBound bitBound
      witness.finalCoordinates witness.finalSizeWitness hfinalAt hinputCount
      hwidthValue htokenCountValue hstateCountValue hfinalCoordinatesValue
      htokenTableSize hstateBoundarySize hfinalCoordinatesSize hnumericSize
  exact
    { count := count
      initialAt := oldLeaves.initialAt
      initial := oldLeaves.initial
      finalAt := finalAt
      final := oldLeaves.final }

#print axioms parserInitialFinalExactFuelFiveFixedLeafBoundsOfGraph

end FoundationCompactNumericListedDirectParserInitialFinalExactFuelFiveFixedLeafBoundsOfGraph
