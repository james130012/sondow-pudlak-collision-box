import integration.FoundationCompactNumericListedDirectParserInitialFinalExactFuelFiveFixedLeafBounds
import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectCheckedData

/-! # Clean five-leaf endpoint wiring from bounded checked data -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserInitialFinalExactFuelFiveFixedLeafBoundsOfData

open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectCheckedData
open FoundationCompactNumericListedDirectParserInitialFinalExactFuelFinalAtFixedBound
open FoundationCompactNumericListedDirectParserInitialFinalExactFuelFiveFixedLeafBounds
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality

noncomputable def parserInitialFinalExactFuelFiveFixedLeafBoundsOfData
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound numericBound bitBound : Nat)
    (data : CompactParserInitialFinalBoundedDirectData tokenTable width
      tokenCount stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
      taskBinderArity taskRepeatCount valueBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hinputCount : inputCount <= numericBound)
    (hexpectedCount : expectedCount <= numericBound)
    (hvalueBoundSucc : valueBound + 1 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hinputBoundarySize : Nat.size inputBoundary <= bitBound)
    (hexpectedBoundarySize : Nat.size expectedBoundary <= bitBound)
    (htaskKindSize : Nat.size taskKind <= bitBound)
    (htaskBinderAritySize : Nat.size taskBinderArity <= bitBound)
    (htaskRepeatCountSize : Nat.size taskRepeatCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ParserInitialFinalExactFuelFiveFixedLeafBounds tokenTable width tokenCount
      stateBoundary stateCount inputCount inputBoundary expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount numericBound
      bitBound data.witness := by
  let witness := data.witness
  have hvalueBound : valueBound <= numericBound := by omega
  have hwitnessValue (coordinate : Fin 23) :
      compactParserInitialFinalBoundedDirectWitnessValues witness coordinate <=
        numericBound :=
    (data.values_le coordinate).trans hvalueBound
  have hwitnessSize (coordinate : Fin 23) :
      Nat.size
          (compactParserInitialFinalBoundedDirectWitnessValues witness
            coordinate) <= bitBound :=
    (Nat.size_le_size (hwitnessValue coordinate)).trans hnumericSize
  have hinitialCoordinatesValue :
      CompactUnifiedParserStateCoordinateValueBound witness.initialCoordinates
        numericBound := by
    intro coordinate
    fin_cases coordinate
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using
        hwitnessValue 22
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using
        hwitnessValue 21
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using
        hwitnessValue 20
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using
        hwitnessValue 19
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using
        hwitnessValue 18
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using
        hwitnessValue 17
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using
        hwitnessValue 16
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using
        hwitnessValue 15
  have hfinalCoordinatesValue :
      CompactUnifiedParserStateCoordinateValueBound witness.finalCoordinates
        numericBound := by
    intro coordinate
    fin_cases coordinate
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using
        hwitnessValue 12
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using
        hwitnessValue 11
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using
        hwitnessValue 10
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using
        hwitnessValue 9
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using
        hwitnessValue 8
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using
        hwitnessValue 7
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using
        hwitnessValue 6
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using
        hwitnessValue 5
  have hinitialCoordinatesSize :
      CompactUnifiedParserStateCoordinateSizeBound witness.initialCoordinates
        bitBound := by
    intro coordinate
    fin_cases coordinate
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using hwitnessSize 22
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using hwitnessSize 21
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using hwitnessSize 20
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using hwitnessSize 19
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using hwitnessSize 18
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using hwitnessSize 17
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using hwitnessSize 16
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using hwitnessSize 15
  have hfinalCoordinatesSize :
      CompactUnifiedParserStateCoordinateSizeBound witness.finalCoordinates
        bitBound := by
    intro coordinate
    fin_cases coordinate
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using hwitnessSize 12
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using hwitnessSize 11
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using hwitnessSize 10
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using hwitnessSize 9
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using hwitnessSize 8
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using hwitnessSize 7
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using hwitnessSize 6
    · simpa [compactUnifiedParserStateCoordinateValues, witness,
        compactParserInitialFinalBoundedDirectWitnessValues] using hwitnessSize 5
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hinputCountSize : Nat.size inputCount <= bitBound :=
    (Nat.size_le_size hinputCount).trans hnumericSize
  have hexpectedCountSize : Nat.size expectedCount <= bitBound :=
    (Nat.size_le_size hexpectedCount).trans hnumericSize
  have hinitialTasksCount := hinitialCoordinatesValue (7 : Fin 8)
  have hinitialTasksFinish := hinitialCoordinatesValue (3 : Fin 8)
  have hfinalTasksFinish := hfinalCoordinatesValue (3 : Fin 8)
  have hfinalTasksFinishSucc : witness.finalCoordinates.tasksFinish + 1 <=
      numericBound := by
    have hraw : witness.finalCoordinates.tasksFinish <= valueBound := by
      simpa [witness, compactParserInitialFinalBoundedDirectWitnessValues] using
        data.values_le 9
    omega
  have hfinalTasksFinishSuccSize :
      Nat.size (witness.finalCoordinates.tasksFinish + 1) <= bitBound :=
    (Nat.size_le_size hfinalTasksFinishSucc).trans hnumericSize
  have houtputStartSize : Nat.size witness.outputStart <= bitBound := by
    simpa [witness, compactParserInitialFinalBoundedDirectWitnessValues] using
      hwitnessSize 2
  have houtputBoundarySize : Nat.size witness.outputBoundary <= bitBound := by
    simpa [witness, compactParserInitialFinalBoundedDirectWitnessValues] using
      hwitnessSize 1
  have houtputBoundarySizeSize : Nat.size witness.outputBoundarySize <=
      bitBound := by
    simpa [witness, compactParserInitialFinalBoundedDirectWitnessValues] using
      hwitnessSize 0
  rcases data.graph with
    ⟨hcount, hinitialAt, hinitial, hfinalAt, hfinal⟩
  let count := parserInitialFinalExactFuelCountFixedClosedDirectBound stateCount
    inputCount numericBound hcount hinputCount
  let initialAt := parserInitialFinalStateAtRowsClosedDirectBoundOfGraph
    tokenTable width tokenCount stateBoundary stateCount 0
    witness.initialCoordinates witness.initialSizeWitness numericBound bitBound
    hinitialAt hwidth htokenCount hstateCount hinitialCoordinatesValue
    htokenTableSize hstateBoundarySize hinitialCoordinatesSize hnumericSize
  let initial := parserInitialStateClosedDirectBoundOfGraph tokenTable width
    tokenCount witness.initialCoordinates inputBoundary inputCount taskKind
    taskBinderArity taskRepeatCount numericBound bitBound hinitial hwidth
    htokenCount hinputCount
    (by simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialTasksCount)
    (by simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialTasksFinish)
    htokenTableSize hwidthSize htokenCountSize
    (by simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialCoordinatesSize (0 : Fin 8))
    (by simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialCoordinatesSize (1 : Fin 8))
    (by simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialCoordinatesSize (2 : Fin 8))
    (by simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialCoordinatesSize (3 : Fin 8))
    (by simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialCoordinatesSize (4 : Fin 8))
    (by simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialCoordinatesSize (5 : Fin 8))
    (by simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialCoordinatesSize (6 : Fin 8))
    (by simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialCoordinatesSize (7 : Fin 8))
    hinputBoundarySize hinputCountSize htaskKindSize htaskBinderAritySize
    htaskRepeatCountSize hnumericSize
  let finalAt :=
    parserInitialFinalExactFuelFinalAtFixedClosedDirectBoundOfGraph tokenTable
      width tokenCount stateBoundary stateCount inputCount numericBound bitBound
      witness.finalCoordinates witness.finalSizeWitness hfinalAt hinputCount
      hwidth htokenCount hstateCount hfinalCoordinatesValue htokenTableSize
      hstateBoundarySize hfinalCoordinatesSize hnumericSize
  let final := parserFinalStateClosedDirectBoundOfGraph tokenTable width
    tokenCount witness.finalCoordinates expectedBoundary expectedCount
    witness.outputStart witness.outputBoundary witness.outputBoundarySize
    numericBound bitBound hfinal hwidth htokenCount hexpectedCount
    (by simpa [compactUnifiedParserStateCoordinateValues] using
      hfinalTasksFinish)
    hfinalTasksFinishSucc htokenTableSize hwidthSize htokenCountSize
    (by simpa [compactUnifiedParserStateCoordinateValues] using
      hfinalCoordinatesSize (0 : Fin 8))
    (by simpa [compactUnifiedParserStateCoordinateValues] using
      hfinalCoordinatesSize (1 : Fin 8))
    (by simpa [compactUnifiedParserStateCoordinateValues] using
      hfinalCoordinatesSize (2 : Fin 8))
    (by simpa [compactUnifiedParserStateCoordinateValues] using
      hfinalCoordinatesSize (3 : Fin 8))
    (by simpa [compactUnifiedParserStateCoordinateValues] using
      hfinalCoordinatesSize (4 : Fin 8))
    (by simpa [compactUnifiedParserStateCoordinateValues] using
      hfinalCoordinatesSize (5 : Fin 8))
    (by simpa [compactUnifiedParserStateCoordinateValues] using
      hfinalCoordinatesSize (6 : Fin 8))
    (by simpa [compactUnifiedParserStateCoordinateValues] using
      hfinalCoordinatesSize (7 : Fin 8))
    hexpectedBoundarySize hexpectedCountSize houtputStartSize
    houtputBoundarySize houtputBoundarySizeSize hfinalTasksFinishSuccSize
    hnumericSize hbitPositive
  exact
    { count := count
      initialAt := initialAt
      initial := initial
      finalAt := finalAt
      final := final }

#print axioms parserInitialFinalExactFuelFiveFixedLeafBoundsOfData

end FoundationCompactNumericListedDirectParserInitialFinalExactFuelFiveFixedLeafBoundsOfData
