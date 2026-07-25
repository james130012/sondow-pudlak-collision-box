import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectCheckedData
import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsCoordinateBounds

/-! # Uniform endpoint bounds extracted from the bounded parser proposition -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectUniformEndpointBounds

open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectCheckedData
open FoundationCompactNumericListedDirectParserInitialFinalRowsCoordinateBounds

def compactParserInitialFinalBoundedDirectNumericBound
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat) : Nat :=
  tokenTable + width + tokenCount + stateBoundary + stateCount + fuel +
    inputBoundary + inputCount + expectedBoundary + expectedCount + taskKind +
    taskBinderArity + taskRepeatCount + valueBound + 1

def compactParserInitialFinalBoundedDirectBitBound
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat) : Nat :=
  Nat.size
    (compactParserInitialFinalBoundedDirectNumericBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      valueBound) + 1

theorem parserInitialFinalRowsValueBound_of_bounded_data
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat)
    (data : CompactParserInitialFinalBoundedDirectData tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      valueBound) :
    ParserInitialFinalRowsValueBound tokenTable width tokenCount stateBoundary
      stateCount fuel inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount
      (compactParserInitialFinalBoundedDirectNumericBound tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound)
      data.witness := by
  let numericBound :=
    compactParserInitialFinalBoundedDirectNumericBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      valueBound
  have hvalueBound : valueBound <= numericBound := by
    unfold numericBound
      compactParserInitialFinalBoundedDirectNumericBound
    omega
  have hwitness (coordinate : Fin 23) :
      compactParserInitialFinalBoundedDirectWitnessValues data.witness
          coordinate <= numericBound :=
    (data.values_le coordinate).trans hvalueBound
  intro coordinate
  fin_cases coordinate
  · simpa [numericBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using
      (show tokenTable <= numericBound by
        unfold numericBound
          compactParserInitialFinalBoundedDirectNumericBound
        omega)
  · simpa [numericBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using
      (show width <= numericBound by
        unfold numericBound
          compactParserInitialFinalBoundedDirectNumericBound
        omega)
  · simpa [numericBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using
      (show tokenCount <= numericBound by
        unfold numericBound
          compactParserInitialFinalBoundedDirectNumericBound
        omega)
  · simpa [numericBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using
      (show stateBoundary <= numericBound by
        unfold numericBound
          compactParserInitialFinalBoundedDirectNumericBound
        omega)
  · simpa [numericBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using
      (show stateCount <= numericBound by
        unfold numericBound
          compactParserInitialFinalBoundedDirectNumericBound
        omega)
  · simpa [numericBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using
      (show fuel <= numericBound by
        unfold numericBound
          compactParserInitialFinalBoundedDirectNumericBound
        omega)
  · simpa [numericBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using
      (show inputBoundary <= numericBound by
        unfold numericBound
          compactParserInitialFinalBoundedDirectNumericBound
        omega)
  · simpa [numericBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using
      (show inputCount <= numericBound by
        unfold numericBound
          compactParserInitialFinalBoundedDirectNumericBound
        omega)
  · simpa [numericBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using
      (show expectedBoundary <= numericBound by
        unfold numericBound
          compactParserInitialFinalBoundedDirectNumericBound
        omega)
  · simpa [numericBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using
      (show expectedCount <= numericBound by
        unfold numericBound
          compactParserInitialFinalBoundedDirectNumericBound
        omega)
  · simpa [numericBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using
      (show taskKind <= numericBound by
        unfold numericBound
          compactParserInitialFinalBoundedDirectNumericBound
        omega)
  · simpa [numericBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using
      (show taskBinderArity <= numericBound by
        unfold numericBound
          compactParserInitialFinalBoundedDirectNumericBound
        omega)
  · simpa [numericBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using
      (show taskRepeatCount <= numericBound by
        unfold numericBound
          compactParserInitialFinalBoundedDirectNumericBound
        omega)
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 22
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 21
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 20
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 19
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 18
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 17
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 16
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 15
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 14
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 13
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 12
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 11
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 10
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 9
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 8
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 7
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 6
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 5
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 4
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 3
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 2
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 1
  · simpa [numericBound, compactUnifiedParserInitialFinalRowsEnvironment,
      compactParserInitialFinalBoundedDirectWitnessValues] using hwitness 0

theorem parserInitialFinalRowsSizeBound_of_valueBound
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount numericBound : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates)
    (hvalue : ParserInitialFinalRowsValueBound tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount numericBound
      witness) :
    ParserInitialFinalRowsSizeBound tokenTable width tokenCount stateBoundary
      stateCount fuel inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount (Nat.size numericBound + 1)
      witness := by
  intro coordinate
  exact (Nat.size_le_size (hvalue coordinate)).trans (Nat.le_succ _)

#print axioms parserInitialFinalRowsValueBound_of_bounded_data
#print axioms parserInitialFinalRowsSizeBound_of_valueBound

end FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectUniformEndpointBounds
