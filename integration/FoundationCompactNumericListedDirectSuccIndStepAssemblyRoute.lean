import integration.FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
import integration.FoundationCompactNumericListedDirectFormulaConstructorSlices

/-!
# Direct checked assembly for the successor-induction step branch

Starting from the open zero and open successor instances, this route builds
the negated quantified step premise and the quantified final conclusion.  All
constructor outputs and both negation traces share one token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSuccIndStepAssemblyRoute

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaConstructors
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpoint
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectFormulaConstructorSlices
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute

structure CompactSuccIndStepAssemblyRouteCoordinates where
  negatedStepZeroTrace : CompactFormulaTransformTraceSlot
  negatedQuantifiedStepTrace : CompactFormulaTransformTraceSlot

def CompactSuccIndStepAssemblyRoute
    (tokenTable width tokenCount : Nat)
    (stepZero stepSuccessor negatedStepZero stepDisjunction quantifiedStep
      negatedQuantifiedStep quantifiedFinal empty : CompactNatListRowSlot)
    (coordinates : CompactSuccIndStepAssemblyRouteCoordinates) : Prop :=
  empty.count = 0 /\
    CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      stepSuccessor.start stepSuccessor.count stepSuccessor.finish
      stepSuccessor.boundary stepSuccessor.boundarySize /\
    CompactFormulaTransformTotalExactEndpoint
      tokenTable width tokenCount 3 1
      empty.start empty.finish empty.boundary empty.count empty.boundarySize
      stepZero.start stepZero.finish stepZero.boundary stepZero.count
        stepZero.boundarySize
      negatedStepZero.start negatedStepZero.finish negatedStepZero.boundary
        negatedStepZero.count negatedStepZero.boundarySize
      empty.start empty.finish empty.boundary empty.boundarySize
      coordinates.negatedStepZeroTrace.stateBoundary
        coordinates.negatedStepZeroTrace.stateCount
      coordinates.negatedStepZeroTrace.tableWidth
        coordinates.negatedStepZeroTrace.valueBound /\
    CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      stepDisjunction.start stepDisjunction.count stepDisjunction.finish
      stepDisjunction.boundary stepDisjunction.boundarySize /\
    CompactAdditiveBinaryFormulaConstructorSlices tokenTable width tokenCount 5
      negatedStepZero.start negatedStepZero.finish negatedStepZero.count
      stepSuccessor.start stepSuccessor.finish stepSuccessor.count
      stepDisjunction.start stepDisjunction.finish stepDisjunction.count /\
    CompactAdditiveUnaryFormulaConstructorSlices tokenTable width tokenCount 6
      stepDisjunction.start stepDisjunction.finish stepDisjunction.count
      quantifiedStep.start quantifiedStep.finish quantifiedStep.count /\
    CompactFormulaTransformTotalExactEndpoint
      tokenTable width tokenCount 3 0
      empty.start empty.finish empty.boundary empty.count empty.boundarySize
      quantifiedStep.start quantifiedStep.finish quantifiedStep.boundary
        quantifiedStep.count quantifiedStep.boundarySize
      negatedQuantifiedStep.start negatedQuantifiedStep.finish
        negatedQuantifiedStep.boundary negatedQuantifiedStep.count
        negatedQuantifiedStep.boundarySize
      empty.start empty.finish empty.boundary empty.boundarySize
      coordinates.negatedQuantifiedStepTrace.stateBoundary
        coordinates.negatedQuantifiedStepTrace.stateCount
      coordinates.negatedQuantifiedStepTrace.tableWidth
        coordinates.negatedQuantifiedStepTrace.valueBound /\
    CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      quantifiedFinal.start quantifiedFinal.count quantifiedFinal.finish
      quantifiedFinal.boundary quantifiedFinal.boundarySize /\
    CompactAdditiveUnaryFormulaConstructorSlices tokenTable width tokenCount 6
      stepZero.start stepZero.finish stepZero.count
      quantifiedFinal.start quantifiedFinal.finish quantifiedFinal.count

def compactSuccIndStepAssemblyRouteDef : 𝚺₀.Semisentence 51 := .mkSigma
  “tokenTable width tokenCount
      stepZeroStart stepZeroFinish stepZeroBoundary stepZeroCount
        stepZeroBoundarySize
      stepSuccessorStart stepSuccessorFinish stepSuccessorBoundary
        stepSuccessorCount stepSuccessorBoundarySize
      negatedStepZeroStart negatedStepZeroFinish negatedStepZeroBoundary
        negatedStepZeroCount negatedStepZeroBoundarySize
      stepDisjunctionStart stepDisjunctionFinish stepDisjunctionBoundary
        stepDisjunctionCount stepDisjunctionBoundarySize
      quantifiedStepStart quantifiedStepFinish quantifiedStepBoundary
        quantifiedStepCount quantifiedStepBoundarySize
      negatedQuantifiedStepStart negatedQuantifiedStepFinish
        negatedQuantifiedStepBoundary negatedQuantifiedStepCount
        negatedQuantifiedStepBoundarySize
      quantifiedFinalStart quantifiedFinalFinish quantifiedFinalBoundary
        quantifiedFinalCount quantifiedFinalBoundarySize
      emptyStart emptyFinish emptyBoundary emptyCount emptyBoundarySize
      negatedStepZeroStateBoundary negatedStepZeroStateCount
        negatedStepZeroTableWidth negatedStepZeroValueBound
      negatedQuantifiedStepStateBoundary negatedQuantifiedStepStateCount
        negatedQuantifiedStepTableWidth negatedQuantifiedStepValueBound.
    emptyCount = 0 ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount
      stepSuccessorStart stepSuccessorCount stepSuccessorFinish
      stepSuccessorBoundary stepSuccessorBoundarySize ∧
    !(compactFormulaTransformTotalExactEndpointDef)
      tokenTable width tokenCount 3 1
      emptyStart emptyFinish emptyBoundary emptyCount emptyBoundarySize
      stepZeroStart stepZeroFinish stepZeroBoundary stepZeroCount
        stepZeroBoundarySize
      negatedStepZeroStart negatedStepZeroFinish negatedStepZeroBoundary
        negatedStepZeroCount negatedStepZeroBoundarySize
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      negatedStepZeroStateBoundary negatedStepZeroStateCount
        negatedStepZeroTableWidth negatedStepZeroValueBound ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount
      stepDisjunctionStart stepDisjunctionCount stepDisjunctionFinish
      stepDisjunctionBoundary stepDisjunctionBoundarySize ∧
    !(compactAdditiveBinaryFormulaConstructorSlicesDef)
      tokenTable width tokenCount 5
      negatedStepZeroStart negatedStepZeroFinish negatedStepZeroCount
      stepSuccessorStart stepSuccessorFinish stepSuccessorCount
      stepDisjunctionStart stepDisjunctionFinish stepDisjunctionCount ∧
    !(compactAdditiveUnaryFormulaConstructorSlicesDef)
      tokenTable width tokenCount 6
      stepDisjunctionStart stepDisjunctionFinish stepDisjunctionCount
      quantifiedStepStart quantifiedStepFinish quantifiedStepCount ∧
    !(compactFormulaTransformTotalExactEndpointDef)
      tokenTable width tokenCount 3 0
      emptyStart emptyFinish emptyBoundary emptyCount emptyBoundarySize
      quantifiedStepStart quantifiedStepFinish quantifiedStepBoundary
        quantifiedStepCount quantifiedStepBoundarySize
      negatedQuantifiedStepStart negatedQuantifiedStepFinish
        negatedQuantifiedStepBoundary negatedQuantifiedStepCount
        negatedQuantifiedStepBoundarySize
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      negatedQuantifiedStepStateBoundary negatedQuantifiedStepStateCount
        negatedQuantifiedStepTableWidth negatedQuantifiedStepValueBound ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount
      quantifiedFinalStart quantifiedFinalCount quantifiedFinalFinish
      quantifiedFinalBoundary quantifiedFinalBoundarySize ∧
    !(compactAdditiveUnaryFormulaConstructorSlicesDef)
      tokenTable width tokenCount 6
      stepZeroStart stepZeroFinish stepZeroCount
      quantifiedFinalStart quantifiedFinalFinish quantifiedFinalCount”

def compactSuccIndStepAssemblyRouteEnvironment
    (tokenTable width tokenCount : Nat)
    (stepZero stepSuccessor negatedStepZero stepDisjunction quantifiedStep
      negatedQuantifiedStep quantifiedFinal empty : CompactNatListRowSlot)
    (coordinates : CompactSuccIndStepAssemblyRouteCoordinates) :
    Fin 51 -> Nat :=
  ![tokenTable, width, tokenCount,
    stepZero.start, stepZero.finish, stepZero.boundary, stepZero.count,
      stepZero.boundarySize,
    stepSuccessor.start, stepSuccessor.finish, stepSuccessor.boundary,
      stepSuccessor.count, stepSuccessor.boundarySize,
    negatedStepZero.start, negatedStepZero.finish,
      negatedStepZero.boundary, negatedStepZero.count,
      negatedStepZero.boundarySize,
    stepDisjunction.start, stepDisjunction.finish,
      stepDisjunction.boundary, stepDisjunction.count,
      stepDisjunction.boundarySize,
    quantifiedStep.start, quantifiedStep.finish, quantifiedStep.boundary,
      quantifiedStep.count, quantifiedStep.boundarySize,
    negatedQuantifiedStep.start, negatedQuantifiedStep.finish,
      negatedQuantifiedStep.boundary, negatedQuantifiedStep.count,
      negatedQuantifiedStep.boundarySize,
    quantifiedFinal.start, quantifiedFinal.finish, quantifiedFinal.boundary,
      quantifiedFinal.count, quantifiedFinal.boundarySize,
    empty.start, empty.finish, empty.boundary, empty.count,
      empty.boundarySize,
    coordinates.negatedStepZeroTrace.stateBoundary,
      coordinates.negatedStepZeroTrace.stateCount,
      coordinates.negatedStepZeroTrace.tableWidth,
      coordinates.negatedStepZeroTrace.valueBound,
    coordinates.negatedQuantifiedStepTrace.stateBoundary,
      coordinates.negatedQuantifiedStepTrace.stateCount,
      coordinates.negatedQuantifiedStepTrace.tableWidth,
      coordinates.negatedQuantifiedStepTrace.valueBound]

set_option maxHeartbeats 1800000 in
-- Eight embedded bounded relations require a local normalization budget.
set_option maxRecDepth 4096 in
@[simp] theorem compactSuccIndStepAssemblyRouteDef_spec
    (tokenTable width tokenCount : Nat)
    (stepZero stepSuccessor negatedStepZero stepDisjunction quantifiedStep
      negatedQuantifiedStep quantifiedFinal empty : CompactNatListRowSlot)
    (coordinates : CompactSuccIndStepAssemblyRouteCoordinates) :
    compactSuccIndStepAssemblyRouteDef.val.Evalb
        (compactSuccIndStepAssemblyRouteEnvironment
          tokenTable width tokenCount stepZero stepSuccessor negatedStepZero
            stepDisjunction quantifiedStep negatedQuantifiedStep
            quantifiedFinal empty coordinates) ↔
      CompactSuccIndStepAssemblyRoute tokenTable width tokenCount
        stepZero stepSuccessor negatedStepZero stepDisjunction quantifiedStep
        negatedQuantifiedStep quantifiedFinal empty coordinates := by
  let env := compactSuccIndStepAssemblyRouteEnvironment
    tokenTable width tokenCount stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      empty coordinates
  change compactSuccIndStepAssemblyRouteDef.val.Evalb env ↔ _
  have hstepSuccessorRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 51), #1, #2,
          #8, #11, #9, #10, #12]) =
        ![tokenTable, width, tokenCount,
          stepSuccessor.start, stepSuccessor.count, stepSuccessor.finish,
          stepSuccessor.boundary, stepSuccessor.boundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hnegatedStepZeroEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 51), #1, #2, ‘3’, ‘1’,
          #38, #39, #40, #41, #42,
          #3, #4, #5, #6, #7,
          #13, #14, #15, #16, #17,
          #38, #39, #40, #42, #43, #44, #45, #46]) =
        ![tokenTable, width, tokenCount, 3, 1,
          empty.start, empty.finish, empty.boundary, empty.count,
            empty.boundarySize,
          stepZero.start, stepZero.finish, stepZero.boundary, stepZero.count,
            stepZero.boundarySize,
          negatedStepZero.start, negatedStepZero.finish,
            negatedStepZero.boundary, negatedStepZero.count,
            negatedStepZero.boundarySize,
          empty.start, empty.finish, empty.boundary, empty.boundarySize,
          coordinates.negatedStepZeroTrace.stateBoundary,
            coordinates.negatedStepZeroTrace.stateCount,
            coordinates.negatedStepZeroTrace.tableWidth,
            coordinates.negatedStepZeroTrace.valueBound] := by
    funext coordinate
    fin_cases coordinate <;> simp [env,
      compactSuccIndStepAssemblyRouteEnvironment]
  have hstepDisjunctionRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 51), #1, #2,
          #18, #21, #19, #20, #22]) =
        ![tokenTable, width, tokenCount,
          stepDisjunction.start, stepDisjunction.count,
          stepDisjunction.finish, stepDisjunction.boundary,
          stepDisjunction.boundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hstepDisjunctionSlicesEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 51), #1, #2, ‘5’,
          #13, #14, #16, #8, #9, #11, #18, #19, #21]) =
        ![tokenTable, width, tokenCount, 5,
          negatedStepZero.start, negatedStepZero.finish,
            negatedStepZero.count,
          stepSuccessor.start, stepSuccessor.finish, stepSuccessor.count,
          stepDisjunction.start, stepDisjunction.finish,
            stepDisjunction.count] := by
    funext coordinate
    fin_cases coordinate <;> simp [env,
      compactSuccIndStepAssemblyRouteEnvironment]
  have hquantifiedStepSlicesEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 51), #1, #2, ‘6’,
          #18, #19, #21, #23, #24, #26]) =
        ![tokenTable, width, tokenCount, 6,
          stepDisjunction.start, stepDisjunction.finish,
            stepDisjunction.count,
          quantifiedStep.start, quantifiedStep.finish,
            quantifiedStep.count] := by
    funext coordinate
    fin_cases coordinate <;> simp [env,
      compactSuccIndStepAssemblyRouteEnvironment]
  have hnegatedQuantifiedStepEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 51), #1, #2, ‘3’, ‘0’,
          #38, #39, #40, #41, #42,
          #23, #24, #25, #26, #27,
          #28, #29, #30, #31, #32,
          #38, #39, #40, #42, #47, #48, #49, #50]) =
        ![tokenTable, width, tokenCount, 3, 0,
          empty.start, empty.finish, empty.boundary, empty.count,
            empty.boundarySize,
          quantifiedStep.start, quantifiedStep.finish,
            quantifiedStep.boundary, quantifiedStep.count,
            quantifiedStep.boundarySize,
          negatedQuantifiedStep.start, negatedQuantifiedStep.finish,
            negatedQuantifiedStep.boundary, negatedQuantifiedStep.count,
            negatedQuantifiedStep.boundarySize,
          empty.start, empty.finish, empty.boundary, empty.boundarySize,
          coordinates.negatedQuantifiedStepTrace.stateBoundary,
            coordinates.negatedQuantifiedStepTrace.stateCount,
            coordinates.negatedQuantifiedStepTrace.tableWidth,
            coordinates.negatedQuantifiedStepTrace.valueBound] := by
    funext coordinate
    fin_cases coordinate <;> simp [env,
      compactSuccIndStepAssemblyRouteEnvironment]
  have hquantifiedFinalRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 51), #1, #2,
          #33, #36, #34, #35, #37]) =
        ![tokenTable, width, tokenCount,
          quantifiedFinal.start, quantifiedFinal.count,
          quantifiedFinal.finish, quantifiedFinal.boundary,
          quantifiedFinal.boundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hquantifiedFinalSlicesEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 51), #1, #2, ‘6’,
          #3, #4, #6, #33, #34, #36]) =
        ![tokenTable, width, tokenCount, 6,
          stepZero.start, stepZero.finish, stepZero.count,
          quantifiedFinal.start, quantifiedFinal.finish,
            quantifiedFinal.count] := by
    funext coordinate
    fin_cases coordinate <;> simp [env,
      compactSuccIndStepAssemblyRouteEnvironment]
  have hstepSuccessorRowsSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 51), #1, #2,
              #8, #11, #9, #10, #12])
          Empty.elim) compactAdditiveNatListWitnessRowsDef.val ↔
        CompactAdditiveNatListWitnessRows tokenTable width tokenCount
          stepSuccessor.start stepSuccessor.count stepSuccessor.finish
          stepSuccessor.boundary stepSuccessor.boundarySize := by
    rw [hstepSuccessorRowsEnv]
    exact compactAdditiveNatListWitnessRowsDef_spec
      tokenTable width tokenCount stepSuccessor.start stepSuccessor.count
      stepSuccessor.finish stepSuccessor.boundary
      stepSuccessor.boundarySize
  have hnegatedStepZeroSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 51), #1, #2, ‘3’, ‘1’,
              #38, #39, #40, #41, #42,
              #3, #4, #5, #6, #7,
              #13, #14, #15, #16, #17,
              #38, #39, #40, #42, #43, #44, #45, #46])
          Empty.elim) compactFormulaTransformTotalExactEndpointDef.val ↔
        CompactFormulaTransformTotalExactEndpoint
          tokenTable width tokenCount 3 1
          empty.start empty.finish empty.boundary empty.count
            empty.boundarySize
          stepZero.start stepZero.finish stepZero.boundary stepZero.count
            stepZero.boundarySize
          negatedStepZero.start negatedStepZero.finish
            negatedStepZero.boundary negatedStepZero.count
            negatedStepZero.boundarySize
          empty.start empty.finish empty.boundary empty.boundarySize
          coordinates.negatedStepZeroTrace.stateBoundary
            coordinates.negatedStepZeroTrace.stateCount
          coordinates.negatedStepZeroTrace.tableWidth
            coordinates.negatedStepZeroTrace.valueBound := by
    rw [hnegatedStepZeroEnv]
    exact compactFormulaTransformTotalExactEndpointDef_spec
      tokenTable width tokenCount 3 1
      empty.start empty.finish empty.boundary empty.count empty.boundarySize
      stepZero.start stepZero.finish stepZero.boundary stepZero.count
        stepZero.boundarySize
      negatedStepZero.start negatedStepZero.finish
        negatedStepZero.boundary negatedStepZero.count
        negatedStepZero.boundarySize
      empty.start empty.finish empty.boundary empty.boundarySize
      coordinates.negatedStepZeroTrace.stateBoundary
        coordinates.negatedStepZeroTrace.stateCount
      coordinates.negatedStepZeroTrace.tableWidth
        coordinates.negatedStepZeroTrace.valueBound
  have hstepDisjunctionRowsSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 51), #1, #2,
              #18, #21, #19, #20, #22])
          Empty.elim) compactAdditiveNatListWitnessRowsDef.val ↔
        CompactAdditiveNatListWitnessRows tokenTable width tokenCount
          stepDisjunction.start stepDisjunction.count stepDisjunction.finish
          stepDisjunction.boundary stepDisjunction.boundarySize := by
    rw [hstepDisjunctionRowsEnv]
    exact compactAdditiveNatListWitnessRowsDef_spec
      tokenTable width tokenCount stepDisjunction.start
      stepDisjunction.count stepDisjunction.finish
      stepDisjunction.boundary stepDisjunction.boundarySize
  have hstepDisjunctionSlicesSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 51), #1, #2, ‘5’,
              #13, #14, #16, #8, #9, #11, #18, #19, #21])
          Empty.elim) compactAdditiveBinaryFormulaConstructorSlicesDef.val ↔
        CompactAdditiveBinaryFormulaConstructorSlices
          tokenTable width tokenCount 5
          negatedStepZero.start negatedStepZero.finish
            negatedStepZero.count
          stepSuccessor.start stepSuccessor.finish stepSuccessor.count
          stepDisjunction.start stepDisjunction.finish
            stepDisjunction.count := by
    rw [hstepDisjunctionSlicesEnv]
    exact compactAdditiveBinaryFormulaConstructorSlicesDef_spec
      tokenTable width tokenCount 5
      negatedStepZero.start negatedStepZero.finish negatedStepZero.count
      stepSuccessor.start stepSuccessor.finish stepSuccessor.count
      stepDisjunction.start stepDisjunction.finish stepDisjunction.count
  have hquantifiedStepSlicesSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 51), #1, #2, ‘6’,
              #18, #19, #21, #23, #24, #26])
          Empty.elim) compactAdditiveUnaryFormulaConstructorSlicesDef.val ↔
        CompactAdditiveUnaryFormulaConstructorSlices
          tokenTable width tokenCount 6
          stepDisjunction.start stepDisjunction.finish
            stepDisjunction.count
          quantifiedStep.start quantifiedStep.finish quantifiedStep.count := by
    rw [hquantifiedStepSlicesEnv]
    exact compactAdditiveUnaryFormulaConstructorSlicesDef_spec
      tokenTable width tokenCount 6
      stepDisjunction.start stepDisjunction.finish stepDisjunction.count
      quantifiedStep.start quantifiedStep.finish quantifiedStep.count
  have hnegatedQuantifiedStepSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 51), #1, #2, ‘3’, ‘0’,
              #38, #39, #40, #41, #42,
              #23, #24, #25, #26, #27,
              #28, #29, #30, #31, #32,
              #38, #39, #40, #42, #47, #48, #49, #50])
          Empty.elim) compactFormulaTransformTotalExactEndpointDef.val ↔
        CompactFormulaTransformTotalExactEndpoint
          tokenTable width tokenCount 3 0
          empty.start empty.finish empty.boundary empty.count
            empty.boundarySize
          quantifiedStep.start quantifiedStep.finish quantifiedStep.boundary
            quantifiedStep.count quantifiedStep.boundarySize
          negatedQuantifiedStep.start negatedQuantifiedStep.finish
            negatedQuantifiedStep.boundary negatedQuantifiedStep.count
            negatedQuantifiedStep.boundarySize
          empty.start empty.finish empty.boundary empty.boundarySize
          coordinates.negatedQuantifiedStepTrace.stateBoundary
            coordinates.negatedQuantifiedStepTrace.stateCount
          coordinates.negatedQuantifiedStepTrace.tableWidth
            coordinates.negatedQuantifiedStepTrace.valueBound := by
    rw [hnegatedQuantifiedStepEnv]
    exact compactFormulaTransformTotalExactEndpointDef_spec
      tokenTable width tokenCount 3 0
      empty.start empty.finish empty.boundary empty.count empty.boundarySize
      quantifiedStep.start quantifiedStep.finish quantifiedStep.boundary
        quantifiedStep.count quantifiedStep.boundarySize
      negatedQuantifiedStep.start negatedQuantifiedStep.finish
        negatedQuantifiedStep.boundary negatedQuantifiedStep.count
        negatedQuantifiedStep.boundarySize
      empty.start empty.finish empty.boundary empty.boundarySize
      coordinates.negatedQuantifiedStepTrace.stateBoundary
        coordinates.negatedQuantifiedStepTrace.stateCount
      coordinates.negatedQuantifiedStepTrace.tableWidth
        coordinates.negatedQuantifiedStepTrace.valueBound
  have hquantifiedFinalRowsSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 51), #1, #2,
              #33, #36, #34, #35, #37])
          Empty.elim) compactAdditiveNatListWitnessRowsDef.val ↔
        CompactAdditiveNatListWitnessRows tokenTable width tokenCount
          quantifiedFinal.start quantifiedFinal.count quantifiedFinal.finish
          quantifiedFinal.boundary quantifiedFinal.boundarySize := by
    rw [hquantifiedFinalRowsEnv]
    exact compactAdditiveNatListWitnessRowsDef_spec
      tokenTable width tokenCount quantifiedFinal.start quantifiedFinal.count
      quantifiedFinal.finish quantifiedFinal.boundary
      quantifiedFinal.boundarySize
  have hquantifiedFinalSlicesSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 51), #1, #2, ‘6’,
              #3, #4, #6, #33, #34, #36])
          Empty.elim) compactAdditiveUnaryFormulaConstructorSlicesDef.val ↔
        CompactAdditiveUnaryFormulaConstructorSlices
          tokenTable width tokenCount 6
          stepZero.start stepZero.finish stepZero.count
          quantifiedFinal.start quantifiedFinal.finish
            quantifiedFinal.count := by
    rw [hquantifiedFinalSlicesEnv]
    exact compactAdditiveUnaryFormulaConstructorSlicesDef_spec
      tokenTable width tokenCount 6
      stepZero.start stepZero.finish stepZero.count
      quantifiedFinal.start quantifiedFinal.finish quantifiedFinal.count
  have hemptyCountValue : env 41 = empty.count := by rfl
  simp [compactSuccIndStepAssemblyRouteDef,
    CompactSuccIndStepAssemblyRoute,
    hstepSuccessorRowsSpec, hnegatedStepZeroSpec,
    hstepDisjunctionRowsSpec, hstepDisjunctionSlicesSpec,
    hquantifiedStepSlicesSpec, hnegatedQuantifiedStepSpec,
    hquantifiedFinalRowsSpec, hquantifiedFinalSlicesSpec,
    hemptyCountValue]

theorem compactSuccIndStepAssemblyRouteDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactSuccIndStepAssemblyRouteDef.val := by
  simp [compactSuccIndStepAssemblyRouteDef]

theorem CompactSuccIndStepAssemblyRoute.sound_canonical
    {tokenTable width tokenCount : Nat}
    {stepZeroSlot stepSuccessorSlot negatedStepZeroSlot
      stepDisjunctionSlot quantifiedStepSlot negatedQuantifiedStepSlot
      quantifiedFinalSlot emptySlot : CompactNatListRowSlot}
    {coordinates : CompactSuccIndStepAssemblyRouteCoordinates}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hroute : CompactSuccIndStepAssemblyRoute tokenTable width tokenCount
      stepZeroSlot stepSuccessorSlot negatedStepZeroSlot
      stepDisjunctionSlot quantifiedStepSlot negatedQuantifiedStepSlot
      quantifiedFinalSlot emptySlot coordinates)
    (hstepZero : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      stepZeroSlot.start stepZeroSlot.finish
        (compactArithmeticFormulaTokens
          (compactSuccIndStepZeroFormula body)))
    (hstepSuccessor : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount stepSuccessorSlot.start
        stepSuccessorSlot.finish
        (compactArithmeticFormulaTokens
          (compactSuccIndStepSuccessorFormula body))) :
    ∃ negatedQuantifiedStepTokens quantifiedFinalTokens : List Nat,
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        negatedQuantifiedStepSlot.start negatedQuantifiedStepSlot.finish
          negatedQuantifiedStepTokens /\
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        quantifiedFinalSlot.start quantifiedFinalSlot.finish
          quantifiedFinalTokens /\
      negatedQuantifiedStepTokens = compactArithmeticFormulaTokens
        (∼(∀⁰ ((∼compactSuccIndStepZeroFormula body) ⋎
          compactSuccIndStepSuccessorFormula body))) /\
      quantifiedFinalTokens = compactArithmeticFormulaTokens
        (∀⁰ compactSuccIndStepZeroFormula body) := by
  rcases hroute with
    ⟨_hemptyCount, hstepSuccessorRows, hnegatedStepZeroEndpoint,
      hstepDisjunctionRows, hstepDisjunctionSlices,
      hquantifiedStepSlices, hnegatedQuantifiedStepEndpoint,
      hquantifiedFinalRows, hquantifiedFinalSlices⟩
  rcases hstepSuccessorRows.realize with
    ⟨stepSuccessorTokens, hstepSuccessorCount,
      hstepSuccessorRowsLayout, _hstepSuccessorElementRows⟩
  have hstepSuccessorEq :
      compactArithmeticFormulaTokens
          (compactSuccIndStepSuccessorFormula body) =
        stepSuccessorTokens :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hstepSuccessorRowsLayout hstepSuccessor).1
  subst stepSuccessorTokens
  have hstepSuccessorCountValue : stepSuccessorSlot.count =
      (compactArithmeticFormulaTokens
        (compactSuccIndStepSuccessorFormula body)).length :=
    hstepSuccessorCount.symm
  rcases hnegatedStepZeroEndpoint.sound with
    ⟨_negationWitness, stepZeroTokens, negatedStepZeroTokens,
      _hnegationWitnessLayout, hstepZeroEndpointLayout,
      hnegatedStepZeroLayout, hnegatedStepZeroResult⟩
  have hstepZeroEq :
      compactArithmeticFormulaTokens (compactSuccIndStepZeroFormula body) =
        stepZeroTokens :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hstepZeroEndpointLayout hstepZero).1
  subst stepZeroTokens
  have hnegatedStepZeroResult' : negatedStepZeroTokens =
      (compactFormulaNegationExact 1
        (compactArithmeticFormulaTokens
          (compactSuccIndStepZeroFormula body))).getD [] := by
    simpa [compactFormulaNegationExact] using hnegatedStepZeroResult
  have hnegatedStepZeroCanonical : negatedStepZeroTokens =
      compactArithmeticFormulaTokens
        (∼compactSuccIndStepZeroFormula body) := by
    rw [compactFormulaNegationExact_canonical] at hnegatedStepZeroResult'
    simpa using hnegatedStepZeroResult'
  rcases hnegatedStepZeroEndpoint.2.1.realize with
    ⟨stepZeroRows, hstepZeroCount, hstepZeroRowsLayout, _hstepZeroRows⟩
  have hstepZeroRowsEq : stepZeroRows =
      compactArithmeticFormulaTokens
        (compactSuccIndStepZeroFormula body) :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hstepZero hstepZeroRowsLayout).1
  have hstepZeroCountValue : stepZeroSlot.count =
      (compactArithmeticFormulaTokens
        (compactSuccIndStepZeroFormula body)).length := by
    rw [← hstepZeroRowsEq]
    exact hstepZeroCount.symm
  rcases hnegatedStepZeroEndpoint.2.2.1.realize with
    ⟨negatedStepZeroRows, hnegatedStepZeroCount,
      hnegatedStepZeroRowsLayout, _hnegatedStepZeroRows⟩
  have hnegatedStepZeroRowsEq : negatedStepZeroRows =
      negatedStepZeroTokens :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hnegatedStepZeroLayout hnegatedStepZeroRowsLayout).1
  have hnegatedStepZeroCountValue : negatedStepZeroSlot.count =
      negatedStepZeroTokens.length := by
    rw [← hnegatedStepZeroRowsEq]
    exact hnegatedStepZeroCount.symm
  rcases hstepDisjunctionRows.realize with
    ⟨stepDisjunctionTokens, hstepDisjunctionCount,
      hstepDisjunctionLayout, _hstepDisjunctionRows⟩
  have hstepDisjunctionCountValue : stepDisjunctionSlot.count =
      stepDisjunctionTokens.length := hstepDisjunctionCount.symm
  have hstepDisjunctionSlices' :
      CompactAdditiveBinaryFormulaConstructorSlices
        tokenTable width tokenCount 5
        negatedStepZeroSlot.start negatedStepZeroSlot.finish
          negatedStepZeroTokens.length
        stepSuccessorSlot.start stepSuccessorSlot.finish
          (compactArithmeticFormulaTokens
            (compactSuccIndStepSuccessorFormula body)).length
        stepDisjunctionSlot.start stepDisjunctionSlot.finish
          stepDisjunctionTokens.length := by
    simpa only [hnegatedStepZeroCountValue,
      hstepSuccessorCountValue, hstepDisjunctionCountValue]
      using hstepDisjunctionSlices
  have hstepDisjunctionValue : stepDisjunctionTokens =
      tokenFormulaOr negatedStepZeroTokens
        (compactArithmeticFormulaTokens
          (compactSuccIndStepSuccessorFormula body)) :=
    (compactAdditiveFormulaOrSlices_iff hnegatedStepZeroLayout
      hstepSuccessor hstepDisjunctionLayout).mp hstepDisjunctionSlices'
  have hstepDisjunctionCanonical : stepDisjunctionTokens =
      compactArithmeticFormulaTokens
        ((∼compactSuccIndStepZeroFormula body) ⋎
          compactSuccIndStepSuccessorFormula body) := by
    rw [hstepDisjunctionValue, hnegatedStepZeroCanonical]
    rfl
  rcases hnegatedQuantifiedStepEndpoint.sound with
    ⟨_negatedQuantifiedStepWitness, quantifiedStepTokens,
      negatedQuantifiedStepTokens, _hnegatedQuantifiedStepWitnessLayout,
      hquantifiedStepLayout, hnegatedQuantifiedStepLayout,
      hnegatedQuantifiedStepResult⟩
  rcases hnegatedQuantifiedStepEndpoint.2.1.realize with
    ⟨quantifiedStepRows, hquantifiedStepCount,
      hquantifiedStepRowsLayout, _hquantifiedStepRows⟩
  have hquantifiedStepRowsEq : quantifiedStepRows = quantifiedStepTokens :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hquantifiedStepLayout hquantifiedStepRowsLayout).1
  have hquantifiedStepCountValue : quantifiedStepSlot.count =
      quantifiedStepTokens.length := by
    rw [← hquantifiedStepRowsEq]
    exact hquantifiedStepCount.symm
  have hquantifiedStepSlices' :
      CompactAdditiveUnaryFormulaConstructorSlices
        tokenTable width tokenCount 6
        stepDisjunctionSlot.start stepDisjunctionSlot.finish
          stepDisjunctionTokens.length
        quantifiedStepSlot.start quantifiedStepSlot.finish
          quantifiedStepTokens.length := by
    simpa only [hstepDisjunctionCountValue, hquantifiedStepCountValue]
      using hquantifiedStepSlices
  have hquantifiedStepValue : quantifiedStepTokens =
      tokenFormulaAll stepDisjunctionTokens :=
    (compactAdditiveFormulaAllSlices_iff hstepDisjunctionLayout
      hquantifiedStepLayout).mp hquantifiedStepSlices'
  have hquantifiedStepCanonical : quantifiedStepTokens =
      compactArithmeticFormulaTokens
        (∀⁰ ((∼compactSuccIndStepZeroFormula body) ⋎
          compactSuccIndStepSuccessorFormula body)) := by
    rw [hquantifiedStepValue, hstepDisjunctionCanonical]
    rfl
  have hnegatedQuantifiedStepResult' : negatedQuantifiedStepTokens =
      (compactFormulaNegationExact 0 quantifiedStepTokens).getD [] := by
    simpa [compactFormulaNegationExact] using hnegatedQuantifiedStepResult
  have hnegatedQuantifiedStepCanonical : negatedQuantifiedStepTokens =
      compactArithmeticFormulaTokens
        (∼(∀⁰ ((∼compactSuccIndStepZeroFormula body) ⋎
          compactSuccIndStepSuccessorFormula body))) := by
    rw [hquantifiedStepCanonical,
      compactFormulaNegationExact_canonical]
      at hnegatedQuantifiedStepResult'
    simpa using hnegatedQuantifiedStepResult'
  rcases hquantifiedFinalRows.realize with
    ⟨quantifiedFinalTokens, hquantifiedFinalCount,
      hquantifiedFinalLayout, _hquantifiedFinalRows⟩
  have hquantifiedFinalCountValue : quantifiedFinalSlot.count =
      quantifiedFinalTokens.length := hquantifiedFinalCount.symm
  have hquantifiedFinalSlices' :
      CompactAdditiveUnaryFormulaConstructorSlices
        tokenTable width tokenCount 6
        stepZeroSlot.start stepZeroSlot.finish
          (compactArithmeticFormulaTokens
            (compactSuccIndStepZeroFormula body)).length
        quantifiedFinalSlot.start quantifiedFinalSlot.finish
          quantifiedFinalTokens.length := by
    simpa only [hstepZeroCountValue, hquantifiedFinalCountValue]
      using hquantifiedFinalSlices
  have hquantifiedFinalValue : quantifiedFinalTokens =
      tokenFormulaAll
        (compactArithmeticFormulaTokens
          (compactSuccIndStepZeroFormula body)) :=
    (compactAdditiveFormulaAllSlices_iff hstepZero
      hquantifiedFinalLayout).mp hquantifiedFinalSlices'
  have hquantifiedFinalCanonical : quantifiedFinalTokens =
      compactArithmeticFormulaTokens
        (∀⁰ compactSuccIndStepZeroFormula body) := by
    rw [hquantifiedFinalValue]
    rfl
  exact ⟨negatedQuantifiedStepTokens, quantifiedFinalTokens,
    hnegatedQuantifiedStepLayout, hquantifiedFinalLayout,
    hnegatedQuantifiedStepCanonical, hquantifiedFinalCanonical⟩

#print axioms CompactSuccIndStepAssemblyRoute.sound_canonical
#print axioms compactSuccIndStepAssemblyRouteDef_spec
#print axioms compactSuccIndStepAssemblyRouteDef_sigmaZero

end FoundationCompactNumericListedDirectSuccIndStepAssemblyRoute
