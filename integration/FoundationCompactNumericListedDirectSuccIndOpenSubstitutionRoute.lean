import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpoint

/-!
# Direct checked route for open successor-induction substitution

The route shares concrete list slots across shift, substitution, and fixitr.
For canonical formulas and terms, its final slot is exactly the public
`compactSuccIndOpenSubstitutionTokens` result.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute

open FoundationCompactSyntaxTokenMachine
open FoundationCompactSyntaxTransformationTrace
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpoint

structure CompactNatListRowSlot where
  start : Nat
  finish : Nat
  boundary : Nat
  count : Nat
  boundarySize : Nat

structure CompactFormulaTransformTraceSlot where
  stateBoundary : Nat
  stateCount : Nat
  tableWidth : Nat
  valueBound : Nat

structure CompactSuccIndOpenSubstitutionRouteCoordinates where
  shifted : CompactNatListRowSlot
  substituted : CompactNatListRowSlot
  shiftTrace : CompactFormulaTransformTraceSlot
  substitutionTrace : CompactFormulaTransformTraceSlot
  fixitrTrace : CompactFormulaTransformTraceSlot

def CompactSuccIndOpenSubstitutionRoute
    (tokenTable width tokenCount : Nat)
    (body witness capture result empty : CompactNatListRowSlot)
    (coordinates : CompactSuccIndOpenSubstitutionRouteCoordinates) : Prop :=
  empty.count = 0 /\
    capture.count = 1 /\
    CompactFormulaTransformTotalExactEndpoint
      tokenTable width tokenCount 1 1
      empty.start empty.finish empty.boundary empty.count empty.boundarySize
      body.start body.finish body.boundary body.count body.boundarySize
      coordinates.shifted.start coordinates.shifted.finish
        coordinates.shifted.boundary coordinates.shifted.count
        coordinates.shifted.boundarySize
      empty.start empty.finish empty.boundary empty.boundarySize
      coordinates.shiftTrace.stateBoundary coordinates.shiftTrace.stateCount
      coordinates.shiftTrace.tableWidth coordinates.shiftTrace.valueBound /\
    CompactFormulaTransformTotalExactEndpoint
      tokenTable width tokenCount 2 1
      witness.start witness.finish witness.boundary
        witness.count witness.boundarySize
      coordinates.shifted.start coordinates.shifted.finish
        coordinates.shifted.boundary coordinates.shifted.count
        coordinates.shifted.boundarySize
      coordinates.substituted.start coordinates.substituted.finish
        coordinates.substituted.boundary coordinates.substituted.count
        coordinates.substituted.boundarySize
      empty.start empty.finish empty.boundary empty.boundarySize
      coordinates.substitutionTrace.stateBoundary
        coordinates.substitutionTrace.stateCount
      coordinates.substitutionTrace.tableWidth
        coordinates.substitutionTrace.valueBound /\
    CompactFormulaTransformTotalExactEndpoint
      tokenTable width tokenCount 5 0
      capture.start capture.finish capture.boundary
        capture.count capture.boundarySize
      coordinates.substituted.start coordinates.substituted.finish
        coordinates.substituted.boundary coordinates.substituted.count
        coordinates.substituted.boundarySize
      result.start result.finish result.boundary result.count result.boundarySize
      empty.start empty.finish empty.boundary empty.boundarySize
      coordinates.fixitrTrace.stateBoundary coordinates.fixitrTrace.stateCount
      coordinates.fixitrTrace.tableWidth coordinates.fixitrTrace.valueBound

def compactSuccIndOpenSubstitutionRouteDef :
    𝚺₀.Semisentence 50 := .mkSigma
  “tokenTable width tokenCount
      bodyStart bodyFinish bodyBoundary bodyCount bodyBoundarySize
      witnessStart witnessFinish witnessBoundary witnessCount witnessBoundarySize
      captureStart captureFinish captureBoundary captureCount captureBoundarySize
      resultStart resultFinish resultBoundary resultCount resultBoundarySize
      emptyStart emptyFinish emptyBoundary emptyCount emptyBoundarySize
      shiftedStart shiftedFinish shiftedBoundary shiftedCount shiftedBoundarySize
      substitutedStart substitutedFinish substitutedBoundary substitutedCount
        substitutedBoundarySize
      shiftStateBoundary shiftStateCount shiftTableWidth shiftValueBound
      substitutionStateBoundary substitutionStateCount substitutionTableWidth
        substitutionValueBound
      fixitrStateBoundary fixitrStateCount fixitrTableWidth fixitrValueBound.
    emptyCount = 0 ∧
    captureCount = 1 ∧
    !(compactFormulaTransformTotalExactEndpointDef)
      tokenTable width tokenCount 1 1
      emptyStart emptyFinish emptyBoundary emptyCount emptyBoundarySize
      bodyStart bodyFinish bodyBoundary bodyCount bodyBoundarySize
      shiftedStart shiftedFinish shiftedBoundary shiftedCount shiftedBoundarySize
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftStateBoundary shiftStateCount shiftTableWidth shiftValueBound ∧
    !(compactFormulaTransformTotalExactEndpointDef)
      tokenTable width tokenCount 2 1
      witnessStart witnessFinish witnessBoundary witnessCount witnessBoundarySize
      shiftedStart shiftedFinish shiftedBoundary shiftedCount shiftedBoundarySize
      substitutedStart substitutedFinish substitutedBoundary substitutedCount
        substitutedBoundarySize
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      substitutionStateBoundary substitutionStateCount substitutionTableWidth
        substitutionValueBound ∧
    !(compactFormulaTransformTotalExactEndpointDef)
      tokenTable width tokenCount 5 0
      captureStart captureFinish captureBoundary captureCount captureBoundarySize
      substitutedStart substitutedFinish substitutedBoundary substitutedCount
        substitutedBoundarySize
      resultStart resultFinish resultBoundary resultCount resultBoundarySize
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      fixitrStateBoundary fixitrStateCount fixitrTableWidth fixitrValueBound”

def compactSuccIndOpenSubstitutionRouteEnvironment
    (tokenTable width tokenCount : Nat)
    (body witness capture result empty : CompactNatListRowSlot)
    (coordinates : CompactSuccIndOpenSubstitutionRouteCoordinates) :
    Fin 50 -> Nat :=
  ![tokenTable, width, tokenCount,
    body.start, body.finish, body.boundary, body.count, body.boundarySize,
    witness.start, witness.finish, witness.boundary, witness.count,
      witness.boundarySize,
    capture.start, capture.finish, capture.boundary, capture.count,
      capture.boundarySize,
    result.start, result.finish, result.boundary, result.count,
      result.boundarySize,
    empty.start, empty.finish, empty.boundary, empty.count, empty.boundarySize,
    coordinates.shifted.start, coordinates.shifted.finish,
      coordinates.shifted.boundary, coordinates.shifted.count,
      coordinates.shifted.boundarySize,
    coordinates.substituted.start, coordinates.substituted.finish,
      coordinates.substituted.boundary, coordinates.substituted.count,
      coordinates.substituted.boundarySize,
    coordinates.shiftTrace.stateBoundary, coordinates.shiftTrace.stateCount,
      coordinates.shiftTrace.tableWidth, coordinates.shiftTrace.valueBound,
    coordinates.substitutionTrace.stateBoundary,
      coordinates.substitutionTrace.stateCount,
      coordinates.substitutionTrace.tableWidth,
      coordinates.substitutionTrace.valueBound,
    coordinates.fixitrTrace.stateBoundary, coordinates.fixitrTrace.stateCount,
      coordinates.fixitrTrace.tableWidth, coordinates.fixitrTrace.valueBound]

set_option maxHeartbeats 1800000 in
-- Three embedded total-transform endpoints require a local normalization budget.
set_option maxRecDepth 4096 in
@[simp] theorem compactSuccIndOpenSubstitutionRouteDef_spec
    (tokenTable width tokenCount : Nat)
    (body witness capture result empty : CompactNatListRowSlot)
    (coordinates : CompactSuccIndOpenSubstitutionRouteCoordinates) :
    compactSuccIndOpenSubstitutionRouteDef.val.Evalb
        (compactSuccIndOpenSubstitutionRouteEnvironment
          tokenTable width tokenCount body witness capture result empty
            coordinates) ↔
      CompactSuccIndOpenSubstitutionRoute
        tokenTable width tokenCount body witness capture result empty
          coordinates := by
  let env := compactSuccIndOpenSubstitutionRouteEnvironment
    tokenTable width tokenCount body witness capture result empty coordinates
  change compactSuccIndOpenSubstitutionRouteDef.val.Evalb env ↔ _
  have hshiftEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 50), #1, #2, ‘1’, ‘1’,
          #23, #24, #25, #26, #27,
          #3, #4, #5, #6, #7,
          #28, #29, #30, #31, #32,
          #23, #24, #25, #27, #38, #39, #40, #41]) =
        ![tokenTable, width, tokenCount, 1, 1,
          empty.start, empty.finish, empty.boundary, empty.count,
            empty.boundarySize,
          body.start, body.finish, body.boundary, body.count,
            body.boundarySize,
          coordinates.shifted.start, coordinates.shifted.finish,
            coordinates.shifted.boundary, coordinates.shifted.count,
            coordinates.shifted.boundarySize,
          empty.start, empty.finish, empty.boundary, empty.boundarySize,
          coordinates.shiftTrace.stateBoundary,
            coordinates.shiftTrace.stateCount,
            coordinates.shiftTrace.tableWidth,
            coordinates.shiftTrace.valueBound] := by
    funext coordinate
    fin_cases coordinate <;> simp [env,
      compactSuccIndOpenSubstitutionRouteEnvironment]
  have hsubstitutionEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 50), #1, #2, ‘2’, ‘1’,
          #8, #9, #10, #11, #12,
          #28, #29, #30, #31, #32,
          #33, #34, #35, #36, #37,
          #23, #24, #25, #27, #42, #43, #44, #45]) =
        ![tokenTable, width, tokenCount, 2, 1,
          witness.start, witness.finish, witness.boundary, witness.count,
            witness.boundarySize,
          coordinates.shifted.start, coordinates.shifted.finish,
            coordinates.shifted.boundary, coordinates.shifted.count,
            coordinates.shifted.boundarySize,
          coordinates.substituted.start, coordinates.substituted.finish,
            coordinates.substituted.boundary, coordinates.substituted.count,
            coordinates.substituted.boundarySize,
          empty.start, empty.finish, empty.boundary, empty.boundarySize,
          coordinates.substitutionTrace.stateBoundary,
            coordinates.substitutionTrace.stateCount,
            coordinates.substitutionTrace.tableWidth,
            coordinates.substitutionTrace.valueBound] := by
    funext coordinate
    fin_cases coordinate <;> simp [env,
      compactSuccIndOpenSubstitutionRouteEnvironment]
  have hfixitrEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 50), #1, #2, ‘5’, ‘0’,
          #13, #14, #15, #16, #17,
          #33, #34, #35, #36, #37,
          #18, #19, #20, #21, #22,
          #23, #24, #25, #27, #46, #47, #48, #49]) =
        ![tokenTable, width, tokenCount, 5, 0,
          capture.start, capture.finish, capture.boundary, capture.count,
            capture.boundarySize,
          coordinates.substituted.start, coordinates.substituted.finish,
            coordinates.substituted.boundary, coordinates.substituted.count,
            coordinates.substituted.boundarySize,
          result.start, result.finish, result.boundary, result.count,
            result.boundarySize,
          empty.start, empty.finish, empty.boundary, empty.boundarySize,
          coordinates.fixitrTrace.stateBoundary,
            coordinates.fixitrTrace.stateCount,
            coordinates.fixitrTrace.tableWidth,
            coordinates.fixitrTrace.valueBound] := by
    funext coordinate
    fin_cases coordinate <;> simp [env,
      compactSuccIndOpenSubstitutionRouteEnvironment]
  have hshiftSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 50), #1, #2, ‘1’, ‘1’,
              #23, #24, #25, #26, #27,
              #3, #4, #5, #6, #7,
              #28, #29, #30, #31, #32,
              #23, #24, #25, #27, #38, #39, #40, #41])
          Empty.elim) compactFormulaTransformTotalExactEndpointDef.val ↔
        CompactFormulaTransformTotalExactEndpoint
          tokenTable width tokenCount 1 1
          empty.start empty.finish empty.boundary empty.count empty.boundarySize
          body.start body.finish body.boundary body.count body.boundarySize
          coordinates.shifted.start coordinates.shifted.finish
            coordinates.shifted.boundary coordinates.shifted.count
            coordinates.shifted.boundarySize
          empty.start empty.finish empty.boundary empty.boundarySize
          coordinates.shiftTrace.stateBoundary coordinates.shiftTrace.stateCount
          coordinates.shiftTrace.tableWidth coordinates.shiftTrace.valueBound := by
    rw [hshiftEnv]
    exact compactFormulaTransformTotalExactEndpointDef_spec
      tokenTable width tokenCount 1 1
      empty.start empty.finish empty.boundary empty.count empty.boundarySize
      body.start body.finish body.boundary body.count body.boundarySize
      coordinates.shifted.start coordinates.shifted.finish
        coordinates.shifted.boundary coordinates.shifted.count
        coordinates.shifted.boundarySize
      empty.start empty.finish empty.boundary empty.boundarySize
      coordinates.shiftTrace.stateBoundary coordinates.shiftTrace.stateCount
      coordinates.shiftTrace.tableWidth coordinates.shiftTrace.valueBound
  have hsubstitutionSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 50), #1, #2, ‘2’, ‘1’,
              #8, #9, #10, #11, #12,
              #28, #29, #30, #31, #32,
              #33, #34, #35, #36, #37,
              #23, #24, #25, #27, #42, #43, #44, #45])
          Empty.elim) compactFormulaTransformTotalExactEndpointDef.val ↔
        CompactFormulaTransformTotalExactEndpoint
          tokenTable width tokenCount 2 1
          witness.start witness.finish witness.boundary witness.count
            witness.boundarySize
          coordinates.shifted.start coordinates.shifted.finish
            coordinates.shifted.boundary coordinates.shifted.count
            coordinates.shifted.boundarySize
          coordinates.substituted.start coordinates.substituted.finish
            coordinates.substituted.boundary coordinates.substituted.count
            coordinates.substituted.boundarySize
          empty.start empty.finish empty.boundary empty.boundarySize
          coordinates.substitutionTrace.stateBoundary
            coordinates.substitutionTrace.stateCount
          coordinates.substitutionTrace.tableWidth
            coordinates.substitutionTrace.valueBound := by
    rw [hsubstitutionEnv]
    exact compactFormulaTransformTotalExactEndpointDef_spec
      tokenTable width tokenCount 2 1
      witness.start witness.finish witness.boundary witness.count
        witness.boundarySize
      coordinates.shifted.start coordinates.shifted.finish
        coordinates.shifted.boundary coordinates.shifted.count
        coordinates.shifted.boundarySize
      coordinates.substituted.start coordinates.substituted.finish
        coordinates.substituted.boundary coordinates.substituted.count
        coordinates.substituted.boundarySize
      empty.start empty.finish empty.boundary empty.boundarySize
      coordinates.substitutionTrace.stateBoundary
        coordinates.substitutionTrace.stateCount
      coordinates.substitutionTrace.tableWidth
        coordinates.substitutionTrace.valueBound
  have hfixitrSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 50), #1, #2, ‘5’, ‘0’,
              #13, #14, #15, #16, #17,
              #33, #34, #35, #36, #37,
              #18, #19, #20, #21, #22,
              #23, #24, #25, #27, #46, #47, #48, #49])
          Empty.elim) compactFormulaTransformTotalExactEndpointDef.val ↔
        CompactFormulaTransformTotalExactEndpoint
          tokenTable width tokenCount 5 0
          capture.start capture.finish capture.boundary capture.count
            capture.boundarySize
          coordinates.substituted.start coordinates.substituted.finish
            coordinates.substituted.boundary coordinates.substituted.count
            coordinates.substituted.boundarySize
          result.start result.finish result.boundary result.count
            result.boundarySize
          empty.start empty.finish empty.boundary empty.boundarySize
          coordinates.fixitrTrace.stateBoundary coordinates.fixitrTrace.stateCount
          coordinates.fixitrTrace.tableWidth coordinates.fixitrTrace.valueBound := by
    rw [hfixitrEnv]
    exact compactFormulaTransformTotalExactEndpointDef_spec
      tokenTable width tokenCount 5 0
      capture.start capture.finish capture.boundary capture.count
        capture.boundarySize
      coordinates.substituted.start coordinates.substituted.finish
        coordinates.substituted.boundary coordinates.substituted.count
        coordinates.substituted.boundarySize
      result.start result.finish result.boundary result.count
        result.boundarySize
      empty.start empty.finish empty.boundary empty.boundarySize
      coordinates.fixitrTrace.stateBoundary coordinates.fixitrTrace.stateCount
      coordinates.fixitrTrace.tableWidth coordinates.fixitrTrace.valueBound
  have hemptyCountValue : env 26 = empty.count := by
    rfl
  have hcaptureCountValue : env 16 = capture.count := by
    rfl
  simp [compactSuccIndOpenSubstitutionRouteDef,
    CompactSuccIndOpenSubstitutionRoute,
    hshiftSpec, hsubstitutionSpec, hfixitrSpec,
    hemptyCountValue, hcaptureCountValue]

theorem compactSuccIndOpenSubstitutionRouteDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactSuccIndOpenSubstitutionRouteDef.val := by
  simp [compactSuccIndOpenSubstitutionRouteDef]

theorem CompactSuccIndOpenSubstitutionRoute.sound_canonical
    {tokenTable width tokenCount : Nat}
    {bodySlot witnessSlot captureSlot resultSlot emptySlot :
      CompactNatListRowSlot}
    {coordinates : CompactSuccIndOpenSubstitutionRouteCoordinates}
    {resultTokens : List Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticTerm Nat)
    (hroute : CompactSuccIndOpenSubstitutionRoute
      tokenTable width tokenCount bodySlot witnessSlot captureSlot
        resultSlot emptySlot coordinates)
    (hbody : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      bodySlot.start bodySlot.finish (compactArithmeticFormulaTokens body))
    (hwitness : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      witnessSlot.start witnessSlot.finish
        (compactArithmeticTermTokens witness))
    (hresult : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      resultSlot.start resultSlot.finish resultTokens) :
    resultTokens = compactArithmeticFormulaTokens
      (Rewriting.app (Rew.subst ![
        (Rew.fixitr (L := ℒₒᵣ) 0 1) witness]) body) := by
  rcases hroute with
    ⟨_hemptyCount, hcaptureCount,
      hshiftEndpoint, hsubstitutionEndpoint, hfixitrEndpoint⟩
  rcases hshiftEndpoint.sound with
    ⟨_shiftControl, shiftInput, shifted,
      _hshiftControlLayout, hshiftInputLayout, hshiftedLayout,
      hshiftResult⟩
  have hshiftInputEq :
      compactArithmeticFormulaTokens body = shiftInput :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hshiftInputLayout hbody).1
  subst shiftInput
  have hshiftResult' : shifted =
      (compactFormulaShiftExact 1
        (compactArithmeticFormulaTokens body)).getD [] := by
    simpa [compactFormulaShiftExact] using hshiftResult
  have hshifted : shifted = compactArithmeticFormulaTokens
      (Rewriting.shift body) := by
    rw [compactFormulaShiftExact_canonical] at hshiftResult'
    simpa using hshiftResult'
  have hshiftOption : compactFormulaShiftExact 1
      (compactArithmeticFormulaTokens body) = some shifted := by
    simpa [hshifted] using compactFormulaShiftExact_canonical body
  rcases hsubstitutionEndpoint.sound with
    ⟨substitutionWitness, substitutionInput, substituted,
      hsubstitutionWitnessLayout, hsubstitutionInputLayout,
      hsubstitutedLayout, hsubstitutionResult⟩
  have hwitnessEq : compactArithmeticTermTokens witness =
      substitutionWitness :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hsubstitutionWitnessLayout hwitness).1
  have hshiftInputShared : shifted = substitutionInput :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hsubstitutionInputLayout hshiftedLayout).1
  subst substitutionWitness
  subst substitutionInput
  have hsubstitutionResult' : substituted =
      (compactFormulaSubstitutionExact 1
        (compactArithmeticTermTokens witness, shifted)).getD [] := by
    simpa [compactFormulaSubstitutionExact] using hsubstitutionResult
  have hsubstituted : substituted = compactArithmeticFormulaTokens
      (Rewriting.app (Rew.subst ![witness]) (Rewriting.shift body)) := by
    rw [hshifted, compactFormulaSubstitutionExact_canonical]
      at hsubstitutionResult'
    simpa using hsubstitutionResult'
  have hsubstitutionOption : compactFormulaSubstitutionExact 1
      (compactArithmeticTermTokens witness, shifted) = some substituted := by
    rw [hshifted]
    simpa [hsubstituted] using
      compactFormulaSubstitutionExact_canonical witness
        (Rewriting.shift body)
  rcases hfixitrEndpoint.sound with
    ⟨fixitrControl, fixitrInput, fixed,
      hfixitrControlLayout, hfixitrInputLayout, hfixedLayout, hfixitrResult⟩
  have hsubstitutionInputShared : substituted = fixitrInput :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hfixitrInputLayout hsubstitutedLayout).1
  have hresultShared : resultTokens = fixed :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hfixedLayout hresult).1
  subst fixitrInput
  subst fixed
  rcases hfixitrEndpoint.1.realize with
    ⟨captureValues, hcaptureValuesCount,
      hcaptureValuesLayout, _hcaptureValuesRows⟩
  have hcaptureEq : fixitrControl = captureValues :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hcaptureValuesLayout hfixitrControlLayout).1
  have hfixitrControlCount : fixitrControl.length = 1 := by
    rw [hcaptureEq, hcaptureValuesCount, hcaptureCount]
  have hfixitrResult' : resultTokens =
      (compactFormulaFixitrExact 0
        (fixitrControl.length, substituted)).getD [] := by
    simpa [compactFormulaFixitrExact] using hfixitrResult
  have hfixitrOption : compactFormulaFixitrExact 0
      (1, substituted) = some resultTokens := by
    rw [hsubstituted]
    have hcanonical := compactFormulaFixitrExact_canonical 0 1
      (Rewriting.app (Rew.subst ![witness]) (Rewriting.shift body))
    have hresultValue : resultTokens = compactArithmeticFormulaTokens
        (Rewriting.app (Rew.fixitr (L := ℒₒᵣ) 0 1)
          (Rewriting.app (Rew.subst ![witness])
            (Rewriting.shift body))) := by
      rw [hfixitrControlCount, hsubstituted, hcanonical] at hfixitrResult'
      simpa using hfixitrResult'
    simpa [hresultValue] using hcanonical
  have hopen : compactSuccIndOpenSubstitutionTokens
      (compactArithmeticFormulaTokens body,
        compactArithmeticTermTokens witness) = some resultTokens := by
    simp [compactSuccIndOpenSubstitutionTokens,
      hshiftOption, hsubstitutionOption, hfixitrOption]
  have hcanonical :=
    compactSuccIndOpenSubstitutionTokens_canonical body witness
  rw [hopen] at hcanonical
  exact Option.some.inj hcanonical

theorem CompactSuccIndOpenSubstitutionRoute.sound_openZero
    {tokenTable width tokenCount : Nat}
    {bodySlot witnessSlot captureSlot resultSlot emptySlot :
      CompactNatListRowSlot}
    {coordinates : CompactSuccIndOpenSubstitutionRouteCoordinates}
    {resultTokens : List Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hroute : CompactSuccIndOpenSubstitutionRoute
      tokenTable width tokenCount bodySlot witnessSlot captureSlot
        resultSlot emptySlot coordinates)
    (hbody : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      bodySlot.start bodySlot.finish (compactArithmeticFormulaTokens body))
    (hwitness : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      witnessSlot.start witnessSlot.finish
        compactSuccIndOpenZeroWitnessTokens)
    (hresult : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      resultSlot.start resultSlot.finish resultTokens) :
    resultTokens = compactArithmeticFormulaTokens
      (compactSuccIndStepZeroFormula body) := by
  have hgeneric := CompactSuccIndOpenSubstitutionRoute.sound_canonical
    body succIndOpenZeroWitness hroute hbody
      (by simpa using hwitness) hresult
  have hbridge := compactSuccIndOpenZeroTokens_canonical body
  unfold compactSuccIndOpenZeroTokens at hbridge
  rw [compactSuccIndOpenZeroWitnessTokens_canonical,
    compactSuccIndOpenSubstitutionTokens_canonical] at hbridge
  exact hgeneric.trans (Option.some.inj hbridge)

theorem CompactSuccIndOpenSubstitutionRoute.sound_openSuccessor
    {tokenTable width tokenCount : Nat}
    {bodySlot witnessSlot captureSlot resultSlot emptySlot :
      CompactNatListRowSlot}
    {coordinates : CompactSuccIndOpenSubstitutionRouteCoordinates}
    {resultTokens : List Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hroute : CompactSuccIndOpenSubstitutionRoute
      tokenTable width tokenCount bodySlot witnessSlot captureSlot
        resultSlot emptySlot coordinates)
    (hbody : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      bodySlot.start bodySlot.finish (compactArithmeticFormulaTokens body))
    (hwitness : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      witnessSlot.start witnessSlot.finish
        compactSuccIndOpenSuccessorWitnessTokens)
    (hresult : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      resultSlot.start resultSlot.finish resultTokens) :
    resultTokens = compactArithmeticFormulaTokens
      (compactSuccIndStepSuccessorFormula body) := by
  have hgeneric := CompactSuccIndOpenSubstitutionRoute.sound_canonical
    body succIndOpenSuccessorWitness hroute hbody
      (by simpa using hwitness) hresult
  have hbridge := compactSuccIndOpenSuccessorTokens_canonical body
  unfold compactSuccIndOpenSuccessorTokens at hbridge
  rw [compactSuccIndOpenSuccessorWitnessTokens_canonical,
    compactSuccIndOpenSubstitutionTokens_canonical] at hbridge
  exact hgeneric.trans (Option.some.inj hbridge)

#print axioms CompactSuccIndOpenSubstitutionRoute.sound_canonical
#print axioms CompactSuccIndOpenSubstitutionRoute.sound_openZero
#print axioms CompactSuccIndOpenSubstitutionRoute.sound_openSuccessor
#print axioms compactSuccIndOpenSubstitutionRouteDef_spec
#print axioms compactSuccIndOpenSubstitutionRouteDef_sigmaZero

end FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
