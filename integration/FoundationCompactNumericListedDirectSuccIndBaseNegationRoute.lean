import integration.FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
import integration.FoundationCompactNumericListedDirectLiteralNatListFormula

/-!
# Direct checked route for the negated successor-induction base case

The route fixes the literal zero witness, shares the generated base formula
between substitution and negation, and exposes both transforms as one bounded
arithmetic graph.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSuccIndBaseNegationRoute

open FoundationCompactSyntaxTokenMachine
open FoundationCompactSyntaxTransformationTrace
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpoint
open FoundationCompactNumericListedDirectLiteralNatListFormula
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute

structure CompactSuccIndBaseNegationRouteCoordinates where
  baseTrace : CompactFormulaTransformTraceSlot
  negationTrace : CompactFormulaTransformTraceSlot

def CompactSuccIndBaseNegationRoute
    (tokenTable width tokenCount : Nat)
    (body zeroWitness base negatedBase empty : CompactNatListRowSlot)
    (coordinates : CompactSuccIndBaseNegationRouteCoordinates) : Prop :=
  empty.count = 0 /\
    CompactAdditiveLiteralNatListRows tokenTable width tokenCount
      zeroWitness.start zeroWitness.count compactSuccIndZeroWitnessTokens /\
    CompactFormulaTransformTotalExactEndpoint
      tokenTable width tokenCount 2 1
      zeroWitness.start zeroWitness.finish zeroWitness.boundary
        zeroWitness.count zeroWitness.boundarySize
      body.start body.finish body.boundary body.count body.boundarySize
      base.start base.finish base.boundary base.count base.boundarySize
      empty.start empty.finish empty.boundary empty.boundarySize
      coordinates.baseTrace.stateBoundary coordinates.baseTrace.stateCount
      coordinates.baseTrace.tableWidth coordinates.baseTrace.valueBound /\
    CompactFormulaTransformTotalExactEndpoint
      tokenTable width tokenCount 3 0
      empty.start empty.finish empty.boundary empty.count empty.boundarySize
      base.start base.finish base.boundary base.count base.boundarySize
      negatedBase.start negatedBase.finish negatedBase.boundary
        negatedBase.count negatedBase.boundarySize
      empty.start empty.finish empty.boundary empty.boundarySize
      coordinates.negationTrace.stateBoundary
        coordinates.negationTrace.stateCount
      coordinates.negationTrace.tableWidth
        coordinates.negationTrace.valueBound

def compactSuccIndBaseNegationRouteDef : 𝚺₀.Semisentence 36 := .mkSigma
  “tokenTable width tokenCount
      bodyStart bodyFinish bodyBoundary bodyCount bodyBoundarySize
      zeroStart zeroFinish zeroBoundary zeroCount zeroBoundarySize
      baseStart baseFinish baseBoundary baseCount baseBoundarySize
      negatedStart negatedFinish negatedBoundary negatedCount negatedBoundarySize
      emptyStart emptyFinish emptyBoundary emptyCount emptyBoundarySize
      baseStateBoundary baseStateCount baseTableWidth baseValueBound
      negationStateBoundary negationStateCount negationTableWidth
        negationValueBound.
    emptyCount = 0 ∧
    !((compactAdditiveLiteralNatListRowsDef compactSuccIndZeroWitnessTokens))
      tokenTable width tokenCount zeroStart zeroCount ∧
    !(compactFormulaTransformTotalExactEndpointDef)
      tokenTable width tokenCount 2 1
      zeroStart zeroFinish zeroBoundary zeroCount zeroBoundarySize
      bodyStart bodyFinish bodyBoundary bodyCount bodyBoundarySize
      baseStart baseFinish baseBoundary baseCount baseBoundarySize
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      baseStateBoundary baseStateCount baseTableWidth baseValueBound ∧
    !(compactFormulaTransformTotalExactEndpointDef)
      tokenTable width tokenCount 3 0
      emptyStart emptyFinish emptyBoundary emptyCount emptyBoundarySize
      baseStart baseFinish baseBoundary baseCount baseBoundarySize
      negatedStart negatedFinish negatedBoundary negatedCount negatedBoundarySize
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      negationStateBoundary negationStateCount negationTableWidth
        negationValueBound”

def compactSuccIndBaseNegationRouteEnvironment
    (tokenTable width tokenCount : Nat)
    (body zeroWitness base negatedBase empty : CompactNatListRowSlot)
    (coordinates : CompactSuccIndBaseNegationRouteCoordinates) :
    Fin 36 -> Nat :=
  ![tokenTable, width, tokenCount,
    body.start, body.finish, body.boundary, body.count, body.boundarySize,
    zeroWitness.start, zeroWitness.finish, zeroWitness.boundary,
      zeroWitness.count, zeroWitness.boundarySize,
    base.start, base.finish, base.boundary, base.count, base.boundarySize,
    negatedBase.start, negatedBase.finish, negatedBase.boundary,
      negatedBase.count, negatedBase.boundarySize,
    empty.start, empty.finish, empty.boundary, empty.count, empty.boundarySize,
    coordinates.baseTrace.stateBoundary, coordinates.baseTrace.stateCount,
      coordinates.baseTrace.tableWidth, coordinates.baseTrace.valueBound,
    coordinates.negationTrace.stateBoundary,
      coordinates.negationTrace.stateCount,
      coordinates.negationTrace.tableWidth,
      coordinates.negationTrace.valueBound]

set_option maxHeartbeats 1400000 in
-- Two embedded total-transform endpoints require a local normalization budget.
set_option maxRecDepth 4096 in
@[simp] theorem compactSuccIndBaseNegationRouteDef_spec
    (tokenTable width tokenCount : Nat)
    (body zeroWitness base negatedBase empty : CompactNatListRowSlot)
    (coordinates : CompactSuccIndBaseNegationRouteCoordinates) :
    compactSuccIndBaseNegationRouteDef.val.Evalb
        (compactSuccIndBaseNegationRouteEnvironment
          tokenTable width tokenCount body zeroWitness base negatedBase empty
            coordinates) ↔
      CompactSuccIndBaseNegationRoute tokenTable width tokenCount
        body zeroWitness base negatedBase empty coordinates := by
  let env := compactSuccIndBaseNegationRouteEnvironment
    tokenTable width tokenCount body zeroWitness base negatedBase empty
      coordinates
  change compactSuccIndBaseNegationRouteDef.val.Evalb env ↔ _
  have hliteralEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 36), #1, #2, #8, #11]) =
        ![tokenTable, width, tokenCount,
          zeroWitness.start, zeroWitness.count] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hbaseEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 36), #1, #2, ‘2’, ‘1’,
          #8, #9, #10, #11, #12,
          #3, #4, #5, #6, #7,
          #13, #14, #15, #16, #17,
          #23, #24, #25, #27, #28, #29, #30, #31]) =
        ![tokenTable, width, tokenCount, 2, 1,
          zeroWitness.start, zeroWitness.finish, zeroWitness.boundary,
            zeroWitness.count, zeroWitness.boundarySize,
          body.start, body.finish, body.boundary, body.count,
            body.boundarySize,
          base.start, base.finish, base.boundary, base.count,
            base.boundarySize,
          empty.start, empty.finish, empty.boundary, empty.boundarySize,
          coordinates.baseTrace.stateBoundary,
            coordinates.baseTrace.stateCount,
            coordinates.baseTrace.tableWidth,
            coordinates.baseTrace.valueBound] := by
    funext coordinate
    fin_cases coordinate <;> simp [env,
      compactSuccIndBaseNegationRouteEnvironment]
  have hnegationEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 36), #1, #2, ‘3’, ‘0’,
          #23, #24, #25, #26, #27,
          #13, #14, #15, #16, #17,
          #18, #19, #20, #21, #22,
          #23, #24, #25, #27, #32, #33, #34, #35]) =
        ![tokenTable, width, tokenCount, 3, 0,
          empty.start, empty.finish, empty.boundary, empty.count,
            empty.boundarySize,
          base.start, base.finish, base.boundary, base.count,
            base.boundarySize,
          negatedBase.start, negatedBase.finish, negatedBase.boundary,
            negatedBase.count, negatedBase.boundarySize,
          empty.start, empty.finish, empty.boundary, empty.boundarySize,
          coordinates.negationTrace.stateBoundary,
            coordinates.negationTrace.stateCount,
            coordinates.negationTrace.tableWidth,
            coordinates.negationTrace.valueBound] := by
    funext coordinate
    fin_cases coordinate <;> simp [env,
      compactSuccIndBaseNegationRouteEnvironment]
  have hliteralSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 36), #1, #2, #8, #11])
          Empty.elim)
          (compactAdditiveLiteralNatListRowsDef
            (compactArithmeticTermTokens succIndZeroWitness)).val ↔
        CompactAdditiveLiteralNatListRows tokenTable width tokenCount
          zeroWitness.start zeroWitness.count
            (compactArithmeticTermTokens succIndZeroWitness) := by
    rw [hliteralEnv]
    exact compactAdditiveLiteralNatListRowsDef_spec
      (compactArithmeticTermTokens succIndZeroWitness)
        tokenTable width tokenCount
        zeroWitness.start zeroWitness.count
  have hbaseSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 36), #1, #2, ‘2’, ‘1’,
              #8, #9, #10, #11, #12,
              #3, #4, #5, #6, #7,
              #13, #14, #15, #16, #17,
              #23, #24, #25, #27, #28, #29, #30, #31])
          Empty.elim) compactFormulaTransformTotalExactEndpointDef.val ↔
        CompactFormulaTransformTotalExactEndpoint
          tokenTable width tokenCount 2 1
          zeroWitness.start zeroWitness.finish zeroWitness.boundary
            zeroWitness.count zeroWitness.boundarySize
          body.start body.finish body.boundary body.count body.boundarySize
          base.start base.finish base.boundary base.count base.boundarySize
          empty.start empty.finish empty.boundary empty.boundarySize
          coordinates.baseTrace.stateBoundary coordinates.baseTrace.stateCount
          coordinates.baseTrace.tableWidth coordinates.baseTrace.valueBound := by
    rw [hbaseEnv]
    exact compactFormulaTransformTotalExactEndpointDef_spec
      tokenTable width tokenCount 2 1
      zeroWitness.start zeroWitness.finish zeroWitness.boundary
        zeroWitness.count zeroWitness.boundarySize
      body.start body.finish body.boundary body.count body.boundarySize
      base.start base.finish base.boundary base.count base.boundarySize
      empty.start empty.finish empty.boundary empty.boundarySize
      coordinates.baseTrace.stateBoundary coordinates.baseTrace.stateCount
      coordinates.baseTrace.tableWidth coordinates.baseTrace.valueBound
  have hnegationSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 36), #1, #2, ‘3’, ‘0’,
              #23, #24, #25, #26, #27,
              #13, #14, #15, #16, #17,
              #18, #19, #20, #21, #22,
              #23, #24, #25, #27, #32, #33, #34, #35])
          Empty.elim) compactFormulaTransformTotalExactEndpointDef.val ↔
        CompactFormulaTransformTotalExactEndpoint
          tokenTable width tokenCount 3 0
          empty.start empty.finish empty.boundary empty.count empty.boundarySize
          base.start base.finish base.boundary base.count base.boundarySize
          negatedBase.start negatedBase.finish negatedBase.boundary
            negatedBase.count negatedBase.boundarySize
          empty.start empty.finish empty.boundary empty.boundarySize
          coordinates.negationTrace.stateBoundary
            coordinates.negationTrace.stateCount
          coordinates.negationTrace.tableWidth
            coordinates.negationTrace.valueBound := by
    rw [hnegationEnv]
    exact compactFormulaTransformTotalExactEndpointDef_spec
      tokenTable width tokenCount 3 0
      empty.start empty.finish empty.boundary empty.count empty.boundarySize
      base.start base.finish base.boundary base.count base.boundarySize
      negatedBase.start negatedBase.finish negatedBase.boundary
        negatedBase.count negatedBase.boundarySize
      empty.start empty.finish empty.boundary empty.boundarySize
      coordinates.negationTrace.stateBoundary coordinates.negationTrace.stateCount
      coordinates.negationTrace.tableWidth coordinates.negationTrace.valueBound
  have hemptyCountValue : env 26 = empty.count := by rfl
  simp [compactSuccIndBaseNegationRouteDef,
    CompactSuccIndBaseNegationRoute,
    hliteralSpec, hbaseSpec, hnegationSpec, hemptyCountValue]

theorem compactSuccIndBaseNegationRouteDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactSuccIndBaseNegationRouteDef.val := by
  simp [compactSuccIndBaseNegationRouteDef]

theorem CompactSuccIndBaseNegationRoute.sound_canonical
    {tokenTable width tokenCount : Nat}
    {bodySlot zeroWitnessSlot baseSlot negatedBaseSlot emptySlot :
      CompactNatListRowSlot}
    {coordinates : CompactSuccIndBaseNegationRouteCoordinates}
    {negatedBaseTokens : List Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hroute : CompactSuccIndBaseNegationRoute
      tokenTable width tokenCount bodySlot zeroWitnessSlot baseSlot
        negatedBaseSlot emptySlot coordinates)
    (hbody : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      bodySlot.start bodySlot.finish (compactArithmeticFormulaTokens body))
    (hnegatedBase : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount negatedBaseSlot.start
        negatedBaseSlot.finish negatedBaseTokens) :
    negatedBaseTokens = compactArithmeticFormulaTokens
      (∼compactSuccIndBaseFormula body) := by
  rcases hroute with
    ⟨_hemptyCount, hliteral, hbaseEndpoint, hnegationEndpoint⟩
  rcases hbaseEndpoint.sound with
    ⟨zeroTokens, bodyTokens, baseTokens,
      hzeroLayout, hbodyLayout, hbaseLayout, hbaseResult⟩
  have hbodyEq : compactArithmeticFormulaTokens body = bodyTokens :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hbodyLayout hbody).1
  subst bodyTokens
  rcases hbaseEndpoint.1.realize with
    ⟨zeroRows, hzeroRowsCount, hzeroRowsLayout, _hzeroRows⟩
  have hzeroRowsEq : zeroRows = zeroTokens :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hzeroLayout hzeroRowsLayout).1
  have hzeroCount : zeroWitnessSlot.count = zeroTokens.length := by
    rw [← hzeroRowsEq]
    exact hzeroRowsCount.symm
  have hzeroTokens : zeroTokens = compactSuccIndZeroWitnessTokens :=
    (compactAdditiveLiteralNatListRows_iff_eq
      hzeroLayout hzeroCount).mp hliteral
  have hbaseResult' : baseTokens =
      (compactFormulaSubstitutionExact 1
        (zeroTokens, compactArithmeticFormulaTokens body)).getD [] := by
    simpa [compactFormulaSubstitutionExact] using hbaseResult
  have hbaseCanonical : baseTokens = compactArithmeticFormulaTokens
      (compactSuccIndBaseFormula body) := by
    rw [hzeroTokens, compactSuccIndZeroWitnessTokens_canonical,
      compactFormulaSubstitutionExact_canonical] at hbaseResult'
    simpa [compactSuccIndBaseFormula] using hbaseResult'
  rcases hnegationEndpoint.sound with
    ⟨_negationControl, negationInput, negationOutput,
      _hnegationControlLayout, hnegationInputLayout,
      hnegationOutputLayout, hnegationResult⟩
  have hbaseShared : baseTokens = negationInput :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hnegationInputLayout hbaseLayout).1
  have hresultShared : negatedBaseTokens = negationOutput :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hnegationOutputLayout hnegatedBase).1
  subst negationInput
  subst negationOutput
  have hnegationResult' : negatedBaseTokens =
      (compactFormulaNegationExact 0 baseTokens).getD [] := by
    simpa [compactFormulaNegationExact] using hnegationResult
  rw [hbaseCanonical, compactFormulaNegationExact_canonical]
    at hnegationResult'
  simpa using hnegationResult'

#print axioms compactSuccIndBaseNegationRouteDef_spec
#print axioms compactSuccIndBaseNegationRouteDef_sigmaZero
#print axioms CompactSuccIndBaseNegationRoute.sound_canonical

end FoundationCompactNumericListedDirectSuccIndBaseNegationRoute
