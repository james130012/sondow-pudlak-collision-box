import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpoint
import integration.FoundationCompactNumericListedDirectAllClosureSlices
import integration.FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute

/-!
# Self-contained direct endpoint for fixed iterated universal closure

The endpoint runs mode-five fixitr with a control list whose checked length is
the requested depth, then prefixes exactly that many universal quantifiers.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFixedAllClosureTotalEndpoint

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericAllClosure
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpoint
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectAllClosureSlices
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute

structure CompactFixedAllClosureTotalEndpointCoordinates where
  trace : CompactFormulaTransformTraceSlot

def CompactFixedAllClosureTotalEndpoint
    (tokenTable width tokenCount depth : Nat)
    (empty capture input fixed closure : CompactNatListRowSlot)
    (coordinates : CompactFixedAllClosureTotalEndpointCoordinates) : Prop :=
  empty.count = 0 /\
    capture.count = depth /\
    CompactFormulaTransformTotalExactEndpoint
      tokenTable width tokenCount 5 0
      capture.start capture.finish capture.boundary capture.count
        capture.boundarySize
      input.start input.finish input.boundary input.count input.boundarySize
      fixed.start fixed.finish fixed.boundary fixed.count fixed.boundarySize
      empty.start empty.finish empty.boundary empty.boundarySize
      coordinates.trace.stateBoundary coordinates.trace.stateCount
      coordinates.trace.tableWidth coordinates.trace.valueBound /\
    CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      closure.start closure.count closure.finish closure.boundary
      closure.boundarySize /\
    CompactAdditiveAllClosureSlices tokenTable width tokenCount depth
      fixed.start fixed.finish fixed.count
      closure.start closure.finish closure.count

def compactFixedAllClosureTotalEndpointDef : 𝚺₀.Semisentence 33 := .mkSigma
  “tokenTable width tokenCount depth
      emptyStart emptyFinish emptyBoundary emptyCount emptyBoundarySize
      captureStart captureFinish captureBoundary captureCount
        captureBoundarySize
      inputStart inputFinish inputBoundary inputCount inputBoundarySize
      fixedStart fixedFinish fixedBoundary fixedCount fixedBoundarySize
      closureStart closureFinish closureBoundary closureCount
        closureBoundarySize
      stateBoundary stateCount tableWidth valueBound.
    emptyCount = 0 ∧
    captureCount = depth ∧
    !(compactFormulaTransformTotalExactEndpointDef)
      tokenTable width tokenCount 5 0
      captureStart captureFinish captureBoundary captureCount
        captureBoundarySize
      inputStart inputFinish inputBoundary inputCount inputBoundarySize
      fixedStart fixedFinish fixedBoundary fixedCount fixedBoundarySize
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      stateBoundary stateCount tableWidth valueBound ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount closureStart closureCount closureFinish
        closureBoundary closureBoundarySize ∧
    !(compactAdditiveAllClosureSlicesDef)
      tokenTable width tokenCount depth
      fixedStart fixedFinish fixedCount
      closureStart closureFinish closureCount”

def compactFixedAllClosureTotalEndpointEnvironment
    (tokenTable width tokenCount depth : Nat)
    (empty capture input fixed closure : CompactNatListRowSlot)
    (coordinates : CompactFixedAllClosureTotalEndpointCoordinates) :
    Fin 33 -> Nat :=
  ![tokenTable, width, tokenCount, depth,
    empty.start, empty.finish, empty.boundary, empty.count,
      empty.boundarySize,
    capture.start, capture.finish, capture.boundary, capture.count,
      capture.boundarySize,
    input.start, input.finish, input.boundary, input.count,
      input.boundarySize,
    fixed.start, fixed.finish, fixed.boundary, fixed.count,
      fixed.boundarySize,
    closure.start, closure.finish, closure.boundary, closure.count,
      closure.boundarySize,
    coordinates.trace.stateBoundary, coordinates.trace.stateCount,
      coordinates.trace.tableWidth, coordinates.trace.valueBound]

set_option maxHeartbeats 1200000 in
-- The embedded total transform and closure slices need local normalization.
set_option maxRecDepth 4096 in
@[simp] theorem compactFixedAllClosureTotalEndpointDef_spec
    (tokenTable width tokenCount depth : Nat)
    (empty capture input fixed closure : CompactNatListRowSlot)
    (coordinates : CompactFixedAllClosureTotalEndpointCoordinates) :
    compactFixedAllClosureTotalEndpointDef.val.Evalb
        (compactFixedAllClosureTotalEndpointEnvironment
          tokenTable width tokenCount depth empty capture input fixed closure
          coordinates) ↔
      CompactFixedAllClosureTotalEndpoint tokenTable width tokenCount depth
        empty capture input fixed closure coordinates := by
  let env := compactFixedAllClosureTotalEndpointEnvironment
    tokenTable width tokenCount depth empty capture input fixed closure
      coordinates
  change compactFixedAllClosureTotalEndpointDef.val.Evalb env ↔ _
  have htransformEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2, ‘5’, ‘0’,
          #9, #10, #11, #12, #13,
          #14, #15, #16, #17, #18,
          #19, #20, #21, #22, #23,
          #4, #5, #6, #8, #29, #30, #31, #32]) =
        ![tokenTable, width, tokenCount, 5, 0,
          capture.start, capture.finish, capture.boundary, capture.count,
            capture.boundarySize,
          input.start, input.finish, input.boundary, input.count,
            input.boundarySize,
          fixed.start, fixed.finish, fixed.boundary, fixed.count,
            fixed.boundarySize,
          empty.start, empty.finish, empty.boundary, empty.boundarySize,
          coordinates.trace.stateBoundary, coordinates.trace.stateCount,
            coordinates.trace.tableWidth, coordinates.trace.valueBound] := by
    funext coordinate
    fin_cases coordinate <;> simp [env,
      compactFixedAllClosureTotalEndpointEnvironment]
  have hclosureRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
          #24, #27, #25, #26, #28]) =
        ![tokenTable, width, tokenCount,
          closure.start, closure.count, closure.finish,
          closure.boundary, closure.boundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hclosureSlicesEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2, #3,
          #19, #20, #22, #24, #25, #27]) =
        ![tokenTable, width, tokenCount, depth,
          fixed.start, fixed.finish, fixed.count,
          closure.start, closure.finish, closure.count] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htransformSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2, ‘5’, ‘0’,
              #9, #10, #11, #12, #13,
              #14, #15, #16, #17, #18,
              #19, #20, #21, #22, #23,
              #4, #5, #6, #8, #29, #30, #31, #32])
          Empty.elim) compactFormulaTransformTotalExactEndpointDef.val ↔
        CompactFormulaTransformTotalExactEndpoint
          tokenTable width tokenCount 5 0
          capture.start capture.finish capture.boundary capture.count
            capture.boundarySize
          input.start input.finish input.boundary input.count
            input.boundarySize
          fixed.start fixed.finish fixed.boundary fixed.count
            fixed.boundarySize
          empty.start empty.finish empty.boundary empty.boundarySize
          coordinates.trace.stateBoundary coordinates.trace.stateCount
          coordinates.trace.tableWidth coordinates.trace.valueBound := by
    rw [htransformEnv]
    exact compactFormulaTransformTotalExactEndpointDef_spec
      tokenTable width tokenCount 5 0
      capture.start capture.finish capture.boundary capture.count
        capture.boundarySize
      input.start input.finish input.boundary input.count input.boundarySize
      fixed.start fixed.finish fixed.boundary fixed.count fixed.boundarySize
      empty.start empty.finish empty.boundary empty.boundarySize
      coordinates.trace.stateBoundary coordinates.trace.stateCount
      coordinates.trace.tableWidth coordinates.trace.valueBound
  have hclosureRowsSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
              #24, #27, #25, #26, #28])
          Empty.elim) compactAdditiveNatListWitnessRowsDef.val ↔
        CompactAdditiveNatListWitnessRows tokenTable width tokenCount
          closure.start closure.count closure.finish closure.boundary
          closure.boundarySize := by
    rw [hclosureRowsEnv]
    exact compactAdditiveNatListWitnessRowsDef_spec
      tokenTable width tokenCount closure.start closure.count
      closure.finish closure.boundary closure.boundarySize
  have hclosureSlicesSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2, #3,
              #19, #20, #22, #24, #25, #27])
          Empty.elim) compactAdditiveAllClosureSlicesDef.val ↔
        CompactAdditiveAllClosureSlices tokenTable width tokenCount depth
          fixed.start fixed.finish fixed.count
          closure.start closure.finish closure.count := by
    rw [hclosureSlicesEnv]
    exact compactAdditiveAllClosureSlicesDef_spec
      tokenTable width tokenCount depth
      fixed.start fixed.finish fixed.count
      closure.start closure.finish closure.count
  have hemptyCountValue : env 7 = empty.count := by rfl
  have hcaptureCountValue : env 12 = capture.count := by rfl
  have hdepthValue : env 3 = depth := by rfl
  simp [compactFixedAllClosureTotalEndpointDef,
    CompactFixedAllClosureTotalEndpoint,
    htransformSpec, hclosureRowsSpec, hclosureSlicesSpec,
    hemptyCountValue, hcaptureCountValue, hdepthValue]

theorem compactFixedAllClosureTotalEndpointDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFixedAllClosureTotalEndpointDef.val := by
  simp [compactFixedAllClosureTotalEndpointDef]

theorem CompactFixedAllClosureTotalEndpoint.sound_canonical
    {tokenTable width tokenCount depth : Nat}
    {emptySlot captureSlot inputSlot fixedSlot closureSlot :
      CompactNatListRowSlot}
    {coordinates : CompactFixedAllClosureTotalEndpointCoordinates}
    (formula : LO.FirstOrder.ArithmeticProposition)
    (hendpoint : CompactFixedAllClosureTotalEndpoint tokenTable width tokenCount
      depth emptySlot captureSlot inputSlot fixedSlot closureSlot coordinates)
    (hinput : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      inputSlot.start inputSlot.finish
        (compactArithmeticFormulaTokens formula)) :
    ∃ closureTokens : List Nat,
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        closureSlot.start closureSlot.finish closureTokens /\
      closureTokens = compactArithmeticFormulaTokens
        (∀⁰* (Rewriting.app
          (Rew.fixitr (L := ℒₒᵣ) 0 depth) formula)) := by
  rcases hendpoint with
    ⟨_hemptyCount, hcaptureCount, htransform,
      hclosureRows, hclosureSlices⟩
  rcases htransform.sound with
    ⟨captureTokens, inputTokens, fixedTokens,
      hcaptureLayout, hinputLayout, hfixedLayout, hfixedResult⟩
  have hinputEq : compactArithmeticFormulaTokens formula = inputTokens :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hinputLayout hinput).1
  subst inputTokens
  rcases htransform.1.realize with
    ⟨captureRows, hcaptureRowsCount,
      hcaptureRowsLayout, _hcaptureRows⟩
  have hcaptureRowsEq : captureRows = captureTokens :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hcaptureLayout hcaptureRowsLayout).1
  have hcaptureLength : captureTokens.length = depth := by
    rw [← hcaptureRowsEq, hcaptureRowsCount, hcaptureCount]
  have hfixedResult' : fixedTokens =
      (compactFormulaFixitrExact 0
        (captureTokens.length,
          compactArithmeticFormulaTokens formula)).getD [] := by
    simpa [compactFormulaFixitrExact] using hfixedResult
  have hfixedCanonical : fixedTokens = compactArithmeticFormulaTokens
      (Rewriting.app (Rew.fixitr (L := ℒₒᵣ) 0 depth) formula) := by
    rw [hcaptureLength, compactFormulaFixitrExact_canonical]
      at hfixedResult'
    simpa using hfixedResult'
  rcases htransform.2.2.1.realize with
    ⟨fixedRows, hfixedRowsCount, hfixedRowsLayout, _hfixedRows⟩
  have hfixedRowsEq : fixedRows = fixedTokens :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hfixedLayout hfixedRowsLayout).1
  have hfixedCountValue : fixedSlot.count = fixedTokens.length := by
    rw [← hfixedRowsEq]
    exact hfixedRowsCount.symm
  rcases hclosureRows.realize with
    ⟨closureTokens, hclosureCount,
      hclosureLayout, _hclosureElementRows⟩
  have hclosureCountValue : closureSlot.count = closureTokens.length :=
    hclosureCount.symm
  have hclosureSlices' : CompactAdditiveAllClosureSlices
      tokenTable width tokenCount depth
      fixedSlot.start fixedSlot.finish fixedTokens.length
      closureSlot.start closureSlot.finish closureTokens.length := by
    simpa only [hfixedCountValue, hclosureCountValue] using hclosureSlices
  have hclosureValue : closureTokens =
      compactAllClosureTokens depth fixedTokens :=
    (compactAdditiveAllClosureSlices_iff
      hfixedLayout hclosureLayout).mp hclosureSlices'
  refine ⟨closureTokens, hclosureLayout, ?_⟩
  rw [hclosureValue, hfixedCanonical]
  simpa using compactAllClosureTokens_canonical
    (Rewriting.app (Rew.fixitr (L := ℒₒᵣ) 0 depth) formula)

#print axioms compactFixedAllClosureTotalEndpointDef_spec
#print axioms compactFixedAllClosureTotalEndpointDef_sigmaZero
#print axioms CompactFixedAllClosureTotalEndpoint.sound_canonical

end FoundationCompactNumericListedDirectFixedAllClosureTotalEndpoint
