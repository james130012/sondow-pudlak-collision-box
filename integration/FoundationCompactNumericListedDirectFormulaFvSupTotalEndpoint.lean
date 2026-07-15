import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpoint
import integration.FoundationCompactNumericListedDirectListFvSupRows
import integration.FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute

/-!
# Self-contained direct endpoint for formula free-variable supremum

The endpoint combines the complete mode-four transform trace, direct rows for
all lists, and the exact maximum relation on the emitted free-variable list.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaFvSupTotalEndpoint

open FoundationCompactSyntaxTokenMachine
open FoundationCompactSyntaxTransformationTraceCore
open FoundationCompactNumericFormulaFvSup
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpoint
open FoundationCompactNumericListedDirectListFvSupRows
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute

structure CompactFormulaFvSupTotalEndpointCoordinates where
  trace : CompactFormulaTransformTraceSlot

def CompactFormulaFvSupTotalEndpoint
    (tokenTable width tokenCount binderArity maximum : Nat)
    (empty input fvarList : CompactNatListRowSlot)
    (coordinates : CompactFormulaFvSupTotalEndpointCoordinates) : Prop :=
  empty.count = 0 /\
    CompactFormulaTransformTotalExactEndpoint
      tokenTable width tokenCount 4 binderArity
      empty.start empty.finish empty.boundary empty.count empty.boundarySize
      input.start input.finish input.boundary input.count input.boundarySize
      fvarList.start fvarList.finish fvarList.boundary fvarList.count
        fvarList.boundarySize
      empty.start empty.finish empty.boundary empty.boundarySize
      coordinates.trace.stateBoundary coordinates.trace.stateCount
      coordinates.trace.tableWidth coordinates.trace.valueBound /\
    CompactAdditiveNatListFvSupRows tokenTable width tokenCount
      fvarList.boundary fvarList.count maximum

def compactFormulaFvSupTotalEndpointDef : 𝚺₀.Semisentence 24 := .mkSigma
  “tokenTable width tokenCount binderArity maximum
      emptyStart emptyFinish emptyBoundary emptyCount emptyBoundarySize
      inputStart inputFinish inputBoundary inputCount inputBoundarySize
      fvarListStart fvarListFinish fvarListBoundary fvarListCount
        fvarListBoundarySize
      stateBoundary stateCount tableWidth valueBound.
    emptyCount = 0 ∧
    !(compactFormulaTransformTotalExactEndpointDef)
      tokenTable width tokenCount 4 binderArity
      emptyStart emptyFinish emptyBoundary emptyCount emptyBoundarySize
      inputStart inputFinish inputBoundary inputCount inputBoundarySize
      fvarListStart fvarListFinish fvarListBoundary fvarListCount
        fvarListBoundarySize
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      stateBoundary stateCount tableWidth valueBound ∧
    !(compactAdditiveNatListFvSupRowsDef)
      tokenTable width tokenCount fvarListBoundary fvarListCount maximum”

def compactFormulaFvSupTotalEndpointEnvironment
    (tokenTable width tokenCount binderArity maximum : Nat)
    (empty input fvarList : CompactNatListRowSlot)
    (coordinates : CompactFormulaFvSupTotalEndpointCoordinates) :
    Fin 24 -> Nat :=
  ![tokenTable, width, tokenCount, binderArity, maximum,
    empty.start, empty.finish, empty.boundary, empty.count,
      empty.boundarySize,
    input.start, input.finish, input.boundary, input.count,
      input.boundarySize,
    fvarList.start, fvarList.finish, fvarList.boundary, fvarList.count,
      fvarList.boundarySize,
    coordinates.trace.stateBoundary, coordinates.trace.stateCount,
      coordinates.trace.tableWidth, coordinates.trace.valueBound]

set_option maxHeartbeats 1000000 in
-- The embedded total transform endpoint requires a local normalization budget.
set_option maxRecDepth 4096 in
@[simp] theorem compactFormulaFvSupTotalEndpointDef_spec
    (tokenTable width tokenCount binderArity maximum : Nat)
    (empty input fvarList : CompactNatListRowSlot)
    (coordinates : CompactFormulaFvSupTotalEndpointCoordinates) :
    compactFormulaFvSupTotalEndpointDef.val.Evalb
        (compactFormulaFvSupTotalEndpointEnvironment
          tokenTable width tokenCount binderArity maximum empty input fvarList
          coordinates) ↔
      CompactFormulaFvSupTotalEndpoint tokenTable width tokenCount
        binderArity maximum empty input fvarList coordinates := by
  let env := compactFormulaFvSupTotalEndpointEnvironment
    tokenTable width tokenCount binderArity maximum empty input fvarList
      coordinates
  change compactFormulaFvSupTotalEndpointDef.val.Evalb env ↔ _
  have htransformEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, ‘4’, #3,
          #5, #6, #7, #8, #9,
          #10, #11, #12, #13, #14,
          #15, #16, #17, #18, #19,
          #5, #6, #7, #9, #20, #21, #22, #23]) =
        ![tokenTable, width, tokenCount, 4, binderArity,
          empty.start, empty.finish, empty.boundary, empty.count,
            empty.boundarySize,
          input.start, input.finish, input.boundary, input.count,
            input.boundarySize,
          fvarList.start, fvarList.finish, fvarList.boundary, fvarList.count,
            fvarList.boundarySize,
          empty.start, empty.finish, empty.boundary, empty.boundarySize,
          coordinates.trace.stateBoundary, coordinates.trace.stateCount,
            coordinates.trace.tableWidth, coordinates.trace.valueBound] := by
    funext coordinate
    fin_cases coordinate <;> simp [env,
      compactFormulaFvSupTotalEndpointEnvironment]
  have hmaximumEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #17, #18, #4]) =
        ![tokenTable, width, tokenCount,
          fvarList.boundary, fvarList.count, maximum] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htransformSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, ‘4’, #3,
              #5, #6, #7, #8, #9,
              #10, #11, #12, #13, #14,
              #15, #16, #17, #18, #19,
              #5, #6, #7, #9, #20, #21, #22, #23])
          Empty.elim) compactFormulaTransformTotalExactEndpointDef.val ↔
        CompactFormulaTransformTotalExactEndpoint
          tokenTable width tokenCount 4 binderArity
          empty.start empty.finish empty.boundary empty.count
            empty.boundarySize
          input.start input.finish input.boundary input.count
            input.boundarySize
          fvarList.start fvarList.finish fvarList.boundary fvarList.count
            fvarList.boundarySize
          empty.start empty.finish empty.boundary empty.boundarySize
          coordinates.trace.stateBoundary coordinates.trace.stateCount
          coordinates.trace.tableWidth coordinates.trace.valueBound := by
    rw [htransformEnv]
    exact compactFormulaTransformTotalExactEndpointDef_spec
      tokenTable width tokenCount 4 binderArity
      empty.start empty.finish empty.boundary empty.count empty.boundarySize
      input.start input.finish input.boundary input.count input.boundarySize
      fvarList.start fvarList.finish fvarList.boundary fvarList.count
        fvarList.boundarySize
      empty.start empty.finish empty.boundary empty.boundarySize
      coordinates.trace.stateBoundary coordinates.trace.stateCount
      coordinates.trace.tableWidth coordinates.trace.valueBound
  have hmaximumSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #17, #18, #4])
          Empty.elim) compactAdditiveNatListFvSupRowsDef.val ↔
        CompactAdditiveNatListFvSupRows tokenTable width tokenCount
          fvarList.boundary fvarList.count maximum := by
    rw [hmaximumEnv]
    exact compactAdditiveNatListFvSupRowsDef_spec
      tokenTable width tokenCount fvarList.boundary fvarList.count maximum
  have hemptyCountValue : env 8 = empty.count := by rfl
  simp [compactFormulaFvSupTotalEndpointDef,
    CompactFormulaFvSupTotalEndpoint,
    htransformSpec, hmaximumSpec, hemptyCountValue]

theorem compactFormulaFvSupTotalEndpointDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaFvSupTotalEndpointDef.val := by
  simp [compactFormulaFvSupTotalEndpointDef]

theorem CompactFormulaFvSupTotalEndpoint.sound_canonical
    {tokenTable width tokenCount maximum : Nat}
    {emptySlot inputSlot fvarListSlot : CompactNatListRowSlot}
    {coordinates : CompactFormulaFvSupTotalEndpointCoordinates}
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (hendpoint : CompactFormulaFvSupTotalEndpoint tokenTable width tokenCount
      binderArity maximum emptySlot inputSlot fvarListSlot coordinates)
    (hinput : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      inputSlot.start inputSlot.finish
        (compactArithmeticFormulaTokens formula)) :
    maximum = formula.fvSup := by
  rcases hendpoint with ⟨_hemptyCount, htransform, hmaximum⟩
  rcases htransform.sound with
    ⟨_control, inputTokens, fvarListTokens,
      _hcontrolLayout, hinputLayout, hfvarListLayout, hresult⟩
  have hinputEq : compactArithmeticFormulaTokens formula = inputTokens :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hinputLayout hinput).1
  subst inputTokens
  have hresult' : fvarListTokens =
      (compactExactFormulaTransformResult
        (compactFormulaFvListTokenTransform binderArity
          (compactArithmeticFormulaTokens formula))).getD [] := by
    simpa using hresult
  have hcanonicalFvList : compactFormulaFvListTokenTransform binderArity
      (compactArithmeticFormulaTokens formula) =
        some (formula.fvarList, []) := by
    simpa using compactFormulaFvListTokenTransform_canonical_append formula []
  rw [hcanonicalFvList] at hresult'
  simp only [compactExactFormulaTransformResult, Option.bind_some,
    ↓reduceIte, Option.getD_some] at hresult'
  rcases htransform.2.2.1.realize with
    ⟨fvarListRows, hfvarListCount,
      hfvarListRowsLayout, hfvarListElementRows⟩
  have hfvarListRowsEq : fvarListRows = fvarListTokens :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hfvarListLayout hfvarListRowsLayout).1
  subst fvarListRows
  have hmaximum' : CompactAdditiveNatListFvSupRows
      tokenTable width tokenCount fvarListSlot.boundary
        fvarListTokens.length maximum := by
    simpa only [hfvarListCount] using hmaximum
  have hmaximumValue : maximum = listFvSup fvarListTokens :=
    (compactAdditiveNatListFvSupRows_iff
      hfvarListElementRows maximum).mp hmaximum'
  rw [hresult'] at hmaximumValue
  simpa [listFvSup_formula_eq_fvSup] using hmaximumValue

#print axioms compactFormulaFvSupTotalEndpointDef_spec
#print axioms compactFormulaFvSupTotalEndpointDef_sigmaZero
#print axioms CompactFormulaFvSupTotalEndpoint.sound_canonical

end FoundationCompactNumericListedDirectFormulaFvSupTotalEndpoint
