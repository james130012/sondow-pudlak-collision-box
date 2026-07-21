import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit certificate for the bounded next formula-transform state

The fourteen next-state coordinates are installed as bounded short-binary
witnesses. The terminal is the exact bounded local-step certificate on the
same current and next state coordinates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedExplicitHybridCertificate

open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private theorem rewriting_bexsLTSucc
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (bound : ArithmeticSemiterm sourceVariables sourceArity)
    (body : ArithmeticSemiformula sourceVariables (sourceArity + 1)) :
    rewriting ▹ body.bexsLTSucc bound =
      (rewriting.q ▹ body).bexsLTSucc (rewriting bound) := by
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT]

private def adjacentNextSourceTerms
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness) :
    Fin 25 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm stateBoundary,
    shortBinaryNumeralTerm stateCount,
    shortBinaryNumeralTerm rowIndex,
    shortBinaryNumeralTerm mode,
    shortBinaryNumeralTerm witnessStart,
    shortBinaryNumeralTerm witnessFinish,
    shortBinaryNumeralTerm witnessCount,
    shortBinaryNumeralTerm valueBound,
    shortBinaryNumeralTerm currentCoordinates.start,
    shortBinaryNumeralTerm currentCoordinates.finish,
    shortBinaryNumeralTerm currentCoordinates.parserFinish,
    shortBinaryNumeralTerm currentCoordinates.parserTokensFinish,
    shortBinaryNumeralTerm currentCoordinates.parserTasksFinish,
    shortBinaryNumeralTerm currentCoordinates.parserTokensBoundary,
    shortBinaryNumeralTerm currentCoordinates.parserTokensCount,
    shortBinaryNumeralTerm currentCoordinates.parserTasksBoundary,
    shortBinaryNumeralTerm currentCoordinates.parserTasksCount,
    shortBinaryNumeralTerm currentCoordinates.outputBoundary,
    shortBinaryNumeralTerm currentCoordinates.outputCount,
    shortBinaryNumeralTerm currentSize.parserTokensBoundarySize,
    shortBinaryNumeralTerm currentSize.parserTasksBoundarySize,
    shortBinaryNumeralTerm currentSize.outputBoundarySize]

def compactFormulaTransformAdjacentNextBoundedClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentNextBoundedDef.val) ⇜
    adjacentNextSourceTerms tokenTable width tokenCount stateBoundary stateCount
      rowIndex mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize

private def compactFormulaTransformAdjacentNextBoundedRawTerminal
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness) :
    ArithmeticSemiformula Nat 14 :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentStepWitnessBoundedDef.val) ⇜
    ![sourceSubstitutionLift 14 (shortBinaryNumeralTerm tokenTable),
      sourceSubstitutionLift 14 (shortBinaryNumeralTerm width),
      sourceSubstitutionLift 14 (shortBinaryNumeralTerm tokenCount),
      sourceSubstitutionLift 14 (shortBinaryNumeralTerm stateBoundary),
      sourceSubstitutionLift 14 (shortBinaryNumeralTerm stateCount),
      sourceSubstitutionLift 14 (shortBinaryNumeralTerm rowIndex),
      sourceSubstitutionLift 14 (shortBinaryNumeralTerm mode),
      sourceSubstitutionLift 14 (shortBinaryNumeralTerm witnessStart),
      sourceSubstitutionLift 14 (shortBinaryNumeralTerm witnessFinish),
      sourceSubstitutionLift 14 (shortBinaryNumeralTerm witnessCount),
      sourceSubstitutionLift 14 (shortBinaryNumeralTerm valueBound),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.start),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.finish),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.parserFinish),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.parserTokensFinish),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.parserTasksFinish),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.parserTokensBoundary),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.parserTokensCount),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.parserTasksBoundary),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.parserTasksCount),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.outputBoundary),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentCoordinates.outputCount),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentSize.parserTokensBoundarySize),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentSize.parserTasksBoundarySize),
      sourceSubstitutionLift 14
        (shortBinaryNumeralTerm currentSize.outputBoundarySize),
      (#13 : ArithmeticSemiterm Nat 14), #12, #11, #10, #9, #8, #7,
      #6, #5, #4, #3, #2, #1, #0]

private def compactFormulaTransformAdjacentNextBoundedSourceRawTerminal :
    ArithmeticSemiformula Nat 39 :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentStepWitnessBoundedDef.val) ⇜
    ![(#14 : ArithmeticSemiterm Nat 39), #15, #16, #17, #18, #19,
      #20, #21, #22, #23, #24, #25, #26, #27, #28, #29, #30,
      #31, #32, #33, #34, #35, #36, #37, #38,
      #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]

private def compactFormulaTransformAdjacentNextBoundedEmptyRawTerminal :
    ArithmeticSemiformula Empty 39 :=
  compactFormulaTransformAdjacentStepWitnessBoundedDef.val ⇜
    ![(#14 : ArithmeticSemiterm Empty 39), #15, #16, #17, #18, #19,
      #20, #21, #22, #23, #24, #25, #26, #27, #28, #29, #30,
      #31, #32, #33, #34, #35, #36, #37, #38,
      #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]

private def compactFormulaTransformAdjacentNextBoundedSourceRawBody :
    ArithmeticSemiformula Nat 25 :=
  let body13 : ArithmeticSemiformula Nat 38 :=
    compactFormulaTransformAdjacentNextBoundedSourceRawTerminal.bexsLTSucc #23
  let body12 : ArithmeticSemiformula Nat 37 := body13.bexsLTSucc #22
  let body11 : ArithmeticSemiformula Nat 36 := body12.bexsLTSucc #21
  let body10 : ArithmeticSemiformula Nat 35 := body11.bexsLTSucc #20
  let body9 : ArithmeticSemiformula Nat 34 := body10.bexsLTSucc #19
  let body8 : ArithmeticSemiformula Nat 33 := body9.bexsLTSucc #18
  let body7 : ArithmeticSemiformula Nat 32 := body8.bexsLTSucc #17
  let body6 : ArithmeticSemiformula Nat 31 := body7.bexsLTSucc #16
  let body5 : ArithmeticSemiformula Nat 30 := body6.bexsLTSucc #15
  let body4 : ArithmeticSemiformula Nat 29 := body5.bexsLTSucc #14
  let body3 : ArithmeticSemiformula Nat 28 := body4.bexsLTSucc #13
  let body2 : ArithmeticSemiformula Nat 27 := body3.bexsLTSucc #12
  let body1 : ArithmeticSemiformula Nat 26 := body2.bexsLTSucc #11
  let body0 : ArithmeticSemiformula Nat 25 := body1.bexsLTSucc #10
  body0

private def compactFormulaTransformAdjacentNextBoundedEmptyRawBody :
    ArithmeticSemiformula Empty 25 :=
  let body13 : ArithmeticSemiformula Empty 38 :=
    compactFormulaTransformAdjacentNextBoundedEmptyRawTerminal.bexsLTSucc #23
  let body12 : ArithmeticSemiformula Empty 37 := body13.bexsLTSucc #22
  let body11 : ArithmeticSemiformula Empty 36 := body12.bexsLTSucc #21
  let body10 : ArithmeticSemiformula Empty 35 := body11.bexsLTSucc #20
  let body9 : ArithmeticSemiformula Empty 34 := body10.bexsLTSucc #19
  let body8 : ArithmeticSemiformula Empty 33 := body9.bexsLTSucc #18
  let body7 : ArithmeticSemiformula Empty 32 := body8.bexsLTSucc #17
  let body6 : ArithmeticSemiformula Empty 31 := body7.bexsLTSucc #16
  let body5 : ArithmeticSemiformula Empty 30 := body6.bexsLTSucc #15
  let body4 : ArithmeticSemiformula Empty 29 := body5.bexsLTSucc #14
  let body3 : ArithmeticSemiformula Empty 28 := body4.bexsLTSucc #13
  let body2 : ArithmeticSemiformula Empty 27 := body3.bexsLTSucc #12
  let body1 : ArithmeticSemiformula Empty 26 := body2.bexsLTSucc #11
  let body0 : ArithmeticSemiformula Empty 25 := body1.bexsLTSucc #10
  body0

private theorem compactFormulaTransformAdjacentNextBoundedDef_eq_emptyRawBody :
    compactFormulaTransformAdjacentNextBoundedDef.val =
      compactFormulaTransformAdjacentNextBoundedEmptyRawBody := by
  unfold compactFormulaTransformAdjacentNextBoundedDef
  unfold compactFormulaTransformAdjacentNextBoundedEmptyRawBody
  unfold compactFormulaTransformAdjacentNextBoundedEmptyRawTerminal
  rfl

private theorem compactFormulaTransformAdjacentNextBoundedEmptyRawTerminal_embedding :
    (Rew.emb : Rew ℒₒᵣ Empty 39 Nat 39) ▹
        compactFormulaTransformAdjacentNextBoundedEmptyRawTerminal =
      compactFormulaTransformAdjacentNextBoundedSourceRawTerminal := by
  unfold compactFormulaTransformAdjacentNextBoundedEmptyRawTerminal
  unfold compactFormulaTransformAdjacentNextBoundedSourceRawTerminal
  simp [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;> simp [Function.comp_apply]

private theorem compactFormulaTransformAdjacentNextBoundedDef_emb_eq_sourceRawBody :
    Rewriting.emb (ξ := Nat) compactFormulaTransformAdjacentNextBoundedDef.val =
      compactFormulaTransformAdjacentNextBoundedSourceRawBody := by
  rw [compactFormulaTransformAdjacentNextBoundedDef_eq_emptyRawBody]
  change (Rew.emb : Rew ℒₒᵣ Empty 25 Nat 25) ▹
      compactFormulaTransformAdjacentNextBoundedEmptyRawBody = _
  unfold compactFormulaTransformAdjacentNextBoundedEmptyRawBody
  unfold compactFormulaTransformAdjacentNextBoundedSourceRawBody
  simp [rewriting_bexsLTSucc,
    compactFormulaTransformAdjacentNextBoundedEmptyRawTerminal_embedding,
    Rew.q_bvar_zero, Rew.q_bvar_succ]

private theorem compactFormulaTransformAdjacentNextBoundedSourceRawTerminal_rewriting
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness) :
    sourceSubstitutionQpow
        (adjacentNextSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndex mode witnessStart witnessFinish witnessCount
          valueBound currentCoordinates currentSize) 14 ▹
      compactFormulaTransformAdjacentNextBoundedSourceRawTerminal =
    compactFormulaTransformAdjacentNextBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize := by
  unfold compactFormulaTransformAdjacentNextBoundedSourceRawTerminal
  unfold compactFormulaTransformAdjacentNextBoundedRawTerminal
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply, adjacentNextSourceTerms]
  all_goals
    rw [sourceSubstitutionQpow_bvar] <;>
      simp [sourceSubstitutionNormalizedBVarResult, adjacentNextSourceTerms]

@[simp] private theorem compactFormulaTransformAdjacentNextBoundedSourceQpow_valueBound
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (depth : Nat) :
    sourceSubstitutionQpow
        (adjacentNextSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndex mode witnessStart witnessFinish witnessCount
          valueBound currentCoordinates currentSize) depth
        (#(⟨depth + 10, by omega⟩ : Fin (25 + depth)) :
          ArithmeticSemiterm Nat (25 + depth)) =
      sourceSubstitutionLift depth (shortBinaryNumeralTerm valueBound) := by
  simpa [adjacentNextSourceTerms] using
    (sourceSubstitutionQpow_shiftedBVar
      (adjacentNextSourceTerms tokenTable width tokenCount stateBoundary
        stateCount rowIndex mode witnessStart witnessFinish witnessCount
        valueBound currentCoordinates currentSize)
      depth (⟨10, by omega⟩ : Fin 25))

private theorem compactFormulaTransformAdjacentNextBoundedSourceRawBody_alignment
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness) :
    Rew.subst
        (adjacentNextSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndex mode witnessStart witnessFinish witnessCount
          valueBound currentCoordinates currentSize) ▹
      compactFormulaTransformAdjacentNextBoundedSourceRawBody =
    explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 14
      (compactFormulaTransformAdjacentNextBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize) := by
  change sourceSubstitutionQpow
      (adjacentNextSourceTerms tokenTable width tokenCount stateBoundary
        stateCount rowIndex mode witnessStart witnessFinish witnessCount
        valueBound currentCoordinates currentSize) 0 ▹
      compactFormulaTransformAdjacentNextBoundedSourceRawBody = _
  unfold compactFormulaTransformAdjacentNextBoundedSourceRawBody
  simp only [sourceSubstitutionQpow_bexsLTSucc]
  rw [compactFormulaTransformAdjacentNextBoundedSourceRawTerminal_rewriting]
  simp_rw [sourceSubstitutionQpow_bvar]
  simp [sourceSubstitutionNormalizedBVarResult, adjacentNextSourceTerms]
  rfl

theorem compactFormulaTransformAdjacentNextBoundedClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness) :
    compactFormulaTransformAdjacentNextBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 14
        (compactFormulaTransformAdjacentNextBoundedRawTerminal
          tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize) := by
  unfold compactFormulaTransformAdjacentNextBoundedClosedFormula
  rw [compactFormulaTransformAdjacentNextBoundedDef_emb_eq_sourceRawBody]
  exact compactFormulaTransformAdjacentNextBoundedSourceRawBody_alignment
    tokenTable width tokenCount stateBoundary stateCount rowIndex mode
    witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize

private structure CompactFormulaTransformAdjacentNextStateWitness where
  coordinates : CompactFormulaTransformStateRowCoordinates
  size : CompactFormulaTransformStateCoreSizeWitness

private def adjacentNextBoundedWitnessValues
    (witness : CompactFormulaTransformAdjacentNextStateWitness) :
    Fin 14 -> Nat :=
  ![witness.size.outputBoundarySize,
    witness.size.parserTasksBoundarySize,
    witness.size.parserTokensBoundarySize,
    witness.coordinates.outputCount,
    witness.coordinates.outputBoundary,
    witness.coordinates.parserTasksCount,
    witness.coordinates.parserTasksBoundary,
    witness.coordinates.parserTokensCount,
    witness.coordinates.parserTokensBoundary,
    witness.coordinates.parserTasksFinish,
    witness.coordinates.parserTokensFinish,
    witness.coordinates.parserFinish,
    witness.coordinates.finish,
    witness.coordinates.start]

private theorem substitute_sourceSubstitutionLift
    {depth : Nat} (values : Fin (0 + depth) -> ValuationTerm)
    (term : ValuationTerm) :
    Rew.subst values (sourceSubstitutionLift depth term) = term := by
  induction depth with
  | zero =>
      have hrew : (Rew.subst values : Rew ℒₒᵣ Nat 0 Nat 0) = Rew.id := by
        apply Rew.ext
        · intro index
          exact Fin.elim0 index
        · intro freeIndex
          rfl
      rw [hrew]
      exact Rew.id_app term
  | succ depth inductionHypothesis =>
      have hrew :
          (Rew.subst values).comp Rew.bShift =
            Rew.subst (fun index : Fin (0 + depth) => values index.succ) := by
        apply Rew.ext
        · intro index
          simp [Rew.comp_app]
        · intro freeIndex
          simp [Rew.comp_app]
      calc
        Rew.subst values (sourceSubstitutionLift (depth + 1) term) =
            ((Rew.subst values).comp Rew.bShift)
              (sourceSubstitutionLift depth term) := by
                simp [sourceSubstitutionLift, Rew.comp_app]
        _ = Rew.subst (fun index : Fin (0 + depth) => values index.succ)
              (sourceSubstitutionLift depth term) := by rw [hrew]
        _ = term := inductionHypothesis _

private theorem substitute_sourceSubstitutionLift14
    (values : Fin 14 -> ValuationTerm) (term : ValuationTerm) :
    Rew.subst values (sourceSubstitutionLift 14 term) = term := by
  simpa only using
    (substitute_sourceSubstitutionLift (depth := 14) values term)

private def adjacentInnerClosedTerms
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates nextCoordinates :
      CompactFormulaTransformStateRowCoordinates)
    (currentSize nextSize : CompactFormulaTransformStateCoreSizeWitness) :
    Fin 39 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm stateBoundary,
    shortBinaryNumeralTerm stateCount,
    shortBinaryNumeralTerm rowIndex,
    shortBinaryNumeralTerm mode,
    shortBinaryNumeralTerm witnessStart,
    shortBinaryNumeralTerm witnessFinish,
    shortBinaryNumeralTerm witnessCount,
    shortBinaryNumeralTerm valueBound,
    shortBinaryNumeralTerm currentCoordinates.start,
    shortBinaryNumeralTerm currentCoordinates.finish,
    shortBinaryNumeralTerm currentCoordinates.parserFinish,
    shortBinaryNumeralTerm currentCoordinates.parserTokensFinish,
    shortBinaryNumeralTerm currentCoordinates.parserTasksFinish,
    shortBinaryNumeralTerm currentCoordinates.parserTokensBoundary,
    shortBinaryNumeralTerm currentCoordinates.parserTokensCount,
    shortBinaryNumeralTerm currentCoordinates.parserTasksBoundary,
    shortBinaryNumeralTerm currentCoordinates.parserTasksCount,
    shortBinaryNumeralTerm currentCoordinates.outputBoundary,
    shortBinaryNumeralTerm currentCoordinates.outputCount,
    shortBinaryNumeralTerm currentSize.parserTokensBoundarySize,
    shortBinaryNumeralTerm currentSize.parserTasksBoundarySize,
    shortBinaryNumeralTerm currentSize.outputBoundarySize,
    shortBinaryNumeralTerm nextCoordinates.start,
    shortBinaryNumeralTerm nextCoordinates.finish,
    shortBinaryNumeralTerm nextCoordinates.parserFinish,
    shortBinaryNumeralTerm nextCoordinates.parserTokensFinish,
    shortBinaryNumeralTerm nextCoordinates.parserTasksFinish,
    shortBinaryNumeralTerm nextCoordinates.parserTokensBoundary,
    shortBinaryNumeralTerm nextCoordinates.parserTokensCount,
    shortBinaryNumeralTerm nextCoordinates.parserTasksBoundary,
    shortBinaryNumeralTerm nextCoordinates.parserTasksCount,
    shortBinaryNumeralTerm nextCoordinates.outputBoundary,
    shortBinaryNumeralTerm nextCoordinates.outputCount,
    shortBinaryNumeralTerm nextSize.parserTokensBoundarySize,
    shortBinaryNumeralTerm nextSize.parserTasksBoundarySize,
    shortBinaryNumeralTerm nextSize.outputBoundarySize]

private theorem compactFormulaTransformAdjacentStepWitnessBoundedClosedFormula_eq_direct
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates nextCoordinates :
      CompactFormulaTransformStateRowCoordinates)
    (currentSize nextSize : CompactFormulaTransformStateCoreSizeWitness) :
    compactFormulaTransformAdjacentStepWitnessBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize =
      (Rewriting.emb (ξ := Nat)
          compactFormulaTransformAdjacentStepWitnessBoundedDef.val) ⇜
        adjacentInnerClosedTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndex mode witnessStart witnessFinish witnessCount
          valueBound currentCoordinates nextCoordinates currentSize nextSize := by
  rfl

private theorem compactFormulaTransformAdjacentNextBoundedRawTerminal_alignment
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (witness : CompactFormulaTransformAdjacentNextStateWitness) :
    compactFormulaTransformAdjacentNextBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize ⇜
      (fun index => shortBinaryNumeralTerm
        (adjacentNextBoundedWitnessValues witness index)) =
    compactFormulaTransformAdjacentStepWitnessBoundedClosedFormula
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size := by
  rw [compactFormulaTransformAdjacentStepWitnessBoundedClosedFormula_eq_direct]
  change Rew.subst
      (fun index => shortBinaryNumeralTerm
        (adjacentNextBoundedWitnessValues witness index)) ▹
    compactFormulaTransformAdjacentNextBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize = _
  unfold compactFormulaTransformAdjacentNextBoundedRawTerminal
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply, adjacentNextBoundedWitnessValues,
      adjacentInnerClosedTerms, Rew.subst_bvar,
      substitute_sourceSubstitutionLift14]

noncomputable def compactFormulaTransformAdjacentNextBoundedExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hnext : CompactFormulaTransformAdjacentNextBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize) :
    HybridCertificate
      (compactFormulaTransformAdjacentNextBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize) := by
  have hexists :
      ∃ witness : CompactFormulaTransformAdjacentNextStateWitness,
        (∀ index, adjacentNextBoundedWitnessValues witness index ≤ valueBound) ∧
        CompactFormulaTransformAdjacentStepWitnessBounded
          tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize witness.coordinates witness.size := by
    rcases hnext with
      ⟨nextStart, hnextStart, nextFinish, hnextFinish,
        nextParserFinish, hnextParserFinish,
        nextParserTokensFinish, hnextParserTokensFinish,
        nextParserTasksFinish, hnextParserTasksFinish,
        nextParserTokensBoundary, hnextParserTokensBoundary,
        nextParserTokensCount, hnextParserTokensCount,
        nextParserTasksBoundary, hnextParserTasksBoundary,
        nextParserTasksCount, hnextParserTasksCount,
        nextOutputBoundary, hnextOutputBoundary,
        nextOutputCount, hnextOutputCount,
        nextParserTokensBoundarySize, hnextParserTokensBoundarySize,
        nextParserTasksBoundarySize, hnextParserTasksBoundarySize,
        nextOutputBoundarySize, hnextOutputBoundarySize, hinner⟩
    let witness : CompactFormulaTransformAdjacentNextStateWitness :=
      { coordinates := compactFormulaTransformStateRowCoordinatesOf
          nextStart nextFinish nextParserFinish nextParserTokensFinish
          nextParserTasksFinish nextParserTokensBoundary nextParserTokensCount
          nextParserTasksBoundary nextParserTasksCount nextOutputBoundary
          nextOutputCount
        size :=
          { parserTokensBoundarySize := nextParserTokensBoundarySize
            parserTasksBoundarySize := nextParserTasksBoundarySize
            outputBoundarySize := nextOutputBoundarySize } }
    refine ⟨witness, ?_, ?_⟩
    · intro index
      fin_cases index
      · exact hnextOutputBoundarySize
      · exact hnextParserTasksBoundarySize
      · exact hnextParserTokensBoundarySize
      · exact hnextOutputCount
      · exact hnextOutputBoundary
      · exact hnextParserTasksCount
      · exact hnextParserTasksBoundary
      · exact hnextParserTokensCount
      · exact hnextParserTokensBoundary
      · exact hnextParserTasksFinish
      · exact hnextParserTokensFinish
      · exact hnextParserFinish
      · exact hnextFinish
      · exact hnextStart
    · simpa [witness] using hinner
  let witness := Classical.choose hexists
  have hwitness := Classical.choose_spec hexists
  let values := adjacentNextBoundedWitnessValues witness
  have hvalues : ∀ index, values index ≤ valueBound := by
    simpa [values] using hwitness.1
  let innerCertificate :=
    compactFormulaTransformAdjacentStepWitnessBoundedExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hwitness.2
  let terminal : HybridCertificate
      (compactFormulaTransformAdjacentNextBoundedRawTerminal
          tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize ⇜
        fun index => shortBinaryNumeralTerm (values index)) :=
    .cast (by
      dsimp only [values]
      exact
        (compactFormulaTransformAdjacentNextBoundedRawTerminal_alignment
          tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize witness).symm) innerCertificate
  rw [compactFormulaTransformAdjacentNextBoundedClosedFormula_alignment]
  exact buildExplicitBoundedWitnessHybridCertificate valueBound
    (compactFormulaTransformAdjacentNextBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize) values hvalues terminal

noncomputable def compileCompactFormulaTransformAdjacentNextBoundedExplicitHybridContext
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hnext : CompactFormulaTransformAdjacentNextBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformAdjacentNextBoundedClosedFormula
          tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize).freeVariables zeroValuation)
      (compactFormulaTransformAdjacentNextBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize) :=
  (compactFormulaTransformAdjacentNextBoundedExplicitHybridCertificateOfGraph
    tokenTable width tokenCount stateBoundary stateCount rowIndex mode
    witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize hnext).compile

noncomputable def compactFormulaTransformAdjacentNextBoundedExplicitStructuralResource
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hnext : CompactFormulaTransformAdjacentNextBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactFormulaTransformAdjacentNextBoundedExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize hnext)

theorem compileCompactFormulaTransformAdjacentNextBoundedExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hnext : CompactFormulaTransformAdjacentNextBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize) :
    (compileCompactFormulaTransformAdjacentNextBoundedExplicitHybridContext
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize hnext).payloadLength ≤
    compactFormulaTransformAdjacentNextBoundedExplicitStructuralResource
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize hnext := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactFormulaTransformAdjacentNextBoundedExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize hnext)

#print axioms compactFormulaTransformAdjacentNextBoundedClosedFormula_alignment
#print axioms compactFormulaTransformAdjacentNextBoundedRawTerminal_alignment
#print axioms compactFormulaTransformAdjacentNextBoundedExplicitHybridCertificateOfGraph
#print axioms compileCompactFormulaTransformAdjacentNextBoundedExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedExplicitHybridCertificate
