import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit certificate for the bounded current formula-transform state

The fourteen current-state coordinates are installed as bounded short-binary
witnesses. The terminal is the exact bounded next-state certificate on those
same current coordinates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedExplicitHybridCertificate

open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedExplicitHybridCertificate
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

private def adjacentCurrentSourceTerms
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat) :
    Fin 11 -> ValuationTerm :=
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
    shortBinaryNumeralTerm valueBound]

def compactFormulaTransformAdjacentCurrentBoundedClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentCurrentBoundedDef.val) ⇜
    adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
      stateCount rowIndex mode witnessStart witnessFinish witnessCount valueBound

private def compactFormulaTransformAdjacentCurrentBoundedRawTerminal
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat) :
    ArithmeticSemiformula Nat 14 :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentNextBoundedDef.val) ⇜
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
      (#13 : ArithmeticSemiterm Nat 14), #12, #11, #10, #9, #8, #7,
      #6, #5, #4, #3, #2, #1, #0]

private def compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal :
    ArithmeticSemiformula Nat 25 :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentNextBoundedDef.val) ⇜
    ![(#14 : ArithmeticSemiterm Nat 25), #15, #16, #17, #18, #19,
      #20, #21, #22, #23, #24,
      #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]

private def compactFormulaTransformAdjacentCurrentBoundedEmptyRawTerminal :
    ArithmeticSemiformula Empty 25 :=
  compactFormulaTransformAdjacentNextBoundedDef.val ⇜
    ![(#14 : ArithmeticSemiterm Empty 25), #15, #16, #17, #18, #19,
      #20, #21, #22, #23, #24,
      #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]

private def compactFormulaTransformAdjacentCurrentBoundedSourceRawBody :
    ArithmeticSemiformula Nat 11 :=
  let body13 : ArithmeticSemiformula Nat 24 :=
    compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal.bexsLTSucc #23
  let body12 : ArithmeticSemiformula Nat 23 := body13.bexsLTSucc #22
  let body11 : ArithmeticSemiformula Nat 22 := body12.bexsLTSucc #21
  let body10 : ArithmeticSemiformula Nat 21 := body11.bexsLTSucc #20
  let body9 : ArithmeticSemiformula Nat 20 := body10.bexsLTSucc #19
  let body8 : ArithmeticSemiformula Nat 19 := body9.bexsLTSucc #18
  let body7 : ArithmeticSemiformula Nat 18 := body8.bexsLTSucc #17
  let body6 : ArithmeticSemiformula Nat 17 := body7.bexsLTSucc #16
  let body5 : ArithmeticSemiformula Nat 16 := body6.bexsLTSucc #15
  let body4 : ArithmeticSemiformula Nat 15 := body5.bexsLTSucc #14
  let body3 : ArithmeticSemiformula Nat 14 := body4.bexsLTSucc #13
  let body2 : ArithmeticSemiformula Nat 13 := body3.bexsLTSucc #12
  let body1 : ArithmeticSemiformula Nat 12 := body2.bexsLTSucc #11
  let body0 : ArithmeticSemiformula Nat 11 := body1.bexsLTSucc #10
  body0

private def compactFormulaTransformAdjacentCurrentBoundedEmptyRawBody :
    ArithmeticSemiformula Empty 11 :=
  let body13 : ArithmeticSemiformula Empty 24 :=
    compactFormulaTransformAdjacentCurrentBoundedEmptyRawTerminal.bexsLTSucc #23
  let body12 : ArithmeticSemiformula Empty 23 := body13.bexsLTSucc #22
  let body11 : ArithmeticSemiformula Empty 22 := body12.bexsLTSucc #21
  let body10 : ArithmeticSemiformula Empty 21 := body11.bexsLTSucc #20
  let body9 : ArithmeticSemiformula Empty 20 := body10.bexsLTSucc #19
  let body8 : ArithmeticSemiformula Empty 19 := body9.bexsLTSucc #18
  let body7 : ArithmeticSemiformula Empty 18 := body8.bexsLTSucc #17
  let body6 : ArithmeticSemiformula Empty 17 := body7.bexsLTSucc #16
  let body5 : ArithmeticSemiformula Empty 16 := body6.bexsLTSucc #15
  let body4 : ArithmeticSemiformula Empty 15 := body5.bexsLTSucc #14
  let body3 : ArithmeticSemiformula Empty 14 := body4.bexsLTSucc #13
  let body2 : ArithmeticSemiformula Empty 13 := body3.bexsLTSucc #12
  let body1 : ArithmeticSemiformula Empty 12 := body2.bexsLTSucc #11
  let body0 : ArithmeticSemiformula Empty 11 := body1.bexsLTSucc #10
  body0

private theorem compactFormulaTransformAdjacentCurrentBoundedDef_eq_emptyRawBody :
    compactFormulaTransformAdjacentCurrentBoundedDef.val =
      compactFormulaTransformAdjacentCurrentBoundedEmptyRawBody := by
  unfold compactFormulaTransformAdjacentCurrentBoundedDef
  unfold compactFormulaTransformAdjacentCurrentBoundedEmptyRawBody
  unfold compactFormulaTransformAdjacentCurrentBoundedEmptyRawTerminal
  rfl

private theorem compactFormulaTransformAdjacentCurrentBoundedEmptyRawTerminal_embedding :
    (Rew.emb : Rew ℒₒᵣ Empty 25 Nat 25) ▹
        compactFormulaTransformAdjacentCurrentBoundedEmptyRawTerminal =
      compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal := by
  unfold compactFormulaTransformAdjacentCurrentBoundedEmptyRawTerminal
  unfold compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal
  simp [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;> simp [Function.comp_apply]

private theorem compactFormulaTransformAdjacentCurrentBoundedDef_emb_eq_sourceRawBody :
    Rewriting.emb (ξ := Nat) compactFormulaTransformAdjacentCurrentBoundedDef.val =
      compactFormulaTransformAdjacentCurrentBoundedSourceRawBody := by
  rw [compactFormulaTransformAdjacentCurrentBoundedDef_eq_emptyRawBody]
  change (Rew.emb : Rew ℒₒᵣ Empty 11 Nat 11) ▹
      compactFormulaTransformAdjacentCurrentBoundedEmptyRawBody = _
  unfold compactFormulaTransformAdjacentCurrentBoundedEmptyRawBody
  unfold compactFormulaTransformAdjacentCurrentBoundedSourceRawBody
  simp [rewriting_bexsLTSucc,
    compactFormulaTransformAdjacentCurrentBoundedEmptyRawTerminal_embedding,
    Rew.q_bvar_zero, Rew.q_bvar_succ]

private theorem compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal_rewriting
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat) :
    sourceSubstitutionQpow
        (adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndex mode witnessStart witnessFinish witnessCount
          valueBound) 14 ▹
      compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal =
    compactFormulaTransformAdjacentCurrentBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound := by
  unfold compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal
  unfold compactFormulaTransformAdjacentCurrentBoundedRawTerminal
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply, adjacentCurrentSourceTerms]
  all_goals
    rw [sourceSubstitutionQpow_bvar] <;>
      simp [sourceSubstitutionNormalizedBVarResult,
        adjacentCurrentSourceTerms]

@[simp] private theorem compactFormulaTransformAdjacentCurrentBoundedSourceQpow_valueBound
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound depth : Nat) :
    sourceSubstitutionQpow
        (adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndex mode witnessStart witnessFinish witnessCount
          valueBound) depth
        (#(⟨depth + 10, by omega⟩ : Fin (11 + depth)) :
          ArithmeticSemiterm Nat (11 + depth)) =
      sourceSubstitutionLift depth (shortBinaryNumeralTerm valueBound) := by
  simpa [adjacentCurrentSourceTerms] using
    (sourceSubstitutionQpow_shiftedBVar
      (adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
        stateCount rowIndex mode witnessStart witnessFinish witnessCount
        valueBound)
      depth (⟨10, by omega⟩ : Fin 11))

private theorem compactFormulaTransformAdjacentCurrentBoundedSourceRawBody_alignment
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat) :
    Rew.subst
        (adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndex mode witnessStart witnessFinish witnessCount
          valueBound) ▹
      compactFormulaTransformAdjacentCurrentBoundedSourceRawBody =
    explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 14
      (compactFormulaTransformAdjacentCurrentBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) := by
  change sourceSubstitutionQpow
      (adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
        stateCount rowIndex mode witnessStart witnessFinish witnessCount
        valueBound) 0 ▹
      compactFormulaTransformAdjacentCurrentBoundedSourceRawBody = _
  unfold compactFormulaTransformAdjacentCurrentBoundedSourceRawBody
  simp only [sourceSubstitutionQpow_bexsLTSucc]
  rw [compactFormulaTransformAdjacentCurrentBoundedSourceRawTerminal_rewriting]
  simp_rw [sourceSubstitutionQpow_bvar]
  simp [sourceSubstitutionNormalizedBVarResult, adjacentCurrentSourceTerms]
  rfl

theorem compactFormulaTransformAdjacentCurrentBoundedClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat) :
    compactFormulaTransformAdjacentCurrentBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 14
        (compactFormulaTransformAdjacentCurrentBoundedRawTerminal
          tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound) := by
  unfold compactFormulaTransformAdjacentCurrentBoundedClosedFormula
  rw [compactFormulaTransformAdjacentCurrentBoundedDef_emb_eq_sourceRawBody]
  exact compactFormulaTransformAdjacentCurrentBoundedSourceRawBody_alignment
    tokenTable width tokenCount stateBoundary stateCount rowIndex mode
    witnessStart witnessFinish witnessCount valueBound

private structure CompactFormulaTransformAdjacentCurrentStateWitness where
  coordinates : CompactFormulaTransformStateRowCoordinates
  size : CompactFormulaTransformStateCoreSizeWitness

private def adjacentCurrentBoundedWitnessValues
    (witness : CompactFormulaTransformAdjacentCurrentStateWitness) :
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

private def adjacentCurrentInnerClosedTerms
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

private theorem compactFormulaTransformAdjacentNextBoundedClosedFormula_eq_direct
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness) :
    compactFormulaTransformAdjacentNextBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize =
      (Rewriting.emb (ξ := Nat)
          compactFormulaTransformAdjacentNextBoundedDef.val) ⇜
        adjacentCurrentInnerClosedTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndex mode witnessStart witnessFinish witnessCount
          valueBound currentCoordinates currentSize := by
  rfl

private theorem compactFormulaTransformAdjacentCurrentBoundedRawTerminal_alignment
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (witness : CompactFormulaTransformAdjacentCurrentStateWitness) :
    compactFormulaTransformAdjacentCurrentBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound ⇜
      (fun index => shortBinaryNumeralTerm
        (adjacentCurrentBoundedWitnessValues witness index)) =
    compactFormulaTransformAdjacentNextBoundedClosedFormula
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size := by
  rw [compactFormulaTransformAdjacentNextBoundedClosedFormula_eq_direct]
  change Rew.subst
      (fun index => shortBinaryNumeralTerm
        (adjacentCurrentBoundedWitnessValues witness index)) ▹
    compactFormulaTransformAdjacentCurrentBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound = _
  unfold compactFormulaTransformAdjacentCurrentBoundedRawTerminal
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply, adjacentCurrentBoundedWitnessValues,
      adjacentCurrentInnerClosedTerms, Rew.subst_bvar,
      substitute_sourceSubstitutionLift14]

noncomputable def compactFormulaTransformAdjacentCurrentBoundedExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound) :
    HybridCertificate
      (compactFormulaTransformAdjacentCurrentBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) := by
  have hexists :
      ∃ witness : CompactFormulaTransformAdjacentCurrentStateWitness,
        (∀ index,
          adjacentCurrentBoundedWitnessValues witness index ≤ valueBound) ∧
        CompactFormulaTransformAdjacentNextBounded
          tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound
          witness.coordinates witness.size := by
    rcases hcurrent with
      ⟨currentStart, hcurrentStart, currentFinish, hcurrentFinish,
        currentParserFinish, hcurrentParserFinish,
        currentParserTokensFinish, hcurrentParserTokensFinish,
        currentParserTasksFinish, hcurrentParserTasksFinish,
        currentParserTokensBoundary, hcurrentParserTokensBoundary,
        currentParserTokensCount, hcurrentParserTokensCount,
        currentParserTasksBoundary, hcurrentParserTasksBoundary,
        currentParserTasksCount, hcurrentParserTasksCount,
        currentOutputBoundary, hcurrentOutputBoundary,
        currentOutputCount, hcurrentOutputCount,
        currentParserTokensBoundarySize, hcurrentParserTokensBoundarySize,
        currentParserTasksBoundarySize, hcurrentParserTasksBoundarySize,
        currentOutputBoundarySize, hcurrentOutputBoundarySize, hinner⟩
    let witness : CompactFormulaTransformAdjacentCurrentStateWitness :=
      { coordinates := compactFormulaTransformStateRowCoordinatesOf
          currentStart currentFinish currentParserFinish
          currentParserTokensFinish currentParserTasksFinish
          currentParserTokensBoundary currentParserTokensCount
          currentParserTasksBoundary currentParserTasksCount
          currentOutputBoundary currentOutputCount
        size :=
          { parserTokensBoundarySize := currentParserTokensBoundarySize
            parserTasksBoundarySize := currentParserTasksBoundarySize
            outputBoundarySize := currentOutputBoundarySize } }
    refine ⟨witness, ?_, ?_⟩
    · intro index
      fin_cases index
      · exact hcurrentOutputBoundarySize
      · exact hcurrentParserTasksBoundarySize
      · exact hcurrentParserTokensBoundarySize
      · exact hcurrentOutputCount
      · exact hcurrentOutputBoundary
      · exact hcurrentParserTasksCount
      · exact hcurrentParserTasksBoundary
      · exact hcurrentParserTokensCount
      · exact hcurrentParserTokensBoundary
      · exact hcurrentParserTasksFinish
      · exact hcurrentParserTokensFinish
      · exact hcurrentParserFinish
      · exact hcurrentFinish
      · exact hcurrentStart
    · simpa [witness] using hinner
  let witness := Classical.choose hexists
  have hwitness := Classical.choose_spec hexists
  let values := adjacentCurrentBoundedWitnessValues witness
  have hvalues : ∀ index, values index ≤ valueBound := by
    simpa [values] using hwitness.1
  let innerCertificate :=
    compactFormulaTransformAdjacentNextBoundedExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size hwitness.2
  let terminal : HybridCertificate
      (compactFormulaTransformAdjacentCurrentBoundedRawTerminal
          tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound ⇜
        fun index => shortBinaryNumeralTerm (values index)) :=
    .cast (by
      dsimp only [values]
      exact
        (compactFormulaTransformAdjacentCurrentBoundedRawTerminal_alignment
          tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound witness).symm)
      innerCertificate
  rw [compactFormulaTransformAdjacentCurrentBoundedClosedFormula_alignment]
  exact buildExplicitBoundedWitnessHybridCertificate valueBound
    (compactFormulaTransformAdjacentCurrentBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound)
    values hvalues terminal

noncomputable def compileCompactFormulaTransformAdjacentCurrentBoundedExplicitHybridContext
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformAdjacentCurrentBoundedClosedFormula
          tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound).freeVariables
            zeroValuation)
      (compactFormulaTransformAdjacentCurrentBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :=
  (compactFormulaTransformAdjacentCurrentBoundedExplicitHybridCertificateOfGraph
    tokenTable width tokenCount stateBoundary stateCount rowIndex mode
    witnessStart witnessFinish witnessCount valueBound hcurrent).compile

noncomputable def compactFormulaTransformAdjacentCurrentBoundedExplicitStructuralResource
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactFormulaTransformAdjacentCurrentBoundedExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound hcurrent)

theorem compileCompactFormulaTransformAdjacentCurrentBoundedExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound) :
    (compileCompactFormulaTransformAdjacentCurrentBoundedExplicitHybridContext
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound hcurrent).payloadLength ≤
    compactFormulaTransformAdjacentCurrentBoundedExplicitStructuralResource
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound hcurrent := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactFormulaTransformAdjacentCurrentBoundedExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound hcurrent)

#print axioms compactFormulaTransformAdjacentCurrentBoundedClosedFormula_alignment
#print axioms compactFormulaTransformAdjacentCurrentBoundedRawTerminal_alignment
#print axioms compactFormulaTransformAdjacentCurrentBoundedExplicitHybridCertificateOfGraph
#print axioms compileCompactFormulaTransformAdjacentCurrentBoundedExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedExplicitHybridCertificate
