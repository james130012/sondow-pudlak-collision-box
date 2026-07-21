import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit certificate for the bounded formula-transform step witnesses

The nine local step coordinates are installed as bounded short-binary
witnesses. The terminal is the exact adjacent-row certificate together with
the two exact bounded status-validity certificates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedExplicitHybridCertificate

open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
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

private theorem emb_comp_subst_eq_subst_comp_emb
    {predicateArity targetArity : Nat}
    (sourceTerms : Fin predicateArity ->
      ArithmeticSemiterm Empty targetArity)
    (targetTerms : Fin predicateArity ->
      ArithmeticSemiterm Nat targetArity)
    (hterms : forall coordinate,
      (Rew.emb : Rew ℒₒᵣ Empty targetArity Nat targetArity)
          (sourceTerms coordinate) = targetTerms coordinate) :
    (Rew.emb : Rew ℒₒᵣ Empty targetArity Nat targetArity).comp
        (Rew.subst sourceTerms) =
      (Rew.subst targetTerms).comp
        (Rew.emb : Rew ℒₒᵣ Empty predicateArity Nat predicateArity) := by
  apply Rew.ext
  · intro coordinate
    simpa [Rew.comp_app, Rew.subst_bvar] using hterms coordinate
  · intro coordinate
    exact Empty.elim coordinate

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

private def boundedSourceTerms
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness) :
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

def compactFormulaTransformAdjacentStepWitnessBoundedClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentStepWitnessBoundedDef.val) ⇜
    boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
      rowIndex mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize

private def compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness) :
    ArithmeticSemiformula Nat 9 :=
  ((Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentStepRowDef.val) ⇜
    ![sourceSubstitutionLift 9 (shortBinaryNumeralTerm tokenTable),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm width),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm tokenCount),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm stateBoundary),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm stateCount),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm rowIndex),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm mode),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm witnessStart),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm witnessFinish),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm witnessCount),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm currentCoordinates.start),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm currentCoordinates.finish),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.parserFinish),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.parserTokensFinish),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.parserTasksFinish),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.parserTokensBoundary),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.parserTokensCount),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.parserTasksBoundary),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.parserTasksCount),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.outputBoundary),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.outputCount),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentSize.parserTokensBoundarySize),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentSize.parserTasksBoundarySize),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentSize.outputBoundarySize),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.start),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.finish),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.parserFinish),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.parserTokensFinish),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.parserTasksFinish),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.parserTokensBoundary),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.parserTokensCount),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.parserTasksBoundary),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.parserTasksCount),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.outputBoundary),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextCoordinates.outputCount),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextSize.parserTokensBoundarySize),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextSize.parserTasksBoundarySize),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm nextSize.outputBoundarySize),
      (#8 : ArithmeticSemiterm Nat 9), #7, #6, #5, #4, #3, #2, #1, #0]) ⋏
  (((Rewriting.emb (ξ := Nat)
      compactBinaryNatStatusValidBoundedDef.val) ⇜
    ![sourceSubstitutionLift 9 (shortBinaryNumeralTerm tokenTable),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm width),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm tokenCount),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.parserTasksFinish),
      sourceSubstitutionLift 9
        (shortBinaryNumeralTerm currentCoordinates.parserFinish),
      sourceSubstitutionLift 9 (shortBinaryNumeralTerm valueBound)]) ⋏
    ((Rewriting.emb (ξ := Nat)
        compactBinaryNatStatusValidBoundedDef.val) ⇜
      ![sourceSubstitutionLift 9 (shortBinaryNumeralTerm tokenTable),
        sourceSubstitutionLift 9 (shortBinaryNumeralTerm width),
        sourceSubstitutionLift 9 (shortBinaryNumeralTerm tokenCount),
        sourceSubstitutionLift 9
          (shortBinaryNumeralTerm nextCoordinates.parserTasksFinish),
        sourceSubstitutionLift 9
          (shortBinaryNumeralTerm nextCoordinates.parserFinish),
        sourceSubstitutionLift 9 (shortBinaryNumeralTerm valueBound)]))

private def compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal :
    ArithmeticSemiformula Nat 48 :=
  ((Rewriting.emb (ξ := Nat)
      compactFormulaTransformAdjacentStepRowDef.val) ⇜
    ![(#9 : ArithmeticSemiterm Nat 48), #10, #11, #12, #13, #14,
      #15, #16, #17, #18,
      #20, #21, #22, #23, #24, #25, #26, #27, #28, #29, #30,
      #31, #32, #33,
      #34, #35, #36, #37, #38, #39, #40, #41, #42, #43, #44,
      #45, #46, #47,
      #8, #7, #6, #5, #4, #3, #2, #1, #0]) ⋏
  (((Rewriting.emb (ξ := Nat)
      compactBinaryNatStatusValidBoundedDef.val) ⇜
    ![(#9 : ArithmeticSemiterm Nat 48), #10, #11, #24, #22, #19]) ⋏
    ((Rewriting.emb (ξ := Nat)
        compactBinaryNatStatusValidBoundedDef.val) ⇜
      ![(#9 : ArithmeticSemiterm Nat 48), #10, #11, #38, #36, #19]))

private def compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawTerminal :
    ArithmeticSemiformula Empty 48 :=
  (compactFormulaTransformAdjacentStepRowDef.val ⇜
    ![(#9 : ArithmeticSemiterm Empty 48), #10, #11, #12, #13, #14,
      #15, #16, #17, #18,
      #20, #21, #22, #23, #24, #25, #26, #27, #28, #29, #30,
      #31, #32, #33,
      #34, #35, #36, #37, #38, #39, #40, #41, #42, #43, #44,
      #45, #46, #47,
      #8, #7, #6, #5, #4, #3, #2, #1, #0]) ⋏
  ((compactBinaryNatStatusValidBoundedDef.val ⇜
    ![(#9 : ArithmeticSemiterm Empty 48), #10, #11, #24, #22, #19]) ⋏
    (compactBinaryNatStatusValidBoundedDef.val ⇜
      ![(#9 : ArithmeticSemiterm Empty 48), #10, #11, #38, #36, #19]))

private def compactFormulaTransformAdjacentStepWitnessBoundedSourceRawBody :
    ArithmeticSemiformula Nat 39 :=
  let body8 : ArithmeticSemiformula Nat 47 :=
    compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal.bexsLTSucc #18
  let body7 : ArithmeticSemiformula Nat 46 := body8.bexsLTSucc #17
  let body6 : ArithmeticSemiformula Nat 45 := body7.bexsLTSucc #16
  let body5 : ArithmeticSemiformula Nat 44 := body6.bexsLTSucc #15
  let body4 : ArithmeticSemiformula Nat 43 := body5.bexsLTSucc #14
  let body3 : ArithmeticSemiformula Nat 42 := body4.bexsLTSucc #13
  let body2 : ArithmeticSemiformula Nat 41 := body3.bexsLTSucc #12
  let body1 : ArithmeticSemiformula Nat 40 := body2.bexsLTSucc #11
  let body0 : ArithmeticSemiformula Nat 39 := body1.bexsLTSucc #10
  body0

private def compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawBody :
    ArithmeticSemiformula Empty 39 :=
  let body8 : ArithmeticSemiformula Empty 47 :=
    compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawTerminal.bexsLTSucc #18
  let body7 : ArithmeticSemiformula Empty 46 := body8.bexsLTSucc #17
  let body6 : ArithmeticSemiformula Empty 45 := body7.bexsLTSucc #16
  let body5 : ArithmeticSemiformula Empty 44 := body6.bexsLTSucc #15
  let body4 : ArithmeticSemiformula Empty 43 := body5.bexsLTSucc #14
  let body3 : ArithmeticSemiformula Empty 42 := body4.bexsLTSucc #13
  let body2 : ArithmeticSemiformula Empty 41 := body3.bexsLTSucc #12
  let body1 : ArithmeticSemiformula Empty 40 := body2.bexsLTSucc #11
  let body0 : ArithmeticSemiformula Empty 39 := body1.bexsLTSucc #10
  body0

private theorem compactFormulaTransformAdjacentStepWitnessBoundedDef_eq_emptyRawBody :
    compactFormulaTransformAdjacentStepWitnessBoundedDef.val =
      compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawBody := by
  unfold compactFormulaTransformAdjacentStepWitnessBoundedDef
  unfold compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawBody
  unfold compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawTerminal
  rfl

private theorem
    compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawTerminal_embedding :
    (Rew.emb : Rew ℒₒᵣ Empty 48 Nat 48) ▹
        compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawTerminal =
      compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal := by
  unfold compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawTerminal
  unfold compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal
  simp [rewriting_embeddedFormulaSubstitution]
  constructor
  · congr 1
    funext coordinate
    fin_cases coordinate <;> simp [Function.comp_apply]
  · constructor
    · congr 1
      funext coordinate
      fin_cases coordinate <;> simp [Function.comp_apply]
    · congr 1
      funext coordinate
      fin_cases coordinate <;> simp [Function.comp_apply]

private theorem
    compactFormulaTransformAdjacentStepWitnessBoundedDef_emb_eq_sourceRawBody :
    Rewriting.emb (ξ := Nat)
        compactFormulaTransformAdjacentStepWitnessBoundedDef.val =
      compactFormulaTransformAdjacentStepWitnessBoundedSourceRawBody := by
  rw [compactFormulaTransformAdjacentStepWitnessBoundedDef_eq_emptyRawBody]
  change (Rew.emb : Rew ℒₒᵣ Empty 39 Nat 39) ▹
      compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawBody = _
  unfold compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawBody
  unfold compactFormulaTransformAdjacentStepWitnessBoundedSourceRawBody
  simp [rewriting_bexsLTSucc,
    compactFormulaTransformAdjacentStepWitnessBoundedEmptyRawTerminal_embedding,
    Rew.q_bvar_zero, Rew.q_bvar_succ]

private theorem
    compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal_rewriting
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness) :
    sourceSubstitutionQpow
        (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
          rowIndex mode witnessStart witnessFinish witnessCount valueBound
          currentCoordinates currentSize nextCoordinates nextSize) 9 ▹
      compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal =
    compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize := by
  unfold compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal
  unfold compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
  simp [rewriting_embeddedFormulaSubstitution]
  repeat' apply And.intro
  all_goals
    congr 1
    funext coordinate
    fin_cases coordinate <;>
      simp [Function.comp_apply, boundedSourceTerms]
  all_goals
    rw [sourceSubstitutionQpow_bvar] <;>
      simp [sourceSubstitutionNormalizedBVarResult, boundedSourceTerms]

@[simp] private theorem
    compactFormulaTransformAdjacentStepWitnessBoundedSourceQpow_valueBound
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (depth : Nat) :
    sourceSubstitutionQpow
        (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
          rowIndex mode witnessStart witnessFinish witnessCount valueBound
          currentCoordinates currentSize nextCoordinates nextSize) depth
        (#(⟨depth + 10, by omega⟩ : Fin (39 + depth)) :
          ArithmeticSemiterm Nat (39 + depth)) =
      sourceSubstitutionLift depth (shortBinaryNumeralTerm valueBound) := by
  simpa [boundedSourceTerms] using
    (sourceSubstitutionQpow_shiftedBVar
      (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
        rowIndex mode witnessStart witnessFinish witnessCount valueBound
        currentCoordinates currentSize nextCoordinates nextSize)
      depth (⟨10, by omega⟩ : Fin 39))

private theorem
    compactFormulaTransformAdjacentStepWitnessBoundedSourceRawBody_alignment
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness) :
    Rew.subst
        (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
          rowIndex mode witnessStart witnessFinish witnessCount valueBound
          currentCoordinates currentSize nextCoordinates nextSize) ▹
      compactFormulaTransformAdjacentStepWitnessBoundedSourceRawBody =
    explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 9
      (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize) := by
  change sourceSubstitutionQpow
      (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
        rowIndex mode witnessStart witnessFinish witnessCount valueBound
        currentCoordinates currentSize nextCoordinates nextSize) 0 ▹
      compactFormulaTransformAdjacentStepWitnessBoundedSourceRawBody = _
  unfold compactFormulaTransformAdjacentStepWitnessBoundedSourceRawBody
  simp only [sourceSubstitutionQpow_bexsLTSucc]
  rw [compactFormulaTransformAdjacentStepWitnessBoundedSourceRawTerminal_rewriting]
  simp_rw [sourceSubstitutionQpow_bvar]
  simp [sourceSubstitutionNormalizedBVarResult, boundedSourceTerms]
  rfl

theorem compactFormulaTransformAdjacentStepWitnessBoundedClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness) :
    compactFormulaTransformAdjacentStepWitnessBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 9
        (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
          tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize nextCoordinates nextSize) := by
  unfold compactFormulaTransformAdjacentStepWitnessBoundedClosedFormula
  rw [compactFormulaTransformAdjacentStepWitnessBoundedDef_emb_eq_sourceRawBody]
  exact
    compactFormulaTransformAdjacentStepWitnessBoundedSourceRawBody_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize

private def boundedWitnessValues
    (row : CompactFormulaTransformAdjacentStepRow) : Fin 9 -> Nat :=
  ![row.mappedHead, row.consumedCount,
    row.stepWitness.slot6, row.stepWitness.slot5, row.stepWitness.slot4,
    row.stepWitness.slot3, row.stepWitness.slot2, row.stepWitness.slot1,
    row.stepWitness.slot0]

private structure CompactFormulaTransformAdjacentStepLocalWitness where
  stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates
  consumedCount : Nat
  mappedHead : Nat

private def compactFormulaTransformAdjacentStepRowOfLocalWitness
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (witness : CompactFormulaTransformAdjacentStepLocalWitness) :
    CompactFormulaTransformAdjacentStepRow :=
  { currentCoordinates := currentCoordinates
    currentSize := currentSize
    nextCoordinates := nextCoordinates
    nextSize := nextSize
    stepWitness := witness.stepWitness
    consumedCount := witness.consumedCount
    mappedHead := witness.mappedHead }

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

private theorem substitute_sourceSubstitutionLift9
    (values : Fin 9 -> ValuationTerm) (term : ValuationTerm) :
    Rew.subst values (sourceSubstitutionLift 9 term) = term := by
  simpa only using
    (substitute_sourceSubstitutionLift (depth := 9) values term)

private theorem
    compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal_alignment
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (row : CompactFormulaTransformAdjacentStepRow) :
    compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound
        row.currentCoordinates row.currentSize row.nextCoordinates row.nextSize ⇜
      (fun index => shortBinaryNumeralTerm (boundedWitnessValues row index)) =
    compactFormulaTransformAdjacentStepRowClosedFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount row ⋏
      (compactBinaryNatStatusValidBoundedClosedFormula
          tokenTable width tokenCount
          row.currentCoordinates.parserTasksFinish
          row.currentCoordinates.parserFinish valueBound ⋏
        compactBinaryNatStatusValidBoundedClosedFormula
          tokenTable width tokenCount
          row.nextCoordinates.parserTasksFinish
          row.nextCoordinates.parserFinish valueBound) := by
  change Rew.subst (fun index => shortBinaryNumeralTerm
      (boundedWitnessValues row index)) ▹
    compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound
      row.currentCoordinates row.currentSize row.nextCoordinates row.nextSize = _
  unfold compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
  unfold compactFormulaTransformAdjacentStepRowClosedFormula
  unfold compactBinaryNatStatusValidBoundedClosedFormula
  simp [rewriting_embeddedFormulaSubstitution]
  repeat' apply And.intro
  all_goals
    congr 1
    funext coordinate
    fin_cases coordinate <;>
      simp [Function.comp_apply, boundedWitnessValues, Rew.subst_bvar,
        substitute_sourceSubstitutionLift9]

noncomputable def
    compactFormulaTransformAdjacentStepWitnessBoundedExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize) :
    HybridCertificate
      (compactFormulaTransformAdjacentStepWitnessBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize) := by
  have hexists :
      ∃ witness : CompactFormulaTransformAdjacentStepLocalWitness,
        (∀ index,
          boundedWitnessValues
            (compactFormulaTransformAdjacentStepRowOfLocalWitness
              currentCoordinates currentSize nextCoordinates nextSize witness)
            index ≤ valueBound) ∧
        CompactFormulaTransformAdjacentStepRowGraph
          tokenTable width tokenCount stateBoundary stateCount rowIndex mode
            witnessStart witnessFinish witnessCount
            (compactFormulaTransformAdjacentStepRowOfLocalWitness
              currentCoordinates currentSize nextCoordinates nextSize witness) ∧
        CompactBinaryNatStatusValidBounded tokenTable width tokenCount
          currentCoordinates.parserTasksFinish currentCoordinates.parserFinish
            valueBound ∧
        CompactBinaryNatStatusValidBounded tokenTable width tokenCount
          nextCoordinates.parserTasksFinish nextCoordinates.parserFinish
            valueBound := by
    rcases hbounded with
      ⟨slot0, hslot0, slot1, hslot1, slot2, hslot2, slot3, hslot3,
        slot4, hslot4, slot5, hslot5, slot6, hslot6,
        consumedCount, hconsumedCount, mappedHead, hmappedHead,
        hrow, hcurrentStatus, hnextStatus⟩
    let witness : CompactFormulaTransformAdjacentStepLocalWitness :=
      { stepWitness :=
          { slot0 := slot0
            slot1 := slot1
            slot2 := slot2
            slot3 := slot3
            slot4 := slot4
            slot5 := slot5
            slot6 := slot6 }
        consumedCount := consumedCount
        mappedHead := mappedHead }
    refine ⟨witness, ?_, ?_, hcurrentStatus, hnextStatus⟩
    intro index
    fin_cases index
    · exact hmappedHead
    · exact hconsumedCount
    · exact hslot6
    · exact hslot5
    · exact hslot4
    · exact hslot3
    · exact hslot2
    · exact hslot1
    · exact hslot0
    · simpa [witness, compactFormulaTransformAdjacentStepRowOfLocalWitness] using hrow
  let witness := Classical.choose hexists
  have hrowData := Classical.choose_spec hexists
  let row := compactFormulaTransformAdjacentStepRowOfLocalWitness
    currentCoordinates currentSize nextCoordinates nextSize witness
  let values := boundedWitnessValues row
  have hvalues : ∀ index, values index ≤ valueBound := by
    simpa [values, row] using hrowData.1
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFormulaTransformAdjacentStepRowExplicitHybridCertificateOfGraph
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount row hrowData.2.1)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactBinaryNatStatusValidBoundedExplicitHybridCertificateOfGraph
          tokenTable width tokenCount
            currentCoordinates.parserTasksFinish
            currentCoordinates.parserFinish valueBound hrowData.2.2.1)
        (compactBinaryNatStatusValidBoundedExplicitHybridCertificateOfGraph
          tokenTable width tokenCount
            nextCoordinates.parserTasksFinish
            nextCoordinates.parserFinish valueBound hrowData.2.2.2))
  let terminal : HybridCertificate
      (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
          tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize nextCoordinates nextSize ⇜
        fun index => shortBinaryNumeralTerm (values index)) :=
    .cast (by
      dsimp only [values, row,
        compactFormulaTransformAdjacentStepRowOfLocalWitness]
      exact
        (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal_alignment
          tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound row).symm)
      terminalParts
  rw [compactFormulaTransformAdjacentStepWitnessBoundedClosedFormula_alignment]
  exact buildExplicitBoundedWitnessHybridCertificate valueBound
    (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize)
    values hvalues terminal

noncomputable def
    compileCompactFormulaTransformAdjacentStepWitnessBoundedExplicitHybridContext
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformAdjacentStepWitnessBoundedClosedFormula
          tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize nextCoordinates nextSize).freeVariables zeroValuation)
      (compactFormulaTransformAdjacentStepWitnessBoundedClosedFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize) :=
  (compactFormulaTransformAdjacentStepWitnessBoundedExplicitHybridCertificateOfGraph
    tokenTable width tokenCount stateBoundary stateCount rowIndex mode
    witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize nextCoordinates nextSize hbounded).compile

noncomputable def
    compactFormulaTransformAdjacentStepWitnessBoundedExplicitStructuralResource
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactFormulaTransformAdjacentStepWitnessBoundedExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize hbounded)

theorem
    compileCompactFormulaTransformAdjacentStepWitnessBoundedExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize) :
    (compileCompactFormulaTransformAdjacentStepWitnessBoundedExplicitHybridContext
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize hbounded).payloadLength ≤
    compactFormulaTransformAdjacentStepWitnessBoundedExplicitStructuralResource
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize hbounded := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactFormulaTransformAdjacentStepWitnessBoundedExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize hbounded)

#print axioms
  compactFormulaTransformAdjacentStepWitnessBoundedClosedFormula_alignment
#print axioms
  compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal_alignment
#print axioms
  compactFormulaTransformAdjacentStepWitnessBoundedExplicitHybridCertificateOfGraph
#print axioms
  compileCompactFormulaTransformAdjacentStepWitnessBoundedExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedExplicitHybridCertificate
