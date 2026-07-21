import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedFormula
import integration.FoundationCompactNumericListedDirectParserInitialFinalExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

/-!
# Explicit hybrid certificate for bounded parser endpoints

The original twenty-three bounded endpoint coordinates are installed directly.
The source formula, its binder stack, and the combined initial/final terminal
are connected by checked syntactic equalities.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedExplicitHybridCertificate

open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectParserInitialFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

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
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat) :
    Fin 14 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm stateBoundary,
    shortBinaryNumeralTerm stateCount,
    shortBinaryNumeralTerm fuel,
    shortBinaryNumeralTerm inputBoundary,
    shortBinaryNumeralTerm inputCount,
    shortBinaryNumeralTerm expectedBoundary,
    shortBinaryNumeralTerm expectedCount,
    shortBinaryNumeralTerm taskKind,
    shortBinaryNumeralTerm taskBinderArity,
    shortBinaryNumeralTerm taskRepeatCount,
    shortBinaryNumeralTerm valueBound]

def compactParserInitialFinalBoundedClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactParserInitialFinalBoundedDef.val) ⇜
    boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount taskKind
      taskBinderArity taskRepeatCount valueBound

private def compactParserInitialFinalBoundedRawTerminal
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat) :
    ArithmeticSemiformula Nat 23 :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserInitialFinalRowsDef.val) ⇜
    ![sourceSubstitutionLift 23 (shortBinaryNumeralTerm tokenTable),
      sourceSubstitutionLift 23 (shortBinaryNumeralTerm width),
      sourceSubstitutionLift 23 (shortBinaryNumeralTerm tokenCount),
      sourceSubstitutionLift 23 (shortBinaryNumeralTerm stateBoundary),
      sourceSubstitutionLift 23 (shortBinaryNumeralTerm stateCount),
      sourceSubstitutionLift 23 (shortBinaryNumeralTerm fuel),
      sourceSubstitutionLift 23 (shortBinaryNumeralTerm inputBoundary),
      sourceSubstitutionLift 23 (shortBinaryNumeralTerm inputCount),
      sourceSubstitutionLift 23 (shortBinaryNumeralTerm expectedBoundary),
      sourceSubstitutionLift 23 (shortBinaryNumeralTerm expectedCount),
      sourceSubstitutionLift 23 (shortBinaryNumeralTerm taskKind),
      sourceSubstitutionLift 23 (shortBinaryNumeralTerm taskBinderArity),
      sourceSubstitutionLift 23 (shortBinaryNumeralTerm taskRepeatCount),
      (#22 : ArithmeticSemiterm Nat 23), #21, #20, #19, #18, #17, #16,
      #15, #14, #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2,
      #1, #0]

private def compactParserInitialFinalBoundedSourceRawTerminal :
    ArithmeticSemiformula Nat 37 :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserInitialFinalRowsDef.val) ⇜
    ![(#23 : ArithmeticSemiterm Nat 37), #24, #25, #26, #27, #28,
      #29, #30, #31, #32, #33, #34, #35,
      #22, #21, #20, #19, #18, #17, #16, #15, #14, #13, #12, #11,
      #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]

private def compactParserInitialFinalBoundedEmptyRawTerminal :
    ArithmeticSemiformula Empty 37 :=
  compactUnifiedParserInitialFinalRowsDef.val ⇜
    ![(#23 : ArithmeticSemiterm Empty 37), #24, #25, #26, #27, #28,
      #29, #30, #31, #32, #33, #34, #35,
      #22, #21, #20, #19, #18, #17, #16, #15, #14, #13, #12, #11,
      #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]

private def compactParserInitialFinalBoundedSourceRawBody :
    ArithmeticSemiformula Nat 14 :=
  let body22 : ArithmeticSemiformula Nat 36 :=
    compactParserInitialFinalBoundedSourceRawTerminal.bexsLTSucc #35
  let body21 : ArithmeticSemiformula Nat 35 := body22.bexsLTSucc #34
  let body20 : ArithmeticSemiformula Nat 34 := body21.bexsLTSucc #33
  let body19 : ArithmeticSemiformula Nat 33 := body20.bexsLTSucc #32
  let body18 : ArithmeticSemiformula Nat 32 := body19.bexsLTSucc #31
  let body17 : ArithmeticSemiformula Nat 31 := body18.bexsLTSucc #30
  let body16 : ArithmeticSemiformula Nat 30 := body17.bexsLTSucc #29
  let body15 : ArithmeticSemiformula Nat 29 := body16.bexsLTSucc #28
  let body14 : ArithmeticSemiformula Nat 28 := body15.bexsLTSucc #27
  let body13 : ArithmeticSemiformula Nat 27 := body14.bexsLTSucc #26
  let body12 : ArithmeticSemiformula Nat 26 := body13.bexsLTSucc #25
  let body11 : ArithmeticSemiformula Nat 25 := body12.bexsLTSucc #24
  let body10 : ArithmeticSemiformula Nat 24 := body11.bexsLTSucc #23
  let body9 : ArithmeticSemiformula Nat 23 := body10.bexsLTSucc #22
  let body8 : ArithmeticSemiformula Nat 22 := body9.bexsLTSucc #21
  let body7 : ArithmeticSemiformula Nat 21 := body8.bexsLTSucc #20
  let body6 : ArithmeticSemiformula Nat 20 := body7.bexsLTSucc #19
  let body5 : ArithmeticSemiformula Nat 19 := body6.bexsLTSucc #18
  let body4 : ArithmeticSemiformula Nat 18 := body5.bexsLTSucc #17
  let body3 : ArithmeticSemiformula Nat 17 := body4.bexsLTSucc #16
  let body2 : ArithmeticSemiformula Nat 16 := body3.bexsLTSucc #15
  let body1 : ArithmeticSemiformula Nat 15 := body2.bexsLTSucc #14
  let body0 : ArithmeticSemiformula Nat 14 := body1.bexsLTSucc #13
  body0

private def compactParserInitialFinalBoundedEmptyRawBody :
    ArithmeticSemiformula Empty 14 :=
  let body22 : ArithmeticSemiformula Empty 36 :=
    compactParserInitialFinalBoundedEmptyRawTerminal.bexsLTSucc #35
  let body21 : ArithmeticSemiformula Empty 35 := body22.bexsLTSucc #34
  let body20 : ArithmeticSemiformula Empty 34 := body21.bexsLTSucc #33
  let body19 : ArithmeticSemiformula Empty 33 := body20.bexsLTSucc #32
  let body18 : ArithmeticSemiformula Empty 32 := body19.bexsLTSucc #31
  let body17 : ArithmeticSemiformula Empty 31 := body18.bexsLTSucc #30
  let body16 : ArithmeticSemiformula Empty 30 := body17.bexsLTSucc #29
  let body15 : ArithmeticSemiformula Empty 29 := body16.bexsLTSucc #28
  let body14 : ArithmeticSemiformula Empty 28 := body15.bexsLTSucc #27
  let body13 : ArithmeticSemiformula Empty 27 := body14.bexsLTSucc #26
  let body12 : ArithmeticSemiformula Empty 26 := body13.bexsLTSucc #25
  let body11 : ArithmeticSemiformula Empty 25 := body12.bexsLTSucc #24
  let body10 : ArithmeticSemiformula Empty 24 := body11.bexsLTSucc #23
  let body9 : ArithmeticSemiformula Empty 23 := body10.bexsLTSucc #22
  let body8 : ArithmeticSemiformula Empty 22 := body9.bexsLTSucc #21
  let body7 : ArithmeticSemiformula Empty 21 := body8.bexsLTSucc #20
  let body6 : ArithmeticSemiformula Empty 20 := body7.bexsLTSucc #19
  let body5 : ArithmeticSemiformula Empty 19 := body6.bexsLTSucc #18
  let body4 : ArithmeticSemiformula Empty 18 := body5.bexsLTSucc #17
  let body3 : ArithmeticSemiformula Empty 17 := body4.bexsLTSucc #16
  let body2 : ArithmeticSemiformula Empty 16 := body3.bexsLTSucc #15
  let body1 : ArithmeticSemiformula Empty 15 := body2.bexsLTSucc #14
  let body0 : ArithmeticSemiformula Empty 14 := body1.bexsLTSucc #13
  body0

set_option maxRecDepth 8192 in
private theorem compactParserInitialFinalBoundedDef_eq_emptyRawBody :
    compactParserInitialFinalBoundedDef.val =
      compactParserInitialFinalBoundedEmptyRawBody := by
  unfold compactParserInitialFinalBoundedDef
  unfold compactParserInitialFinalBoundedEmptyRawBody
  unfold compactParserInitialFinalBoundedEmptyRawTerminal
  rfl

private theorem compactParserInitialFinalBoundedEmptyRawTerminal_embedding :
    (Rew.emb : Rew ℒₒᵣ Empty 37 Nat 37) ▹
        compactParserInitialFinalBoundedEmptyRawTerminal =
      compactParserInitialFinalBoundedSourceRawTerminal := by
  have hterminal :
      (Rew.emb : Rew ℒₒᵣ Empty 37 Nat 37).comp
          (Rew.subst
            ![(#23 : ArithmeticSemiterm Empty 37), #24, #25, #26, #27,
              #28, #29, #30, #31, #32, #33, #34, #35,
              #22, #21, #20, #19, #18, #17, #16, #15, #14, #13,
              #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1,
              #0]) =
        (Rew.subst
          ![(#23 : ArithmeticSemiterm Nat 37), #24, #25, #26, #27, #28,
            #29, #30, #31, #32, #33, #34, #35,
            #22, #21, #20, #19, #18, #17, #16, #15, #14, #13, #12,
            #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]).comp
          (Rew.emb : Rew ℒₒᵣ Empty 36 Nat 36) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  unfold compactParserInitialFinalBoundedEmptyRawTerminal
  unfold compactParserInitialFinalBoundedSourceRawTerminal
  calc
    (Rew.emb : Rew ℒₒᵣ Empty 37 Nat 37) ▹
        (compactUnifiedParserInitialFinalRowsDef.val ⇜
          ![(#23 : ArithmeticSemiterm Empty 37), #24, #25, #26, #27,
            #28, #29, #30, #31, #32, #33, #34, #35,
            #22, #21, #20, #19, #18, #17, #16, #15, #14, #13,
            #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1,
            #0]) =
        ((Rew.emb : Rew ℒₒᵣ Empty 37 Nat 37).comp
          (Rew.subst
            ![(#23 : ArithmeticSemiterm Empty 37), #24, #25, #26, #27,
              #28, #29, #30, #31, #32, #33, #34, #35,
              #22, #21, #20, #19, #18, #17, #16, #15, #14, #13,
              #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1,
              #0])) ▹ compactUnifiedParserInitialFinalRowsDef.val := by
          rw [TransitiveRewriting.comp_app]
    _ = ((Rew.subst
          ![(#23 : ArithmeticSemiterm Nat 37), #24, #25, #26, #27, #28,
            #29, #30, #31, #32, #33, #34, #35,
            #22, #21, #20, #19, #18, #17, #16, #15, #14, #13, #12,
            #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]).comp
          (Rew.emb : Rew ℒₒᵣ Empty 36 Nat 36)) ▹
        compactUnifiedParserInitialFinalRowsDef.val := by rw [hterminal]
    _ = (Rewriting.emb (ξ := Nat)
          compactUnifiedParserInitialFinalRowsDef.val) ⇜
        ![(#23 : ArithmeticSemiterm Nat 37), #24, #25, #26, #27, #28,
          #29, #30, #31, #32, #33, #34, #35,
          #22, #21, #20, #19, #18, #17, #16, #15, #14, #13, #12,
          #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0] := by
        rw [TransitiveRewriting.comp_app]

private theorem compactParserInitialFinalBoundedEmbeddingQpow_eq_emb :
    rewritingQpow
        (Rew.emb : Rew ℒₒᵣ Empty 14 Nat 14) 23 =
      (Rew.emb : Rew ℒₒᵣ Empty 37 Nat 37) := by
  apply Rew.ext
  · intro coordinate
    simp [rewritingQpow, Rew.q_bvar_zero, Rew.q_bvar_succ]
  · intro coordinate
    exact Empty.elim coordinate

private theorem compactParserInitialFinalBoundedDef_emb_eq_sourceRawBody :
    Rewriting.emb (ξ := Nat) compactParserInitialFinalBoundedDef.val =
      compactParserInitialFinalBoundedSourceRawBody := by
  rw [compactParserInitialFinalBoundedDef_eq_emptyRawBody]
  change (Rew.emb : Rew ℒₒᵣ Empty 14 Nat 14) ▹
      compactParserInitialFinalBoundedEmptyRawBody = _
  unfold compactParserInitialFinalBoundedEmptyRawBody
  unfold compactParserInitialFinalBoundedSourceRawBody
  simp [rewriting_bexsLTSucc,
    compactParserInitialFinalBoundedEmptyRawTerminal_embedding,
    Rew.q_bvar_zero, Rew.q_bvar_succ]

set_option maxHeartbeats 1200000 in
private theorem compactParserInitialFinalBoundedSourceRawTerminal_rewriting
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat) :
    sourceSubstitutionQpow
        (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
          fuel inputBoundary inputCount expectedBoundary expectedCount taskKind
          taskBinderArity taskRepeatCount valueBound) 23 ▹
      compactParserInitialFinalBoundedSourceRawTerminal =
    compactParserInitialFinalBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount := by
  unfold compactParserInitialFinalBoundedSourceRawTerminal
  unfold compactParserInitialFinalBoundedRawTerminal
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply, boundedSourceTerms]
  all_goals
    rw [sourceSubstitutionQpow_bvar] <;>
    simp [sourceSubstitutionNormalizedBVarResult]

@[simp] private theorem compactParserInitialFinalBoundedSourceQpow_valueBound
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound depth : Nat) :
    sourceSubstitutionQpow
        (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
          fuel inputBoundary inputCount expectedBoundary expectedCount taskKind
          taskBinderArity taskRepeatCount valueBound) depth
        (#(⟨depth + 13, by omega⟩ : Fin (14 + depth)) :
          ArithmeticSemiterm Nat (14 + depth)) =
      sourceSubstitutionLift depth (shortBinaryNumeralTerm valueBound) := by
  simpa [boundedSourceTerms] using
    (sourceSubstitutionQpow_shiftedBVar
      (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
        fuel inputBoundary inputCount expectedBoundary expectedCount taskKind
        taskBinderArity taskRepeatCount valueBound)
      depth (⟨13, by omega⟩ : Fin 14))

private theorem compactParserInitialFinalBoundedSourceRawBody_alignment
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat) :
    Rew.subst
        (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
          fuel inputBoundary inputCount expectedBoundary expectedCount taskKind
          taskBinderArity taskRepeatCount valueBound) ▹
      compactParserInitialFinalBoundedSourceRawBody =
    explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 23
      (compactParserInitialFinalBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount) := by
  change sourceSubstitutionQpow
      (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
        fuel inputBoundary inputCount expectedBoundary expectedCount taskKind
        taskBinderArity taskRepeatCount valueBound) 0 ▹
      compactParserInitialFinalBoundedSourceRawBody = _
  unfold compactParserInitialFinalBoundedSourceRawBody
  simp only [sourceSubstitutionQpow_bexsLTSucc]
  rw [compactParserInitialFinalBoundedSourceRawTerminal_rewriting]
  simp_rw [sourceSubstitutionQpow_bvar]
  simp [sourceSubstitutionNormalizedBVarResult, boundedSourceTerms]
  rfl

theorem compactParserInitialFinalBoundedClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat) :
    compactParserInitialFinalBoundedClosedFormula tokenTable width tokenCount
        stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
        expectedCount taskKind taskBinderArity taskRepeatCount valueBound =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 23
        (compactParserInitialFinalBoundedRawTerminal
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedBoundary expectedCount taskKind
          taskBinderArity taskRepeatCount) := by
  unfold compactParserInitialFinalBoundedClosedFormula
  rw [compactParserInitialFinalBoundedDef_emb_eq_sourceRawBody]
  exact compactParserInitialFinalBoundedSourceRawBody_alignment
    tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
    inputCount expectedBoundary expectedCount taskKind taskBinderArity
    taskRepeatCount valueBound

private def boundedWitnessValues
    (witness : CompactParserInitialFinalWitnessCoordinates) : Fin 23 -> Nat :=
  ![witness.outputBoundarySize,
    witness.outputBoundary,
    witness.outputStart,
    witness.finalSizeWitness.tasksBoundarySize,
    witness.finalSizeWitness.tokensBoundarySize,
    witness.finalCoordinates.tasksCount,
    witness.finalCoordinates.tasksBoundary,
    witness.finalCoordinates.tokensCount,
    witness.finalCoordinates.tokensBoundary,
    witness.finalCoordinates.tasksFinish,
    witness.finalCoordinates.tokensFinish,
    witness.finalCoordinates.finish,
    witness.finalCoordinates.start,
    witness.initialSizeWitness.tasksBoundarySize,
    witness.initialSizeWitness.tokensBoundarySize,
    witness.initialCoordinates.tasksCount,
    witness.initialCoordinates.tasksBoundary,
    witness.initialCoordinates.tokensCount,
    witness.initialCoordinates.tokensBoundary,
    witness.initialCoordinates.tasksFinish,
    witness.initialCoordinates.tokensFinish,
    witness.initialCoordinates.finish,
    witness.initialCoordinates.start]

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

private theorem substitute_sourceSubstitutionLift23
    (values : Fin 23 -> ValuationTerm) (term : ValuationTerm) :
    Rew.subst values (sourceSubstitutionLift 23 term) = term := by
  simpa only using
    (substitute_sourceSubstitutionLift (depth := 23) values term)

private theorem compactParserInitialFinalBoundedRawTerminal_alignment
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    compactParserInitialFinalBoundedRawTerminal tokenTable width tokenCount
        stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
        expectedCount taskKind taskBinderArity taskRepeatCount ⇜
      (fun index => shortBinaryNumeralTerm
        (boundedWitnessValues witness index)) =
    compactUnifiedParserInitialFinalRowsClosedFormula tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount witness := by
  change Rew.subst (fun index => shortBinaryNumeralTerm
      (boundedWitnessValues witness index)) ▹
    compactParserInitialFinalBoundedRawTerminal tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount = _
  unfold compactParserInitialFinalBoundedRawTerminal
  unfold compactUnifiedParserInitialFinalRowsClosedFormula
  rw [rewriting_embeddedFormulaSubstitution]
  unfold boundedWitnessValues
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply, Rew.comp_app, Rew.subst_bvar]
  all_goals
    rw [substitute_sourceSubstitutionLift23]

noncomputable def compactParserInitialFinalBoundedExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat)
    (hbounded : CompactParserInitialFinalBounded tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount valueBound) :
    HybridCertificate
      (compactParserInitialFinalBoundedClosedFormula tokenTable width tokenCount
        stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
        expectedCount taskKind taskBinderArity taskRepeatCount valueBound) := by
  have hexists :
      ∃ witness : CompactParserInitialFinalWitnessCoordinates,
        (∀ index, boundedWitnessValues witness index ≤ valueBound) ∧
        CompactUnifiedParserInitialFinalRows
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedBoundary expectedCount taskKind
          taskBinderArity taskRepeatCount witness := by
    rcases hbounded with
    ⟨initialStart, hinitialStart, initialFinish, hinitialFinish,
      initialTokensFinish, hinitialTokensFinish,
      initialTasksFinish, hinitialTasksFinish,
      initialTokensBoundary, hinitialTokensBoundary,
      initialTokensCount, hinitialTokensCount,
      initialTasksBoundary, hinitialTasksBoundary,
      initialTasksCount, hinitialTasksCount,
      initialTokensBoundarySize, hinitialTokensBoundarySize,
      initialTasksBoundarySize, hinitialTasksBoundarySize,
      finalStart, hfinalStart, finalFinish, hfinalFinish,
      finalTokensFinish, hfinalTokensFinish,
      finalTasksFinish, hfinalTasksFinish,
      finalTokensBoundary, hfinalTokensBoundary,
      finalTokensCount, hfinalTokensCount,
      finalTasksBoundary, hfinalTasksBoundary,
      finalTasksCount, hfinalTasksCount,
      finalTokensBoundarySize, hfinalTokensBoundarySize,
      finalTasksBoundarySize, hfinalTasksBoundarySize,
      outputStart, houtputStart, outputBoundary, houtputBoundary,
        outputBoundarySize, houtputBoundarySize, hrelation⟩
    let witness := compactParserInitialFinalWitnessOfValues
      initialStart initialFinish initialTokensFinish initialTasksFinish
      initialTokensBoundary initialTokensCount initialTasksBoundary
      initialTasksCount initialTokensBoundarySize initialTasksBoundarySize
      finalStart finalFinish finalTokensFinish finalTasksFinish
      finalTokensBoundary finalTokensCount finalTasksBoundary finalTasksCount
      finalTokensBoundarySize finalTasksBoundarySize outputStart outputBoundary
      outputBoundarySize
    refine ⟨witness, ?_, ?_⟩
    · intro index
      fin_cases index
      · exact houtputBoundarySize
      · exact houtputBoundary
      · exact houtputStart
      · exact hfinalTasksBoundarySize
      · exact hfinalTokensBoundarySize
      · exact hfinalTasksCount
      · exact hfinalTasksBoundary
      · exact hfinalTokensCount
      · exact hfinalTokensBoundary
      · exact hfinalTasksFinish
      · exact hfinalTokensFinish
      · exact hfinalFinish
      · exact hfinalStart
      · exact hinitialTasksBoundarySize
      · exact hinitialTokensBoundarySize
      · exact hinitialTasksCount
      · exact hinitialTasksBoundary
      · exact hinitialTokensCount
      · exact hinitialTokensBoundary
      · exact hinitialTasksFinish
      · exact hinitialTokensFinish
      · exact hinitialFinish
      · exact hinitialStart
    · simpa [witness, compactParserInitialFinalWitnessOfValues,
        compactUnifiedParserStateRowCoordinatesOf] using hrelation
  let witness := Classical.choose hexists
  have hwitness := Classical.choose_spec hexists
  let values := boundedWitnessValues witness
  let endpointCertificate :=
    compactUnifiedParserInitialFinalRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount witness hwitness.2
  let terminal : HybridCertificate
      (compactParserInitialFinalBoundedRawTerminal tokenTable width tokenCount
          stateBoundary stateCount fuel inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount ⇜
        fun index => shortBinaryNumeralTerm (values index)) :=
    .cast (by
      dsimp only [values]
      exact
        (compactParserInitialFinalBoundedRawTerminal_alignment tokenTable width
          tokenCount stateBoundary stateCount fuel inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount witness).symm) endpointCertificate
  rw [compactParserInitialFinalBoundedClosedFormula_alignment]
  exact buildExplicitBoundedWitnessHybridCertificate valueBound
    (compactParserInitialFinalBoundedRawTerminal tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount)
    values (by simpa [values] using hwitness.1) terminal

#print axioms compactParserInitialFinalBoundedClosedFormula_alignment
#print axioms compactParserInitialFinalBoundedRawTerminal_alignment
#print axioms compactParserInitialFinalBoundedExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectParserInitialFinalBoundedExplicitHybridCertificate
