import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
import integration.FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity27

/-! # Exact terminal syntax for the twenty-seven bounded adjacent-row witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedWitnessSyntax

open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

def compactParserSyntaxAdjacentRowBoundedClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount index valueBound :
      Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactParserSyntaxAdjacentRowBoundedDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm stateBoundary,
      shortBinaryNumeralTerm stateCount,
      shortBinaryNumeralTerm index,
      shortBinaryNumeralTerm valueBound]

def compactParserSyntaxAdjacentRowBoundedRawTerminal
    (tokenTable width tokenCount stateBoundary stateCount index valueBound :
      Nat) : ArithmeticSemiformula Nat 27 :=
  ((Rewriting.emb (ξ := Nat)
      compactParserSyntaxAdjacentStepRowDef.val) ⇜
    ![sourceSubstitutionLift 27 (shortBinaryNumeralTerm tokenTable),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm width),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm tokenCount),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm stateBoundary),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm stateCount),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm index),
      (#26 : ArithmeticSemiterm Nat 27), #25, #24, #23, #22, #21, #20,
      #19, #18, #17, #16, #15, #14, #13, #12, #11, #10, #9, #8, #7,
      #6, #5, #4, #3, #2, #1, #0]) ⋏
  (((Rewriting.emb (ξ := Nat)
      compactBinaryNatStatusValidBoundedDef.val) ⇜
    ![sourceSubstitutionLift 27 (shortBinaryNumeralTerm tokenTable),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm width),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm tokenCount),
      (#23 : ArithmeticSemiterm Nat 27), #25,
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm valueBound)]) ⋏
    ((Rewriting.emb (ξ := Nat)
        compactBinaryNatStatusValidBoundedDef.val) ⇜
      ![sourceSubstitutionLift 27 (shortBinaryNumeralTerm tokenTable),
        sourceSubstitutionLift 27 (shortBinaryNumeralTerm width),
        sourceSubstitutionLift 27 (shortBinaryNumeralTerm tokenCount),
        (#13 : ArithmeticSemiterm Nat 27), #15,
        sourceSubstitutionLift 27 (shortBinaryNumeralTerm valueBound)]))

def compactParserSyntaxAdjacentRowBoundedWitnessValues
    (row : CompactParserSyntaxAdjacentStepRow) : Fin 27 -> Nat :=
  ![row.stepWitness.slot6, row.stepWitness.slot5, row.stepWitness.slot4,
    row.stepWitness.slot3, row.stepWitness.slot2, row.stepWitness.slot1,
    row.stepWitness.slot0,
    row.nextSize.tasksBoundarySize, row.nextSize.tokensBoundarySize,
    row.nextCoordinates.tasksCount, row.nextCoordinates.tasksBoundary,
    row.nextCoordinates.tokensCount, row.nextCoordinates.tokensBoundary,
    row.nextCoordinates.tasksFinish, row.nextCoordinates.tokensFinish,
    row.nextCoordinates.finish, row.nextCoordinates.start,
    row.currentSize.tasksBoundarySize, row.currentSize.tokensBoundarySize,
    row.currentCoordinates.tasksCount, row.currentCoordinates.tasksBoundary,
    row.currentCoordinates.tokensCount, row.currentCoordinates.tokensBoundary,
    row.currentCoordinates.tasksFinish, row.currentCoordinates.tokensFinish,
    row.currentCoordinates.finish, row.currentCoordinates.start]

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

private theorem substitute_sourceSubstitutionLift27
    (values : Fin 27 -> ValuationTerm) (term : ValuationTerm) :
    Rew.subst values (sourceSubstitutionLift 27 term) = term := by
  simpa only using
    (substitute_sourceSubstitutionLift (depth := 27) values term)

theorem compactParserSyntaxAdjacentRowBoundedRawTerminal_alignment
    (tokenTable width tokenCount stateBoundary stateCount index valueBound :
      Nat)
    (row : CompactParserSyntaxAdjacentStepRow) :
    compactParserSyntaxAdjacentRowBoundedRawTerminal tokenTable width tokenCount
          stateBoundary stateCount index valueBound ⇜
        (fun coordinate => shortBinaryNumeralTerm
          (compactParserSyntaxAdjacentRowBoundedWitnessValues row coordinate)) =
      compactParserSyntaxAdjacentStepRowClosedFormula tokenTable width tokenCount
          stateBoundary stateCount index row ⋏
        (compactParserSyntaxAdjacentRowCurrentStatusFormula tokenTable width
            tokenCount valueBound row ⋏
          compactParserSyntaxAdjacentRowNextStatusFormula tokenTable width
            tokenCount valueBound row) := by
  change Rew.subst (fun coordinate => shortBinaryNumeralTerm
      (compactParserSyntaxAdjacentRowBoundedWitnessValues row coordinate)) ▹
    compactParserSyntaxAdjacentRowBoundedRawTerminal tokenTable width tokenCount
      stateBoundary stateCount index valueBound = _
  unfold compactParserSyntaxAdjacentRowBoundedRawTerminal
  unfold compactParserSyntaxAdjacentStepRowClosedFormula
  unfold compactParserSyntaxAdjacentRowCurrentStatusFormula
  unfold compactParserSyntaxAdjacentRowNextStatusFormula
  simp [rewriting_embeddedFormulaSubstitution]
  repeat' apply And.intro
  all_goals
    congr 1
    funext coordinate
    fin_cases coordinate <;>
      simp [Function.comp_apply,
        compactParserSyntaxAdjacentRowBoundedWitnessValues, Rew.subst_bvar,
        substitute_sourceSubstitutionLift27]

#print axioms compactParserSyntaxAdjacentRowBoundedRawTerminal_alignment

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedWitnessSyntax
