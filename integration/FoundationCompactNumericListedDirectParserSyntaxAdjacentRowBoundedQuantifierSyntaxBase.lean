import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedWitnessSyntax

/-! # Source syntax below the twenty-seven adjacent-row quantifiers -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSyntaxBase

open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

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

def compactParserSyntaxAdjacentRowBoundedSourceTerms
    (tokenTable width tokenCount stateBoundary stateCount index valueBound :
      Nat) : Fin 7 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm stateBoundary,
    shortBinaryNumeralTerm stateCount,
    shortBinaryNumeralTerm index,
    shortBinaryNumeralTerm valueBound]

def compactParserSyntaxAdjacentRowBoundedSourceRawTerminal :
    ArithmeticSemiformula Nat 34 :=
  ((Rewriting.emb (ξ := Nat)
      compactParserSyntaxAdjacentStepRowDef.val) ⇜
    ![(#27 : ArithmeticSemiterm Nat 34), #28, #29, #30, #31, #32,
      #26, #25, #24, #23, #22, #21, #20, #19, #18, #17, #16, #15,
      #14, #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1,
      #0]) ⋏
  (((Rewriting.emb (ξ := Nat)
      compactBinaryNatStatusValidBoundedDef.val) ⇜
    ![(#27 : ArithmeticSemiterm Nat 34), #28, #29, #23, #25, #33]) ⋏
    ((Rewriting.emb (ξ := Nat)
        compactBinaryNatStatusValidBoundedDef.val) ⇜
      ![(#27 : ArithmeticSemiterm Nat 34), #28, #29, #13, #15, #33]))

def compactParserSyntaxAdjacentRowBoundedEmptyRawTerminal :
    ArithmeticSemiformula Empty 34 :=
  (compactParserSyntaxAdjacentStepRowDef.val ⇜
    ![(#27 : ArithmeticSemiterm Empty 34), #28, #29, #30, #31, #32,
      #26, #25, #24, #23, #22, #21, #20, #19, #18, #17, #16, #15,
      #14, #13, #12, #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1,
      #0]) ⋏
  ((compactBinaryNatStatusValidBoundedDef.val ⇜
    ![(#27 : ArithmeticSemiterm Empty 34), #28, #29, #23, #25, #33]) ⋏
    (compactBinaryNatStatusValidBoundedDef.val ⇜
      ![(#27 : ArithmeticSemiterm Empty 34), #28, #29, #13, #15, #33]))

def compactParserSyntaxAdjacentRowBoundedSourceRawBody :
    ArithmeticSemiformula Nat 7 :=
  sourceBoundedWitnessFormula (#6 : ArithmeticSemiterm Nat 7) 27
    compactParserSyntaxAdjacentRowBoundedSourceRawTerminal

def compactParserSyntaxAdjacentRowBoundedEmptyRawBody :
    ArithmeticSemiformula Empty 7 :=
  sourceBoundedWitnessFormula (#6 : ArithmeticSemiterm Empty 7) 27
    compactParserSyntaxAdjacentRowBoundedEmptyRawTerminal

private theorem compactParserSyntaxAdjacentRowBoundedDef_eq_emptyRawBody :
    compactParserSyntaxAdjacentRowBoundedDef.val =
      compactParserSyntaxAdjacentRowBoundedEmptyRawBody := by
  unfold compactParserSyntaxAdjacentRowBoundedDef
  unfold compactParserSyntaxAdjacentRowBoundedEmptyRawBody
  unfold sourceBoundedWitnessFormula
  unfold sourceSubstitutionLift
  unfold compactParserSyntaxAdjacentRowBoundedEmptyRawTerminal
  rfl

private theorem
    compactParserSyntaxAdjacentRowBoundedEmptyRawTerminal_embedding :
    (Rew.emb : Rew ℒₒᵣ Empty 34 Nat 34) ▹
        compactParserSyntaxAdjacentRowBoundedEmptyRawTerminal =
      compactParserSyntaxAdjacentRowBoundedSourceRawTerminal := by
  unfold compactParserSyntaxAdjacentRowBoundedEmptyRawTerminal
  unfold compactParserSyntaxAdjacentRowBoundedSourceRawTerminal
  simp [rewriting_embeddedFormulaSubstitution]
  repeat' apply And.intro
  all_goals
    congr 1
    funext coordinate
    fin_cases coordinate <;> simp [Function.comp_apply]

theorem compactParserSyntaxAdjacentRowBoundedDef_emb_eq_sourceRawBody :
    Rewriting.emb (ξ := Nat) compactParserSyntaxAdjacentRowBoundedDef.val =
      compactParserSyntaxAdjacentRowBoundedSourceRawBody := by
  rw [compactParserSyntaxAdjacentRowBoundedDef_eq_emptyRawBody]
  change (Rew.emb : Rew ℒₒᵣ Empty 7 Nat 7) ▹
      compactParserSyntaxAdjacentRowBoundedEmptyRawBody = _
  unfold compactParserSyntaxAdjacentRowBoundedEmptyRawBody
  unfold compactParserSyntaxAdjacentRowBoundedSourceRawBody
  rw [rewriting_sourceBoundedWitnessFormula]
  rw [rewritingQpow_emb_eq_emb]
  rw [compactParserSyntaxAdjacentRowBoundedEmptyRawTerminal_embedding]
  rfl

#print axioms compactParserSyntaxAdjacentRowBoundedDef_emb_eq_sourceRawBody

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSyntaxBase
