import integration.FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
import integration.FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport

/-! # Quantifier syntax for eighteen bounded sequent-step witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax

open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula

def compactSequentFormulaStepRowBoundedDirectSourceRawPublicTerms :
    Fin 8 -> ArithmeticSemiterm Nat 27 :=
  fun coordinate =>
    #(⟨18 + coordinate.val, by omega⟩ : Fin 27)

def compactSequentFormulaStepRowBoundedDirectReverseIndex
    (coordinate : Fin 18) : Fin 18 :=
  ⟨17 - coordinate, by omega⟩

def compactSequentFormulaStepRowBoundedDirectSourceRawWitnessTerms :
    Fin 18 -> ArithmeticSemiterm Nat 27 :=
  fun coordinate =>
    #(⟨(compactSequentFormulaStepRowBoundedDirectReverseIndex coordinate).val,
      by omega⟩ : Fin 27)

def compactSequentFormulaStepRowBoundedDirectSourceRawTerms :
    Fin 26 -> ArithmeticSemiterm Nat 27 :=
  Matrix.vecAppend rfl
    compactSequentFormulaStepRowBoundedDirectSourceRawPublicTerms
    compactSequentFormulaStepRowBoundedDirectSourceRawWitnessTerms

def compactSequentFormulaStepRowBoundedDirectEmptyRawTerms :
    Fin 26 -> ArithmeticSemiterm Empty 27 :=
  compactSequentFormulaStepRowBoundedEmptyRawTerms

def compactSequentFormulaStepRowBoundedDirectEmptyRawTerminal :
    ArithmeticSemiformula Empty 27 :=
  compactSequentFormulaStepRowBoundedEmptyRawTerminal

def compactSequentFormulaStepRowBoundedDirectSourceRawTerminal :
    ArithmeticSemiformula Nat 27 :=
  (Rewriting.emb (ξ := Nat) compactSequentFormulaStepDef.val) ⇜
    compactSequentFormulaStepRowBoundedDirectSourceRawTerms

def compactSequentFormulaStepRowBoundedDirectSourceRawBody :
    ArithmeticSemiformula Nat 9 :=
  sourceBoundedWitnessFormula (#8 : ArithmeticSemiterm Nat 9) 18
    compactSequentFormulaStepRowBoundedDirectSourceRawTerminal

def compactSequentFormulaStepRowBoundedDirectEmptyRawBody :
    ArithmeticSemiformula Empty 9 :=
  sourceBoundedWitnessFormula (#8 : ArithmeticSemiterm Empty 9) 18
    compactSequentFormulaStepRowBoundedDirectEmptyRawTerminal

theorem compactSequentFormulaStepRowBoundedDirectEmptyRawTerms_embedding :
    (Rew.emb : Rew ℒₒᵣ Empty 27 Nat 27) ∘
        compactSequentFormulaStepRowBoundedDirectEmptyRawTerms =
      compactSequentFormulaStepRowBoundedDirectSourceRawTerms := by
  funext coordinate
  fin_cases coordinate <;>
    rfl

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

private theorem rewriting_emb_empty
    {boundArity : Nat}
    (formula : ArithmeticSemiformula Empty boundArity) :
    (Rewriting.emb (ξ := Empty) formula) = formula := by
  change
    (Rew.emb : Rew ℒₒᵣ Empty boundArity Empty boundArity) ▹ formula =
      formula
  rw [Rew.emb_eq_id]
  exact ReflectiveRewriting.id_app formula

theorem
    compactSequentFormulaStepRowBoundedDirectEmptyRawTerminal_embedding :
    (Rew.emb : Rew ℒₒᵣ Empty 27 Nat 27) ▹
        compactSequentFormulaStepRowBoundedDirectEmptyRawTerminal =
      compactSequentFormulaStepRowBoundedDirectSourceRawTerminal := by
  unfold compactSequentFormulaStepRowBoundedDirectEmptyRawTerminal
    compactSequentFormulaStepRowBoundedEmptyRawTerminal
    compactSequentFormulaStepRowBoundedDirectSourceRawTerminal
  calc
    (Rew.emb : Rew ℒₒᵣ Empty 27 Nat 27) ▹
        (compactSequentFormulaStepDef.val ⇜
          compactSequentFormulaStepRowBoundedDirectEmptyRawTerms) =
      (Rew.emb : Rew ℒₒᵣ Empty 27 Nat 27) ▹
        ((Rewriting.emb (ξ := Empty) compactSequentFormulaStepDef.val) ⇜
          compactSequentFormulaStepRowBoundedDirectEmptyRawTerms) := by
            rw [rewriting_emb_empty]
    _ =
      (Rewriting.emb (ξ := Nat) compactSequentFormulaStepDef.val) ⇜
        ((Rew.emb : Rew ℒₒᵣ Empty 27 Nat 27) ∘
          compactSequentFormulaStepRowBoundedDirectEmptyRawTerms) := by
            exact
              rewriting_embeddedFormulaSubstitution
                (Rew.emb : Rew ℒₒᵣ Empty 27 Nat 27)
                compactSequentFormulaStepDef.val
                compactSequentFormulaStepRowBoundedDirectEmptyRawTerms
    _ = (Rewriting.emb (ξ := Nat) compactSequentFormulaStepDef.val) ⇜
        compactSequentFormulaStepRowBoundedDirectSourceRawTerms := by
          rw [
            compactSequentFormulaStepRowBoundedDirectEmptyRawTerms_embedding]

#print axioms
  compactSequentFormulaStepRowBoundedDirectEmptyRawTerms_embedding
#print axioms
  compactSequentFormulaStepRowBoundedDirectEmptyRawTerminal_embedding

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
