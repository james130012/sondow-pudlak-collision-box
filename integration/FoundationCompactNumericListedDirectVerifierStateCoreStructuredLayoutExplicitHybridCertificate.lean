import integration.FoundationCompactNumericListedDirectVerifierStateCoreLeafExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate

/-!
# Structured-list layout certificates at verifier state coordinates

The task and child-result list layouts are aligned with the exact 24-field
state environment and discharged from their concrete structured layouts.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierStateCoreStructuredLayoutExplicitHybridCertificate

open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectVerifierStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierStateCoreLeafExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAValuationTermCompiler

private abbrev zeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
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

theorem compactNumericVerifierStateTaskLayoutAtEnvironmentFormula_eq_closed
    (values : Fin 24 -> Nat) :
    compactNumericVerifierStateTaskLayoutAtEnvironmentFormula values =
      compactAdditiveStructuredListLayoutClosedFormula
        (values 0) (values 1) (values 2) (values 7)
        (values 10) (values 9) (values 11) := by
  unfold compactNumericVerifierStateTaskLayoutAtEnvironmentFormula
  unfold compactAdditiveStructuredListLayoutClosedFormula
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar,
        compactNumericVerifierStateEnvironmentTerms]
  · intro coordinate
    exact Empty.elim coordinate

noncomputable def
    compactNumericVerifierStateTaskLayoutExplicitHybridCertificate
    (values : Fin 24 -> Nat)
    (hlayout : CompactAdditiveStructuredListLayout
      (values 0) (values 1) (values 2) (values 7)
      (values 10) (values 9) (values 11)) :
    HybridCertificate
      (compactNumericVerifierStateTaskLayoutAtEnvironmentFormula values) := by
  rw [compactNumericVerifierStateTaskLayoutAtEnvironmentFormula_eq_closed]
  exact
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
      (values 0) (values 1) (values 2) (values 7)
      (values 10) (values 9) (values 11) hlayout

theorem compactNumericVerifierStateValueLayoutAtEnvironmentFormula_eq_closed
    (values : Fin 24 -> Nat) :
    compactNumericVerifierStateValueLayoutAtEnvironmentFormula values =
      compactAdditiveStructuredListLayoutClosedFormula
        (values 0) (values 1) (values 2) (values 9)
        (values 13) (values 12) (values 14) := by
  unfold compactNumericVerifierStateValueLayoutAtEnvironmentFormula
  unfold compactAdditiveStructuredListLayoutClosedFormula
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar,
        compactNumericVerifierStateEnvironmentTerms]
  · intro coordinate
    exact Empty.elim coordinate

noncomputable def
    compactNumericVerifierStateValueLayoutExplicitHybridCertificate
    (values : Fin 24 -> Nat)
    (hlayout : CompactAdditiveStructuredListLayout
      (values 0) (values 1) (values 2) (values 9)
      (values 13) (values 12) (values 14)) :
    HybridCertificate
      (compactNumericVerifierStateValueLayoutAtEnvironmentFormula values) := by
  rw [compactNumericVerifierStateValueLayoutAtEnvironmentFormula_eq_closed]
  exact
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
      (values 0) (values 1) (values 2) (values 9)
      (values 13) (values 12) (values 14) hlayout

#print axioms
  compactNumericVerifierStateTaskLayoutAtEnvironmentFormula_eq_closed
#print axioms
  compactNumericVerifierStateTaskLayoutExplicitHybridCertificate
#print axioms
  compactNumericVerifierStateValueLayoutAtEnvironmentFormula_eq_closed
#print axioms
  compactNumericVerifierStateValueLayoutExplicitHybridCertificate

end FoundationCompactNumericListedDirectVerifierStateCoreStructuredLayoutExplicitHybridCertificate
