import integration.FoundationCompactNumericListedDirectVerifierTerminalStepBranchGraphExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierTaskBoundedHeadExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierParseStateFrameRowsExplicitHybridCertificate

/-!
# Explicit common certificates for a parse-state branch

This module connects the bounded task head and parse frame to their exact
coordinates in the 429-column verifier-step environment.  It closes only the
common parse components; branch-specific leaf and non-leaf graphs remain
separate obligations.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierParseStateCommonGraphExplicitHybridCertificate

open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierParseStateFrameRows
open FoundationCompactNumericListedDirectVerifierStepGraphExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierTerminalStepBranchExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseStateFrameRowsExplicitHybridCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

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

def compactNumericVerifierParseTaskCoordinatesAtValues
    (values : Fin 429 -> Nat) : CompactNumericVerifierTaskRowCoordinates :=
  compactNumericVerifierTaskRowCoordinatesOf
    (values 45) (values 46) (values 47) (values 48) (values 49)
    (values 50) (values 51) (values 52) (values 53) (values 54)
    (values 55) (values 56) (values 57)

def compactNumericVerifierParseTaskSizeWitnessAtValues
    (values : Fin 429 -> Nat) : CompactNumericVerifierTaskSizeWitness where
  gammaBoundarySize := values 58

def compactNumericVerifierParseTaskHeadAtEnvironmentFormula
    (values : Fin 429 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactNumericVerifierTaskBoundedHeadDef.val ⇜
        compactNumericVerifierParseHeadTerms)) ⇜
    compactNumericVerifierStepEnvironmentTerms values

theorem compactNumericVerifierParseTaskHeadAtEnvironmentFormula_eq_closed
    (values : Fin 429 -> Nat) :
    compactNumericVerifierParseTaskHeadAtEnvironmentFormula values =
      compactNumericVerifierTaskBoundedHeadClosedFormula
        (values 0) (values 1) (values 2) (values 11) (values 21)
        (compactNumericVerifierParseTaskCoordinatesAtValues values)
        (compactNumericVerifierParseTaskSizeWitnessAtValues values) := by
  unfold compactNumericVerifierParseTaskHeadAtEnvironmentFormula
  unfold compactNumericVerifierTaskBoundedHeadClosedFormula
  unfold compactNumericVerifierParseHeadTerms
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar,
        compactNumericVerifierStepEnvironmentTerms,
        compactNumericVerifierParseTaskCoordinatesAtValues,
        compactNumericVerifierParseTaskSizeWitnessAtValues,
        compactNumericVerifierTaskRowCoordinatesOf]
  · intro coordinate
    exact Empty.elim coordinate

noncomputable def
    compactNumericVerifierParseTaskHeadAtEnvironmentExplicitHybridCertificateOfGraph
    (values : Fin 429 -> Nat)
    (hhead : CompactNumericVerifierTaskBoundedHead
      (values 0) (values 1) (values 2) (values 11) (values 21)
      (compactNumericVerifierParseTaskCoordinatesAtValues values)
      (compactNumericVerifierParseTaskSizeWitnessAtValues values)) :
    HybridCertificate
      (compactNumericVerifierParseTaskHeadAtEnvironmentFormula values) := by
  rw [compactNumericVerifierParseTaskHeadAtEnvironmentFormula_eq_closed]
  exact compactNumericVerifierTaskBoundedHeadExplicitHybridCertificate
    (values 0) (values 1) (values 2) (values 11) (values 21)
    (compactNumericVerifierParseTaskCoordinatesAtValues values)
    (compactNumericVerifierParseTaskSizeWitnessAtValues values) hhead

def compactNumericVerifierParseFrameAtEnvironmentFormula
    (values : Fin 429 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactNumericVerifierParseStateFrameRowsDef.val ⇜
        compactNumericVerifierParseFrameTerms)) ⇜
    compactNumericVerifierStepEnvironmentTerms values

theorem compactNumericVerifierParseFrameAtEnvironmentFormula_eq_closed
    (values : Fin 429 -> Nat) :
    compactNumericVerifierParseFrameAtEnvironmentFormula values =
      compactNumericVerifierParseStateFrameRowsClosedFormula
        (values 10) (values 15)
        (compactNumericVerifierParseTaskCoordinatesAtValues values) := by
  unfold compactNumericVerifierParseFrameAtEnvironmentFormula
  unfold compactNumericVerifierParseStateFrameRowsClosedFormula
  unfold compactNumericVerifierParseFrameTerms
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar,
        compactNumericVerifierStepEnvironmentTerms,
        compactNumericVerifierParseTaskCoordinatesAtValues,
        compactNumericVerifierTaskRowCoordinatesOf]
  · intro coordinate
    exact Empty.elim coordinate

noncomputable def
    compactNumericVerifierParseFrameAtEnvironmentExplicitHybridCertificateOfGraph
    (values : Fin 429 -> Nat)
    (hframe : CompactNumericVerifierParseStateFrameRows
      (values 10) (values 15)
      (compactNumericVerifierParseTaskCoordinatesAtValues values)) :
    HybridCertificate
      (compactNumericVerifierParseFrameAtEnvironmentFormula values) := by
  rw [compactNumericVerifierParseFrameAtEnvironmentFormula_eq_closed]
  exact
    compactNumericVerifierParseStateFrameRowsExplicitHybridCertificateOfGraph
      (values 10) (values 15)
      (compactNumericVerifierParseTaskCoordinatesAtValues values) hframe

#print axioms
  compactNumericVerifierParseTaskHeadAtEnvironmentFormula_eq_closed
#print axioms
  compactNumericVerifierParseTaskHeadAtEnvironmentExplicitHybridCertificateOfGraph
#print axioms compactNumericVerifierParseFrameAtEnvironmentFormula_eq_closed
#print axioms
  compactNumericVerifierParseFrameAtEnvironmentExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectVerifierParseStateCommonGraphExplicitHybridCertificate
