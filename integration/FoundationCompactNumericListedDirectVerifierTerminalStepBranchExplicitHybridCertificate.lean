import integration.FoundationCompactNumericListedDirectVerifierStepGraphExplicitHybridCertificate

/-!
# Explicit assembly of the terminal verifier-step branches

The halted and finish branches each consist of the current state core, the
next state core, and one branch-specific row relation.  This module fixes those
three exact substituted formulas and assembles their checked hybrid
certificates without consulting semantic truth.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierTerminalStepBranchExplicitHybridCertificate

open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierHaltedFormula
open FoundationCompactNumericListedDirectVerifierFinishFormula
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableBoundedGraphExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierStepGraphExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private abbrev HybridCertificate
    (valuation : Nat -> Nat) (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate valuation formula

def compactNumericVerifierStepEnvironmentTerms
    (values : Fin 429 -> Nat) : Fin 429 -> ValuationTerm :=
  fun coordinate => shortBinaryNumeralTerm (values coordinate)

def compactNumericVerifierCurrentStateCoreAtEnvironmentFormula
    (values : Fin 429 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactNumericVerifierStateCoreGraphDef.val ⇜
        compactNumericVerifierParseCurrentStateTerms)) ⇜
    compactNumericVerifierStepEnvironmentTerms values

def compactNumericVerifierNextStateCoreAtEnvironmentFormula
    (values : Fin 429 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactNumericVerifierStateCoreGraphDef.val ⇜
        compactNumericVerifierParseNextStateTerms)) ⇜
    compactNumericVerifierStepEnvironmentTerms values

def compactNumericVerifierHaltedRowsAtEnvironmentFormula
    (values : Fin 429 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactNumericVerifierHaltedRowsDef.val ⇜
        compactNumericVerifierStepHaltedTerms)) ⇜
    compactNumericVerifierStepEnvironmentTerms values

def compactNumericVerifierFinishRowsAtEnvironmentFormula
    (values : Fin 429 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactNumericVerifierFinishRowsDef.val ⇜
        compactNumericVerifierStepFinishTerms)) ⇜
    compactNumericVerifierStepEnvironmentTerms values

theorem compactNumericVerifierStepHaltedBranchAtEnvironmentFormula_eq_components
    (values : Fin 429 -> Nat) :
    compactNumericVerifierStepHaltedBranchAtEnvironmentFormula values =
      compactNumericVerifierCurrentStateCoreAtEnvironmentFormula values ⋏
        (compactNumericVerifierNextStateCoreAtEnvironmentFormula values ⋏
          compactNumericVerifierHaltedRowsAtEnvironmentFormula values) := by
  unfold compactNumericVerifierStepHaltedBranchAtEnvironmentFormula
  unfold compactNumericVerifierStepHaltedBranchFormula
  unfold compactNumericVerifierCurrentStateCoreAtEnvironmentFormula
  unfold compactNumericVerifierNextStateCoreAtEnvironmentFormula
  unfold compactNumericVerifierHaltedRowsAtEnvironmentFormula
  rfl

theorem compactNumericVerifierStepFinishBranchAtEnvironmentFormula_eq_components
    (values : Fin 429 -> Nat) :
    compactNumericVerifierStepFinishBranchAtEnvironmentFormula values =
      compactNumericVerifierCurrentStateCoreAtEnvironmentFormula values ⋏
        (compactNumericVerifierNextStateCoreAtEnvironmentFormula values ⋏
          compactNumericVerifierFinishRowsAtEnvironmentFormula values) := by
  unfold compactNumericVerifierStepFinishBranchAtEnvironmentFormula
  unfold compactNumericVerifierStepFinishBranchFormula
  unfold compactNumericVerifierCurrentStateCoreAtEnvironmentFormula
  unfold compactNumericVerifierNextStateCoreAtEnvironmentFormula
  unfold compactNumericVerifierFinishRowsAtEnvironmentFormula
  rfl

noncomputable def compactNumericVerifierStepHaltedBranchExplicitHybridCertificate
    {valuation : Nat -> Nat} (values : Fin 429 -> Nat)
    (currentState : HybridCertificate valuation
      (compactNumericVerifierCurrentStateCoreAtEnvironmentFormula values))
    (nextState : HybridCertificate valuation
      (compactNumericVerifierNextStateCoreAtEnvironmentFormula values))
    (haltedRows : HybridCertificate valuation
      (compactNumericVerifierHaltedRowsAtEnvironmentFormula values)) :
    HybridCertificate valuation
      (compactNumericVerifierStepHaltedBranchAtEnvironmentFormula values) := by
  rw [compactNumericVerifierStepHaltedBranchAtEnvironmentFormula_eq_components]
  exact .conjunction currentState (.conjunction nextState haltedRows)

noncomputable def compactNumericVerifierStepFinishBranchExplicitHybridCertificate
    {valuation : Nat -> Nat} (values : Fin 429 -> Nat)
    (currentState : HybridCertificate valuation
      (compactNumericVerifierCurrentStateCoreAtEnvironmentFormula values))
    (nextState : HybridCertificate valuation
      (compactNumericVerifierNextStateCoreAtEnvironmentFormula values))
    (finishRows : HybridCertificate valuation
      (compactNumericVerifierFinishRowsAtEnvironmentFormula values)) :
    HybridCertificate valuation
      (compactNumericVerifierStepFinishBranchAtEnvironmentFormula values) := by
  rw [compactNumericVerifierStepFinishBranchAtEnvironmentFormula_eq_components]
  exact .conjunction currentState (.conjunction nextState finishRows)

#print axioms
  compactNumericVerifierStepHaltedBranchAtEnvironmentFormula_eq_components
#print axioms
  compactNumericVerifierStepFinishBranchAtEnvironmentFormula_eq_components
#print axioms
  compactNumericVerifierStepHaltedBranchExplicitHybridCertificate
#print axioms
  compactNumericVerifierStepFinishBranchExplicitHybridCertificate

end FoundationCompactNumericListedDirectVerifierTerminalStepBranchExplicitHybridCertificate
