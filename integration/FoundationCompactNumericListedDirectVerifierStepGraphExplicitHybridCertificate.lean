import integration.FoundationCompactNumericListedDirectVerifierStepWitnessTableBoundedGraphExplicitHybridCertificate

/-!
# Explicit four-way assembly of one verifier step graph

The complete step formula is exposed as its halted, finish, parse, and combine
branches at one fixed 429-coordinate environment.  Each constructor selects a
branch directly in the checked hybrid certificate; no branch is recovered from
semantic formula truth.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierStepGraphExplicitHybridCertificate

open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierCombineStateGraph
open FoundationCompactNumericListedDirectVerifierHaltedFormula
open FoundationCompactNumericListedDirectVerifierFinishFormula
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableBoundedGraphExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private abbrev HybridCertificate
    (valuation : Nat -> Nat) (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate valuation formula

def compactNumericVerifierStepHaltedBranchFormula :
    ArithmeticSemiformula Empty 429 :=
  (compactNumericVerifierStateCoreGraphDef.val ⇜
      compactNumericVerifierParseCurrentStateTerms) ⋏
    (compactNumericVerifierStateCoreGraphDef.val ⇜
      compactNumericVerifierParseNextStateTerms) ⋏
    (compactNumericVerifierHaltedRowsDef.val ⇜
      compactNumericVerifierStepHaltedTerms)

def compactNumericVerifierStepFinishBranchFormula :
    ArithmeticSemiformula Empty 429 :=
  (compactNumericVerifierStateCoreGraphDef.val ⇜
      compactNumericVerifierParseCurrentStateTerms) ⋏
    (compactNumericVerifierStateCoreGraphDef.val ⇜
      compactNumericVerifierParseNextStateTerms) ⋏
    (compactNumericVerifierFinishRowsDef.val ⇜
      compactNumericVerifierStepFinishTerms)

def compactNumericVerifierStepParseBranchFormula :
    ArithmeticSemiformula Empty 429 :=
  compactNumericVerifierParseStateGraphDef.val

def compactNumericVerifierStepCombineBranchFormula :
    ArithmeticSemiformula Empty 429 :=
  compactNumericVerifierCombineStateGraphDef.val ⇜
    compactNumericVerifierStepCombineTerms

theorem compactNumericVerifierStepGraphDef_val_eq_fourBranches :
    compactNumericVerifierStepGraphDef.val =
      compactNumericVerifierStepHaltedBranchFormula ⋎
        (compactNumericVerifierStepFinishBranchFormula ⋎
          (compactNumericVerifierStepParseBranchFormula ⋎
            compactNumericVerifierStepCombineBranchFormula)) := by
  rfl

private def environmentTerms
    (values : Fin 429 -> Nat) : Fin 429 -> ValuationTerm :=
  fun coordinate => shortBinaryNumeralTerm (values coordinate)

def compactNumericVerifierStepHaltedBranchAtEnvironmentFormula
    (values : Fin 429 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierStepHaltedBranchFormula) ⇜ environmentTerms values

def compactNumericVerifierStepFinishBranchAtEnvironmentFormula
    (values : Fin 429 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierStepFinishBranchFormula) ⇜ environmentTerms values

def compactNumericVerifierStepParseBranchAtEnvironmentFormula
    (values : Fin 429 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierStepParseBranchFormula) ⇜ environmentTerms values

def compactNumericVerifierStepCombineBranchAtEnvironmentFormula
    (values : Fin 429 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierStepCombineBranchFormula) ⇜ environmentTerms values

/-- Exact formula alignment at an arbitrary fixed 429-coordinate environment. -/
theorem compactNumericVerifierStepGraphAtEnvironmentFormula_eq_fourBranches
    (values : Fin 429 -> Nat) :
    compactNumericVerifierStepGraphAtEnvironmentFormula values =
      compactNumericVerifierStepHaltedBranchAtEnvironmentFormula values ⋎
        (compactNumericVerifierStepFinishBranchAtEnvironmentFormula values ⋎
          (compactNumericVerifierStepParseBranchAtEnvironmentFormula values ⋎
            compactNumericVerifierStepCombineBranchAtEnvironmentFormula
              values)) := by
  unfold compactNumericVerifierStepGraphAtEnvironmentFormula
  rw [compactNumericVerifierStepGraphDef_val_eq_fourBranches]
  unfold compactNumericVerifierStepHaltedBranchAtEnvironmentFormula
  unfold compactNumericVerifierStepFinishBranchAtEnvironmentFormula
  unfold compactNumericVerifierStepParseBranchAtEnvironmentFormula
  unfold compactNumericVerifierStepCombineBranchAtEnvironmentFormula
  rfl

/-- Select the halted branch explicitly. -/
noncomputable def compactNumericVerifierStepGraphExplicitHybridCertificateOfHalted
    {valuation : Nat -> Nat} (values : Fin 429 -> Nat)
    (halted : HybridCertificate valuation
      (compactNumericVerifierStepHaltedBranchAtEnvironmentFormula values)) :
    HybridCertificate valuation
      (compactNumericVerifierStepGraphAtEnvironmentFormula values) := by
  rw [compactNumericVerifierStepGraphAtEnvironmentFormula_eq_fourBranches]
  exact .disjunctionLeft halted

/-- Select the finish branch explicitly. -/
noncomputable def compactNumericVerifierStepGraphExplicitHybridCertificateOfFinish
    {valuation : Nat -> Nat} (values : Fin 429 -> Nat)
    (finish : HybridCertificate valuation
      (compactNumericVerifierStepFinishBranchAtEnvironmentFormula values)) :
    HybridCertificate valuation
      (compactNumericVerifierStepGraphAtEnvironmentFormula values) := by
  rw [compactNumericVerifierStepGraphAtEnvironmentFormula_eq_fourBranches]
  exact .disjunctionRight (.disjunctionLeft finish)

/-- Select the parse branch explicitly. -/
noncomputable def compactNumericVerifierStepGraphExplicitHybridCertificateOfParse
    {valuation : Nat -> Nat} (values : Fin 429 -> Nat)
    (parse : HybridCertificate valuation
      (compactNumericVerifierStepParseBranchAtEnvironmentFormula values)) :
    HybridCertificate valuation
      (compactNumericVerifierStepGraphAtEnvironmentFormula values) := by
  rw [compactNumericVerifierStepGraphAtEnvironmentFormula_eq_fourBranches]
  exact .disjunctionRight (.disjunctionRight (.disjunctionLeft parse))

/-- Select the combine branch explicitly. -/
noncomputable def compactNumericVerifierStepGraphExplicitHybridCertificateOfCombine
    {valuation : Nat -> Nat} (values : Fin 429 -> Nat)
    (combine : HybridCertificate valuation
      (compactNumericVerifierStepCombineBranchAtEnvironmentFormula values)) :
    HybridCertificate valuation
      (compactNumericVerifierStepGraphAtEnvironmentFormula values) := by
  rw [compactNumericVerifierStepGraphAtEnvironmentFormula_eq_fourBranches]
  exact .disjunctionRight (.disjunctionRight (.disjunctionRight combine))

#print axioms compactNumericVerifierStepGraphDef_val_eq_fourBranches
#print axioms compactNumericVerifierStepGraphAtEnvironmentFormula_eq_fourBranches
#print axioms compactNumericVerifierStepGraphExplicitHybridCertificateOfHalted
#print axioms compactNumericVerifierStepGraphExplicitHybridCertificateOfFinish
#print axioms compactNumericVerifierStepGraphExplicitHybridCertificateOfParse
#print axioms compactNumericVerifierStepGraphExplicitHybridCertificateOfCombine

end FoundationCompactNumericListedDirectVerifierStepGraphExplicitHybridCertificate
