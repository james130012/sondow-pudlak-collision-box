import integration.FoundationCompactNumericListedDirectVerifierParseStateCommonGraphExplicitHybridCertificate

/-!
# Exact checked assembly of the verifier parse-state graph

This module closes the common parse-state components and exposes one checked
input for the selected branch body.  It is an assembly layer only: the failure,
verum, closed, PA-leaf, and non-leaf branch bodies must be constructed by
their own direct certificate modules.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierParseStateGraphAssemblyExplicitHybridCertificate

open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStateGraph
open FoundationCompactNumericListedDirectVerifierVerumLeafStateGraph
open FoundationCompactNumericListedDirectVerifierClosedLeafStateGraph
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraph
open FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafStateGraph
open FoundationCompactNumericListedDirectVerifierStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierStateCoreGraphExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseStateFrameRows
open FoundationCompactNumericListedDirectVerifierStepGraphExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierTerminalStepBranchExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierTerminalStepBranchGraphExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseStateCommonGraphExplicitHybridCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

def compactNumericVerifierParseFailureStateAtEnvironmentFormula
    (values : Fin 429 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactNumericVerifierParseFailureSeparatedTablesStateGraphDef.val ⇜
        compactNumericVerifierParseFailureTerms)) ⇜
    compactNumericVerifierStepEnvironmentTerms values

def compactNumericVerifierParseVerumStateAtEnvironmentFormula
    (values : Fin 429 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactNumericVerifierVerumLeafStateGraphDef.val ⇜
        compactNumericVerifierParseVerumTerms)) ⇜
    compactNumericVerifierStepEnvironmentTerms values

def compactNumericVerifierParseClosedStateAtEnvironmentFormula
    (values : Fin 429 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactNumericVerifierClosedLeafStateGraphDef.val ⇜
        compactNumericVerifierParseClosedTerms)) ⇜
    compactNumericVerifierStepEnvironmentTerms values

def compactNumericVerifierParsePAStateAtEnvironmentFormula
    (values : Fin 429 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactNumericVerifierPAAxiomLeafStateGraphDef.val ⇜
        compactNumericVerifierParsePABranchTerms)) ⇜
    compactNumericVerifierStepEnvironmentTerms values

def compactNumericVerifierParseNonLeafStateAtEnvironmentFormula
    (values : Fin 429 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactNumericVerifierParseSuccessNonLeafStateGraphDef.val ⇜
        compactNumericVerifierParseSuccessNonLeafTerms)) ⇜
    compactNumericVerifierStepEnvironmentTerms values

def compactNumericVerifierParseSuccessCasesAtEnvironmentFormula
    (values : Fin 429 -> Nat) : ValuationFormula :=
  compactNumericVerifierParseVerumStateAtEnvironmentFormula values ⋎
    (compactNumericVerifierParseClosedStateAtEnvironmentFormula values ⋎
      (compactNumericVerifierParsePAStateAtEnvironmentFormula values ⋎
        compactNumericVerifierParseNonLeafStateAtEnvironmentFormula values))

def compactNumericVerifierParseSuccessAtEnvironmentFormula
    (values : Fin 429 -> Nat) : ValuationFormula :=
  compactNumericVerifierCurrentStateCoreAtEnvironmentFormula values ⋏
    (compactNumericVerifierNextStateCoreAtEnvironmentFormula values ⋏
      (compactNumericVerifierParseTaskHeadAtEnvironmentFormula values ⋏
        (compactNumericVerifierParseFrameAtEnvironmentFormula values ⋏
          compactNumericVerifierParseSuccessCasesAtEnvironmentFormula
            values)))

theorem compactNumericVerifierStepParseBranchAtEnvironmentFormula_eq_cases
    (values : Fin 429 -> Nat) :
    compactNumericVerifierStepParseBranchAtEnvironmentFormula values =
      compactNumericVerifierParseFailureStateAtEnvironmentFormula values ⋎
        compactNumericVerifierParseSuccessAtEnvironmentFormula values := by
  unfold compactNumericVerifierStepParseBranchAtEnvironmentFormula
  unfold compactNumericVerifierStepParseBranchFormula
  unfold compactNumericVerifierParseFailureStateAtEnvironmentFormula
  unfold compactNumericVerifierParseSuccessAtEnvironmentFormula
  unfold compactNumericVerifierParseSuccessCasesAtEnvironmentFormula
  unfold compactNumericVerifierParseVerumStateAtEnvironmentFormula
  unfold compactNumericVerifierParseClosedStateAtEnvironmentFormula
  unfold compactNumericVerifierParsePAStateAtEnvironmentFormula
  unfold compactNumericVerifierParseNonLeafStateAtEnvironmentFormula
  unfold compactNumericVerifierCurrentStateCoreAtEnvironmentFormula
  unfold compactNumericVerifierNextStateCoreAtEnvironmentFormula
  unfold compactNumericVerifierParseTaskHeadAtEnvironmentFormula
  unfold compactNumericVerifierParseFrameAtEnvironmentFormula
  unfold compactNumericVerifierParseStateGraphDef
  rfl

noncomputable def
    compactNumericVerifierParseSuccessAtEnvironmentExplicitHybridCertificate
    (values : Fin 429 -> Nat)
    (hcurrent : CompactNumericVerifierStateCoreGraph
      (values 0) (values 1) (values 2)
      (compactNumericVerifierStateCoordinatesAtValues
        (compactNumericVerifierCurrentStateValues values))
      (compactNumericVerifierStateSizeWitnessAtValues
        (compactNumericVerifierCurrentStateValues values)))
    (hnext : CompactNumericVerifierStateCoreGraph
      (values 0) (values 1) (values 2)
      (compactNumericVerifierStateCoordinatesAtValues
        (compactNumericVerifierNextStateValues values))
      (compactNumericVerifierStateSizeWitnessAtValues
        (compactNumericVerifierNextStateValues values)))
    (hhead : CompactNumericVerifierTaskBoundedHead
      (values 0) (values 1) (values 2) (values 11) (values 21)
      (compactNumericVerifierParseTaskCoordinatesAtValues values)
      (compactNumericVerifierParseTaskSizeWitnessAtValues values))
    (hframe : CompactNumericVerifierParseStateFrameRows
      (values 10) (values 15)
      (compactNumericVerifierParseTaskCoordinatesAtValues values))
    (cases : HybridCertificate
      (compactNumericVerifierParseSuccessCasesAtEnvironmentFormula values)) :
    HybridCertificate
      (compactNumericVerifierParseSuccessAtEnvironmentFormula values) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactNumericVerifierCurrentStateCoreExplicitHybridCertificateOfGraph
      values hcurrent)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactNumericVerifierNextStateCoreExplicitHybridCertificateOfGraph
        values hnext)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactNumericVerifierParseTaskHeadAtEnvironmentExplicitHybridCertificateOfGraph
          values hhead)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactNumericVerifierParseFrameAtEnvironmentExplicitHybridCertificateOfGraph
            values hframe)
          cases)))

noncomputable def
    compactNumericVerifierStepParseBranchExplicitHybridCertificateOfFailure
    (values : Fin 429 -> Nat)
    (failure : HybridCertificate
      (compactNumericVerifierParseFailureStateAtEnvironmentFormula values)) :
    HybridCertificate
      (compactNumericVerifierStepParseBranchAtEnvironmentFormula values) := by
  rw [compactNumericVerifierStepParseBranchAtEnvironmentFormula_eq_cases]
  exact .disjunctionLeft failure

private noncomputable def
    compactNumericVerifierStepParseBranchExplicitHybridCertificateOfSuccessCases
    (values : Fin 429 -> Nat)
    (hcurrent : CompactNumericVerifierStateCoreGraph
      (values 0) (values 1) (values 2)
      (compactNumericVerifierStateCoordinatesAtValues
        (compactNumericVerifierCurrentStateValues values))
      (compactNumericVerifierStateSizeWitnessAtValues
        (compactNumericVerifierCurrentStateValues values)))
    (hnext : CompactNumericVerifierStateCoreGraph
      (values 0) (values 1) (values 2)
      (compactNumericVerifierStateCoordinatesAtValues
        (compactNumericVerifierNextStateValues values))
      (compactNumericVerifierStateSizeWitnessAtValues
        (compactNumericVerifierNextStateValues values)))
    (hhead : CompactNumericVerifierTaskBoundedHead
      (values 0) (values 1) (values 2) (values 11) (values 21)
      (compactNumericVerifierParseTaskCoordinatesAtValues values)
      (compactNumericVerifierParseTaskSizeWitnessAtValues values))
    (hframe : CompactNumericVerifierParseStateFrameRows
      (values 10) (values 15)
      (compactNumericVerifierParseTaskCoordinatesAtValues values))
    (cases : HybridCertificate
      (compactNumericVerifierParseSuccessCasesAtEnvironmentFormula values)) :
    HybridCertificate
      (compactNumericVerifierStepParseBranchAtEnvironmentFormula values) := by
  rw [compactNumericVerifierStepParseBranchAtEnvironmentFormula_eq_cases]
  exact .disjunctionRight
    (compactNumericVerifierParseSuccessAtEnvironmentExplicitHybridCertificate
      values hcurrent hnext hhead hframe cases)

noncomputable def
    compactNumericVerifierStepParseBranchExplicitHybridCertificateOfVerum
    (values : Fin 429 -> Nat)
    (hcurrent : CompactNumericVerifierStateCoreGraph
      (values 0) (values 1) (values 2)
      (compactNumericVerifierStateCoordinatesAtValues
        (compactNumericVerifierCurrentStateValues values))
      (compactNumericVerifierStateSizeWitnessAtValues
        (compactNumericVerifierCurrentStateValues values)))
    (hnext : CompactNumericVerifierStateCoreGraph
      (values 0) (values 1) (values 2)
      (compactNumericVerifierStateCoordinatesAtValues
        (compactNumericVerifierNextStateValues values))
      (compactNumericVerifierStateSizeWitnessAtValues
        (compactNumericVerifierNextStateValues values)))
    (hhead : CompactNumericVerifierTaskBoundedHead
      (values 0) (values 1) (values 2) (values 11) (values 21)
      (compactNumericVerifierParseTaskCoordinatesAtValues values)
      (compactNumericVerifierParseTaskSizeWitnessAtValues values))
    (hframe : CompactNumericVerifierParseStateFrameRows
      (values 10) (values 15)
      (compactNumericVerifierParseTaskCoordinatesAtValues values))
    (verum : HybridCertificate
      (compactNumericVerifierParseVerumStateAtEnvironmentFormula values)) :
    HybridCertificate
      (compactNumericVerifierStepParseBranchAtEnvironmentFormula values) :=
  compactNumericVerifierStepParseBranchExplicitHybridCertificateOfSuccessCases
    values hcurrent hnext hhead hframe (.disjunctionLeft verum)

noncomputable def
    compactNumericVerifierStepParseBranchExplicitHybridCertificateOfClosed
    (values : Fin 429 -> Nat)
    (hcurrent : CompactNumericVerifierStateCoreGraph
      (values 0) (values 1) (values 2)
      (compactNumericVerifierStateCoordinatesAtValues
        (compactNumericVerifierCurrentStateValues values))
      (compactNumericVerifierStateSizeWitnessAtValues
        (compactNumericVerifierCurrentStateValues values)))
    (hnext : CompactNumericVerifierStateCoreGraph
      (values 0) (values 1) (values 2)
      (compactNumericVerifierStateCoordinatesAtValues
        (compactNumericVerifierNextStateValues values))
      (compactNumericVerifierStateSizeWitnessAtValues
        (compactNumericVerifierNextStateValues values)))
    (hhead : CompactNumericVerifierTaskBoundedHead
      (values 0) (values 1) (values 2) (values 11) (values 21)
      (compactNumericVerifierParseTaskCoordinatesAtValues values)
      (compactNumericVerifierParseTaskSizeWitnessAtValues values))
    (hframe : CompactNumericVerifierParseStateFrameRows
      (values 10) (values 15)
      (compactNumericVerifierParseTaskCoordinatesAtValues values))
    (closed : HybridCertificate
      (compactNumericVerifierParseClosedStateAtEnvironmentFormula values)) :
    HybridCertificate
      (compactNumericVerifierStepParseBranchAtEnvironmentFormula values) :=
  compactNumericVerifierStepParseBranchExplicitHybridCertificateOfSuccessCases
    values hcurrent hnext hhead hframe
      (.disjunctionRight (.disjunctionLeft closed))

noncomputable def
    compactNumericVerifierStepParseBranchExplicitHybridCertificateOfPA
    (values : Fin 429 -> Nat)
    (hcurrent : CompactNumericVerifierStateCoreGraph
      (values 0) (values 1) (values 2)
      (compactNumericVerifierStateCoordinatesAtValues
        (compactNumericVerifierCurrentStateValues values))
      (compactNumericVerifierStateSizeWitnessAtValues
        (compactNumericVerifierCurrentStateValues values)))
    (hnext : CompactNumericVerifierStateCoreGraph
      (values 0) (values 1) (values 2)
      (compactNumericVerifierStateCoordinatesAtValues
        (compactNumericVerifierNextStateValues values))
      (compactNumericVerifierStateSizeWitnessAtValues
        (compactNumericVerifierNextStateValues values)))
    (hhead : CompactNumericVerifierTaskBoundedHead
      (values 0) (values 1) (values 2) (values 11) (values 21)
      (compactNumericVerifierParseTaskCoordinatesAtValues values)
      (compactNumericVerifierParseTaskSizeWitnessAtValues values))
    (hframe : CompactNumericVerifierParseStateFrameRows
      (values 10) (values 15)
      (compactNumericVerifierParseTaskCoordinatesAtValues values))
    (pa : HybridCertificate
      (compactNumericVerifierParsePAStateAtEnvironmentFormula values)) :
    HybridCertificate
      (compactNumericVerifierStepParseBranchAtEnvironmentFormula values) :=
  compactNumericVerifierStepParseBranchExplicitHybridCertificateOfSuccessCases
    values hcurrent hnext hhead hframe
      (.disjunctionRight (.disjunctionRight (.disjunctionLeft pa)))

noncomputable def
    compactNumericVerifierStepParseBranchExplicitHybridCertificateOfNonLeaf
    (values : Fin 429 -> Nat)
    (hcurrent : CompactNumericVerifierStateCoreGraph
      (values 0) (values 1) (values 2)
      (compactNumericVerifierStateCoordinatesAtValues
        (compactNumericVerifierCurrentStateValues values))
      (compactNumericVerifierStateSizeWitnessAtValues
        (compactNumericVerifierCurrentStateValues values)))
    (hnext : CompactNumericVerifierStateCoreGraph
      (values 0) (values 1) (values 2)
      (compactNumericVerifierStateCoordinatesAtValues
        (compactNumericVerifierNextStateValues values))
      (compactNumericVerifierStateSizeWitnessAtValues
        (compactNumericVerifierNextStateValues values)))
    (hhead : CompactNumericVerifierTaskBoundedHead
      (values 0) (values 1) (values 2) (values 11) (values 21)
      (compactNumericVerifierParseTaskCoordinatesAtValues values)
      (compactNumericVerifierParseTaskSizeWitnessAtValues values))
    (hframe : CompactNumericVerifierParseStateFrameRows
      (values 10) (values 15)
      (compactNumericVerifierParseTaskCoordinatesAtValues values))
    (nonLeaf : HybridCertificate
      (compactNumericVerifierParseNonLeafStateAtEnvironmentFormula values)) :
    HybridCertificate
      (compactNumericVerifierStepParseBranchAtEnvironmentFormula values) :=
  compactNumericVerifierStepParseBranchExplicitHybridCertificateOfSuccessCases
    values hcurrent hnext hhead hframe
      (.disjunctionRight (.disjunctionRight (.disjunctionRight nonLeaf)))

#print axioms compactNumericVerifierStepParseBranchAtEnvironmentFormula_eq_cases
#print axioms
  compactNumericVerifierParseSuccessAtEnvironmentExplicitHybridCertificate
#print axioms
  compactNumericVerifierStepParseBranchExplicitHybridCertificateOfFailure
#print axioms
  compactNumericVerifierStepParseBranchExplicitHybridCertificateOfVerum
#print axioms
  compactNumericVerifierStepParseBranchExplicitHybridCertificateOfClosed
#print axioms compactNumericVerifierStepParseBranchExplicitHybridCertificateOfPA
#print axioms
  compactNumericVerifierStepParseBranchExplicitHybridCertificateOfNonLeaf

end FoundationCompactNumericListedDirectVerifierParseStateGraphAssemblyExplicitHybridCertificate
