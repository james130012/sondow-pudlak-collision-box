import integration.FoundationCompactNumericListedDirectPredicateMatrixClosedInstance
import integration.FoundationCompactPAHybridValuationBoundedFormulaBuilder

/-!
# Hybrid PA compiler for the complete direct-predicate matrix

This module connects the already proved truth of the exact closed 22-coordinate
matrix to the fast-leaf hybrid compiler.  It establishes formula identity and
public verifier acceptance only.  Quantitative payload bounds are deliberately
kept in the separate bounds layer.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectPredicateMatrixHybridCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactNumericListedPublicVerifier
open FoundationCompactNumericListedDirectProofPredicate
open FoundationCompactNumericListedAcceptedDirectPACompiler
open FoundationCompactNumericListedDirectPredicateMatrixClosedInstance
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaBuilder
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof

abbrev DirectMatrixHybridCertificate
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :=
  CheckedHybridValuationBoundedFormulaCertificate
    (fun _ => 0)
    (compactNumericListedDirectPredicateMatrixClosedInstance witness)

/-- The proof-free hybrid certificate chosen from the exact matrix truth. -/
noncomputable def directMatrixHybridCertificate
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    DirectMatrixHybridCertificate witness :=
  ofSigmaZeroTruth
    (compactNumericListedDirectPredicateMatrixClosedInstance witness)
    (compactNumericListedDirectPredicateMatrixClosedInstance_sigmaZero witness)
    (fun _ => 0)
    (compactNumericListedDirectPredicateMatrixClosedInstance_truth witness)

noncomputable def compileDirectMatrixHybridContext
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    CertifiedPAContextProof ∅
      (compactNumericListedDirectPredicateMatrixClosedInstance witness) := by
  let raw := (directMatrixHybridCertificate witness).compile
  have hcontext : valuationContext
      (compactNumericListedDirectPredicateMatrixClosedInstance witness).freeVariables
      (fun _ => 0) = ∅ := by
    rw [
      compactNumericListedDirectPredicateMatrixClosedInstance_freeVariables_eq_empty]
    simp [valuationContext]
  rw [hcontext] at raw
  exact raw

noncomputable def compileDirectMatrixHybrid
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    CertifiedPAProof
      (compactNumericListedDirectPredicateMatrixClosedInstance witness) :=
  certifiedContextProofOfEmpty (compileDirectMatrixHybridContext witness)

theorem compileDirectMatrixHybrid_publicVerifier_eq_true
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    compactNumericListedPublicVerifier
        (compileDirectMatrixHybrid witness).code
        (compactFormulaCode
          (compactNumericListedDirectPredicateMatrixClosedInstance witness)) =
      true := by
  rw [compactNumericListedPublicVerifier_pointwise]
  exact (compileDirectMatrixHybrid witness).verifier_eq_true

#print axioms directMatrixHybridCertificate
#print axioms compileDirectMatrixHybrid
#print axioms compileDirectMatrixHybrid_publicVerifier_eq_true

end FoundationCompactNumericListedDirectPredicateMatrixHybridCompiler
