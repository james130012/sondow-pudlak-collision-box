import integration.FoundationCompactNumericListedDirectExplicitWitnessPACompiler
import integration.FoundationCompactPAExplicitWitnessExsClosureBuilder

/-!
# Explicit-witness PA payload for the direct listed predicate

The twenty witness coordinates are introduced in their exact outer-binder
order.  The terminal body is the checked certificate for the same closed direct
matrix; no witness is selected from semantic existential truth.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectExplicitWitnessPACompiler

open FoundationCompactNumericListedDirectProofPredicate
open FoundationCompactNumericListedAcceptedDirectPACompiler
open FoundationCompactNumericListedPublicVerifier
open FoundationCompactListedCertifiedVerifier
open FoundationPudlakQuantitativeConditions
open FoundationCompactNumericListedDirectPredicateMatrixClosedInstance
open FoundationCompactNumericListedDirectPredicateMatrixHybridCompiler
open FoundationCompactNumericListedDirectBoundedProofWitness
open FoundationCompactPAExplicitWitnessHybridSigmaOneFormulaBuilder
open FoundationCompactPAExplicitWitnessHybridSigmaOneFormulaBuilder.ExplicitWitnessHybridSigmaOnePayload
open FoundationCompactPAExplicitWitnessExsClosureBuilder
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof

private def zeroValuation : Nat -> Nat := fun _ => 0

private def directExplicitWitnessSubstitutionValues
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    Fin 20 -> Nat :=
  ![witness.formulaWidth,
    witness.formulaOffsetTable,
    witness.formulaTable,
    witness.formulaTokenCount,
    witness.traceValueBound,
    witness.traceTable,
    witness.traceWidth,
    witness.split,
    witness.certificateFinish,
    witness.certificateStart,
    witness.proofFinish,
    witness.proofStart,
    witness.sourceTokenCount,
    witness.sourceWidth,
    witness.sourceTable,
    witness.inputWidth,
    witness.inputOffsetTable,
    witness.inputTable,
    witness.inputTokenCount,
    witness.proofCode]

private theorem directExplicitWitnessSubstitution_eq_closed
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    compactListedPADirectOpenWitnessMatrix bound formulaCode ⇜
        (fun index => shortBinaryNumeralTerm
          (directExplicitWitnessSubstitutionValues witness index)) =
      compactListedPADirectOpenWitnessMatrixClosed witness := by
  unfold compactListedPADirectOpenWitnessMatrixClosed
  apply Rewriting.smul_ext'
  apply Rew.ext
  · intro index
    fin_cases index <;>
      rfl
  · intro freeIndex
    rfl

/- The twenty public witness fields are introduced explicitly, in the exact
outer-binder order of `compactListedPADirectProofFormula`. -/
set_option maxHeartbeats 12000000 in
noncomputable def directExplicitWitnessPayload
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    ExplicitWitnessHybridSigmaOnePayload zeroValuation
      (compactListedPADirectProofInstance bound formulaCode) := by
  rw [compactListedPADirectProofInstance_eq_openWitnessExsClosure]
  let witness := bounded.witness
  let terminal : ExplicitWitnessHybridSigmaOnePayload zeroValuation
      (compactNumericListedDirectPredicateMatrixClosedInstance witness) :=
    .boundedBody
      (compactNumericListedDirectPredicateMatrixClosedInstance witness)
      (compactNumericListedDirectPredicateMatrixClosedInstance_sigmaZero witness)
      (compactNumericListedDirectPredicateMatrixClosedInstance_truth witness)
      (directMatrixHybridCertificate witness)
  have hterminal : ExplicitWitnessHybridSigmaOnePayload zeroValuation
      (compactListedPADirectOpenWitnessMatrix bound formulaCode ⇜
        (fun index => shortBinaryNumeralTerm
          (directExplicitWitnessSubstitutionValues witness index))) := by
    rw [directExplicitWitnessSubstitution_eq_closed]
    rw [compactListedPADirectOpenWitnessMatrixClosed_eq_closedInstance]
    exact terminal
  exact buildExplicitWitnessHybridExsClosureFromVector
    (body := compactListedPADirectOpenWitnessMatrix bound formulaCode)
    (values := directExplicitWitnessSubstitutionValues witness)
    hterminal

/-- The explicit payload compiles to a genuine certified PA proof under the
empty context. -/
noncomputable def compileDirectExplicitWitnessContext
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    CertifiedPAContextProof ∅
      (compactListedPADirectProofInstance bound formulaCode) := by
  let raw := compileExplicitWitnessHybridSigmaOne
    (directExplicitWitnessPayload bounded)
  have hcontext :
      valuationContext
        (compactListedPADirectProofInstance bound formulaCode).freeVariables
        zeroValuation = ∅ := by
    rw [compactListedPADirectProofInstance_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext raw

/-- Context-free certified PA proof produced from the same explicit witness. -/
noncomputable def compileDirectExplicitWitness
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    CertifiedPAProof
      (compactListedPADirectProofInstance bound formulaCode) :=
  certifiedContextProofOfEmpty
    (compileDirectExplicitWitnessContext bounded)

/-- The compiled proof is accepted by the same public numeric verifier. -/
theorem compileDirectExplicitWitness_publicVerifier_eq_true
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    compactNumericListedPublicVerifier
        (compileDirectExplicitWitness bounded).code
        (compactFormulaCode
          (compactListedPADirectProofInstance bound formulaCode)) = true := by
  rw [compactNumericListedPublicVerifier_pointwise]
  exact (compileDirectExplicitWitness bounded).verifier_eq_true

/-- The complete contextual proof is bounded by the proof-free resource stored
in the explicit payload.  A public polynomial bound for that resource is the
remaining quantitative obligation. -/
theorem compileDirectExplicitWitnessContext_payloadLength_le
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    (compileDirectExplicitWitnessContext bounded).payloadLength <=
      (directExplicitWitnessPayload bounded).compilePayloadResource := by
  unfold compileDirectExplicitWitnessContext
  simp only [CertifiedPAContextProof.castContext_payloadLength]
  exact compileExplicitWitnessHybridSigmaOne_payloadLength_le
    (directExplicitWitnessPayload bounded)

#print axioms directExplicitWitnessPayload
#print axioms compileDirectExplicitWitness
#print axioms compileDirectExplicitWitness_publicVerifier_eq_true
#print axioms compileDirectExplicitWitnessContext_payloadLength_le

end FoundationCompactNumericListedDirectExplicitWitnessPACompiler
