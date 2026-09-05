import integration.FoundationCompactPAClosedHybridContextTransport

/-! # Transporting direct proofs of closed formulas between valuations -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactPAClosedDirectContextTransport

open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

noncomputable def transportClosedDirectProofAtValuation
    {source target : Nat -> Nat}
    {formula : ValuationFormula}
    (proof : CertifiedPAContextProof
      (valuationContext formula.freeVariables source) formula)
    (hclosed : formula.freeVariables = ∅) :
    CertifiedPAContextProof
      (valuationContext formula.freeVariables target) formula := by
  have hcontext :
      valuationContext formula.freeVariables source =
        valuationContext formula.freeVariables target := by
    rw [hclosed]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext proof

theorem transportClosedDirectProofAtValuation_payloadLength_eq
    {source target : Nat -> Nat}
    {formula : ValuationFormula}
    (proof : CertifiedPAContextProof
      (valuationContext formula.freeVariables source) formula)
    (hclosed : formula.freeVariables = ∅) :
    (transportClosedDirectProofAtValuation
      (target := target) proof hclosed).payloadLength = proof.payloadLength := by
  unfold transportClosedDirectProofAtValuation
  rw [CertifiedPAContextProof.castContext_payloadLength]

#print axioms transportClosedDirectProofAtValuation
#print axioms transportClosedDirectProofAtValuation_payloadLength_eq

end FoundationCompactPAClosedDirectContextTransport
