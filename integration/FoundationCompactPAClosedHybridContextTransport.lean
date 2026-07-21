import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Transporting compiled closed hybrid certificates

A closed formula has the empty valuation context under every valuation.  Its
already compiled PA proof can therefore be transported to another valuation
without rebuilding the certificate tree and without changing payload length.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAClosedHybridContextTransport

open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate

noncomputable def compileClosedHybridAtValuation
    {source target : Nat -> Nat}
    {formula : ValuationFormula}
    (certificate :
      CheckedHybridValuationBoundedFormulaCertificate source formula)
    (hclosed : formula.freeVariables = ∅) :
    CertifiedPAContextProof
      (valuationContext formula.freeVariables target) formula := by
  have hcontext :
      valuationContext formula.freeVariables source =
        valuationContext formula.freeVariables target := by
    rw [hclosed]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext certificate.compile

theorem compileClosedHybridAtValuation_payloadLength_eq
    {source target : Nat -> Nat}
    {formula : ValuationFormula}
    (certificate :
      CheckedHybridValuationBoundedFormulaCertificate source formula)
    (hclosed : formula.freeVariables = ∅) :
    (compileClosedHybridAtValuation
      (target := target) certificate hclosed).payloadLength =
        certificate.compile.payloadLength := by
  unfold compileClosedHybridAtValuation
  rw [CertifiedPAContextProof.castContext_payloadLength]

theorem compileClosedHybridAtValuation_payloadLength_le_structural
    {source target : Nat -> Nat}
    {formula : ValuationFormula}
    (certificate :
      CheckedHybridValuationBoundedFormulaCertificate source formula)
    (hclosed : formula.freeVariables = ∅) :
    (compileClosedHybridAtValuation
      (target := target) certificate hclosed).payloadLength <=
        hybridFormulaStructuralPayloadBound certificate := by
  rw [compileClosedHybridAtValuation_payloadLength_eq]
  exact compile_payloadLength_le_structuralPayloadBound certificate

#print axioms compileClosedHybridAtValuation
#print axioms compileClosedHybridAtValuation_payloadLength_eq
#print axioms compileClosedHybridAtValuation_payloadLength_le_structural

end FoundationCompactPAClosedHybridContextTransport
