import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
import integration.FoundationCompactPAValuationTermCompilerPublicBounds

/-!
# Conclusion-code lower bounds for certified context proofs

The displayed root sequent is stored in every derivation code.  Consequently,
the code of a proved conclusion is already charged by the proof payload.  This
fact lets downstream resource proofs reuse genuine certificate bounds as
syntax bounds without inspecting a large specialized formula again.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactCertifiedContextProofConclusionCodeBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate

theorem formulaCodeSum_le_binarySequentCode_length
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition) :
    formulaCodeSum Gamma <= (binarySequentCode Gamma).length := by
  unfold formulaCodeSum binarySequentCode
  simp only [List.length_append]
  rw [List.length_flatMap]
  simp

theorem binaryFormulaCode_length_le_binarySequentCode_length_of_mem
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (hformula : formula ∈ Gamma) :
    (binaryFormulaCode formula).length <=
      (binarySequentCode Gamma).length :=
  (formulaCode_le_formulaCodeSum hformula).trans
    (formulaCodeSum_le_binarySequentCode_length Gamma)

theorem binarySequentCode_length_le_binaryProofLength
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (proof : LO.FirstOrder.Derivation2 PA Gamma) :
    (binarySequentCode Gamma).length <= binaryProofLength proof := by
  cases proof <;> simp [binaryProofLength, binaryDerivationCode] <;> omega

theorem CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAContextProof Gamma formula) :
    (binaryFormulaCode formula).length <= proof.payloadLength := by
  have hformula : formula ∈ insert formula Gamma := Finset.mem_insert_self _ _
  have hsequent :=
    binaryFormulaCode_length_le_binarySequentCode_length_of_mem
      (insert formula Gamma) formula hformula
  have hproof := binarySequentCode_length_le_binaryProofLength proof.derivation
  unfold CertifiedPAContextProof.payloadLength
  exact (hsequent.trans hproof).trans (by omega)

theorem
    CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
    {valuation : Nat -> Nat} {formula : ValuationFormula}
    (certificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula) :
    (binaryFormulaCode formula).length <=
      hybridFormulaStructuralPayloadBound certificate := by
  exact
    (FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      certificate.compile).trans
      (compile_payloadLength_le_hybridFormulaStructuralPayloadBound certificate)

#print axioms formulaCodeSum_le_binarySequentCode_length
#print axioms binarySequentCode_length_le_binaryProofLength
#print axioms CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
#print axioms
  CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound

end FoundationCompactCertifiedContextProofConclusionCodeBounds
