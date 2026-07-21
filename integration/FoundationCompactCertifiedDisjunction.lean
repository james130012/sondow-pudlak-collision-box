import integration.FoundationCompactPAQuantitativeCompilerCore

/-!
# Explicit certified disjunction introduction

These two proof-producing primitives lift a checked proof of either disjunct
to a checked proof of the disjunction.  The emitted proof tree contains one
real `Derivation2.or` node and one weakening node; its certificate mirrors
that exact structure.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactCertifiedDisjunction

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationComputableCompactPAProofEncoder
open FoundationCompactListedCertifiedVerifier
open FoundationCompactCertifiedConjunction
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof

def disjunctionSyntaxBudget
    (left right : LO.FirstOrder.ArithmeticProposition) : Nat :=
  (binaryFormulaCode left).length +
    (binaryFormulaCode right).length +
    (binaryFormulaCode (left ⋎ right)).length

def checkedDisjunctionLeftTree
    (left right : LO.FirstOrder.ArithmeticProposition)
    (leftTree : CheckedPAProofTree) : CheckedPAProofTree :=
  .or {left ⋎ right} left right
    (.wk (insert left (insert right {left ⋎ right})) leftTree)

def checkedDisjunctionRightTree
    (left right : LO.FirstOrder.ArithmeticProposition)
    (rightTree : CheckedPAProofTree) : CheckedPAProofTree :=
  .or {left ⋎ right} left right
    (.wk (insert left (insert right {left ⋎ right})) rightTree)

def disjunctionCertificate
    (certificate : StructuralValidityCertificate) :
    StructuralValidityCertificate :=
  .unary (.unary certificate)

theorem checkedDisjunctionLeftCertificate_valid
    {left right : LO.FirstOrder.ArithmeticProposition}
    (leftTree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hconclusion : leftTree.conclusion = {left})
    (hvalid : certificateValid leftTree certificate) :
    certificateValid
      (checkedDisjunctionLeftTree left right leftTree)
      (disjunctionCertificate certificate) := by
  simp [checkedDisjunctionLeftTree, disjunctionCertificate,
    CheckedPAProofTree.conclusion, certificateValid, hvalid]
  change leftTree.conclusion ⊆ _
  rw [hconclusion]
  simp

theorem checkedDisjunctionRightCertificate_valid
    {left right : LO.FirstOrder.ArithmeticProposition}
    (rightTree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hconclusion : rightTree.conclusion = {right})
    (hvalid : certificateValid rightTree certificate) :
    certificateValid
      (checkedDisjunctionRightTree left right rightTree)
      (disjunctionCertificate certificate) := by
  simp [checkedDisjunctionRightTree, disjunctionCertificate,
    CheckedPAProofTree.conclusion, certificateValid, hvalid]
  change rightTree.conclusion ⊆ _
  rw [hconclusion]
  simp

theorem disjunctionCertificate_code_length_le
    (certificate : StructuralValidityCertificate) :
    (binaryStructuralValidityCertificateCode
      (disjunctionCertificate certificate)).length <=
      (binaryStructuralValidityCertificateCode certificate).length + 32 := by
  have htag : (binaryNatCode 2).length <= 16 := by decide
  simp only [disjunctionCertificate,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

def disjunctionLeftDerivation
    {left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : LO.FirstOrder.Derivation2 PA {left}) :
    LO.FirstOrder.Derivation2 PA {left ⋎ right} :=
  LO.FirstOrder.Derivation2.or (Γ := {left ⋎ right})
    (φ := left) (ψ := right) (by simp)
    (LO.FirstOrder.Derivation2.wk leftProof (by simp))

def disjunctionRightDerivation
    {left right : LO.FirstOrder.ArithmeticProposition}
    (rightProof : LO.FirstOrder.Derivation2 PA {right}) :
    LO.FirstOrder.Derivation2 PA {left ⋎ right} :=
  LO.FirstOrder.Derivation2.or (Γ := {left ⋎ right})
    (φ := left) (ψ := right) (by simp)
    (LO.FirstOrder.Derivation2.wk rightProof (by simp))

@[simp] theorem ofDerivation_disjunctionLeftDerivation
    {left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : LO.FirstOrder.Derivation2 PA {left}) :
    CheckedPAProofTree.ofDerivation
        (disjunctionLeftDerivation (right := right) leftProof) =
      checkedDisjunctionLeftTree left right
        (CheckedPAProofTree.ofDerivation leftProof) := by
  rfl

@[simp] theorem ofDerivation_disjunctionRightDerivation
    {left right : LO.FirstOrder.ArithmeticProposition}
    (rightProof : LO.FirstOrder.Derivation2 PA {right}) :
    CheckedPAProofTree.ofDerivation
        (disjunctionRightDerivation (left := left) rightProof) =
      checkedDisjunctionRightTree left right
        (CheckedPAProofTree.ofDerivation rightProof) := by
  rfl

theorem disjunctionLeftDerivation_binaryProofLength_le
    {left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : LO.FirstOrder.Derivation2 PA {left}) :
    binaryProofLength
        (disjunctionLeftDerivation (right := right) leftProof) <=
      binaryProofLength leftProof + 64 +
        8 * disjunctionSyntaxBudget left right := by
  let disjunction := left ⋎ right
  let syntaxBudget := disjunctionSyntaxBudget left right
  have hbudget : syntaxBudget =
      (binaryFormulaCode left).length +
        (binaryFormulaCode right).length +
        (binaryFormulaCode disjunction).length := by rfl
  have hseq
      (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
      (hmem : ∀ candidate ∈ Gamma,
        candidate = left ∨ candidate = right ∨ candidate = disjunction) :
      (binarySequentCode Gamma).length <=
        (binaryNatCode 3).length + 3 * syntaxBudget := by
    simpa [hbudget] using
      binarySequentCode_length_le_three_formula_budget
        Gamma left right disjunction hmem
  have hroot := hseq {disjunction} (by simp)
  have hpremise := hseq
    (insert left (insert right {disjunction})) (by simp)
  have htag4 : (binaryNatCode 4).length <= 16 := by decide
  have htag7 : (binaryNatCode 7).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  have hleft : (binaryFormulaCode left).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
    omega
  have hright : (binaryFormulaCode right).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
    omega
  simp only [disjunctionLeftDerivation, binaryProofLength,
    binaryDerivationCode, List.length_append]
  dsimp only [disjunction] at hroot hpremise
  change _ <= (binaryDerivationCode leftProof).length + 64 +
    8 * syntaxBudget
  omega

theorem disjunctionRightDerivation_binaryProofLength_le
    {left right : LO.FirstOrder.ArithmeticProposition}
    (rightProof : LO.FirstOrder.Derivation2 PA {right}) :
    binaryProofLength
        (disjunctionRightDerivation (left := left) rightProof) <=
      binaryProofLength rightProof + 64 +
        8 * disjunctionSyntaxBudget left right := by
  let disjunction := left ⋎ right
  let syntaxBudget := disjunctionSyntaxBudget left right
  have hbudget : syntaxBudget =
      (binaryFormulaCode left).length +
        (binaryFormulaCode right).length +
        (binaryFormulaCode disjunction).length := by rfl
  have hseq
      (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
      (hmem : ∀ candidate ∈ Gamma,
        candidate = left ∨ candidate = right ∨ candidate = disjunction) :
      (binarySequentCode Gamma).length <=
        (binaryNatCode 3).length + 3 * syntaxBudget := by
    simpa [hbudget] using
      binarySequentCode_length_le_three_formula_budget
        Gamma left right disjunction hmem
  have hroot := hseq {disjunction} (by simp)
  have hpremise := hseq
    (insert left (insert right {disjunction})) (by simp)
  have htag4 : (binaryNatCode 4).length <= 16 := by decide
  have htag7 : (binaryNatCode 7).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  have hleft : (binaryFormulaCode left).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
    omega
  have hright : (binaryFormulaCode right).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
    omega
  simp only [disjunctionRightDerivation, binaryProofLength,
    binaryDerivationCode, List.length_append]
  dsimp only [disjunction] at hroot hpremise
  change _ <= (binaryDerivationCode rightProof).length + 64 +
    8 * syntaxBudget
  omega

def disjunctionLeft
    {left right : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAProof left) :
    CertifiedPAProof (left ⋎ right) where
  derivation := disjunctionLeftDerivation proof.derivation
  certificate := disjunctionCertificate proof.certificate
  certificate_valid := by
    rw [ofDerivation_disjunctionLeftDerivation]
    exact checkedDisjunctionLeftCertificate_valid
      (CheckedPAProofTree.ofDerivation proof.derivation) proof.certificate
      (CheckedPAProofTree.conclusion_ofDerivation proof.derivation)
      proof.certificate_valid

def disjunctionRight
    {left right : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAProof right) :
    CertifiedPAProof (left ⋎ right) where
  derivation := disjunctionRightDerivation proof.derivation
  certificate := disjunctionCertificate proof.certificate
  certificate_valid := by
    rw [ofDerivation_disjunctionRightDerivation]
    exact checkedDisjunctionRightCertificate_valid
      (CheckedPAProofTree.ofDerivation proof.derivation) proof.certificate
      (CheckedPAProofTree.conclusion_ofDerivation proof.derivation)
      proof.certificate_valid

theorem disjunctionLeft_payloadLength_le
    {left right : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAProof left) :
    (disjunctionLeft (right := right) proof).payloadLength <=
      proof.payloadLength + 96 + 8 * disjunctionSyntaxBudget left right := by
  have hproof := disjunctionLeftDerivation_binaryProofLength_le
    (right := right) proof.derivation
  have hcertificate := disjunctionCertificate_code_length_le proof.certificate
  rw [CertifiedPAProof.payloadLength_eq,
    CertifiedPAProof.payloadLength_eq]
  change
    binaryProofLength (disjunctionLeftDerivation proof.derivation) +
      (binaryStructuralValidityCertificateCode
        (disjunctionCertificate proof.certificate)).length <= _
  omega

theorem disjunctionRight_payloadLength_le
    {left right : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAProof right) :
    (disjunctionRight (left := left) proof).payloadLength <=
      proof.payloadLength + 96 + 8 * disjunctionSyntaxBudget left right := by
  have hproof := disjunctionRightDerivation_binaryProofLength_le
    (left := left) proof.derivation
  have hcertificate := disjunctionCertificate_code_length_le proof.certificate
  rw [CertifiedPAProof.payloadLength_eq,
    CertifiedPAProof.payloadLength_eq]
  change
    binaryProofLength (disjunctionRightDerivation proof.derivation) +
      (binaryStructuralValidityCertificateCode
        (disjunctionCertificate proof.certificate)).length <= _
  omega

theorem disjunctionLeft_verifier_eq_true
    {left right : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAProof left) :
    listedCompactCertifiedPAProofVerifier
      (disjunctionLeft (right := right) proof).code
      (compactFormulaCode (left ⋎ right)) = true :=
  (disjunctionLeft (right := right) proof).verifier_eq_true

theorem disjunctionRight_verifier_eq_true
    {left right : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAProof right) :
    listedCompactCertifiedPAProofVerifier
      (disjunctionRight (left := left) proof).code
      (compactFormulaCode (left ⋎ right)) = true :=
  (disjunctionRight (left := left) proof).verifier_eq_true

#print axioms disjunctionLeft_payloadLength_le
#print axioms disjunctionRight_payloadLength_le
#print axioms disjunctionLeft_verifier_eq_true
#print axioms disjunctionRight_verifier_eq_true

end FoundationCompactCertifiedDisjunction
