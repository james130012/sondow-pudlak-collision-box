import integration.FoundationCompactCertifiedContextProof

/-!
# Certified disjunction and existential introduction under a shared context

These constructors keep the same finite context in every premise.  Their
proof trees contain the actual `Derivation2.or`, `Derivation2.exs`, and
weakening nodes, and their structural certificates mirror those nodes.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactCertifiedContextProof

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextualModusPonens

namespace CertifiedPAContextProof

def castContext
    {Gamma Delta : Finset LO.FirstOrder.ArithmeticProposition}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (contextEq : Gamma = Delta)
    (proof : CertifiedPAContextProof Gamma formula) :
    CertifiedPAContextProof Delta formula := by
  subst Delta
  exact proof

@[simp] theorem castContext_payloadLength
    {Gamma Delta : Finset LO.FirstOrder.ArithmeticProposition}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (contextEq : Gamma = Delta)
    (proof : CertifiedPAContextProof Gamma formula) :
    (castContext contextEq proof).payloadLength = proof.payloadLength := by
  subst Delta
  rfl

def exFalsoAssumption
    (target : LO.FirstOrder.ArithmeticProposition) :
    CertifiedPAContextProof
      ({∼(⊥ : LO.FirstOrder.ArithmeticProposition)} :
        Finset LO.FirstOrder.ArithmeticProposition) target where
  derivation := LO.FirstOrder.Derivation2.verum (by simp)
  certificate := .leaf
  certificate_valid := by
    simp [CheckedPAProofTree.ofDerivation, certificateValid]

def exFalsoAssumptionFullPayloadCost
    (target : LO.FirstOrder.ArithmeticProposition) : Nat :=
  (binaryNatCode 2).length +
    (binarySequentCode
      (insert target
        ({∼(⊥ : LO.FirstOrder.ArithmeticProposition)} :
          Finset LO.FirstOrder.ArithmeticProposition))).length +
    (binaryNatCode 0).length

theorem exFalsoAssumption_payloadLength_eq
    (target : LO.FirstOrder.ArithmeticProposition) :
    (exFalsoAssumption target).payloadLength =
      exFalsoAssumptionFullPayloadCost target := by
  simp [payloadLength, exFalsoAssumption,
    exFalsoAssumptionFullPayloadCost, binaryProofLength,
    binaryDerivationCode, binaryStructuralValidityCertificateCode]

def insertSubsetOfSubset
    {Gamma Delta : Finset LO.FirstOrder.ArithmeticProposition}
    (formula : LO.FirstOrder.ArithmeticProposition)
    (hsubset : Gamma ⊆ Delta) :
    insert formula Gamma ⊆ insert formula Delta := by
  intro candidate hcandidate
  simp only [Finset.mem_insert] at hcandidate ⊢
  rcases hcandidate with hcandidate | hcandidate
  · exact Or.inl hcandidate
  · exact Or.inr (hsubset hcandidate)

def weakenContext
    {Gamma Delta : Finset LO.FirstOrder.ArithmeticProposition}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAContextProof Gamma formula)
    (hsubset : Gamma ⊆ Delta) :
    CertifiedPAContextProof Delta formula where
  derivation := LO.FirstOrder.Derivation2.wk proof.derivation
    (insertSubsetOfSubset formula hsubset)
  certificate := .unary proof.certificate
  certificate_valid := weakeningCertificate_valid
    proof.derivation proof.certificate
    (insertSubsetOfSubset formula hsubset)
    proof.certificate_valid

theorem weakenContext_payloadLength_le
    {Gamma Delta : Finset LO.FirstOrder.ArithmeticProposition}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAContextProof Gamma formula)
    (hsubset : Gamma ⊆ Delta) :
    (weakenContext proof hsubset).payloadLength <=
      proof.payloadLength +
        weakeningFullAssemblyCost (insert formula Delta) := by
  have hbound := weakening_full_payload_le
    proof.derivation proof.certificate
    (insertSubsetOfSubset formula hsubset)
  simpa [payloadLength, weakenContext] using hbound

def byCasesPositivePremiseSubset
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (target caseFormula : LO.FirstOrder.ArithmeticProposition) :
    insert target (insert (∼caseFormula) Gamma) ⊆
      insert (∼caseFormula) (insert target Gamma) := by
  intro formula hformula
  simp only [Finset.mem_insert] at hformula ⊢
  rcases hformula with hformula | hformula
  · exact Or.inr (Or.inl hformula)
  · rcases hformula with hformula | hformula
    · exact Or.inl hformula
    · exact Or.inr (Or.inr hformula)

def byCasesNegativePremiseSubset
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (target caseFormula : LO.FirstOrder.ArithmeticProposition) :
    insert target (insert caseFormula Gamma) ⊆
      insert caseFormula (insert target Gamma) := by
  intro formula hformula
  simp only [Finset.mem_insert] at hformula ⊢
  rcases hformula with hformula | hformula
  · exact Or.inr (Or.inl hformula)
  · rcases hformula with hformula | hformula
    · exact Or.inl hformula
    · exact Or.inr (Or.inr hformula)

def byCasesDerivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {target caseFormula : LO.FirstOrder.ArithmeticProposition}
    (positiveProof : LO.FirstOrder.Derivation2 PA
      (insert target (insert (∼caseFormula) Gamma)))
    (negativeProof : LO.FirstOrder.Derivation2 PA
      (insert target (insert caseFormula Gamma))) :
    LO.FirstOrder.Derivation2 PA (insert target Gamma) :=
  LO.FirstOrder.Derivation2.cut (φ := caseFormula)
    (LO.FirstOrder.Derivation2.wk negativeProof
      (byCasesNegativePremiseSubset Gamma target caseFormula))
    (LO.FirstOrder.Derivation2.wk positiveProof
      (byCasesPositivePremiseSubset Gamma target caseFormula))

def byCasesCertificate
    (positiveCertificate negativeCertificate :
      StructuralValidityCertificate) : StructuralValidityCertificate :=
  .binary (.unary negativeCertificate) (.unary positiveCertificate)

theorem byCasesCertificate_valid
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {target caseFormula : LO.FirstOrder.ArithmeticProposition}
    (positiveProof : LO.FirstOrder.Derivation2 PA
      (insert target (insert (∼caseFormula) Gamma)))
    (negativeProof : LO.FirstOrder.Derivation2 PA
      (insert target (insert caseFormula Gamma)))
    (positiveCertificate negativeCertificate :
      StructuralValidityCertificate)
    (hpositive : certificateValid
      (CheckedPAProofTree.ofDerivation positiveProof) positiveCertificate)
    (hnegative : certificateValid
      (CheckedPAProofTree.ofDerivation negativeProof) negativeCertificate) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (byCasesDerivation positiveProof negativeProof))
      (byCasesCertificate positiveCertificate negativeCertificate) := by
  have hnegativeSubset :
      (CheckedPAProofTree.ofDerivation negativeProof).conclusion ⊆
        insert caseFormula (insert target Gamma) := by
    rw [CheckedPAProofTree.conclusion_ofDerivation negativeProof]
    exact byCasesNegativePremiseSubset Gamma target caseFormula
  have hpositiveSubset :
      (CheckedPAProofTree.ofDerivation positiveProof).conclusion ⊆
        insert (∼caseFormula) (insert target Gamma) := by
    rw [CheckedPAProofTree.conclusion_ofDerivation positiveProof]
    exact byCasesPositivePremiseSubset Gamma target caseFormula
  simp [byCasesDerivation, byCasesCertificate,
    CheckedPAProofTree.ofDerivation, CheckedPAProofTree.conclusion,
    certificateValid, hpositive, hnegative]
  exact ⟨hnegativeSubset, hpositiveSubset⟩

def byCases
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {target caseFormula : LO.FirstOrder.ArithmeticProposition}
    (positiveProof : CertifiedPAContextProof
      (insert (∼caseFormula) Gamma) target)
    (negativeProof : CertifiedPAContextProof
      (insert caseFormula Gamma) target) :
    CertifiedPAContextProof Gamma target where
  derivation := byCasesDerivation
    positiveProof.derivation negativeProof.derivation
  certificate := byCasesCertificate
    positiveProof.certificate negativeProof.certificate
  certificate_valid := byCasesCertificate_valid
    positiveProof.derivation negativeProof.derivation
    positiveProof.certificate negativeProof.certificate
    positiveProof.certificate_valid negativeProof.certificate_valid

def byCasesDerivationCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (target caseFormula : LO.FirstOrder.ArithmeticProposition) : Nat :=
  (binaryNatCode 9).length +
      (binarySequentCode (insert target Gamma)).length +
      (binaryFormulaCode caseFormula).length +
    (binaryNatCode 7).length +
      (binarySequentCode
        (insert caseFormula (insert target Gamma))).length +
    (binaryNatCode 7).length +
      (binarySequentCode
        (insert (∼caseFormula) (insert target Gamma))).length

theorem byCasesDerivation_binaryProofLength_eq
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {target caseFormula : LO.FirstOrder.ArithmeticProposition}
    (positiveProof : LO.FirstOrder.Derivation2 PA
      (insert target (insert (∼caseFormula) Gamma)))
    (negativeProof : LO.FirstOrder.Derivation2 PA
      (insert target (insert caseFormula Gamma))) :
    binaryProofLength
        (byCasesDerivation positiveProof negativeProof) =
      binaryProofLength positiveProof + binaryProofLength negativeProof +
        byCasesDerivationCost Gamma target caseFormula := by
  simp only [byCasesDerivation, byCasesDerivationCost,
    binaryProofLength, binaryDerivationCode, List.length_append]
  omega

theorem byCasesCertificate_code_length_le
    (positiveCertificate negativeCertificate :
      StructuralValidityCertificate) :
    (binaryStructuralValidityCertificateCode
      (byCasesCertificate positiveCertificate negativeCertificate)).length <=
      (binaryStructuralValidityCertificateCode positiveCertificate).length +
      (binaryStructuralValidityCertificateCode negativeCertificate).length +
        48 := by
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  simp only [byCasesCertificate,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

def byCasesFullAssemblyCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (target caseFormula : LO.FirstOrder.ArithmeticProposition) : Nat :=
  byCasesDerivationCost Gamma target caseFormula + 48

theorem byCases_payloadLength_le
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {target caseFormula : LO.FirstOrder.ArithmeticProposition}
    (positiveProof : CertifiedPAContextProof
      (insert (∼caseFormula) Gamma) target)
    (negativeProof : CertifiedPAContextProof
      (insert caseFormula Gamma) target) :
    (byCases positiveProof negativeProof).payloadLength <=
      positiveProof.payloadLength + negativeProof.payloadLength +
        byCasesFullAssemblyCost Gamma target caseFormula := by
  have hproof := byCasesDerivation_binaryProofLength_eq
    positiveProof.derivation negativeProof.derivation
  have hcertificate := byCasesCertificate_code_length_le
    positiveProof.certificate negativeProof.certificate
  unfold payloadLength byCasesFullAssemblyCost
  change binaryProofLength
      (byCasesDerivation positiveProof.derivation
        negativeProof.derivation) +
    (binaryStructuralValidityCertificateCode
      (byCasesCertificate positiveProof.certificate
        negativeProof.certificate)).length <= _
  omega

def disjunctionAssumptionLeftPremiseSubset
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (target left right : LO.FirstOrder.ArithmeticProposition) :
    insert target (insert (∼left) Gamma) ⊆
      insert (∼left)
        (insert target (insert (∼(left ⋎ right)) Gamma)) := by
  intro formula hformula
  simp only [Finset.mem_insert] at hformula ⊢
  rcases hformula with hformula | hformula
  · exact Or.inr (Or.inl hformula)
  · rcases hformula with hformula | hformula
    · exact Or.inl hformula
    · exact Or.inr (Or.inr (Or.inr hformula))

def disjunctionAssumptionRightPremiseSubset
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (target left right : LO.FirstOrder.ArithmeticProposition) :
    insert target (insert (∼right) Gamma) ⊆
      insert (∼right)
        (insert target (insert (∼(left ⋎ right)) Gamma)) := by
  intro formula hformula
  simp only [Finset.mem_insert] at hformula ⊢
  rcases hformula with hformula | hformula
  · exact Or.inr (Or.inl hformula)
  · rcases hformula with hformula | hformula
    · exact Or.inl hformula
    · exact Or.inr (Or.inr (Or.inr hformula))

def eliminateDisjunctionAssumptionDerivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {target left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : LO.FirstOrder.Derivation2 PA
      (insert target (insert (∼left) Gamma)))
    (rightProof : LO.FirstOrder.Derivation2 PA
      (insert target (insert (∼right) Gamma))) :
    LO.FirstOrder.Derivation2 PA
      (insert target (insert (∼(left ⋎ right)) Gamma)) :=
  LO.FirstOrder.Derivation2.and
    (φ := ∼left) (ψ := ∼right)
    (by simp)
    (LO.FirstOrder.Derivation2.wk leftProof
      (disjunctionAssumptionLeftPremiseSubset
        Gamma target left right))
    (LO.FirstOrder.Derivation2.wk rightProof
      (disjunctionAssumptionRightPremiseSubset
        Gamma target left right))

def eliminateDisjunctionAssumptionCertificate
    (leftCertificate rightCertificate : StructuralValidityCertificate) :
    StructuralValidityCertificate :=
  .binary (.unary leftCertificate) (.unary rightCertificate)

theorem eliminateDisjunctionAssumptionCertificate_valid
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {target left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : LO.FirstOrder.Derivation2 PA
      (insert target (insert (∼left) Gamma)))
    (rightProof : LO.FirstOrder.Derivation2 PA
      (insert target (insert (∼right) Gamma)))
    (leftCertificate rightCertificate : StructuralValidityCertificate)
    (hleft : certificateValid
      (CheckedPAProofTree.ofDerivation leftProof) leftCertificate)
    (hright : certificateValid
      (CheckedPAProofTree.ofDerivation rightProof) rightCertificate) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (eliminateDisjunctionAssumptionDerivation leftProof rightProof))
      (eliminateDisjunctionAssumptionCertificate
        leftCertificate rightCertificate) := by
  have hleftSubset :
      (CheckedPAProofTree.ofDerivation leftProof).conclusion ⊆
        insert (∼left)
          (insert target (insert (∼(left ⋎ right)) Gamma)) := by
    rw [CheckedPAProofTree.conclusion_ofDerivation leftProof]
    exact disjunctionAssumptionLeftPremiseSubset Gamma target left right
  have hrightSubset :
      (CheckedPAProofTree.ofDerivation rightProof).conclusion ⊆
        insert (∼right)
          (insert target (insert (∼(left ⋎ right)) Gamma)) := by
    rw [CheckedPAProofTree.conclusion_ofDerivation rightProof]
    exact disjunctionAssumptionRightPremiseSubset Gamma target left right
  simp [eliminateDisjunctionAssumptionDerivation,
    eliminateDisjunctionAssumptionCertificate,
    CheckedPAProofTree.ofDerivation, CheckedPAProofTree.conclusion,
    certificateValid, hleft, hright]
  exact ⟨hleftSubset, hrightSubset⟩

def eliminateDisjunctionAssumption
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {target left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : CertifiedPAContextProof (insert (∼left) Gamma) target)
    (rightProof : CertifiedPAContextProof (insert (∼right) Gamma) target) :
    CertifiedPAContextProof (insert (∼(left ⋎ right)) Gamma) target where
  derivation := eliminateDisjunctionAssumptionDerivation
    leftProof.derivation rightProof.derivation
  certificate := eliminateDisjunctionAssumptionCertificate
    leftProof.certificate rightProof.certificate
  certificate_valid := eliminateDisjunctionAssumptionCertificate_valid
    leftProof.derivation rightProof.derivation
    leftProof.certificate rightProof.certificate
    leftProof.certificate_valid rightProof.certificate_valid

def eliminateDisjunctionAssumptionDerivationCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (target left right : LO.FirstOrder.ArithmeticProposition) : Nat :=
  let rootContext := insert target (insert (∼(left ⋎ right)) Gamma)
  (binaryNatCode 3).length +
      (binarySequentCode rootContext).length +
      (binaryFormulaCode (∼left)).length +
      (binaryFormulaCode (∼right)).length +
    (binaryNatCode 7).length +
      (binarySequentCode (insert (∼left) rootContext)).length +
    (binaryNatCode 7).length +
      (binarySequentCode (insert (∼right) rootContext)).length

theorem eliminateDisjunctionAssumptionDerivation_binaryProofLength_eq
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {target left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : LO.FirstOrder.Derivation2 PA
      (insert target (insert (∼left) Gamma)))
    (rightProof : LO.FirstOrder.Derivation2 PA
      (insert target (insert (∼right) Gamma))) :
    binaryProofLength
        (eliminateDisjunctionAssumptionDerivation leftProof rightProof) =
      binaryProofLength leftProof + binaryProofLength rightProof +
        eliminateDisjunctionAssumptionDerivationCost
          Gamma target left right := by
  simp only [eliminateDisjunctionAssumptionDerivation,
    eliminateDisjunctionAssumptionDerivationCost,
    binaryProofLength, binaryDerivationCode, List.length_append]
  omega

theorem eliminateDisjunctionAssumptionCertificate_code_length_le
    (leftCertificate rightCertificate : StructuralValidityCertificate) :
    (binaryStructuralValidityCertificateCode
      (eliminateDisjunctionAssumptionCertificate
        leftCertificate rightCertificate)).length <=
      (binaryStructuralValidityCertificateCode leftCertificate).length +
      (binaryStructuralValidityCertificateCode rightCertificate).length +
        48 := by
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  simp only [eliminateDisjunctionAssumptionCertificate,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

def eliminateDisjunctionAssumptionFullAssemblyCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (target left right : LO.FirstOrder.ArithmeticProposition) : Nat :=
  eliminateDisjunctionAssumptionDerivationCost
    Gamma target left right + 48

theorem eliminateDisjunctionAssumption_payloadLength_le
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {target left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : CertifiedPAContextProof (insert (∼left) Gamma) target)
    (rightProof : CertifiedPAContextProof (insert (∼right) Gamma) target) :
    (eliminateDisjunctionAssumption leftProof rightProof).payloadLength <=
      leftProof.payloadLength + rightProof.payloadLength +
        eliminateDisjunctionAssumptionFullAssemblyCost
          Gamma target left right := by
  have hproof :=
    eliminateDisjunctionAssumptionDerivation_binaryProofLength_eq
      leftProof.derivation rightProof.derivation
  have hcertificate :=
    eliminateDisjunctionAssumptionCertificate_code_length_le
      leftProof.certificate rightProof.certificate
  unfold payloadLength eliminateDisjunctionAssumptionFullAssemblyCost
  change binaryProofLength
      (eliminateDisjunctionAssumptionDerivation
        leftProof.derivation rightProof.derivation) +
    (binaryStructuralValidityCertificateCode
      (eliminateDisjunctionAssumptionCertificate
        leftProof.certificate rightProof.certificate)).length <= _
  omega

def disjunctionLeftDerivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : LO.FirstOrder.Derivation2 PA (insert left Gamma)) :
    LO.FirstOrder.Derivation2 PA (insert (left ⋎ right) Gamma) :=
  LO.FirstOrder.Derivation2.or
    (Γ := insert (left ⋎ right) Gamma) (φ := left) (ψ := right)
    (by simp)
    (LO.FirstOrder.Derivation2.wk leftProof (by
      intro formula hformula
      simp only [Finset.mem_insert] at hformula ⊢
      rcases hformula with hformula | hformula
      · exact Or.inl hformula
      · exact Or.inr (Or.inr (Or.inr hformula))))

def disjunctionRightDerivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {left right : LO.FirstOrder.ArithmeticProposition}
    (rightProof : LO.FirstOrder.Derivation2 PA (insert right Gamma)) :
    LO.FirstOrder.Derivation2 PA (insert (left ⋎ right) Gamma) :=
  LO.FirstOrder.Derivation2.or
    (Γ := insert (left ⋎ right) Gamma) (φ := left) (ψ := right)
    (by simp)
    (LO.FirstOrder.Derivation2.wk rightProof (by
      intro formula hformula
      simp only [Finset.mem_insert] at hformula ⊢
      rcases hformula with hformula | hformula
      · exact Or.inr (Or.inl hformula)
      · exact Or.inr (Or.inr (Or.inr hformula))))

def disjunctionCertificate
    (certificate : StructuralValidityCertificate) :
    StructuralValidityCertificate :=
  .unary (.unary certificate)

theorem disjunctionLeftCertificate_valid
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : LO.FirstOrder.Derivation2 PA (insert left Gamma))
    (certificate : StructuralValidityCertificate)
    (hvalid : certificateValid
      (CheckedPAProofTree.ofDerivation leftProof) certificate) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (disjunctionLeftDerivation (right := right) leftProof))
      (disjunctionCertificate certificate) := by
  have hconclusion := CheckedPAProofTree.conclusion_ofDerivation leftProof
  simp [disjunctionLeftDerivation, disjunctionCertificate,
    CheckedPAProofTree.ofDerivation, CheckedPAProofTree.conclusion,
    certificateValid, hvalid]
  change (CheckedPAProofTree.ofDerivation leftProof).conclusion ⊆ _
  rw [hconclusion]
  intro formula hformula
  simp only [Finset.mem_insert] at hformula ⊢
  rcases hformula with hformula | hformula
  · exact Or.inl hformula
  · exact Or.inr (Or.inr (Or.inr hformula))

theorem disjunctionRightCertificate_valid
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {left right : LO.FirstOrder.ArithmeticProposition}
    (rightProof : LO.FirstOrder.Derivation2 PA (insert right Gamma))
    (certificate : StructuralValidityCertificate)
    (hvalid : certificateValid
      (CheckedPAProofTree.ofDerivation rightProof) certificate) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (disjunctionRightDerivation (left := left) rightProof))
      (disjunctionCertificate certificate) := by
  have hconclusion := CheckedPAProofTree.conclusion_ofDerivation rightProof
  simp [disjunctionRightDerivation, disjunctionCertificate,
    CheckedPAProofTree.ofDerivation, CheckedPAProofTree.conclusion,
    certificateValid, hvalid]
  change (CheckedPAProofTree.ofDerivation rightProof).conclusion ⊆ _
  rw [hconclusion]
  intro formula hformula
  simp only [Finset.mem_insert] at hformula ⊢
  rcases hformula with hformula | hformula
  · exact Or.inr (Or.inl hformula)
  · exact Or.inr (Or.inr (Or.inr hformula))

def disjunctionLeft
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {left right : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAContextProof Gamma left) :
    CertifiedPAContextProof Gamma (left ⋎ right) where
  derivation := disjunctionLeftDerivation proof.derivation
  certificate := disjunctionCertificate proof.certificate
  certificate_valid := disjunctionLeftCertificate_valid
    proof.derivation proof.certificate proof.certificate_valid

def disjunctionRight
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {left right : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAContextProof Gamma right) :
    CertifiedPAContextProof Gamma (left ⋎ right) where
  derivation := disjunctionRightDerivation proof.derivation
  certificate := disjunctionCertificate proof.certificate
  certificate_valid := disjunctionRightCertificate_valid
    proof.derivation proof.certificate proof.certificate_valid

def disjunctionDerivationCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (left right : LO.FirstOrder.ArithmeticProposition) : Nat :=
  let disjunctionFormula := left ⋎ right
  (binaryNatCode 4).length +
      (binarySequentCode (insert disjunctionFormula Gamma)).length +
      (binaryFormulaCode left).length +
      (binaryFormulaCode right).length +
    (binaryNatCode 7).length +
      (binarySequentCode
        (insert left (insert right (insert disjunctionFormula Gamma)))).length

theorem disjunctionLeftDerivation_binaryProofLength_eq
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {left right : LO.FirstOrder.ArithmeticProposition}
    (proof : LO.FirstOrder.Derivation2 PA (insert left Gamma)) :
    binaryProofLength
        (disjunctionLeftDerivation (right := right) proof) =
      binaryProofLength proof +
        disjunctionDerivationCost Gamma left right := by
  simp only [disjunctionLeftDerivation, disjunctionDerivationCost,
    binaryProofLength, binaryDerivationCode, List.length_append]
  omega

theorem disjunctionRightDerivation_binaryProofLength_eq
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {left right : LO.FirstOrder.ArithmeticProposition}
    (proof : LO.FirstOrder.Derivation2 PA (insert right Gamma)) :
    binaryProofLength
        (disjunctionRightDerivation (left := left) proof) =
      binaryProofLength proof +
        disjunctionDerivationCost Gamma left right := by
  simp only [disjunctionRightDerivation, disjunctionDerivationCost,
    binaryProofLength, binaryDerivationCode, List.length_append]
  omega

theorem disjunctionCertificate_code_length_le
    (certificate : StructuralValidityCertificate) :
    (binaryStructuralValidityCertificateCode
      (disjunctionCertificate certificate)).length <=
      (binaryStructuralValidityCertificateCode certificate).length + 32 := by
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  simp only [disjunctionCertificate,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

def disjunctionFullAssemblyCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (left right : LO.FirstOrder.ArithmeticProposition) : Nat :=
  disjunctionDerivationCost Gamma left right + 32

theorem disjunctionLeft_payloadLength_le
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {left right : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAContextProof Gamma left) :
    (disjunctionLeft (right := right) proof).payloadLength <=
      proof.payloadLength +
        disjunctionFullAssemblyCost Gamma left right := by
  have hproof := disjunctionLeftDerivation_binaryProofLength_eq
    (right := right) proof.derivation
  have hcertificate := disjunctionCertificate_code_length_le
    proof.certificate
  unfold payloadLength disjunctionFullAssemblyCost
  change binaryProofLength
      (disjunctionLeftDerivation proof.derivation) +
    (binaryStructuralValidityCertificateCode
      (disjunctionCertificate proof.certificate)).length <= _
  omega

theorem disjunctionRight_payloadLength_le
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {left right : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAContextProof Gamma right) :
    (disjunctionRight (left := left) proof).payloadLength <=
      proof.payloadLength +
        disjunctionFullAssemblyCost Gamma left right := by
  have hproof := disjunctionRightDerivation_binaryProofLength_eq
    (left := left) proof.derivation
  have hcertificate := disjunctionCertificate_code_length_le
    proof.certificate
  unfold payloadLength disjunctionFullAssemblyCost
  change binaryProofLength
      (disjunctionRightDerivation proof.derivation) +
    (binaryStructuralValidityCertificateCode
      (disjunctionCertificate proof.certificate)).length <= _
  omega

def existsIntroDerivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bodyProof : LO.FirstOrder.Derivation2 PA
      (insert (formula/[witness]) Gamma)) :
    LO.FirstOrder.Derivation2 PA (insert (∃⁰ formula) Gamma) :=
  LO.FirstOrder.Derivation2.exs
    (Γ := insert (∃⁰ formula) Gamma) (φ := formula) (by simp) witness
    (LO.FirstOrder.Derivation2.wk bodyProof (by simp))

def existsIntroCertificate
    (bodyCertificate : StructuralValidityCertificate) :
    StructuralValidityCertificate :=
  .unary (.unary bodyCertificate)

theorem existsIntroCertificate_valid
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bodyProof : LO.FirstOrder.Derivation2 PA
      (insert (formula/[witness]) Gamma))
    (certificate : StructuralValidityCertificate)
    (hvalid : certificateValid
      (CheckedPAProofTree.ofDerivation bodyProof) certificate) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (existsIntroDerivation witness bodyProof))
      (existsIntroCertificate certificate) := by
  have hconclusion := CheckedPAProofTree.conclusion_ofDerivation bodyProof
  simp [existsIntroDerivation, existsIntroCertificate,
    CheckedPAProofTree.ofDerivation, CheckedPAProofTree.conclusion,
    certificateValid, hvalid]
  change (CheckedPAProofTree.ofDerivation bodyProof).conclusion ⊆ _
  rw [hconclusion]
  simp

def existsIntro
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bodyProof : CertifiedPAContextProof Gamma (formula/[witness])) :
    CertifiedPAContextProof Gamma (∃⁰ formula) where
  derivation := existsIntroDerivation witness bodyProof.derivation
  certificate := existsIntroCertificate bodyProof.certificate
  certificate_valid := existsIntroCertificate_valid
    witness bodyProof.derivation bodyProof.certificate
      bodyProof.certificate_valid

def existsIntroDerivationCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  let instantiated := formula/[witness]
  let existential := (∃⁰ formula : LO.FirstOrder.ArithmeticProposition)
  (binaryNatCode 6).length +
      (binarySequentCode (insert existential Gamma)).length +
      (binaryFormulaCode formula).length +
      (binaryTermCode witness).length +
    (binaryNatCode 7).length +
      (binarySequentCode
        (insert instantiated (insert existential Gamma))).length

theorem existsIntroDerivation_binaryProofLength_eq
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bodyProof : LO.FirstOrder.Derivation2 PA
      (insert (formula/[witness]) Gamma)) :
    binaryProofLength (existsIntroDerivation witness bodyProof) =
      binaryProofLength bodyProof +
        existsIntroDerivationCost Gamma formula witness := by
  simp only [existsIntroDerivation, existsIntroDerivationCost,
    binaryProofLength, binaryDerivationCode, List.length_append]
  omega

theorem existsIntroCertificate_code_length_le
    (certificate : StructuralValidityCertificate) :
    (binaryStructuralValidityCertificateCode
      (existsIntroCertificate certificate)).length <=
      (binaryStructuralValidityCertificateCode certificate).length + 32 := by
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  simp only [existsIntroCertificate,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

def existsIntroFullAssemblyCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  existsIntroDerivationCost Gamma formula witness + 32

theorem existsIntro_payloadLength_le
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (bodyProof : CertifiedPAContextProof Gamma (formula/[witness])) :
    (existsIntro witness bodyProof).payloadLength <=
      bodyProof.payloadLength +
        existsIntroFullAssemblyCost Gamma formula witness := by
  have hproof := existsIntroDerivation_binaryProofLength_eq
    witness bodyProof.derivation
  have hcertificate := existsIntroCertificate_code_length_le
    bodyProof.certificate
  unfold payloadLength existsIntroFullAssemblyCost
  change binaryProofLength
      (existsIntroDerivation witness bodyProof.derivation) +
    (binaryStructuralValidityCertificateCode
      (existsIntroCertificate bodyProof.certificate)).length <= _
  omega

#print axioms disjunctionLeft_payloadLength_le
#print axioms disjunctionRight_payloadLength_le
#print axioms existsIntro_payloadLength_le

end CertifiedPAContextProof

end FoundationCompactCertifiedContextProof
