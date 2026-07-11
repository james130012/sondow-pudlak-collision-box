import integration.FoundationComputableCompactPAProofEncoder

/-!
# Honest finite-consistency semantics for the compact certified PA checker

The cutoff is the complete binary proof-string payload length.  Foundation's
nested raw proof code is absent from both the checker and the bound.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCertifiedFiniteConsistencyTarget

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationComputableCompactPAProofEncoder

def CertifiedPAProofOf
    (code : Nat)
    (formula : LO.FirstOrder.ArithmeticProposition) : Prop :=
  compactCertifiedPAProofVerifier code (compactFormulaCode formula) = true

theorem certifiedPAProofOf_iff_checks
    (code : Nat)
    (formula : LO.FirstOrder.ArithmeticProposition) :
    CertifiedPAProofOf code formula ↔
      CompactCertifiedPAProofChecks code (compactFormulaCode formula) := by
  exact compactCertifiedPAProofVerifier_eq_true_iff _ _

theorem CertifiedPAProofOf.toDerivation
    {code : Nat}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hproof : CertifiedPAProofOf code formula) :
    Nonempty (LO.FirstOrder.Derivation2 PA {formula}) := by
  exact (certifiedPAProofOf_iff_checks code formula).mp hproof |>.toDerivation

theorem no_certifiedPAProofOf_falsum (code : Nat) :
    ¬ CertifiedPAProofOf code
      (⊥ : LO.FirstOrder.ArithmeticProposition) := by
  intro hproof
  rcases hproof.toDerivation with ⟨derivation⟩
  have proof2 :
      PA ⊢!₂! ((⊥ : LO.FirstOrder.ArithmeticSentence) :
        LO.FirstOrder.ArithmeticProposition) := by
    simpa using derivation
  have hprovable : PA ⊢ (⊥ : LO.FirstOrder.ArithmeticSentence) :=
    ⟨LO.FirstOrder.Theory.Proof2.toProof proof2⟩
  exact LO.Entailment.Consistent.not_bot (𝓢 := PA) inferInstance hprovable

/-- Buss-style finite consistency for the exact compact symbol-length
coordinate: no accepted proof string of contradiction has payload at most the
cutoff. -/
def CertifiedFiniteConsistencyAt (cutoff : Nat) : Prop :=
  ¬∃ code : Nat,
    packedPayloadLength code ≤ cutoff ∧
      CertifiedPAProofOf code (⊥ : LO.FirstOrder.ArithmeticProposition)

theorem certifiedFiniteConsistencyAt (cutoff : Nat) :
    CertifiedFiniteConsistencyAt cutoff := by
  rintro ⟨code, _, hproof⟩
  exact no_certifiedPAProofOf_falsum code hproof

theorem certifiedFiniteConsistencyAt_iff_forall
    (cutoff : Nat) :
    CertifiedFiniteConsistencyAt cutoff ↔
      ∀ code : Nat, packedPayloadLength code ≤ cutoff →
        ¬CertifiedPAProofOf code
          (⊥ : LO.FirstOrder.ArithmeticProposition) := by
  simp [CertifiedFiniteConsistencyAt]

def amplifiedCertifiedFiniteConsistency
    (amplification n : Nat) : Prop :=
  CertifiedFiniteConsistencyAt (2 ^ (amplification * n))

theorem amplifiedCertifiedFiniteConsistency_true
    (amplification n : Nat) :
    amplifiedCertifiedFiniteConsistency amplification n :=
  certifiedFiniteConsistencyAt _

theorem canonicalCode_is_certifiedProofOf
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (hcertificate : certificateValid tree certificate)
    (hconclusion : tree.conclusion = {formula}) :
    CertifiedPAProofOf
      (canonicalPackedCertifiedPAProofCode tree certificate) formula := by
  rw [certifiedPAProofOf_iff_checks]
  exact ⟨tree, certificate, formula, by simp,
    hcertificate, hconclusion, rfl⟩

theorem derivation_has_canonicalCertifiedCode
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (derivation : LO.FirstOrder.Derivation2 PA Gamma)
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hconclusion : Gamma = {formula}) :
    ∃ (tree : CheckedPAProofTree)
        (certificate : StructuralValidityCertificate),
      CertifiedPAProofOf
        (canonicalPackedCertifiedPAProofCode tree certificate) formula := by
  let tree := CheckedPAProofTree.ofDerivation derivation
  have hvalid : structurallyValid tree :=
    structurallyValid_ofDerivation derivation
  rcases exists_certificateValid tree hvalid with
    ⟨certificate, hcertificate⟩
  refine ⟨tree, certificate,
    canonicalCode_is_certifiedProofOf tree certificate formula
      hcertificate ?_⟩
  simpa [tree] using hconclusion

end FoundationCertifiedFiniteConsistencyTarget
