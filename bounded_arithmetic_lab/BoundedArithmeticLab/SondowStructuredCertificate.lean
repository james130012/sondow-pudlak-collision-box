/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.SondowCertificateTrace

/-!
# Structured Sondow certificate components

This module specializes `SondowCertificateSystem` to the audit-facing Sondow
components:

* product,
* log relation,
* decomposition,
* `3^n`/LCM bound,
* payload.

The certificate-to-proof map is no longer a free field.  It is the fixed
right-nested conjunction of the five component proof objects.
-/

namespace BoundedArithmeticLab

structure SondowComponentFormulas where
  product : ℕ → BAFormula
  logRelation : ℕ → BAFormula
  decomposition : ℕ → BAFormula
  threePow : ℕ → BAFormula
  payload : ℕ → BAFormula

namespace SondowComponentFormulas

def target (components : SondowComponentFormulas) (n : ℕ) : BAFormula :=
  BAFormula.and (components.product n)
    (BAFormula.and (components.logRelation n)
      (BAFormula.and (components.decomposition n)
        (BAFormula.and (components.threePow n) (components.payload n))))

end SondowComponentFormulas

namespace BAProofObject

def andIntro {Ax : BAFormula → Prop}
    (p q : BAProofObject Ax) : BAProofObject Ax where
  conclusion := BAFormula.and p.conclusion q.conclusion
  derivation := BADerivation.andIntro p.derivation q.derivation

@[simp] theorem size_andIntro {Ax : BAFormula → Prop}
    (p q : BAProofObject Ax) :
    (p.andIntro q).size = p.size + q.size + 1 := by
  rfl

end BAProofObject

structure SondowComponentCertificate where
  productProof : BAProofObject BussS21Axiom
  logProof : BAProofObject BussS21Axiom
  decompositionProof : BAProofObject BussS21Axiom
  threePowProof : BAProofObject BussS21Axiom
  payloadProof : BAProofObject BussS21Axiom

structure SondowComponentBounds where
  product : ℕ → ℝ
  logRelation : ℕ → ℝ
  decomposition : ℕ → ℝ
  threePow : ℕ → ℝ
  payload : ℕ → ℝ
  product_poly : IsPolynomialBound product
  log_poly : IsPolynomialBound logRelation
  decomposition_poly : IsPolynomialBound decomposition
  threePow_poly : IsPolynomialBound threePow
  payload_poly : IsPolynomialBound payload

namespace SondowComponentBounds

def combined (bounds : SondowComponentBounds) (n : ℕ) : ℝ :=
  bounds.product n +
    (bounds.logRelation n +
      (bounds.decomposition n +
        (bounds.threePow n + bounds.payload n + 1) + 1) + 1) + 1 + 2

theorem combined_poly (bounds : SondowComponentBounds) :
    IsPolynomialBound bounds.combined := by
  have h_three_payload :
      IsPolynomialBound
        (fun n : ℕ => bounds.threePow n + bounds.payload n) :=
    bounds.threePow_poly.add bounds.payload_poly
  have h_three_payload_one :
      IsPolynomialBound
        (fun n : ℕ => bounds.threePow n + bounds.payload n + 1) :=
    h_three_payload.add_const 1
  have h_decomp :
      IsPolynomialBound
        (fun n : ℕ =>
          bounds.decomposition n + (bounds.threePow n + bounds.payload n + 1)) :=
    bounds.decomposition_poly.add h_three_payload_one
  have h_decomp_one :
      IsPolynomialBound
        (fun n : ℕ =>
          bounds.decomposition n + (bounds.threePow n + bounds.payload n + 1) + 1) :=
    h_decomp.add_const 1
  have h_log :
      IsPolynomialBound
        (fun n : ℕ =>
          bounds.logRelation n +
            (bounds.decomposition n + (bounds.threePow n + bounds.payload n + 1) + 1)) :=
    bounds.log_poly.add h_decomp_one
  have h_log_one :
      IsPolynomialBound
        (fun n : ℕ =>
          bounds.logRelation n +
            (bounds.decomposition n + (bounds.threePow n + bounds.payload n + 1) + 1) + 1) :=
    h_log.add_const 1
  have h_product :
      IsPolynomialBound
        (fun n : ℕ =>
          bounds.product n +
            (bounds.logRelation n +
              (bounds.decomposition n +
                (bounds.threePow n + bounds.payload n + 1) + 1) + 1)) :=
    bounds.product_poly.add h_log_one
  have h_product_one :
      IsPolynomialBound
        (fun n : ℕ =>
          bounds.product n +
            (bounds.logRelation n +
              (bounds.decomposition n +
                (bounds.threePow n + bounds.payload n + 1) + 1) + 1) + 1) :=
    h_product.add_const 1
  change IsPolynomialBound
    (fun n : ℕ =>
      bounds.product n +
        (bounds.logRelation n +
          (bounds.decomposition n +
            (bounds.threePow n + bounds.payload n + 1) + 1) + 1) + 1 + 2)
  exact h_product_one.add_const 2

end SondowComponentBounds

namespace SondowComponentCertificate

def buildProof (cert : SondowComponentCertificate) :
    BAProofObject BussS21Axiom :=
  cert.productProof.andIntro
    (cert.logProof.andIntro
      (cert.decompositionProof.andIntro
        (cert.threePowProof.andIntro cert.payloadProof)))

def certSize (cert : SondowComponentCertificate) : ℕ :=
  cert.buildProof.size + 2

structure Valid
    (components : SondowComponentFormulas) (bound : ℕ → ℝ)
    (n : ℕ) (cert : SondowComponentCertificate) : Prop where
  product_conclusion :
    cert.productProof.conclusion = components.product n
  log_conclusion :
    cert.logProof.conclusion = components.logRelation n
  decomposition_conclusion :
    cert.decompositionProof.conclusion = components.decomposition n
  threePow_conclusion :
    cert.threePowProof.conclusion = components.threePow n
  payload_conclusion :
    cert.payloadProof.conclusion = components.payload n
  size_le_bound :
    (cert.certSize : ℝ) ≤ bound n

theorem buildProof_conclusion
    {components : SondowComponentFormulas} {bound : ℕ → ℝ}
    {n : ℕ} {cert : SondowComponentCertificate}
    (hvalid : Valid components bound n cert) :
    cert.buildProof.conclusion = components.target n := by
  change
    BAFormula.and cert.productProof.conclusion
      (BAFormula.and cert.logProof.conclusion
        (BAFormula.and cert.decompositionProof.conclusion
          (BAFormula.and cert.threePowProof.conclusion
            cert.payloadProof.conclusion))) =
      components.target n
  rw [hvalid.product_conclusion, hvalid.log_conclusion,
    hvalid.decomposition_conclusion, hvalid.threePow_conclusion,
    hvalid.payload_conclusion]
  rfl

theorem buildProof_size_plus_two_le_certSize
    (cert : SondowComponentCertificate) :
    cert.buildProof.size + 2 ≤ cert.certSize := by
  rfl

structure ComponentSizeValid
    (components : SondowComponentFormulas) (bounds : SondowComponentBounds)
    (n : ℕ) (cert : SondowComponentCertificate) : Prop where
  product_conclusion :
    cert.productProof.conclusion = components.product n
  log_conclusion :
    cert.logProof.conclusion = components.logRelation n
  decomposition_conclusion :
    cert.decompositionProof.conclusion = components.decomposition n
  threePow_conclusion :
    cert.threePowProof.conclusion = components.threePow n
  payload_conclusion :
    cert.payloadProof.conclusion = components.payload n
  product_size_le :
    (cert.productProof.size : ℝ) ≤ bounds.product n
  log_size_le :
    (cert.logProof.size : ℝ) ≤ bounds.logRelation n
  decomposition_size_le :
    (cert.decompositionProof.size : ℝ) ≤ bounds.decomposition n
  threePow_size_le :
    (cert.threePowProof.size : ℝ) ≤ bounds.threePow n
  payload_size_le :
    (cert.payloadProof.size : ℝ) ≤ bounds.payload n

theorem certSize_le_combined_bound
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {n : ℕ} {cert : SondowComponentCertificate}
    (hvalid : ComponentSizeValid components bounds n cert) :
    (cert.certSize : ℝ) ≤ bounds.combined n := by
  have hproduct : (cert.productProof.derivation.size : ℝ) ≤ bounds.product n := by
    simpa [BAProofObject.size] using hvalid.product_size_le
  have hlog : (cert.logProof.derivation.size : ℝ) ≤ bounds.logRelation n := by
    simpa [BAProofObject.size] using hvalid.log_size_le
  have hdecomp :
      (cert.decompositionProof.derivation.size : ℝ) ≤ bounds.decomposition n := by
    simpa [BAProofObject.size] using hvalid.decomposition_size_le
  have hthree :
      (cert.threePowProof.derivation.size : ℝ) ≤ bounds.threePow n := by
    simpa [BAProofObject.size] using hvalid.threePow_size_le
  have hpayload : (cert.payloadProof.derivation.size : ℝ) ≤ bounds.payload n := by
    simpa [BAProofObject.size] using hvalid.payload_size_le
  dsimp [certSize, buildProof, BAProofObject.andIntro, BAProofObject.size,
    BADerivation.size, SondowComponentBounds.combined]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  linarith

def ComponentSizeValid.toValid
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {n : ℕ} {cert : SondowComponentCertificate}
    (hvalid : ComponentSizeValid components bounds n cert) :
    Valid components bounds.combined n cert where
  product_conclusion := hvalid.product_conclusion
  log_conclusion := hvalid.log_conclusion
  decomposition_conclusion := hvalid.decomposition_conclusion
  threePow_conclusion := hvalid.threePow_conclusion
  payload_conclusion := hvalid.payload_conclusion
  size_le_bound := certSize_le_combined_bound hvalid

end SondowComponentCertificate

def sondowComponentCertificateSystem
    (components : SondowComponentFormulas) (bound : ℕ → ℝ) :
    SondowCertificateSystem (components.target) bound where
  Cert := SondowComponentCertificate
  valid := SondowComponentCertificate.Valid components bound
  certSize := SondowComponentCertificate.certSize
  proofOfValid := by
    intro n cert _hvalid
    exact cert.buildProof
  proof_conclusion := by
    intro n cert hvalid
    exact SondowComponentCertificate.buildProof_conclusion hvalid
  proof_size_le_cert_size := by
    intro n cert _hvalid
    exact SondowComponentCertificate.buildProof_size_plus_two_le_certSize cert
  cert_size_le_bound := by
    intro n cert hvalid
    exact hvalid.size_le_bound

structure SondowComponentCertificatesEventually
    (components : SondowComponentFormulas) (bound : ℕ → ℝ) where
  exists_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ cert : SondowComponentCertificate,
        SondowComponentCertificate.Valid components bound n cert

def SondowComponentCertificatesEventually.toSondowCertificatesEventually
    {components : SondowComponentFormulas} {bound : ℕ → ℝ}
    (h : SondowComponentCertificatesEventually components bound) :
    SondowCertificatesEventually
      (sondowComponentCertificateSystem components bound) where
  exists_eventually := h.exists_eventually

theorem collision_of_sondow_component_certificates_formula_length_calibrated_pudlak
    {components : SondowComponentFormulas}
    {code : BAFormula → FormulaCode} {bound : ℕ → ℝ}
    (hbound : IsPolynomialBound bound)
    (hcerts : SondowComponentCertificatesEventually components bound)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration components.target code) :
    False :=
  collision_of_sondow_certificates_formula_length_calibrated_pudlak
    (system := sondowComponentCertificateSystem components bound)
    hbound hcerts.toSondowCertificatesEventually calibration

structure SondowComponentSizeCertificatesEventually
    (components : SondowComponentFormulas) (bounds : SondowComponentBounds) where
  exists_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ cert : SondowComponentCertificate,
        SondowComponentCertificate.ComponentSizeValid components bounds n cert

def SondowComponentSizeCertificatesEventually.toComponentCertificatesEventually
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    (h : SondowComponentSizeCertificatesEventually components bounds) :
    SondowComponentCertificatesEventually components bounds.combined where
  exists_eventually := by
    rcases h.exists_eventually with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    rcases hN n hn with ⟨cert, hvalid⟩
    exact ⟨cert, hvalid.toValid⟩

theorem collision_of_sondow_component_size_certificates_formula_length_calibrated_pudlak
    {components : SondowComponentFormulas}
    {code : BAFormula → FormulaCode}
    {bounds : SondowComponentBounds}
    (hcerts : SondowComponentSizeCertificatesEventually components bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration components.target code) :
    False :=
  collision_of_sondow_component_certificates_formula_length_calibrated_pudlak
    bounds.combined_poly hcerts.toComponentCertificatesEventually calibration

end BoundedArithmeticLab
