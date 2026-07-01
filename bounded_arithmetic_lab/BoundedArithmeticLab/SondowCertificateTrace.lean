/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CertificateVerifier

/-!
# Sondow certificates to verifier traces

This module separates three audit layers:

* a Sondow certificate is the mathematical witness,
* a compiler turns a valid Sondow certificate into an S21 proof certificate,
* the proof-certificate verifier accepts that proof certificate.
-/

namespace BoundedArithmeticLab

universe u

structure SondowCertificateSystem
    (target : ℕ → BAFormula) (bound : ℕ → ℝ) where
  Cert : Type u
  valid : ℕ → Cert → Prop
  certSize : Cert → ℕ
  proofOfValid :
    ∀ n : ℕ, ∀ cert : Cert, valid n cert → BAProofObject BussS21Axiom
  proof_conclusion :
    ∀ n : ℕ, ∀ cert : Cert, ∀ hvalid : valid n cert,
      (proofOfValid n cert hvalid).conclusion = target n
  proof_size_le_cert_size :
    ∀ n : ℕ, ∀ cert : Cert, ∀ hvalid : valid n cert,
      ((proofOfValid n cert hvalid).size + 2 : ℕ) ≤ certSize cert
  cert_size_le_bound :
    ∀ n : ℕ, ∀ cert : Cert, valid n cert →
      (certSize cert : ℝ) ≤ bound n

structure SondowCertificatesEventually
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    (system : SondowCertificateSystem.{u} target bound) where
  exists_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ cert : system.Cert, system.valid n cert

def SondowCertificateSystem.toProofCertificate
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    (system : SondowCertificateSystem.{u} target bound)
    {n : ℕ} {cert : system.Cert} (hvalid : system.valid n cert) :
    BAProofObject BussS21Axiom :=
  system.proofOfValid n cert hvalid

theorem SondowCertificateSystem.proof_size_plus_two_le_bound
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    (system : SondowCertificateSystem.{u} target bound)
    {n : ℕ} {cert : system.Cert} (hvalid : system.valid n cert) :
    (((system.toProofCertificate hvalid).size + 2 : ℕ) : ℝ) ≤ bound n := by
  have hcertNat := system.proof_size_le_cert_size n cert hvalid
  have hcertReal : (((system.toProofCertificate hvalid).size + 2 : ℕ) : ℝ) ≤
      (system.certSize cert : ℝ) := by
    exact_mod_cast hcertNat
  exact hcertReal.trans (system.cert_size_le_bound n cert hvalid)

def SondowCertificateSystem.acceptedTraceOfValid
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    (system : SondowCertificateSystem.{u} target bound)
    {n : ℕ} {cert : system.Cert} (hvalid : system.valid n cert) :
    CertificateVerifierMachine.AcceptedTrace
      (proofCertificateVerifierMachine target bound) n where
  cert := system.toProofCertificate hvalid
  final :=
    ProofCertificateState.accepted n (system.toProofCertificate hvalid)
      (system.proof_conclusion n cert hvalid)
      (system.proof_size_plus_two_le_bound hvalid)
  steps := 1
  reaches :=
    CertificateVerifierMachine.Reaches.cons
      (ProofCertificateState.Step.accept
        (system.proof_conclusion n cert hvalid)
        (system.proof_size_plus_two_le_bound hvalid))
      (CertificateVerifierMachine.Reaches.refl _)
  accepts := by
    simp [proofCertificateVerifierMachine, ProofCertificateState.accepting]

theorem SondowCertificateSystem.acceptsInput_of_valid
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    (system : SondowCertificateSystem.{u} target bound)
    {n : ℕ} {cert : system.Cert} (hvalid : system.valid n cert) :
    CertificateVerifierMachine.acceptsInput
      (proofCertificateVerifierMachine target bound) n :=
  ⟨system.acceptedTraceOfValid hvalid⟩

theorem SondowCertificatesEventually.toEventualAcceptance
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    {system : SondowCertificateSystem.{u} target bound}
    (h : SondowCertificatesEventually system) :
    EventualAcceptanceUnderRationality
      (CertificateVerifierMachine.acceptsInput
        (proofCertificateVerifierMachine target bound)) where
  accepts_eventually := by
    rcases h.exists_eventually with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    rcases hN n hn with ⟨cert, hvalid⟩
    exact system.acceptsInput_of_valid hvalid

theorem collision_of_sondow_certificates_calibrated_pudlak
    {target : ℕ → BAFormula} {code : BAFormula → FormulaCode}
    {bound : ℕ → ℝ}
    {system : SondowCertificateSystem.{u} target bound}
    (hbound : IsPolynomialBound bound)
    (hcerts : SondowCertificatesEventually system)
    (calibration : ConcreteBussPudlakBoxCalibration target code) :
    False :=
  proofCertificateVerifierMachine.collision_of_proof_certificate_verifier_calibrated_pudlak
    hbound hcerts.toEventualAcceptance calibration

theorem collision_of_sondow_certificates_formula_length_calibrated_pudlak
    {target : ℕ → BAFormula} {code : BAFormula → FormulaCode}
    {bound : ℕ → ℝ}
    {system : SondowCertificateSystem.{u} target bound}
    (hbound : IsPolynomialBound bound)
    (hcerts : SondowCertificatesEventually system)
    (calibration : ConcreteBussPudlakFormulaLengthCalibration target code) :
    False :=
  collision_of_sondow_certificates_calibrated_pudlak
    hbound hcerts calibration.toBoxCalibration

end BoundedArithmeticLab
