/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.SondowProjectComponents

/-!
# Component certificate systems to Sondow exports

This file is the audit-facing construction of component exports from accepted
component certificates.

The important separation is:

* a component certificate system supplies a verifier/compiler theorem from a
  valid certificate to an S21 `BAProofObject`;
* eventual component certificates supply the data produced by the Sondow
  rationality route;
* Lean combines these two inputs into
  `SondowMainReproofBlockCertificatesEventually`.

No opaque project atom is declared as an S21 axiom here.
-/

namespace BoundedArithmeticLab

universe u

namespace BAProofObjectCertificate

structure Valid
    (target : ℕ → BAFormula) (bound : ℕ → ℝ)
    (n : ℕ) (cert : BAProofObject BussS21Axiom) : Prop where
  conclusion_eq : cert.conclusion = target n
  size_plus_two_le_bound :
    (((cert.size + 2 : ℕ) : ℝ)) ≤ bound n

def system (target : ℕ → BAFormula) (bound : ℕ → ℝ) :
    SondowCertificateSystem target bound where
  Cert := BAProofObject BussS21Axiom
  valid := Valid target bound
  certSize := fun cert => cert.size + 2
  proofOfValid := by
    intro _n cert _hvalid
    exact cert
  proof_conclusion := by
    intro _n _cert hvalid
    exact hvalid.conclusion_eq
  proof_size_le_cert_size := by
    intro _n _cert _hvalid
    rfl
  cert_size_le_bound := by
    intro _n _cert hvalid
    exact hvalid.size_plus_two_le_bound

end BAProofObjectCertificate

structure SondowComponentCertificateSystems
    (components : SondowComponentFormulas) (bounds : SondowComponentBounds)
    where
  productSystem :
    SondowCertificateSystem.{u} components.product bounds.product
  logSystem :
    SondowCertificateSystem.{u} components.logRelation bounds.logRelation
  decompositionSystem :
    SondowCertificateSystem.{u} components.decomposition bounds.decomposition
  threePowSystem :
    SondowCertificateSystem.{u} components.threePow bounds.threePow
  payloadSystem :
    SondowCertificateSystem.{u} components.payload bounds.payload

def proofObjectComponentCertificateSystems
    (components : SondowComponentFormulas) (bounds : SondowComponentBounds) :
    SondowComponentCertificateSystems components bounds where
  productSystem :=
    BAProofObjectCertificate.system components.product bounds.product
  logSystem :=
    BAProofObjectCertificate.system
      components.logRelation bounds.logRelation
  decompositionSystem :=
    BAProofObjectCertificate.system
      components.decomposition bounds.decomposition
  threePowSystem :=
    BAProofObjectCertificate.system components.threePow bounds.threePow
  payloadSystem :=
    BAProofObjectCertificate.system components.payload bounds.payload

def sondowProjectProofObjectCertificateSystems
    (bounds : SondowComponentBounds) :
    SondowComponentCertificateSystems sondowProjectComponentFormulas bounds :=
  proofObjectComponentCertificateSystems sondowProjectComponentFormulas bounds

namespace SondowCertificateSystem

theorem proof_size_le_bound
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    (system : SondowCertificateSystem.{u} target bound)
    {n : ℕ} {cert : system.Cert} (hvalid : system.valid n cert) :
    ((system.toProofCertificate hvalid).size : ℝ) ≤ bound n := by
  have hwithOverhead := system.proof_size_plus_two_le_bound hvalid
  have hnat :
      (system.toProofCertificate hvalid).size ≤
        (system.toProofCertificate hvalid).size + 2 :=
    Nat.le_add_right _ _
  have hreal :
      ((system.toProofCertificate hvalid).size : ℝ) ≤
        (((system.toProofCertificate hvalid).size + 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  exact hreal.trans hwithOverhead

end SondowCertificateSystem

structure SondowComponentSystemCertificateAt
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    (systems : SondowComponentCertificateSystems.{u} components bounds)
    (n : ℕ) where
  productCert : systems.productSystem.Cert
  productValid : systems.productSystem.valid n productCert
  logCert : systems.logSystem.Cert
  logValid : systems.logSystem.valid n logCert
  decompositionCert : systems.decompositionSystem.Cert
  decompositionValid :
    systems.decompositionSystem.valid n decompositionCert
  threePowCert : systems.threePowSystem.Cert
  threePowValid : systems.threePowSystem.valid n threePowCert
  payloadCert : systems.payloadSystem.Cert
  payloadValid : systems.payloadSystem.valid n payloadCert

structure SondowComponentSystemCertificatesEventually
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    (systems : SondowComponentCertificateSystems.{u} components bounds) where
  exists_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty (SondowComponentSystemCertificateAt systems n)

namespace SondowComponentSystemCertificateAt

def productProof
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {systems : SondowComponentCertificateSystems.{u} components bounds}
    {n : ℕ} (certs : SondowComponentSystemCertificateAt systems n) :
    BAProofObject BussS21Axiom :=
  systems.productSystem.toProofCertificate certs.productValid

def logProof
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {systems : SondowComponentCertificateSystems.{u} components bounds}
    {n : ℕ} (certs : SondowComponentSystemCertificateAt systems n) :
    BAProofObject BussS21Axiom :=
  systems.logSystem.toProofCertificate certs.logValid

def decompositionProof
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {systems : SondowComponentCertificateSystems.{u} components bounds}
    {n : ℕ} (certs : SondowComponentSystemCertificateAt systems n) :
    BAProofObject BussS21Axiom :=
  systems.decompositionSystem.toProofCertificate certs.decompositionValid

def threePowProof
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {systems : SondowComponentCertificateSystems.{u} components bounds}
    {n : ℕ} (certs : SondowComponentSystemCertificateAt systems n) :
    BAProofObject BussS21Axiom :=
  systems.threePowSystem.toProofCertificate certs.threePowValid

def payloadProof
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {systems : SondowComponentCertificateSystems.{u} components bounds}
    {n : ℕ} (certs : SondowComponentSystemCertificateAt systems n) :
    BAProofObject BussS21Axiom :=
  systems.payloadSystem.toProofCertificate certs.payloadValid

theorem productProof_conclusion
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {systems : SondowComponentCertificateSystems.{u} components bounds}
    {n : ℕ} (certs : SondowComponentSystemCertificateAt systems n) :
    certs.productProof.conclusion = components.product n :=
  systems.productSystem.proof_conclusion n certs.productCert
    certs.productValid

theorem logProof_conclusion
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {systems : SondowComponentCertificateSystems.{u} components bounds}
    {n : ℕ} (certs : SondowComponentSystemCertificateAt systems n) :
    certs.logProof.conclusion = components.logRelation n :=
  systems.logSystem.proof_conclusion n certs.logCert certs.logValid

theorem decompositionProof_conclusion
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {systems : SondowComponentCertificateSystems.{u} components bounds}
    {n : ℕ} (certs : SondowComponentSystemCertificateAt systems n) :
    certs.decompositionProof.conclusion = components.decomposition n :=
  systems.decompositionSystem.proof_conclusion n certs.decompositionCert
    certs.decompositionValid

theorem threePowProof_conclusion
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {systems : SondowComponentCertificateSystems.{u} components bounds}
    {n : ℕ} (certs : SondowComponentSystemCertificateAt systems n) :
    certs.threePowProof.conclusion = components.threePow n :=
  systems.threePowSystem.proof_conclusion n certs.threePowCert
    certs.threePowValid

theorem payloadProof_conclusion
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {systems : SondowComponentCertificateSystems.{u} components bounds}
    {n : ℕ} (certs : SondowComponentSystemCertificateAt systems n) :
    certs.payloadProof.conclusion = components.payload n :=
  systems.payloadSystem.proof_conclusion n certs.payloadCert
    certs.payloadValid

theorem productProof_size_le
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {systems : SondowComponentCertificateSystems.{u} components bounds}
    {n : ℕ} (certs : SondowComponentSystemCertificateAt systems n) :
    (certs.productProof.size : ℝ) ≤ bounds.product n :=
  systems.productSystem.proof_size_le_bound certs.productValid

theorem logProof_size_le
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {systems : SondowComponentCertificateSystems.{u} components bounds}
    {n : ℕ} (certs : SondowComponentSystemCertificateAt systems n) :
    (certs.logProof.size : ℝ) ≤ bounds.logRelation n :=
  systems.logSystem.proof_size_le_bound certs.logValid

theorem decompositionProof_size_le
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {systems : SondowComponentCertificateSystems.{u} components bounds}
    {n : ℕ} (certs : SondowComponentSystemCertificateAt systems n) :
    (certs.decompositionProof.size : ℝ) ≤ bounds.decomposition n :=
  systems.decompositionSystem.proof_size_le_bound certs.decompositionValid

theorem threePowProof_size_le
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {systems : SondowComponentCertificateSystems.{u} components bounds}
    {n : ℕ} (certs : SondowComponentSystemCertificateAt systems n) :
    (certs.threePowProof.size : ℝ) ≤ bounds.threePow n :=
  systems.threePowSystem.proof_size_le_bound certs.threePowValid

theorem payloadProof_size_le
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {systems : SondowComponentCertificateSystems.{u} components bounds}
    {n : ℕ} (certs : SondowComponentSystemCertificateAt systems n) :
    (certs.payloadProof.size : ℝ) ≤ bounds.payload n :=
  systems.payloadSystem.proof_size_le_bound certs.payloadValid

end SondowComponentSystemCertificateAt

namespace SondowComponentCertificate

structure ProofObjectSystemValid
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
  product_size_plus_two_le :
    (((cert.productProof.size + 2 : ℕ) : ℝ)) ≤ bounds.product n
  log_size_plus_two_le :
    (((cert.logProof.size + 2 : ℕ) : ℝ)) ≤ bounds.logRelation n
  decomposition_size_plus_two_le :
    (((cert.decompositionProof.size + 2 : ℕ) : ℝ)) ≤
      bounds.decomposition n
  threePow_size_plus_two_le :
    (((cert.threePowProof.size + 2 : ℕ) : ℝ)) ≤ bounds.threePow n
  payload_size_plus_two_le :
    (((cert.payloadProof.size + 2 : ℕ) : ℝ)) ≤ bounds.payload n

def ProofObjectSystemValid.toSystemCertificateAt
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {n : ℕ} {cert : SondowComponentCertificate}
    (hvalid : ProofObjectSystemValid components bounds n cert) :
    SondowComponentSystemCertificateAt
      (proofObjectComponentCertificateSystems components bounds) n where
  productCert := cert.productProof
  productValid :=
    { conclusion_eq := hvalid.product_conclusion
      size_plus_two_le_bound := hvalid.product_size_plus_two_le }
  logCert := cert.logProof
  logValid :=
    { conclusion_eq := hvalid.log_conclusion
      size_plus_two_le_bound := hvalid.log_size_plus_two_le }
  decompositionCert := cert.decompositionProof
  decompositionValid :=
    { conclusion_eq := hvalid.decomposition_conclusion
      size_plus_two_le_bound := hvalid.decomposition_size_plus_two_le }
  threePowCert := cert.threePowProof
  threePowValid :=
    { conclusion_eq := hvalid.threePow_conclusion
      size_plus_two_le_bound := hvalid.threePow_size_plus_two_le }
  payloadCert := cert.payloadProof
  payloadValid :=
    { conclusion_eq := hvalid.payload_conclusion
      size_plus_two_le_bound := hvalid.payload_size_plus_two_le }

end SondowComponentCertificate

namespace SondowComponentSystemCertificatesEventually

noncomputable def chooseAt
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {systems : SondowComponentCertificateSystems.{u} components bounds}
    (h : SondowComponentSystemCertificatesEventually systems)
    (n : ℕ) (hn : Classical.choose h.exists_eventually ≤ n) :
    SondowComponentSystemCertificateAt systems n :=
  Classical.choice ((Classical.choose_spec h.exists_eventually) n hn)

noncomputable def toMainReproofBlockCertificatesEventually
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    {systems : SondowComponentCertificateSystems.{u} components bounds}
    (h : SondowComponentSystemCertificatesEventually systems) :
    SondowMainReproofBlockCertificatesEventually components bounds where
  threshold := Classical.choose h.exists_eventually
  productLog := by
    intro n hn
    let certs := h.chooseAt n hn
    exact
      { productProof := certs.productProof
        logProof := certs.logProof }
  decompositionProof := by
    intro n hn
    exact (h.chooseAt n hn).decompositionProof
  threePowProof := by
    intro n hn
    exact (h.chooseAt n hn).threePowProof
  payloadProof := by
    intro n hn
    exact (h.chooseAt n hn).payloadProof
  product_conclusion := by
    intro n hn
    exact (h.chooseAt n hn).productProof_conclusion
  log_conclusion := by
    intro n hn
    exact (h.chooseAt n hn).logProof_conclusion
  decomposition_conclusion := by
    intro n hn
    exact (h.chooseAt n hn).decompositionProof_conclusion
  threePow_conclusion := by
    intro n hn
    exact (h.chooseAt n hn).threePowProof_conclusion
  payload_conclusion := by
    intro n hn
    exact (h.chooseAt n hn).payloadProof_conclusion
  product_size_le := by
    intro n hn
    exact (h.chooseAt n hn).productProof_size_le
  log_size_le := by
    intro n hn
    exact (h.chooseAt n hn).logProof_size_le
  decomposition_size_le := by
    intro n hn
    exact (h.chooseAt n hn).decompositionProof_size_le
  threePow_size_le := by
    intro n hn
    exact (h.chooseAt n hn).threePowProof_size_le
  payload_size_le := by
    intro n hn
    exact (h.chooseAt n hn).payloadProof_size_le

end SondowComponentSystemCertificatesEventually

end BoundedArithmeticLab
