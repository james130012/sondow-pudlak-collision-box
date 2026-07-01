/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.SondowRationalityExports

/-!
# Hilbert/proof-code bridge to project BA proof objects

This module is the narrow bridge expected from the main repository's
Hilbert/proof-code route.

It does not identify main-library Hilbert proofs with sidecar `BAProofObject`s
by definitional equality.  Instead it states the exact compiler obligation:
each accepted source proof-code certificate must compile to an S21
`BAProofObject` of the corresponding project component formula, with the
declared size bound.  Once those five compiler obligations and the rationality
source certificates are supplied, Lean constructs
`SondowRationalityToProjectProofObjectCertificates`.
-/

namespace BoundedArithmeticLab

universe u

structure ComponentProofCodeCompiler
    (target : ℕ → BAFormula) (bound : ℕ → ℝ)
    (expectedCode : ℕ → FormulaCode) where
  SourceCert : Type u
  valid : ℕ → SourceCert → Prop
  sourceCode : ℕ → FormulaCode
  sourceCode_eq_expected : ∀ n : ℕ, sourceCode n = expectedCode n
  sourceSize : SourceCert → ℕ
  compile :
    ∀ n : ℕ, ∀ cert : SourceCert, valid n cert →
      BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ n : ℕ, ∀ cert : SourceCert, ∀ hvalid : valid n cert,
      (compile n cert hvalid).conclusion = target n
  compile_size_plus_two_le :
    ∀ n : ℕ, ∀ cert : SourceCert, ∀ hvalid : valid n cert,
      ((((compile n cert hvalid).size + 2 : ℕ) : ℝ)) ≤ bound n

namespace ComponentProofCodeCompiler

def toProofObjectCertificate
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    {expectedCode : ℕ → FormulaCode}
    (compiler : ComponentProofCodeCompiler.{u} target bound expectedCode)
    {n : ℕ} {cert : compiler.SourceCert}
    (hvalid : compiler.valid n cert) :
    BAProofObject BussS21Axiom :=
  compiler.compile n cert hvalid

theorem proof_conclusion
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    {expectedCode : ℕ → FormulaCode}
    (compiler : ComponentProofCodeCompiler.{u} target bound expectedCode)
    {n : ℕ} {cert : compiler.SourceCert}
    (hvalid : compiler.valid n cert) :
    (compiler.toProofObjectCertificate hvalid).conclusion = target n :=
  compiler.compile_conclusion n cert hvalid

theorem proof_size_plus_two_le
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    {expectedCode : ℕ → FormulaCode}
    (compiler : ComponentProofCodeCompiler.{u} target bound expectedCode)
    {n : ℕ} {cert : compiler.SourceCert}
    (hvalid : compiler.valid n cert) :
    ((((compiler.toProofObjectCertificate hvalid).size + 2 : ℕ) : ℝ)) ≤
      bound n :=
  compiler.compile_size_plus_two_le n cert hvalid

end ComponentProofCodeCompiler

structure ComponentSourceCertificatesEventually
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    {expectedCode : ℕ → FormulaCode}
    (compiler : ComponentProofCodeCompiler.{u} target bound expectedCode) where
  exists_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ cert : compiler.SourceCert, compiler.valid n cert

structure SondowProjectComponentProofCodeCompilers
    (bounds : SondowComponentBounds) where
  product :
    ComponentProofCodeCompiler.{u}
      sondowProjectComponentFormulas.product bounds.product
      sondowProductCode
  logRelation :
    ComponentProofCodeCompiler.{u}
      sondowProjectComponentFormulas.logRelation bounds.logRelation
      sondowLogRelationCode
  decomposition :
    ComponentProofCodeCompiler.{u}
      sondowProjectComponentFormulas.decomposition bounds.decomposition
      sondowDecompositionCode
  threePow :
    ComponentProofCodeCompiler.{u}
      sondowProjectComponentFormulas.threePow bounds.threePow
      sondowThreePowCode
  payload :
    ComponentProofCodeCompiler.{u}
      sondowProjectComponentFormulas.payload bounds.payload
      sondowPayloadCode

namespace SondowProjectComponentProofCodeCompilers

structure SourceCodeAligned
    {bounds : SondowComponentBounds}
    (compilers : SondowProjectComponentProofCodeCompilers.{u} bounds) :
    Prop where
  product_code_eq :
    ∀ n : ℕ, compilers.product.sourceCode n = sondowProductCode n
  log_code_eq :
    ∀ n : ℕ, compilers.logRelation.sourceCode n = sondowLogRelationCode n
  decomposition_code_eq :
    ∀ n : ℕ, compilers.decomposition.sourceCode n = sondowDecompositionCode n
  threePow_code_eq :
    ∀ n : ℕ, compilers.threePow.sourceCode n = sondowThreePowCode n
  payload_code_eq :
    ∀ n : ℕ, compilers.payload.sourceCode n = sondowPayloadCode n

theorem sourceCodeAligned
    {bounds : SondowComponentBounds}
    (compilers : SondowProjectComponentProofCodeCompilers.{u} bounds) :
    SourceCodeAligned compilers where
  product_code_eq := compilers.product.sourceCode_eq_expected
  log_code_eq := compilers.logRelation.sourceCode_eq_expected
  decomposition_code_eq := compilers.decomposition.sourceCode_eq_expected
  threePow_code_eq := compilers.threePow.sourceCode_eq_expected
  payload_code_eq := compilers.payload.sourceCode_eq_expected

end SondowProjectComponentProofCodeCompilers

structure SondowProjectProofCodeCertificateAt
    {bounds : SondowComponentBounds}
    (compilers : SondowProjectComponentProofCodeCompilers.{u} bounds)
    (n : ℕ) where
  productCert : compilers.product.SourceCert
  productValid : compilers.product.valid n productCert
  logCert : compilers.logRelation.SourceCert
  logValid : compilers.logRelation.valid n logCert
  decompositionCert : compilers.decomposition.SourceCert
  decompositionValid :
    compilers.decomposition.valid n decompositionCert
  threePowCert : compilers.threePow.SourceCert
  threePowValid : compilers.threePow.valid n threePowCert
  payloadCert : compilers.payload.SourceCert
  payloadValid : compilers.payload.valid n payloadCert

namespace SondowProjectProofCodeCertificateAt

def toComponentCertificate
    {bounds : SondowComponentBounds}
    {compilers : SondowProjectComponentProofCodeCompilers.{u} bounds}
    {n : ℕ} (certs : SondowProjectProofCodeCertificateAt compilers n) :
    SondowComponentCertificate where
  productProof :=
    compilers.product.toProofObjectCertificate certs.productValid
  logProof :=
    compilers.logRelation.toProofObjectCertificate certs.logValid
  decompositionProof :=
    compilers.decomposition.toProofObjectCertificate
      certs.decompositionValid
  threePowProof :=
    compilers.threePow.toProofObjectCertificate certs.threePowValid
  payloadProof :=
    compilers.payload.toProofObjectCertificate certs.payloadValid

theorem toComponentCertificate_valid
    {bounds : SondowComponentBounds}
    {compilers : SondowProjectComponentProofCodeCompilers.{u} bounds}
    {n : ℕ} (certs : SondowProjectProofCodeCertificateAt compilers n) :
    SondowComponentCertificate.ProofObjectSystemValid
      sondowProjectComponentFormulas bounds n certs.toComponentCertificate where
  product_conclusion :=
    compilers.product.proof_conclusion certs.productValid
  log_conclusion :=
    compilers.logRelation.proof_conclusion certs.logValid
  decomposition_conclusion :=
    compilers.decomposition.proof_conclusion certs.decompositionValid
  threePow_conclusion :=
    compilers.threePow.proof_conclusion certs.threePowValid
  payload_conclusion :=
    compilers.payload.proof_conclusion certs.payloadValid
  product_size_plus_two_le :=
    compilers.product.proof_size_plus_two_le certs.productValid
  log_size_plus_two_le :=
    compilers.logRelation.proof_size_plus_two_le certs.logValid
  decomposition_size_plus_two_le :=
    compilers.decomposition.proof_size_plus_two_le
      certs.decompositionValid
  threePow_size_plus_two_le :=
    compilers.threePow.proof_size_plus_two_le certs.threePowValid
  payload_size_plus_two_le :=
    compilers.payload.proof_size_plus_two_le certs.payloadValid

end SondowProjectProofCodeCertificateAt

structure SondowProjectComponentSourceCertificatesEventually
    {bounds : SondowComponentBounds}
    (compilers : SondowProjectComponentProofCodeCompilers.{u} bounds)
    where
  product :
    ComponentSourceCertificatesEventually compilers.product
  logRelation :
    ComponentSourceCertificatesEventually compilers.logRelation
  decomposition :
    ComponentSourceCertificatesEventually compilers.decomposition
  threePow :
    ComponentSourceCertificatesEventually compilers.threePow
  payload :
    ComponentSourceCertificatesEventually compilers.payload

namespace SondowProjectComponentSourceCertificatesEventually

theorem toProjectProofCodeCertificatesEventually
    {bounds : SondowComponentBounds}
    {compilers : SondowProjectComponentProofCodeCompilers.{u} bounds}
    (hcerts :
      SondowProjectComponentSourceCertificatesEventually compilers) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty (SondowProjectProofCodeCertificateAt compilers n) := by
  rcases hcerts.product.exists_eventually with ⟨Nproduct, hproduct⟩
  rcases hcerts.logRelation.exists_eventually with ⟨Nlog, hlog⟩
  rcases hcerts.decomposition.exists_eventually with ⟨Ndecomp, hdecomp⟩
  rcases hcerts.threePow.exists_eventually with ⟨Nthree, hthree⟩
  rcases hcerts.payload.exists_eventually with ⟨Npayload, hpayload⟩
  let N :=
    max Nproduct (max Nlog (max Ndecomp (max Nthree Npayload)))
  refine ⟨N, ?_⟩
  intro n hn
  have hNproduct : Nproduct ≤ n := by
    exact le_trans (Nat.le_max_left Nproduct
      (max Nlog (max Ndecomp (max Nthree Npayload)))) hn
  have hNlog : Nlog ≤ n := by
    exact le_trans
      (le_trans
        (Nat.le_max_left Nlog (max Ndecomp (max Nthree Npayload)))
        (Nat.le_max_right Nproduct
          (max Nlog (max Ndecomp (max Nthree Npayload))))) hn
  have hNdecomp : Ndecomp ≤ n := by
    exact le_trans
      (le_trans
        (le_trans
          (Nat.le_max_left Ndecomp (max Nthree Npayload))
          (Nat.le_max_right Nlog (max Ndecomp (max Nthree Npayload))))
        (Nat.le_max_right Nproduct
          (max Nlog (max Ndecomp (max Nthree Npayload))))) hn
  have hNthree : Nthree ≤ n := by
    exact le_trans
      (le_trans
        (le_trans
          (le_trans
            (Nat.le_max_left Nthree Npayload)
            (Nat.le_max_right Ndecomp (max Nthree Npayload)))
          (Nat.le_max_right Nlog (max Ndecomp (max Nthree Npayload))))
        (Nat.le_max_right Nproduct
          (max Nlog (max Ndecomp (max Nthree Npayload))))) hn
  have hNpayload : Npayload ≤ n := by
    exact le_trans
      (le_trans
        (le_trans
          (le_trans
            (Nat.le_max_right Nthree Npayload)
            (Nat.le_max_right Ndecomp (max Nthree Npayload)))
          (Nat.le_max_right Nlog (max Ndecomp (max Nthree Npayload))))
        (Nat.le_max_right Nproduct
          (max Nlog (max Ndecomp (max Nthree Npayload))))) hn
  rcases hproduct n hNproduct with ⟨productCert, productValid⟩
  rcases hlog n hNlog with ⟨logCert, logValid⟩
  rcases hdecomp n hNdecomp with ⟨decompositionCert, decompositionValid⟩
  rcases hthree n hNthree with ⟨threePowCert, threePowValid⟩
  rcases hpayload n hNpayload with ⟨payloadCert, payloadValid⟩
  exact ⟨{
    productCert := productCert
    productValid := productValid
    logCert := logCert
    logValid := logValid
    decompositionCert := decompositionCert
    decompositionValid := decompositionValid
    threePowCert := threePowCert
    threePowValid := threePowValid
    payloadCert := payloadCert
    payloadValid := payloadValid
  }⟩

end SondowProjectComponentSourceCertificatesEventually

structure SondowProjectCombinedSourceCertificateProjectors
    {bounds : SondowComponentBounds}
    (compilers : SondowProjectComponentProofCodeCompilers.{u} bounds)
    where
  SourceCert : Type u
  valid : ℕ → SourceCert → Prop
  productCert : SourceCert → compilers.product.SourceCert
  logCert : SourceCert → compilers.logRelation.SourceCert
  decompositionCert : SourceCert → compilers.decomposition.SourceCert
  threePowCert : SourceCert → compilers.threePow.SourceCert
  payloadCert : SourceCert → compilers.payload.SourceCert
  product_valid :
    ∀ n : ℕ, ∀ cert : SourceCert, valid n cert →
      compilers.product.valid n (productCert cert)
  log_valid :
    ∀ n : ℕ, ∀ cert : SourceCert, valid n cert →
      compilers.logRelation.valid n (logCert cert)
  decomposition_valid :
    ∀ n : ℕ, ∀ cert : SourceCert, valid n cert →
      compilers.decomposition.valid n (decompositionCert cert)
  threePow_valid :
    ∀ n : ℕ, ∀ cert : SourceCert, valid n cert →
      compilers.threePow.valid n (threePowCert cert)
  payload_valid :
    ∀ n : ℕ, ∀ cert : SourceCert, valid n cert →
      compilers.payload.valid n (payloadCert cert)

structure SondowProjectCombinedSourceCertificatesEventually
    {bounds : SondowComponentBounds}
    {compilers : SondowProjectComponentProofCodeCompilers.{u} bounds}
    (projectors :
      SondowProjectCombinedSourceCertificateProjectors compilers)
    where
  exists_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ cert : projectors.SourceCert, projectors.valid n cert

namespace SondowProjectCombinedSourceCertificatesEventually

def toComponentSourceCertificatesEventually
    {bounds : SondowComponentBounds}
    {compilers : SondowProjectComponentProofCodeCompilers.{u} bounds}
    {projectors :
      SondowProjectCombinedSourceCertificateProjectors compilers}
    (hcerts :
      SondowProjectCombinedSourceCertificatesEventually projectors) :
    SondowProjectComponentSourceCertificatesEventually compilers where
  product := by
    rcases hcerts.exists_eventually with ⟨N, hN⟩
    exact ⟨N, fun n hn => by
      rcases hN n hn with ⟨cert, hvalid⟩
      exact ⟨projectors.productCert cert,
        projectors.product_valid n cert hvalid⟩⟩
  logRelation := by
    rcases hcerts.exists_eventually with ⟨N, hN⟩
    exact ⟨N, fun n hn => by
      rcases hN n hn with ⟨cert, hvalid⟩
      exact ⟨projectors.logCert cert,
        projectors.log_valid n cert hvalid⟩⟩
  decomposition := by
    rcases hcerts.exists_eventually with ⟨N, hN⟩
    exact ⟨N, fun n hn => by
      rcases hN n hn with ⟨cert, hvalid⟩
      exact ⟨projectors.decompositionCert cert,
        projectors.decomposition_valid n cert hvalid⟩⟩
  threePow := by
    rcases hcerts.exists_eventually with ⟨N, hN⟩
    exact ⟨N, fun n hn => by
      rcases hN n hn with ⟨cert, hvalid⟩
      exact ⟨projectors.threePowCert cert,
        projectors.threePow_valid n cert hvalid⟩⟩
  payload := by
    rcases hcerts.exists_eventually with ⟨N, hN⟩
    exact ⟨N, fun n hn => by
      rcases hN n hn with ⟨cert, hvalid⟩
      exact ⟨projectors.payloadCert cert,
        projectors.payload_valid n cert hvalid⟩⟩

theorem toProjectProofCodeCertificatesEventually
    {bounds : SondowComponentBounds}
    {compilers : SondowProjectComponentProofCodeCompilers.{u} bounds}
    {projectors :
      SondowProjectCombinedSourceCertificateProjectors compilers}
    (hcerts :
      SondowProjectCombinedSourceCertificatesEventually projectors) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty (SondowProjectProofCodeCertificateAt compilers n) :=
  hcerts.toComponentSourceCertificatesEventually
    |>.toProjectProofCodeCertificatesEventually

end SondowProjectCombinedSourceCertificatesEventually

/-- A source proof-code certificate after the Hilbert/proof-code route has been
compiled into the sidecar bounded-arithmetic proof object language.  This is the
exact hand-off object required from the main repository: it carries the compiled
`BAProofObject`, its conclusion, and the component size bound. -/
structure CompiledComponentProofCodeCert
    (target : ℕ → BAFormula) (bound : ℕ → ℝ)
    (expectedCode : ℕ → FormulaCode) where
  index : ℕ
  sourceSize : ℕ
  proof : BAProofObject BussS21Axiom
  proof_conclusion : proof.conclusion = target index
  proof_size_plus_two_le :
    (((proof.size + 2 : ℕ) : ℝ)) ≤ bound index

def CompiledComponentProofCodeCert.ofProofCertificateTrace
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    {expectedCode : ℕ → FormulaCode} {n : ℕ}
    (tr :
      CertificateVerifierMachine.AcceptedTrace
        (proofCertificateVerifierMachine target bound) n) :
    CompiledComponentProofCodeCert target bound expectedCode where
  index := n
  sourceSize := tr.size
  proof := tr.cert
  proof_conclusion :=
    proofCertificateVerifierMachine.acceptedTrace_conclusion tr
  proof_size_plus_two_le := by
    simpa [CertificateVerifierMachine.AcceptedTrace.size,
      proofCertificateVerifierMachine, ProofCertificateState.size,
      Nat.add_assoc] using
      proofCertificateVerifierMachine.acceptedTrace_size_le_bound tr

def CompiledComponentProofCodeCert.toProofCertificateTrace
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    {expectedCode : ℕ → FormulaCode}
    (cert :
      CompiledComponentProofCodeCert target bound expectedCode) :
    CertificateVerifierMachine.AcceptedTrace
      (proofCertificateVerifierMachine target bound) cert.index where
  cert := cert.proof
  final :=
    ProofCertificateState.accepted cert.index cert.proof
      cert.proof_conclusion cert.proof_size_plus_two_le
  steps := 1
  reaches :=
    CertificateVerifierMachine.Reaches.cons
      (ProofCertificateState.Step.accept
        cert.proof_conclusion cert.proof_size_plus_two_le)
      (CertificateVerifierMachine.Reaches.refl _)
  accepts := by
    simp [proofCertificateVerifierMachine, ProofCertificateState.accepting]

def CompiledComponentProofCodeCert.toProofCertificateTraceAt
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    {expectedCode : ℕ → FormulaCode}
    (cert :
      CompiledComponentProofCodeCert target bound expectedCode)
    {n : ℕ} (hindex : cert.index = n) :
    CertificateVerifierMachine.AcceptedTrace
      (proofCertificateVerifierMachine target bound) n := by
  cases hindex
  exact cert.toProofCertificateTrace

def compiledComponentProofCodeCompiler
    (target : ℕ → BAFormula) (bound : ℕ → ℝ)
    (expectedCode : ℕ → FormulaCode) :
    ComponentProofCodeCompiler target bound expectedCode where
  SourceCert := CompiledComponentProofCodeCert target bound expectedCode
  valid := fun n cert => cert.index = n
  sourceCode := expectedCode
  sourceCode_eq_expected := by
    intro n
    rfl
  sourceSize := fun cert => cert.sourceSize
  compile := fun _n cert _hvalid => cert.proof
  compile_conclusion := by
    intro n cert hvalid
    rw [cert.proof_conclusion, hvalid]
  compile_size_plus_two_le := by
    intro n cert hvalid
    simpa [hvalid] using cert.proof_size_plus_two_le

def compiledSondowProjectComponentProofCodeCompilers
    (bounds : SondowComponentBounds) :
    SondowProjectComponentProofCodeCompilers bounds where
  product :=
    compiledComponentProofCodeCompiler
      sondowProjectComponentFormulas.product bounds.product
      sondowProductCode
  logRelation :=
    compiledComponentProofCodeCompiler
      sondowProjectComponentFormulas.logRelation bounds.logRelation
      sondowLogRelationCode
  decomposition :=
    compiledComponentProofCodeCompiler
      sondowProjectComponentFormulas.decomposition bounds.decomposition
      sondowDecompositionCode
  threePow :=
    compiledComponentProofCodeCompiler
      sondowProjectComponentFormulas.threePow bounds.threePow
      sondowThreePowCode
  payload :=
    compiledComponentProofCodeCompiler
      sondowProjectComponentFormulas.payload bounds.payload
      sondowPayloadCode

theorem compiledSondowProjectComponentProofCodeCompilers_sourceCodeAligned
    (bounds : SondowComponentBounds) :
    (compiledSondowProjectComponentProofCodeCompilers bounds).SourceCodeAligned :=
  (compiledSondowProjectComponentProofCodeCompilers bounds).sourceCodeAligned

structure CompiledSondowProjectSourceCertificateAt
    (bounds : SondowComponentBounds) (n : ℕ) where
  product :
    CompiledComponentProofCodeCert
      sondowProjectComponentFormulas.product bounds.product
      sondowProductCode
  product_index_eq : product.index = n
  logRelation :
    CompiledComponentProofCodeCert
      sondowProjectComponentFormulas.logRelation bounds.logRelation
      sondowLogRelationCode
  log_index_eq : logRelation.index = n
  decomposition :
    CompiledComponentProofCodeCert
      sondowProjectComponentFormulas.decomposition bounds.decomposition
      sondowDecompositionCode
  decomposition_index_eq : decomposition.index = n
  threePow :
    CompiledComponentProofCodeCert
      sondowProjectComponentFormulas.threePow bounds.threePow
      sondowThreePowCode
  threePow_index_eq : threePow.index = n
  payload :
    CompiledComponentProofCodeCert
      sondowProjectComponentFormulas.payload bounds.payload
      sondowPayloadCode
  payload_index_eq : payload.index = n

abbrev CompiledSondowProjectSourceCertificate
    (bounds : SondowComponentBounds) :=
  Sigma (CompiledSondowProjectSourceCertificateAt bounds)

structure AcceptedToProjectComponentProofCertificateTraces
    (Accepted : ℕ → Prop) (bounds : SondowComponentBounds) where
  productTrace :
    ∀ n : ℕ, Accepted n →
      CertificateVerifierMachine.AcceptedTrace
        (proofCertificateVerifierMachine
          sondowProjectComponentFormulas.product bounds.product) n
  logTrace :
    ∀ n : ℕ, Accepted n →
      CertificateVerifierMachine.AcceptedTrace
        (proofCertificateVerifierMachine
          sondowProjectComponentFormulas.logRelation bounds.logRelation) n
  decompositionTrace :
    ∀ n : ℕ, Accepted n →
      CertificateVerifierMachine.AcceptedTrace
        (proofCertificateVerifierMachine
          sondowProjectComponentFormulas.decomposition
          bounds.decomposition) n
  threePowTrace :
    ∀ n : ℕ, Accepted n →
      CertificateVerifierMachine.AcceptedTrace
        (proofCertificateVerifierMachine
          sondowProjectComponentFormulas.threePow bounds.threePow) n
  payloadTrace :
    ∀ n : ℕ, Accepted n →
      CertificateVerifierMachine.AcceptedTrace
        (proofCertificateVerifierMachine
          sondowProjectComponentFormulas.payload bounds.payload) n

structure AcceptedCheckedCodeSemantics
    (sourceCode : ℕ → FormulaCode) (Accepted : ℕ → Prop) where
  Code : Type u
  checks : Code → FormulaCode → Prop
  size : Code → ℕ
  accepted_iff_checked :
    ∀ n : ℕ, Accepted n ↔ ∃ c : Code, checks c (sourceCode n)

namespace AcceptedCheckedCodeSemantics

theorem checked_of_accepted
    {sourceCode : ℕ → FormulaCode} {Accepted : ℕ → Prop}
    (sem : AcceptedCheckedCodeSemantics.{u} sourceCode Accepted)
    {n : ℕ} (haccepted : Accepted n) :
    ∃ c : sem.Code, sem.checks c (sourceCode n) :=
  (sem.accepted_iff_checked n).1 haccepted

theorem accepted_of_checked
    {sourceCode : ℕ → FormulaCode} {Accepted : ℕ → Prop}
    (sem : AcceptedCheckedCodeSemantics.{u} sourceCode Accepted)
    {n : ℕ} {c : sem.Code}
    (hchecked : sem.checks c (sourceCode n)) :
    Accepted n :=
  (sem.accepted_iff_checked n).2 ⟨c, hchecked⟩

end AcceptedCheckedCodeSemantics

structure CheckedCodeToProjectComponentProofCertificateTraces
    {sourceCode : ℕ → FormulaCode} {Accepted : ℕ → Prop}
    (sem : AcceptedCheckedCodeSemantics.{u} sourceCode Accepted)
    (bounds : SondowComponentBounds) where
  productTraceOfChecked :
    ∀ n : ℕ, ∀ c : sem.Code, sem.checks c (sourceCode n) →
      CertificateVerifierMachine.AcceptedTrace
        (proofCertificateVerifierMachine
          sondowProjectComponentFormulas.product bounds.product) n
  logTraceOfChecked :
    ∀ n : ℕ, ∀ c : sem.Code, sem.checks c (sourceCode n) →
      CertificateVerifierMachine.AcceptedTrace
        (proofCertificateVerifierMachine
          sondowProjectComponentFormulas.logRelation bounds.logRelation) n
  decompositionTraceOfChecked :
    ∀ n : ℕ, ∀ c : sem.Code, sem.checks c (sourceCode n) →
      CertificateVerifierMachine.AcceptedTrace
        (proofCertificateVerifierMachine
          sondowProjectComponentFormulas.decomposition
          bounds.decomposition) n
  threePowTraceOfChecked :
    ∀ n : ℕ, ∀ c : sem.Code, sem.checks c (sourceCode n) →
      CertificateVerifierMachine.AcceptedTrace
        (proofCertificateVerifierMachine
          sondowProjectComponentFormulas.threePow bounds.threePow) n
  payloadTraceOfChecked :
    ∀ n : ℕ, ∀ c : sem.Code, sem.checks c (sourceCode n) →
      CertificateVerifierMachine.AcceptedTrace
        (proofCertificateVerifierMachine
          sondowProjectComponentFormulas.payload bounds.payload) n

structure AcceptedCheckedCodeToProjectComponentTracePackage
    (sourceCode : ℕ → FormulaCode) (Accepted : ℕ → Prop)
    (bounds : SondowComponentBounds) where
  codeSemantics : AcceptedCheckedCodeSemantics.{u} sourceCode Accepted
  traceCompiler :
    CheckedCodeToProjectComponentProofCertificateTraces codeSemantics bounds

structure ExternalAcceptedCheckedCodeSemantics
    (Accepted : ℕ → Prop) where
  Code : Type u
  checksAt : Code → ℕ → Prop
  size : Code → ℕ
  accepted_iff_checked_at :
    ∀ n : ℕ, Accepted n ↔ ∃ c : Code, checksAt c n

namespace ExternalAcceptedCheckedCodeSemantics

theorem checked_of_accepted
    {Accepted : ℕ → Prop}
    (sem : ExternalAcceptedCheckedCodeSemantics.{u} Accepted)
    {n : ℕ} (haccepted : Accepted n) :
    ∃ c : sem.Code, sem.checksAt c n :=
  (sem.accepted_iff_checked_at n).1 haccepted

theorem accepted_of_checked
    {Accepted : ℕ → Prop}
    (sem : ExternalAcceptedCheckedCodeSemantics.{u} Accepted)
    {n : ℕ} {c : sem.Code}
    (hchecked : sem.checksAt c n) :
    Accepted n :=
  (sem.accepted_iff_checked_at n).2 ⟨c, hchecked⟩

def toAcceptedCheckedCodeSemantics
    {Accepted : ℕ → Prop}
    (sem : ExternalAcceptedCheckedCodeSemantics.{u} Accepted)
    (sourceCode : ℕ → FormulaCode)
    (hsource : Function.Injective sourceCode) :
    AcceptedCheckedCodeSemantics sourceCode Accepted where
  Code := sem.Code
  checks := fun c code =>
    ∃ n : ℕ, code = sourceCode n ∧ sem.checksAt c n
  size := sem.size
  accepted_iff_checked := by
    intro n
    constructor
    · intro haccepted
      rcases sem.checked_of_accepted haccepted with ⟨c, hc⟩
      exact ⟨c, n, rfl, hc⟩
    · intro hchecked
      rcases hchecked with ⟨c, m, hcode, hcm⟩
      have hmn : n = m := hsource hcode
      cases hmn
      exact sem.accepted_of_checked hcm

end ExternalAcceptedCheckedCodeSemantics

structure ExternalCheckedCodeToProjectComponentProofCertificateTraces
    {Accepted : ℕ → Prop}
    (sem : ExternalAcceptedCheckedCodeSemantics.{u} Accepted)
    (bounds : SondowComponentBounds) where
  productTraceOfChecked :
    ∀ n : ℕ, ∀ c : sem.Code, sem.checksAt c n →
      CertificateVerifierMachine.AcceptedTrace
        (proofCertificateVerifierMachine
          sondowProjectComponentFormulas.product bounds.product) n
  logTraceOfChecked :
    ∀ n : ℕ, ∀ c : sem.Code, sem.checksAt c n →
      CertificateVerifierMachine.AcceptedTrace
        (proofCertificateVerifierMachine
          sondowProjectComponentFormulas.logRelation bounds.logRelation) n
  decompositionTraceOfChecked :
    ∀ n : ℕ, ∀ c : sem.Code, sem.checksAt c n →
      CertificateVerifierMachine.AcceptedTrace
        (proofCertificateVerifierMachine
          sondowProjectComponentFormulas.decomposition
          bounds.decomposition) n
  threePowTraceOfChecked :
    ∀ n : ℕ, ∀ c : sem.Code, sem.checksAt c n →
      CertificateVerifierMachine.AcceptedTrace
        (proofCertificateVerifierMachine
          sondowProjectComponentFormulas.threePow bounds.threePow) n
  payloadTraceOfChecked :
    ∀ n : ℕ, ∀ c : sem.Code, sem.checksAt c n →
      CertificateVerifierMachine.AcceptedTrace
        (proofCertificateVerifierMachine
          sondowProjectComponentFormulas.payload bounds.payload) n

structure ExternalAcceptedCheckedCodeToProjectComponentTracePackage
    (Accepted : ℕ → Prop) (bounds : SondowComponentBounds) where
  codeSemantics : ExternalAcceptedCheckedCodeSemantics.{u} Accepted
  traceCompiler :
    ExternalCheckedCodeToProjectComponentProofCertificateTraces
      codeSemantics bounds

def compiledSondowProjectCombinedSourceCertificateProjectors
    (bounds : SondowComponentBounds) :
    SondowProjectCombinedSourceCertificateProjectors
      (compiledSondowProjectComponentProofCodeCompilers bounds) where
  SourceCert := CompiledSondowProjectSourceCertificate bounds
  valid := fun n cert => cert.1 = n
  productCert := fun cert => cert.2.product
  logCert := fun cert => cert.2.logRelation
  decompositionCert := fun cert => cert.2.decomposition
  threePowCert := fun cert => cert.2.threePow
  payloadCert := fun cert => cert.2.payload
  product_valid := by
    intro _n cert hvalid
    exact cert.2.product_index_eq.trans hvalid
  log_valid := by
    intro _n cert hvalid
    exact cert.2.log_index_eq.trans hvalid
  decomposition_valid := by
    intro _n cert hvalid
    exact cert.2.decomposition_index_eq.trans hvalid
  threePow_valid := by
    intro _n cert hvalid
    exact cert.2.threePow_index_eq.trans hvalid
  payload_valid := by
    intro _n cert hvalid
    exact cert.2.payload_index_eq.trans hvalid

structure SondowRationalityToCompiledProjectSourceCertificates
    (ctx : GammaRationalityContext) (bounds : SondowComponentBounds)
    where
  compiled_certificates_of_rationality :
    GammaRationalityWitness ctx →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        Nonempty (CompiledSondowProjectSourceCertificateAt bounds n)

def MainCompiledProjectSourceCertificatesEventually
    (MainRationality : Prop) (bounds : SondowComponentBounds) : Prop :=
  MainRationality →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty (CompiledSondowProjectSourceCertificateAt bounds n)

def MainCompiledProjectSourceCertificatesEventually.toPackage
    {MainRationality : Prop} {bounds : SondowComponentBounds}
    (h :
      MainCompiledProjectSourceCertificatesEventually
        MainRationality bounds) :
    SondowRationalityToCompiledProjectSourceCertificates
      (mainGammaRationalityContext MainRationality) bounds where
  compiled_certificates_of_rationality := h

def SondowRationalityToCompiledProjectSourceCertificates.toMainEventually
    {MainRationality : Prop} {bounds : SondowComponentBounds}
    (h :
      SondowRationalityToCompiledProjectSourceCertificates
        (mainGammaRationalityContext MainRationality) bounds) :
    MainCompiledProjectSourceCertificatesEventually
      MainRationality bounds :=
  h.compiled_certificates_of_rationality

theorem mainCompiledProjectSourceCertificatesEventually_iff_package
    {MainRationality : Prop} {bounds : SondowComponentBounds} :
    MainCompiledProjectSourceCertificatesEventually MainRationality bounds ↔
      SondowRationalityToCompiledProjectSourceCertificates
        (mainGammaRationalityContext MainRationality) bounds := by
  constructor
  · exact MainCompiledProjectSourceCertificatesEventually.toPackage
  · exact SondowRationalityToCompiledProjectSourceCertificates.toMainEventually

def MainAcceptedEventuallyUnderRationality
    (MainRationality : Prop) (Accepted : ℕ → Prop) : Prop :=
  MainRationality →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Accepted n

structure AcceptedToCompiledProjectSourceCertificateCompiler
    (Accepted : ℕ → Prop) (bounds : SondowComponentBounds) where
  compile :
    ∀ n : ℕ, Accepted n →
      CompiledSondowProjectSourceCertificateAt bounds n

def AcceptedToCompiledProjectSourceCertificateExists
    (Accepted : ℕ → Prop) (bounds : SondowComponentBounds) : Prop :=
  ∀ n : ℕ, Accepted n →
    Nonempty (CompiledSondowProjectSourceCertificateAt bounds n)

noncomputable def AcceptedToCompiledProjectSourceCertificateCompiler.ofExists
    {Accepted : ℕ → Prop} {bounds : SondowComponentBounds}
    (h :
      AcceptedToCompiledProjectSourceCertificateExists Accepted bounds) :
    AcceptedToCompiledProjectSourceCertificateCompiler Accepted bounds where
  compile := fun n haccepted => Classical.choice (h n haccepted)

theorem acceptedToCompiledProjectSourceCertificateCompiler_nonempty_iff_exists
    {Accepted : ℕ → Prop} {bounds : SondowComponentBounds} :
    Nonempty
      (AcceptedToCompiledProjectSourceCertificateCompiler Accepted bounds) ↔
      AcceptedToCompiledProjectSourceCertificateExists Accepted bounds := by
  constructor
  · intro hcompiler n haccepted
    rcases hcompiler with ⟨compiler⟩
    exact ⟨compiler.compile n haccepted⟩
  · intro h
    exact ⟨AcceptedToCompiledProjectSourceCertificateCompiler.ofExists h⟩

def AcceptedToProjectComponentProofCertificateTraces.toCompiledExists
    {Accepted : ℕ → Prop} {bounds : SondowComponentBounds}
    (traces :
      AcceptedToProjectComponentProofCertificateTraces Accepted bounds) :
    AcceptedToCompiledProjectSourceCertificateExists Accepted bounds := by
  intro n haccepted
  let productTrace := traces.productTrace n haccepted
  let logTrace := traces.logTrace n haccepted
  let decompositionTrace := traces.decompositionTrace n haccepted
  let threePowTrace := traces.threePowTrace n haccepted
  let payloadTrace := traces.payloadTrace n haccepted
  exact ⟨{
    product :=
      CompiledComponentProofCodeCert.ofProofCertificateTrace
        (expectedCode := sondowProductCode) productTrace
    product_index_eq := rfl
    logRelation :=
      CompiledComponentProofCodeCert.ofProofCertificateTrace
        (expectedCode := sondowLogRelationCode) logTrace
    log_index_eq := rfl
    decomposition :=
      CompiledComponentProofCodeCert.ofProofCertificateTrace
        (expectedCode := sondowDecompositionCode) decompositionTrace
    decomposition_index_eq := rfl
    threePow :=
      CompiledComponentProofCodeCert.ofProofCertificateTrace
        (expectedCode := sondowThreePowCode) threePowTrace
    threePow_index_eq := rfl
    payload :=
      CompiledComponentProofCodeCert.ofProofCertificateTrace
        (expectedCode := sondowPayloadCode) payloadTrace
    payload_index_eq := rfl
  }⟩

noncomputable def
    AcceptedToProjectComponentProofCertificateTraces.toCompiler
    {Accepted : ℕ → Prop} {bounds : SondowComponentBounds}
    (traces :
      AcceptedToProjectComponentProofCertificateTraces Accepted bounds) :
    AcceptedToCompiledProjectSourceCertificateCompiler Accepted bounds :=
  AcceptedToCompiledProjectSourceCertificateCompiler.ofExists
    traces.toCompiledExists

def AcceptedToCompiledProjectSourceCertificateCompiler.toComponentTraces
    {Accepted : ℕ → Prop} {bounds : SondowComponentBounds}
    (compiler :
      AcceptedToCompiledProjectSourceCertificateCompiler Accepted bounds) :
    AcceptedToProjectComponentProofCertificateTraces Accepted bounds where
  productTrace := by
    intro n haccepted
    exact
      (compiler.compile n haccepted).product.toProofCertificateTraceAt
        (compiler.compile n haccepted).product_index_eq
  logTrace := by
    intro n haccepted
    exact
      (compiler.compile n haccepted).logRelation.toProofCertificateTraceAt
        (compiler.compile n haccepted).log_index_eq
  decompositionTrace := by
    intro n haccepted
    exact
      (compiler.compile n haccepted).decomposition.toProofCertificateTraceAt
        (compiler.compile n haccepted).decomposition_index_eq
  threePowTrace := by
    intro n haccepted
    exact
      (compiler.compile n haccepted).threePow.toProofCertificateTraceAt
        (compiler.compile n haccepted).threePow_index_eq
  payloadTrace := by
    intro n haccepted
    exact
      (compiler.compile n haccepted).payload.toProofCertificateTraceAt
        (compiler.compile n haccepted).payload_index_eq

theorem acceptedToCompiledCompiler_nonempty_iff_componentTraces_nonempty
    {Accepted : ℕ → Prop} {bounds : SondowComponentBounds} :
    Nonempty
      (AcceptedToCompiledProjectSourceCertificateCompiler Accepted bounds) ↔
      Nonempty
        (AcceptedToProjectComponentProofCertificateTraces Accepted bounds) := by
  constructor
  · intro hcompiler
    rcases hcompiler with ⟨compiler⟩
    exact ⟨compiler.toComponentTraces⟩
  · intro htraces
    rcases htraces with ⟨traces⟩
    exact ⟨traces.toCompiler⟩

noncomputable def
    ExternalAcceptedCheckedCodeToProjectComponentTracePackage.toComponentTraces
    {Accepted : ℕ → Prop} {bounds : SondowComponentBounds}
    (pkg :
      ExternalAcceptedCheckedCodeToProjectComponentTracePackage.{u}
        Accepted bounds) :
    AcceptedToProjectComponentProofCertificateTraces Accepted bounds where
  productTrace := by
    intro n haccepted
    let c := Classical.choose
      (pkg.codeSemantics.checked_of_accepted haccepted)
    have hchecked := Classical.choose_spec
      (pkg.codeSemantics.checked_of_accepted haccepted)
    exact pkg.traceCompiler.productTraceOfChecked n c hchecked
  logTrace := by
    intro n haccepted
    let c := Classical.choose
      (pkg.codeSemantics.checked_of_accepted haccepted)
    have hchecked := Classical.choose_spec
      (pkg.codeSemantics.checked_of_accepted haccepted)
    exact pkg.traceCompiler.logTraceOfChecked n c hchecked
  decompositionTrace := by
    intro n haccepted
    let c := Classical.choose
      (pkg.codeSemantics.checked_of_accepted haccepted)
    have hchecked := Classical.choose_spec
      (pkg.codeSemantics.checked_of_accepted haccepted)
    exact pkg.traceCompiler.decompositionTraceOfChecked n c hchecked
  threePowTrace := by
    intro n haccepted
    let c := Classical.choose
      (pkg.codeSemantics.checked_of_accepted haccepted)
    have hchecked := Classical.choose_spec
      (pkg.codeSemantics.checked_of_accepted haccepted)
    exact pkg.traceCompiler.threePowTraceOfChecked n c hchecked
  payloadTrace := by
    intro n haccepted
    let c := Classical.choose
      (pkg.codeSemantics.checked_of_accepted haccepted)
    have hchecked := Classical.choose_spec
      (pkg.codeSemantics.checked_of_accepted haccepted)
    exact pkg.traceCompiler.payloadTraceOfChecked n c hchecked

def AcceptedToProjectComponentProofCertificateTraces.toExternalCheckedCodePackage
    {Accepted : ℕ → Prop} {bounds : SondowComponentBounds}
    (traces :
      AcceptedToProjectComponentProofCertificateTraces Accepted bounds) :
    ExternalAcceptedCheckedCodeToProjectComponentTracePackage Accepted bounds where
  codeSemantics :=
    { Code := ULift.{u} { n : ℕ // Accepted n }
      checksAt := fun c n => c.down.1 = n
      size := fun c => c.down.1 + 1
      accepted_iff_checked_at := by
        intro n
        constructor
        · intro haccepted
          exact ⟨ULift.up ⟨n, haccepted⟩, rfl⟩
        · intro hchecked
          rcases hchecked with ⟨c, hc⟩
          rcases c with ⟨c⟩
          rcases c with ⟨m, haccepted_m⟩
          cases hc
          exact haccepted_m }
  traceCompiler :=
    { productTraceOfChecked := by
        intro n c hchecked
        rcases c with ⟨c⟩
        rcases c with ⟨m, haccepted_m⟩
        cases hchecked
        exact traces.productTrace _ haccepted_m
      logTraceOfChecked := by
        intro n c hchecked
        rcases c with ⟨c⟩
        rcases c with ⟨m, haccepted_m⟩
        cases hchecked
        exact traces.logTrace _ haccepted_m
      decompositionTraceOfChecked := by
        intro n c hchecked
        rcases c with ⟨c⟩
        rcases c with ⟨m, haccepted_m⟩
        cases hchecked
        exact traces.decompositionTrace _ haccepted_m
      threePowTraceOfChecked := by
        intro n c hchecked
        rcases c with ⟨c⟩
        rcases c with ⟨m, haccepted_m⟩
        cases hchecked
        exact traces.threePowTrace _ haccepted_m
      payloadTraceOfChecked := by
        intro n c hchecked
        rcases c with ⟨c⟩
        rcases c with ⟨m, haccepted_m⟩
        cases hchecked
        exact traces.payloadTrace _ haccepted_m }

theorem
    externalCheckedCodeTracePackage_nonempty_iff_componentTraces_nonempty
    {Accepted : ℕ → Prop} {bounds : SondowComponentBounds} :
    Nonempty
      (ExternalAcceptedCheckedCodeToProjectComponentTracePackage
        Accepted bounds) ↔
      Nonempty
        (AcceptedToProjectComponentProofCertificateTraces Accepted bounds) := by
  constructor
  · intro hpkg
    rcases hpkg with ⟨pkg⟩
    exact ⟨pkg.toComponentTraces⟩
  · intro htraces
    rcases htraces with ⟨traces⟩
    exact ⟨traces.toExternalCheckedCodePackage⟩

noncomputable def
    ExternalAcceptedCheckedCodeToProjectComponentTracePackage.toCheckedCodePackage
    {sourceCode : ℕ → FormulaCode} {Accepted : ℕ → Prop}
    {bounds : SondowComponentBounds}
    (hsource : Function.Injective sourceCode)
    (pkg :
      ExternalAcceptedCheckedCodeToProjectComponentTracePackage.{u}
        Accepted bounds) :
    AcceptedCheckedCodeToProjectComponentTracePackage
      sourceCode Accepted bounds where
  codeSemantics :=
    pkg.codeSemantics.toAcceptedCheckedCodeSemantics sourceCode hsource
  traceCompiler :=
    { productTraceOfChecked := by
        intro n c hchecked
        let m := Classical.choose hchecked
        have hspec := Classical.choose_spec hchecked
        have hnm : n = m := hsource hspec.1
        exact hnm.symm ▸
          pkg.traceCompiler.productTraceOfChecked m c hspec.2
      logTraceOfChecked := by
        intro n c hchecked
        let m := Classical.choose hchecked
        have hspec := Classical.choose_spec hchecked
        have hnm : n = m := hsource hspec.1
        exact hnm.symm ▸
          pkg.traceCompiler.logTraceOfChecked m c hspec.2
      decompositionTraceOfChecked := by
        intro n c hchecked
        let m := Classical.choose hchecked
        have hspec := Classical.choose_spec hchecked
        have hnm : n = m := hsource hspec.1
        exact hnm.symm ▸
          pkg.traceCompiler.decompositionTraceOfChecked m c hspec.2
      threePowTraceOfChecked := by
        intro n c hchecked
        let m := Classical.choose hchecked
        have hspec := Classical.choose_spec hchecked
        have hnm : n = m := hsource hspec.1
        exact hnm.symm ▸
          pkg.traceCompiler.threePowTraceOfChecked m c hspec.2
      payloadTraceOfChecked := by
        intro n c hchecked
        let m := Classical.choose hchecked
        have hspec := Classical.choose_spec hchecked
        have hnm : n = m := hsource hspec.1
        exact hnm.symm ▸
          pkg.traceCompiler.payloadTraceOfChecked m c hspec.2 }

noncomputable def
    AcceptedCheckedCodeToProjectComponentTracePackage.toComponentTraces
    {sourceCode : ℕ → FormulaCode} {Accepted : ℕ → Prop}
    {bounds : SondowComponentBounds}
    (pkg :
      AcceptedCheckedCodeToProjectComponentTracePackage.{u}
        sourceCode Accepted bounds) :
    AcceptedToProjectComponentProofCertificateTraces Accepted bounds where
  productTrace := by
    intro n haccepted
    let c := Classical.choose
      (pkg.codeSemantics.checked_of_accepted haccepted)
    have hchecked := Classical.choose_spec
      (pkg.codeSemantics.checked_of_accepted haccepted)
    exact pkg.traceCompiler.productTraceOfChecked n c hchecked
  logTrace := by
    intro n haccepted
    let c := Classical.choose
      (pkg.codeSemantics.checked_of_accepted haccepted)
    have hchecked := Classical.choose_spec
      (pkg.codeSemantics.checked_of_accepted haccepted)
    exact pkg.traceCompiler.logTraceOfChecked n c hchecked
  decompositionTrace := by
    intro n haccepted
    let c := Classical.choose
      (pkg.codeSemantics.checked_of_accepted haccepted)
    have hchecked := Classical.choose_spec
      (pkg.codeSemantics.checked_of_accepted haccepted)
    exact pkg.traceCompiler.decompositionTraceOfChecked n c hchecked
  threePowTrace := by
    intro n haccepted
    let c := Classical.choose
      (pkg.codeSemantics.checked_of_accepted haccepted)
    have hchecked := Classical.choose_spec
      (pkg.codeSemantics.checked_of_accepted haccepted)
    exact pkg.traceCompiler.threePowTraceOfChecked n c hchecked
  payloadTrace := by
    intro n haccepted
    let c := Classical.choose
      (pkg.codeSemantics.checked_of_accepted haccepted)
    have hchecked := Classical.choose_spec
      (pkg.codeSemantics.checked_of_accepted haccepted)
    exact pkg.traceCompiler.payloadTraceOfChecked n c hchecked

def AcceptedToProjectComponentProofCertificateTraces.toCheckedCodePackage
    {sourceCode : ℕ → FormulaCode} {Accepted : ℕ → Prop}
    {bounds : SondowComponentBounds}
    (hsource : Function.Injective sourceCode)
    (traces :
      AcceptedToProjectComponentProofCertificateTraces Accepted bounds) :
    AcceptedCheckedCodeToProjectComponentTracePackage sourceCode Accepted bounds where
  codeSemantics :=
    { Code := ULift.{u} { n : ℕ // Accepted n }
      checks := fun c code => sourceCode c.down.1 = code
      size := fun c => c.down.1 + 1
      accepted_iff_checked := by
        intro n
        constructor
        · intro haccepted
          exact ⟨ULift.up ⟨n, haccepted⟩, rfl⟩
        · intro hchecked
          rcases hchecked with ⟨c, hc⟩
          rcases c with ⟨c⟩
          rcases c with ⟨m, haccepted_m⟩
          have hmn : m = n := hsource hc
          cases hmn
          exact haccepted_m }
  traceCompiler :=
    { productTraceOfChecked := by
        intro n c hchecked
        rcases c with ⟨c⟩
        rcases c with ⟨m, haccepted_m⟩
        have hmn : m = n := hsource hchecked
        cases hmn
        exact traces.productTrace _ haccepted_m
      logTraceOfChecked := by
        intro n c hchecked
        rcases c with ⟨c⟩
        rcases c with ⟨m, haccepted_m⟩
        have hmn : m = n := hsource hchecked
        cases hmn
        exact traces.logTrace _ haccepted_m
      decompositionTraceOfChecked := by
        intro n c hchecked
        rcases c with ⟨c⟩
        rcases c with ⟨m, haccepted_m⟩
        have hmn : m = n := hsource hchecked
        cases hmn
        exact traces.decompositionTrace _ haccepted_m
      threePowTraceOfChecked := by
        intro n c hchecked
        rcases c with ⟨c⟩
        rcases c with ⟨m, haccepted_m⟩
        have hmn : m = n := hsource hchecked
        cases hmn
        exact traces.threePowTrace _ haccepted_m
      payloadTraceOfChecked := by
        intro n c hchecked
        rcases c with ⟨c⟩
        rcases c with ⟨m, haccepted_m⟩
        have hmn : m = n := hsource hchecked
        cases hmn
        exact traces.payloadTrace _ haccepted_m }

theorem acceptedCheckedCodeTracePackage_nonempty_iff_componentTraces_nonempty
    {sourceCode : ℕ → FormulaCode} {Accepted : ℕ → Prop}
    {bounds : SondowComponentBounds}
    (hsource : Function.Injective sourceCode) :
    Nonempty
      (AcceptedCheckedCodeToProjectComponentTracePackage
        sourceCode Accepted bounds) ↔
      Nonempty
        (AcceptedToProjectComponentProofCertificateTraces Accepted bounds) := by
  constructor
  · intro hpkg
    rcases hpkg with ⟨pkg⟩
    exact ⟨pkg.toComponentTraces⟩
  · intro htraces
    rcases htraces with ⟨traces⟩
    exact ⟨traces.toCheckedCodePackage hsource⟩

theorem
    sondowCertificateValid_checkedCodeTracePackage_nonempty_iff_componentTraces_nonempty
    {Accepted : ℕ → Prop} {bounds : SondowComponentBounds} :
    Nonempty
      (AcceptedCheckedCodeToProjectComponentTracePackage
        sondowCertificateValidCode Accepted bounds) ↔
      Nonempty
        (AcceptedToProjectComponentProofCertificateTraces Accepted bounds) :=
  acceptedCheckedCodeTracePackage_nonempty_iff_componentTraces_nonempty
    sondowCertificateValidCode_injective

def MainCompiledProjectSourceCertificatesEventually.ofAcceptedCompiler
    {MainRationality : Prop} {Accepted : ℕ → Prop}
    {bounds : SondowComponentBounds}
    (haccepted :
      MainAcceptedEventuallyUnderRationality MainRationality Accepted)
    (compiler :
      AcceptedToCompiledProjectSourceCertificateCompiler Accepted bounds) :
    MainCompiledProjectSourceCertificatesEventually MainRationality bounds := by
  intro hmain
  rcases haccepted hmain with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact ⟨compiler.compile n (hN n hn)⟩

noncomputable def MainCompiledProjectSourceCertificatesEventually.ofAcceptedExists
    {MainRationality : Prop} {Accepted : ℕ → Prop}
    {bounds : SondowComponentBounds}
    (haccepted :
      MainAcceptedEventuallyUnderRationality MainRationality Accepted)
    (hcompile :
      AcceptedToCompiledProjectSourceCertificateExists Accepted bounds) :
    MainCompiledProjectSourceCertificatesEventually MainRationality bounds :=
  MainCompiledProjectSourceCertificatesEventually.ofAcceptedCompiler
    haccepted
    (AcceptedToCompiledProjectSourceCertificateCompiler.ofExists hcompile)


structure SondowRationalityToProjectProofCodeCertificates
    (ctx : GammaRationalityContext) {bounds : SondowComponentBounds}
    (compilers : SondowProjectComponentProofCodeCompilers.{u} bounds) where
  certificates_of_rationality :
    GammaRationalityWitness ctx →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        Nonempty (SondowProjectProofCodeCertificateAt compilers n)

namespace SondowRationalityToProjectProofCodeCertificates

noncomputable def toProjectProofObjectCertificates
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    {compilers : SondowProjectComponentProofCodeCompilers.{u} bounds}
    (hcerts :
      SondowRationalityToProjectProofCodeCertificates ctx compilers) :
    SondowRationalityToProjectProofObjectCertificates ctx bounds where
  certificates_of_rationality := by
    intro hgamma
    rcases hcerts.certificates_of_rationality hgamma with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    rcases hN n hn with ⟨certs⟩
    exact ⟨certs.toComponentCertificate,
      certs.toComponentCertificate_valid⟩

end SondowRationalityToProjectProofCodeCertificates

structure SondowRationalityToProjectComponentSourceCertificates
    (ctx : GammaRationalityContext) {bounds : SondowComponentBounds}
    (compilers : SondowProjectComponentProofCodeCompilers.{u} bounds)
    where
  component_certificates_of_rationality :
    GammaRationalityWitness ctx →
      SondowProjectComponentSourceCertificatesEventually compilers

namespace SondowRationalityToProjectComponentSourceCertificates

def toProjectProofCodeCertificates
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    {compilers : SondowProjectComponentProofCodeCompilers.{u} bounds}
    (hcerts :
      SondowRationalityToProjectComponentSourceCertificates ctx compilers) :
    SondowRationalityToProjectProofCodeCertificates ctx compilers where
  certificates_of_rationality := by
    intro hgamma
    exact
      (hcerts.component_certificates_of_rationality hgamma)
        |>.toProjectProofCodeCertificatesEventually

end SondowRationalityToProjectComponentSourceCertificates

structure SondowRationalityToProjectCombinedSourceCertificates
    (ctx : GammaRationalityContext) {bounds : SondowComponentBounds}
    {compilers : SondowProjectComponentProofCodeCompilers.{u} bounds}
    (projectors :
      SondowProjectCombinedSourceCertificateProjectors compilers)
    where
  combined_certificates_of_rationality :
    GammaRationalityWitness ctx →
      SondowProjectCombinedSourceCertificatesEventually projectors

namespace SondowRationalityToProjectCombinedSourceCertificates

def toProjectComponentSourceCertificates
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    {compilers : SondowProjectComponentProofCodeCompilers.{u} bounds}
    {projectors :
      SondowProjectCombinedSourceCertificateProjectors compilers}
    (hcerts :
      SondowRationalityToProjectCombinedSourceCertificates
        ctx projectors) :
    SondowRationalityToProjectComponentSourceCertificates ctx compilers where
  component_certificates_of_rationality := by
    intro hgamma
    exact
      (hcerts.combined_certificates_of_rationality hgamma)
        |>.toComponentSourceCertificatesEventually

def toProjectProofCodeCertificates
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    {compilers : SondowProjectComponentProofCodeCompilers.{u} bounds}
    {projectors :
      SondowProjectCombinedSourceCertificateProjectors compilers}
    (hcerts :
      SondowRationalityToProjectCombinedSourceCertificates
        ctx projectors) :
    SondowRationalityToProjectProofCodeCertificates ctx compilers :=
  hcerts.toProjectComponentSourceCertificates
    |>.toProjectProofCodeCertificates

end SondowRationalityToProjectCombinedSourceCertificates

namespace SondowRationalityToCompiledProjectSourceCertificates

def toProjectCombinedSourceCertificates
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    (hcerts :
      SondowRationalityToCompiledProjectSourceCertificates ctx bounds) :
    SondowRationalityToProjectCombinedSourceCertificates ctx
      (compiledSondowProjectCombinedSourceCertificateProjectors bounds) where
  combined_certificates_of_rationality := by
    intro hgamma
    rcases hcerts.compiled_certificates_of_rationality hgamma with ⟨N, hN⟩
    refine ⟨?exists_eventually⟩
    exact ⟨N, fun n hn => by
      rcases hN n hn with ⟨cert⟩
      exact ⟨⟨n, cert⟩, rfl⟩⟩

def toProjectProofCodeCertificates
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    (hcerts :
      SondowRationalityToCompiledProjectSourceCertificates ctx bounds) :
    SondowRationalityToProjectProofCodeCertificates ctx
      (compiledSondowProjectComponentProofCodeCompilers bounds) :=
  hcerts.toProjectCombinedSourceCertificates
    |>.toProjectProofCodeCertificates

end SondowRationalityToCompiledProjectSourceCertificates

namespace SondowComponentCertificate.ProofObjectSystemValid

def toCompiledProjectSourceCertificateAt
    {bounds : SondowComponentBounds} {n : ℕ}
    {cert : SondowComponentCertificate}
    (hvalid :
      SondowComponentCertificate.ProofObjectSystemValid
        sondowProjectComponentFormulas bounds n cert) :
    CompiledSondowProjectSourceCertificateAt bounds n where
  product :=
    { index := n
      sourceSize := cert.productProof.size + 2
      proof := cert.productProof
      proof_conclusion := hvalid.product_conclusion
      proof_size_plus_two_le := hvalid.product_size_plus_two_le }
  product_index_eq := rfl
  logRelation :=
    { index := n
      sourceSize := cert.logProof.size + 2
      proof := cert.logProof
      proof_conclusion := hvalid.log_conclusion
      proof_size_plus_two_le := hvalid.log_size_plus_two_le }
  log_index_eq := rfl
  decomposition :=
    { index := n
      sourceSize := cert.decompositionProof.size + 2
      proof := cert.decompositionProof
      proof_conclusion := hvalid.decomposition_conclusion
      proof_size_plus_two_le := hvalid.decomposition_size_plus_two_le }
  decomposition_index_eq := rfl
  threePow :=
    { index := n
      sourceSize := cert.threePowProof.size + 2
      proof := cert.threePowProof
      proof_conclusion := hvalid.threePow_conclusion
      proof_size_plus_two_le := hvalid.threePow_size_plus_two_le }
  threePow_index_eq := rfl
  payload :=
    { index := n
      sourceSize := cert.payloadProof.size + 2
      proof := cert.payloadProof
      proof_conclusion := hvalid.payload_conclusion
      proof_size_plus_two_le := hvalid.payload_size_plus_two_le }
  payload_index_eq := rfl

end SondowComponentCertificate.ProofObjectSystemValid

def SondowRationalityToProjectProofObjectCertificates.toCompiledProjectSourceCertificates
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    (hcerts : SondowRationalityToProjectProofObjectCertificates ctx bounds) :
    SondowRationalityToCompiledProjectSourceCertificates ctx bounds where
  compiled_certificates_of_rationality := by
    intro hgamma
    rcases hcerts.certificates_of_rationality hgamma with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    rcases hN n hn with ⟨cert, hvalid⟩
    exact ⟨hvalid.toCompiledProjectSourceCertificateAt⟩

noncomputable def SondowRationalityCollisionInputs.ofProjectProofCodeCertificates
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    {compilers : SondowProjectComponentProofCodeCompilers.{u} bounds}
    (hcerts :
      SondowRationalityToProjectProofCodeCertificates ctx compilers)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    SondowRationalityCollisionInputs ctx where
  bounds := bounds
  exports :=
    SondowRationalityToComponentExports.ofProjectProofObjectCertificates
      hcerts.toProjectProofObjectCertificates
  calibration := calibration

theorem not_gamma_rationality_witness_of_project_proof_code_certificates
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    {compilers : SondowProjectComponentProofCodeCompilers.{u} bounds}
    (hcerts :
      SondowRationalityToProjectProofCodeCertificates ctx compilers)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ GammaRationalityWitness ctx :=
  not_gamma_rationality_witness_of_project_proof_object_certificates
    hcerts.toProjectProofObjectCertificates calibration

theorem not_main_rationality_of_project_proof_code_certificates
    {MainRationality : Prop} {bounds : SondowComponentBounds}
    {compilers : SondowProjectComponentProofCodeCompilers.{u} bounds}
    (hcerts :
      SondowRationalityToProjectProofCodeCertificates
        (mainGammaRationalityContext MainRationality) compilers)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ MainRationality :=
  not_main_rationality_of_refl_gamma_collision
    (SondowRationalityCollisionInputs.ofProjectProofCodeCertificates
      hcerts calibration)

theorem not_gamma_rationality_witness_of_project_component_source_certificates
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    {compilers : SondowProjectComponentProofCodeCompilers.{u} bounds}
    (hcerts :
      SondowRationalityToProjectComponentSourceCertificates ctx compilers)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ GammaRationalityWitness ctx :=
  not_gamma_rationality_witness_of_project_proof_code_certificates
    hcerts.toProjectProofCodeCertificates calibration

theorem not_main_rationality_of_project_component_source_certificates
    {MainRationality : Prop} {bounds : SondowComponentBounds}
    {compilers : SondowProjectComponentProofCodeCompilers.{u} bounds}
    (hcerts :
      SondowRationalityToProjectComponentSourceCertificates
        (mainGammaRationalityContext MainRationality) compilers)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ MainRationality :=
  not_main_rationality_of_project_proof_code_certificates
    hcerts.toProjectProofCodeCertificates calibration

theorem not_gamma_rationality_witness_of_project_combined_source_certificates
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    {compilers : SondowProjectComponentProofCodeCompilers.{u} bounds}
    {projectors :
      SondowProjectCombinedSourceCertificateProjectors compilers}
    (hcerts :
      SondowRationalityToProjectCombinedSourceCertificates ctx projectors)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ GammaRationalityWitness ctx :=
  not_gamma_rationality_witness_of_project_proof_code_certificates
    hcerts.toProjectProofCodeCertificates calibration

theorem not_main_rationality_of_project_combined_source_certificates
    {MainRationality : Prop} {bounds : SondowComponentBounds}
    {compilers : SondowProjectComponentProofCodeCompilers.{u} bounds}
    {projectors :
      SondowProjectCombinedSourceCertificateProjectors compilers}
    (hcerts :
      SondowRationalityToProjectCombinedSourceCertificates
        (mainGammaRationalityContext MainRationality) projectors)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ MainRationality :=
  not_main_rationality_of_project_proof_code_certificates
    hcerts.toProjectProofCodeCertificates calibration

theorem not_gamma_rationality_witness_of_compiled_project_source_certificates
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    (hcerts :
      SondowRationalityToCompiledProjectSourceCertificates ctx bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ GammaRationalityWitness ctx :=
  not_gamma_rationality_witness_of_project_proof_code_certificates
    hcerts.toProjectProofCodeCertificates calibration

theorem not_main_rationality_of_compiled_project_source_certificates
    {MainRationality : Prop} {bounds : SondowComponentBounds}
    (hcerts :
      SondowRationalityToCompiledProjectSourceCertificates
        (mainGammaRationalityContext MainRationality) bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ MainRationality :=
  not_main_rationality_of_project_proof_code_certificates
    hcerts.toProjectProofCodeCertificates calibration

theorem not_main_rationality_of_main_compiled_project_source_certificates_eventually
    {MainRationality : Prop} {bounds : SondowComponentBounds}
    (hcerts :
      MainCompiledProjectSourceCertificatesEventually MainRationality bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ MainRationality :=
  not_main_rationality_of_compiled_project_source_certificates
    hcerts.toPackage calibration

theorem not_main_rationality_of_accepted_compiled_project_source_certificates
    {MainRationality : Prop} {Accepted : ℕ → Prop}
    {bounds : SondowComponentBounds}
    (haccepted :
      MainAcceptedEventuallyUnderRationality MainRationality Accepted)
    (compiler :
      AcceptedToCompiledProjectSourceCertificateCompiler Accepted bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ MainRationality :=
  not_main_rationality_of_main_compiled_project_source_certificates_eventually
    (MainCompiledProjectSourceCertificatesEventually.ofAcceptedCompiler
      haccepted compiler)
    calibration

theorem
    not_main_rationality_of_accepted_compiled_project_source_certificate_exists
    {MainRationality : Prop} {Accepted : ℕ → Prop}
    {bounds : SondowComponentBounds}
    (haccepted :
      MainAcceptedEventuallyUnderRationality MainRationality Accepted)
    (hcompile :
      AcceptedToCompiledProjectSourceCertificateExists Accepted bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ MainRationality :=
  not_main_rationality_of_main_compiled_project_source_certificates_eventually
    (MainCompiledProjectSourceCertificatesEventually.ofAcceptedExists
      haccepted hcompile)
    calibration

theorem
    not_main_rationality_of_accepted_component_proof_certificate_traces
    {MainRationality : Prop} {Accepted : ℕ → Prop}
    {bounds : SondowComponentBounds}
    (haccepted :
      MainAcceptedEventuallyUnderRationality MainRationality Accepted)
    (traces :
      AcceptedToProjectComponentProofCertificateTraces Accepted bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ MainRationality :=
  not_main_rationality_of_accepted_compiled_project_source_certificate_exists
    haccepted traces.toCompiledExists calibration

theorem
    not_main_rationality_of_accepted_checked_code_trace_package
    {MainRationality : Prop} {sourceCode : ℕ → FormulaCode}
    {Accepted : ℕ → Prop} {bounds : SondowComponentBounds}
    (haccepted :
      MainAcceptedEventuallyUnderRationality MainRationality Accepted)
    (pkg :
      AcceptedCheckedCodeToProjectComponentTracePackage
        sourceCode Accepted bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ MainRationality :=
  not_main_rationality_of_accepted_component_proof_certificate_traces
    haccepted pkg.toComponentTraces calibration

theorem
    not_main_rationality_of_external_checked_code_trace_package
    {MainRationality : Prop} {Accepted : ℕ → Prop}
    {bounds : SondowComponentBounds}
    (haccepted :
      MainAcceptedEventuallyUnderRationality MainRationality Accepted)
    (pkg :
      ExternalAcceptedCheckedCodeToProjectComponentTracePackage
        Accepted bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ MainRationality :=
  not_main_rationality_of_accepted_component_proof_certificate_traces
    haccepted pkg.toComponentTraces calibration

theorem
    not_main_rationality_of_sondow_certificate_valid_checked_code_trace_package
    {MainRationality : Prop} {Accepted : ℕ → Prop}
    {bounds : SondowComponentBounds}
    (haccepted :
      MainAcceptedEventuallyUnderRationality MainRationality Accepted)
    (pkg :
      AcceptedCheckedCodeToProjectComponentTracePackage
        sondowCertificateValidCode Accepted bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ MainRationality :=
  not_main_rationality_of_accepted_checked_code_trace_package
    haccepted pkg calibration

end BoundedArithmeticLab
