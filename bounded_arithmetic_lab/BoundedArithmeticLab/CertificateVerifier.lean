/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.OperationalVerifier

/-!
# Certificate verifier machines

This module replaces a bare accepting predicate by an explicit verifier with
certificates.  The concrete proof-certificate verifier accepts exactly when the
certificate is an S21 derivation of the target formula and its encoded size is
within the declared polynomial bound.
-/

namespace BoundedArithmeticLab

universe u v

structure CertificateVerifierMachine where
  Cert : Type u
  State : Type v
  initial : ℕ → Cert → State
  step : State → State → Prop
  accepting : State → Prop
  stateSize : State → ℕ

namespace CertificateVerifierMachine

inductive Reaches (M : CertificateVerifierMachine.{u, v}) :
    M.State → M.State → ℕ → Prop where
  | refl (s : M.State) : Reaches M s s 0
  | cons {s t u : M.State} {k : ℕ} :
      M.step s t → Reaches M t u k → Reaches M s u (k + 1)

structure AcceptedTrace (M : CertificateVerifierMachine.{u, v}) (n : ℕ) where
  cert : M.Cert
  final : M.State
  steps : ℕ
  reaches : Reaches M (M.initial n cert) final steps
  accepts : M.accepting final

def AcceptedTrace.size {M : CertificateVerifierMachine.{u, v}} {n : ℕ}
    (tr : AcceptedTrace M n) : ℕ :=
  M.stateSize (M.initial n tr.cert) + 1

def acceptsInput (M : CertificateVerifierMachine.{u, v}) (n : ℕ) : Prop :=
  Nonempty (AcceptedTrace M n)

structure CertificateOperationalS21Compiler
    (M : CertificateVerifierMachine.{u, v}) (target : ℕ → BAFormula) where
  trace_bound : ℕ → ℝ
  trace_bound_poly : IsPolynomialBound trace_bound
  trace_size_le :
    ∀ n : ℕ, ∀ tr : AcceptedTrace M n,
      (tr.size : ℝ) ≤ trace_bound n
  compileTrace :
    ∀ n : ℕ, AcceptedTrace M n → BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ n : ℕ, ∀ tr : AcceptedTrace M n,
      (compileTrace n tr).conclusion = target n
  compile_size_le_trace_size :
    ∀ n : ℕ, ∀ tr : AcceptedTrace M n,
      ((compileTrace n tr).size : ℝ) ≤ tr.size

def CertificateOperationalS21Compiler.toConcreteTraceSystem
    {M : CertificateVerifierMachine.{u, v}} {target : ℕ → BAFormula}
    (compiler : CertificateOperationalS21Compiler M target) :
    ConcreteVerifierTraceSystem target M.acceptsInput where
  Trace := Σ n : ℕ, AcceptedTrace M n
  index := fun tr => tr.1
  traceAccepted := fun _ => True
  accepted_has_trace := by
    intro n hn
    rcases hn with ⟨tr⟩
    exact ⟨⟨n, tr⟩, rfl, trivial⟩
  trace_bound := compiler.trace_bound
  trace_bound_poly := compiler.trace_bound_poly
  trace_size := fun tr => tr.2.size
  trace_size_le := by
    intro tr _htr
    exact compiler.trace_size_le tr.1 tr.2
  compileTrace := by
    intro tr _htr
    exact compiler.compileTrace tr.1 tr.2
  compile_conclusion := by
    intro tr _htr
    exact compiler.compile_conclusion tr.1 tr.2
  compile_size_le_trace_size := by
    intro tr _htr
    exact compiler.compile_size_le_trace_size tr.1 tr.2

theorem collision_of_certificate_verifier_exact_pa_pudlak
    {M : CertificateVerifierMachine.{u, v}} {target : ℕ → BAFormula}
    {code : BAFormula → FormulaCode}
    (haccept : EventualAcceptanceUnderRationality M.acceptsInput)
    (compiler : CertificateOperationalS21Compiler M target)
    (lower : ConcreteBussPudlakExactLowerForPA target code) :
    False :=
  collision_of_concrete_trace_system_exact_pa_pudlak
    { acceptance := haccept
      trace_system := compiler.toConcreteTraceSystem
      exact_lower := lower }

end CertificateVerifierMachine

inductive ProofCertificateState
    (target : ℕ → BAFormula) (bound : ℕ → ℝ) where
  | start (n : ℕ) (cert : BAProofObject BussS21Axiom)
  | accepted (n : ℕ) (cert : BAProofObject BussS21Axiom)
      (hconclusion : cert.conclusion = target n)
      (hsize : ((cert.size + 2 : ℕ) : ℝ) ≤ bound n)

namespace ProofCertificateState

def size {target : ℕ → BAFormula} {bound : ℕ → ℝ} :
    ProofCertificateState target bound → ℕ
  | start _ cert => cert.size + 1
  | accepted _ cert _ _ => cert.size + 1

def accepting {target : ℕ → BAFormula} {bound : ℕ → ℝ} :
    ProofCertificateState target bound → Prop
  | accepted _ _ _ _ => True
  | start _ _ => False

inductive Step {target : ℕ → BAFormula} {bound : ℕ → ℝ} :
    ProofCertificateState target bound →
    ProofCertificateState target bound → Prop where
  | accept {n : ℕ} {cert : BAProofObject BussS21Axiom}
      (hconclusion : cert.conclusion = target n)
      (hsize : ((cert.size + 2 : ℕ) : ℝ) ≤ bound n) :
      Step (start n cert) (accepted n cert hconclusion hsize)

end ProofCertificateState

def proofCertificateVerifierMachine
    (target : ℕ → BAFormula) (bound : ℕ → ℝ) :
    CertificateVerifierMachine where
  Cert := BAProofObject BussS21Axiom
  State := ProofCertificateState target bound
  initial := fun n cert => ProofCertificateState.start n cert
  step := ProofCertificateState.Step
  accepting := ProofCertificateState.accepting
  stateSize := ProofCertificateState.size

namespace proofCertificateVerifierMachine

theorem acceptedTrace_conclusion
    {target : ℕ → BAFormula} {bound : ℕ → ℝ} {n : ℕ}
    (tr : CertificateVerifierMachine.AcceptedTrace
      (proofCertificateVerifierMachine target bound) n) :
    tr.cert.conclusion = target n := by
  cases tr with
  | mk cert final steps reaches accepts =>
      cases reaches with
      | refl s =>
          simp [proofCertificateVerifierMachine,
            ProofCertificateState.accepting] at accepts
      | cons hstep _rest =>
          cases hstep with
          | accept hconclusion _hsize =>
              exact hconclusion

theorem acceptedTrace_size_le_bound
    {target : ℕ → BAFormula} {bound : ℕ → ℝ} {n : ℕ}
    (tr : CertificateVerifierMachine.AcceptedTrace
      (proofCertificateVerifierMachine target bound) n) :
    (tr.size : ℝ) ≤ bound n := by
  cases tr with
  | mk cert final steps reaches accepts =>
      cases reaches with
      | refl s =>
          simp [proofCertificateVerifierMachine,
            ProofCertificateState.accepting] at accepts
      | cons hstep _rest =>
          cases hstep with
          | accept _hconclusion hsize =>
              simpa [CertificateVerifierMachine.AcceptedTrace.size,
                proofCertificateVerifierMachine, ProofCertificateState.size,
                Nat.add_assoc] using hsize

theorem acceptedTrace_compile_size_le_trace_size
    {target : ℕ → BAFormula} {bound : ℕ → ℝ} {n : ℕ}
    (tr : CertificateVerifierMachine.AcceptedTrace
      (proofCertificateVerifierMachine target bound) n) :
    (tr.cert.size : ℝ) ≤ tr.size := by
  dsimp [CertificateVerifierMachine.AcceptedTrace.size,
    proofCertificateVerifierMachine, ProofCertificateState.size]
  exact_mod_cast (Nat.le_add_right tr.cert.size 2)

def compiler
    (target : ℕ → BAFormula) {bound : ℕ → ℝ}
    (hbound : IsPolynomialBound bound) :
    CertificateVerifierMachine.CertificateOperationalS21Compiler
      (proofCertificateVerifierMachine target bound) target where
  trace_bound := bound
  trace_bound_poly := hbound
  trace_size_le := by
    intro n tr
    exact acceptedTrace_size_le_bound tr
  compileTrace := by
    intro n tr
    exact tr.cert
  compile_conclusion := by
    intro n tr
    exact acceptedTrace_conclusion tr
  compile_size_le_trace_size := by
    intro n tr
    exact acceptedTrace_compile_size_le_trace_size tr

theorem collision_of_proof_certificate_verifier_exact_pa_pudlak
    {target : ℕ → BAFormula} {code : BAFormula → FormulaCode}
    {bound : ℕ → ℝ}
    (hbound : IsPolynomialBound bound)
    (haccept :
      EventualAcceptanceUnderRationality
        (CertificateVerifierMachine.acceptsInput
          (proofCertificateVerifierMachine target bound)))
    (lower : ConcreteBussPudlakExactLowerForPA target code) :
    False :=
  CertificateVerifierMachine.collision_of_certificate_verifier_exact_pa_pudlak
    haccept (compiler target hbound) lower

theorem collision_of_proof_certificate_verifier_calibrated_pudlak
    {target : ℕ → BAFormula} {code : BAFormula → FormulaCode}
    {bound : ℕ → ℝ}
    (hbound : IsPolynomialBound bound)
    (haccept :
      EventualAcceptanceUnderRationality
        (CertificateVerifierMachine.acceptsInput
          (proofCertificateVerifierMachine target bound)))
    (calibration : ConcreteBussPudlakBoxCalibration target code) :
    False :=
  collision_of_proof_certificate_verifier_exact_pa_pudlak
    hbound haccept calibration.toExactLower

end proofCertificateVerifierMachine

end BoundedArithmeticLab
