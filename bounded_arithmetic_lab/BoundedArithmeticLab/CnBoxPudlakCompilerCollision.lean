/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakGap

/-!
# Compiler-facing collision route for canonical Cn boxes

This module connects the canonical Cn-box proof-length gap to the existing
concrete S21 verifier compiler.  It packages the audit-facing obligations that
remain before the project can instantiate the final collision: eventual
acceptance, a compiler for the canonical target, semantic relabeling, and length
calibration for the Pudlak lower source.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

structure CanonicalCnBoxShortUpperCertificate
    (accepted : Nat → Prop) where
  compiler :
    ConcreteS21VerifierCompiler
      canonicalPudlakTargetFamilySpec.target accepted

noncomputable def CanonicalCnBoxShortUpperCertificate.toShortUpper
    {accepted : Nat → Prop}
    (cert : CanonicalCnBoxShortUpperCertificate accepted) :
    EventualShortProofUpperBound canonicalCnBoxPABox accepted := by
  simpa [canonicalCnBoxPABox]
    using (cert.compiler.toPAShortProofUpper
      (code := canonicalPudlakTargetFamilySpec.code))

structure CanonicalCnBoxCompilerGapCollisionInputs
    (accepted : Nat → Prop) where
  acceptance : EventualAcceptanceUnderRationality accepted
  short_upper : CanonicalCnBoxShortUpperCertificate accepted
  lower_source : BussPudlakTheorem5PALowerBoundSource
  lower_calibration : CanonicalRelabeledPudlakCalibration lower_source

noncomputable def CanonicalCnBoxCompilerGapCollisionInputs.toGapInputs
    {accepted : Nat → Prop}
    (inputs : CanonicalCnBoxCompilerGapCollisionInputs accepted) :
    CanonicalCnBoxGapCollisionInputs accepted where
  acceptance := inputs.acceptance
  short_upper := inputs.short_upper.toShortUpper
  lower_source := inputs.lower_source
  lower_calibration := inputs.lower_calibration

noncomputable def CanonicalCnBoxCompilerGapCollisionInputs.gap
    {accepted : Nat → Prop}
    (inputs : CanonicalCnBoxCompilerGapCollisionInputs accepted) :
    CanonicalCnBoxProofLengthGap :=
  inputs.toGapInputs.gap

theorem canonicalCnBox_compiler_gap_collision
    {accepted : Nat → Prop}
    (inputs : CanonicalCnBoxCompilerGapCollisionInputs accepted) :
    False :=
  canonicalCnBox_gap_collision inputs.toGapInputs

structure CanonicalCnBoxTraceGapCollisionInputs
    (accepted : Nat → Prop) where
  acceptance : EventualAcceptanceUnderRationality accepted
  trace_system :
    ConcreteVerifierTraceSystem
      canonicalPudlakTargetFamilySpec.target accepted
  lower_source : BussPudlakTheorem5PALowerBoundSource
  lower_calibration : CanonicalRelabeledPudlakCalibration lower_source

noncomputable def CanonicalCnBoxTraceGapCollisionInputs.toCompilerInputs
    {accepted : Nat → Prop}
    (inputs : CanonicalCnBoxTraceGapCollisionInputs accepted) :
    CanonicalCnBoxCompilerGapCollisionInputs accepted where
  acceptance := inputs.acceptance
  short_upper := {
    compiler := inputs.trace_system.toCompiler }
  lower_source := inputs.lower_source
  lower_calibration := inputs.lower_calibration

theorem canonicalCnBox_trace_gap_collision
    {accepted : Nat → Prop}
    (inputs : CanonicalCnBoxTraceGapCollisionInputs accepted) :
    False :=
  canonicalCnBox_compiler_gap_collision inputs.toCompilerInputs

structure CanonicalCnBoxExternalObligationChecklist
    (accepted : Nat → Prop) where
  acceptance : EventualAcceptanceUnderRationality accepted
  compiler :
    ConcreteS21VerifierCompiler
      canonicalPudlakTargetFamilySpec.target accepted
  lower_source : BussPudlakTheorem5PALowerBoundSource
  relabeling :
    SemanticFormulaRelabeling lower_source.box.formula
      (concretePAFormalization
        canonicalPudlakTargetFamilySpec.target
        canonicalPudlakTargetFamilySpec.code).box.formula
  length_eq :
    ∀ n : Nat,
      lower_source.pa_length n =
        semanticBAProofLength PAAxiom finiteConsistencyFormula n

def CanonicalCnBoxExternalObligationChecklist.toRelabeledCalibration
    {accepted : Nat → Prop}
    (checklist : CanonicalCnBoxExternalObligationChecklist accepted) :
    CanonicalRelabeledPudlakCalibration checklist.lower_source where
  relabeling := checklist.relabeling
  length_eq := checklist.length_eq

noncomputable def CanonicalCnBoxExternalObligationChecklist.toCompilerInputs
    {accepted : Nat → Prop}
    (checklist : CanonicalCnBoxExternalObligationChecklist accepted) :
    CanonicalCnBoxCompilerGapCollisionInputs accepted where
  acceptance := checklist.acceptance
  short_upper := { compiler := checklist.compiler }
  lower_source := checklist.lower_source
  lower_calibration := checklist.toRelabeledCalibration

def CanonicalCnBoxCompilerGapCollisionInputs.toExternalChecklist
    {accepted : Nat → Prop}
    (inputs : CanonicalCnBoxCompilerGapCollisionInputs accepted) :
    CanonicalCnBoxExternalObligationChecklist accepted where
  acceptance := inputs.acceptance
  compiler := inputs.short_upper.compiler
  lower_source := inputs.lower_source
  relabeling := inputs.lower_calibration.relabeling
  length_eq := inputs.lower_calibration.length_eq

theorem canonicalCnBox_external_obligation_collision
    {accepted : Nat → Prop}
    (checklist : CanonicalCnBoxExternalObligationChecklist accepted) :
    False :=
  canonicalCnBox_compiler_gap_collision checklist.toCompilerInputs

end BoundedProofPredicate
end BoundedArithmeticLab
