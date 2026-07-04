/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakAcceptedTransport

/-!
# Sondow certificate bridge into canonical CnBox certificates

This module names the final assembly obligation between the Sondow project
certificate route and the canonical CnBox/Pudlak route.  It does not identify
the Sondow component certificates with the canonical finite-consistency
certificate by fiat; the required conversion is an explicit assembler.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

structure SondowProjectToCanonicalProofCertificateAssembler
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  assemble :
    ∀ n : Nat,
      CompiledSondowProjectSourceCertificateAt bounds n →
        CanonicalProofCertificateAt bound n

namespace AcceptedToCompiledProjectSourceCertificateCompiler

def toCanonicalProofCertificateTransport
    {Accepted : Nat → Prop} {bounds : SondowComponentBounds}
    {bound : Nat → Real}
    (compiler :
      AcceptedToCompiledProjectSourceCertificateCompiler Accepted bounds)
    (assembler :
      SondowProjectToCanonicalProofCertificateAssembler bounds bound) :
    AcceptedToCanonicalProofCertificateTransport Accepted bound where
  certificate_of_accepted := by
    intro n haccepted
    exact ⟨assembler.assemble n (compiler.compile n haccepted)⟩

end AcceptedToCompiledProjectSourceCertificateCompiler

namespace AcceptedToCompiledProjectSourceCertificateExists

def toCanonicalProofCertificateTransport
    {Accepted : Nat → Prop} {bounds : SondowComponentBounds}
    {bound : Nat → Real}
    (compiled_exists :
      AcceptedToCompiledProjectSourceCertificateExists Accepted bounds)
    (assembler :
      SondowProjectToCanonicalProofCertificateAssembler bounds bound) :
    AcceptedToCanonicalProofCertificateTransport Accepted bound where
  certificate_of_accepted := by
    intro n haccepted
    rcases compiled_exists n haccepted with ⟨sourceCert⟩
    exact ⟨assembler.assemble n sourceCert⟩

end AcceptedToCompiledProjectSourceCertificateExists

namespace AcceptedToProjectComponentProofCertificateTraces

noncomputable def toCanonicalProofCertificateTransport
    {Accepted : Nat → Prop} {bounds : SondowComponentBounds}
    {bound : Nat → Real}
    (traces :
      AcceptedToProjectComponentProofCertificateTraces Accepted bounds)
    (assembler :
      SondowProjectToCanonicalProofCertificateAssembler bounds bound) :
    AcceptedToCanonicalProofCertificateTransport Accepted bound :=
  AcceptedToCompiledProjectSourceCertificateCompiler.toCanonicalProofCertificateTransport
    traces.toCompiler assembler

end AcceptedToProjectComponentProofCertificateTraces

namespace ExternalAcceptedCheckedCodeToProjectComponentTracePackage

noncomputable def toCanonicalProofCertificateTransport
    {Accepted : Nat → Prop} {bounds : SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      ExternalAcceptedCheckedCodeToProjectComponentTracePackage
        Accepted bounds)
    (assembler :
      SondowProjectToCanonicalProofCertificateAssembler bounds bound) :
    AcceptedToCanonicalProofCertificateTransport Accepted bound :=
  AcceptedToProjectComponentProofCertificateTraces.toCanonicalProofCertificateTransport
    pkg.toComponentTraces assembler

end ExternalAcceptedCheckedCodeToProjectComponentTracePackage

structure ProjectLevelCnBoxSondowCompiledChecklist
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  bound_poly : IsPolynomialBound bound
  sondow_eventual_accepted :
    MainAcceptedEventuallyUnderRationality
      MainRationality SondowAccepted
  accepted_to_compiled_source :
    AcceptedToCompiledProjectSourceCertificateCompiler
      SondowAccepted bounds
  canonical_assembler :
    SondowProjectToCanonicalProofCertificateAssembler bounds bound
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

noncomputable def
    ProjectLevelCnBoxSondowCompiledChecklist.toProofCertificateTransportChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowCompiledChecklist
        MainRationality SondowAccepted bounds bound) :
    ProjectLevelCnBoxProofCertificateTransportChecklist
      MainRationality SondowAccepted bound where
  bound_poly := checklist.bound_poly
  sondow_eventual_accepted := checklist.sondow_eventual_accepted
  accepted_to_certificate :=
    AcceptedToCompiledProjectSourceCertificateCompiler.toCanonicalProofCertificateTransport
      checklist.accepted_to_compiled_source checklist.canonical_assembler
  lower_source := checklist.lower_source
  relabeling := checklist.relabeling
  length_eq := checklist.length_eq

noncomputable def ProjectLevelCnBoxSondowCompiledChecklist.toProjectChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowCompiledChecklist
        MainRationality SondowAccepted bounds bound) :
    ProjectLevelCnBoxCollisionChecklist
      MainRationality SondowAccepted bound :=
  checklist.toProofCertificateTransportChecklist.toProjectChecklist

theorem ProjectLevelCnBoxSondowCompiledChecklist.not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowCompiledChecklist
        MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  checklist.toProofCertificateTransportChecklist.not_main_rationality

end BoundedProofPredicate
end BoundedArithmeticLab
