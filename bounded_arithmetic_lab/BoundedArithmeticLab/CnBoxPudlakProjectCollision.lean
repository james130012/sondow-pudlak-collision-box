/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakProofCertificateCollision
import BoundedArithmeticLab.SondowHilbertProofCodeBridge

/-!
# Project-level Sondow-to-CnBox collision checklist

This module states the final interface between the Sondow rationality-to-
accepted route and the canonical Cn-box/Pudlak proof-length gap route.  The
accepted predicates are not identified by definitional equality; the connection
is an explicit predicate-transport certificate.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

structure AcceptedPredicateTransport
    (source target : Nat → Prop) : Prop where
  map_accepted : ∀ n : Nat, source n → target n

theorem acceptedPredicateTransport_refl
    (accepted : Nat → Prop) :
    AcceptedPredicateTransport accepted accepted where
  map_accepted := by intro _n h; exact h

theorem mainAcceptedEventually_transport
    {MainRationality : Prop}
    {source target : Nat → Prop}
    (transport : AcceptedPredicateTransport source target)
    (haccepted :
      MainAcceptedEventuallyUnderRationality MainRationality source) :
    MainAcceptedEventuallyUnderRationality MainRationality target := by
  intro hmain
  rcases haccepted hmain with ⟨N, hN⟩
  exact ⟨N, fun n hn => transport.map_accepted n (hN n hn)⟩

def EventualAcceptanceUnderRationality.ofMainAccepted
    {MainRationality : Prop} {accepted : Nat → Prop}
    (hmain : MainRationality)
    (haccepted :
      MainAcceptedEventuallyUnderRationality MainRationality accepted) :
    EventualAcceptanceUnderRationality accepted where
  accepts_eventually := haccepted hmain

structure ProjectLevelCnBoxCollisionChecklist
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bound : Nat → Real) where
  bound_poly : IsPolynomialBound bound
  sondow_eventual_accepted :
    MainAcceptedEventuallyUnderRationality
      MainRationality SondowAccepted
  accepted_transport :
    AcceptedPredicateTransport
      SondowAccepted (CanonicalProofCertificateAccepted bound)
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

def ProjectLevelCnBoxCollisionChecklist.canonicalAcceptance
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxCollisionChecklist
        MainRationality SondowAccepted bound) :
    MainAcceptedEventuallyUnderRationality
      MainRationality (CanonicalProofCertificateAccepted bound) :=
  mainAcceptedEventually_transport
    checklist.accepted_transport checklist.sondow_eventual_accepted

noncomputable def ProjectLevelCnBoxCollisionChecklist.toProofCertificateChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxCollisionChecklist
        MainRationality SondowAccepted bound)
    (hmain : MainRationality) :
    CanonicalCnBoxProofCertificateChecklist bound where
  bound_poly := checklist.bound_poly
  acceptance :=
    EventualAcceptanceUnderRationality.ofMainAccepted
      hmain checklist.canonicalAcceptance
  lower_source := checklist.lower_source
  relabeling := checklist.relabeling
  length_eq := checklist.length_eq

def ProjectLevelCnBoxCollisionChecklist.ofCanonicalAccepted
    {MainRationality : Prop} {bound : Nat → Real}
    (bound_poly : IsPolynomialBound bound)
    (accepted :
      MainAcceptedEventuallyUnderRationality
        MainRationality (CanonicalProofCertificateAccepted bound))
    (lower_source : BussPudlakTheorem5PALowerBoundSource)
    (relabeling :
      SemanticFormulaRelabeling lower_source.box.formula
        (concretePAFormalization
          canonicalPudlakTargetFamilySpec.target
          canonicalPudlakTargetFamilySpec.code).box.formula)
    (length_eq :
      ∀ n : Nat,
        lower_source.pa_length n =
          semanticBAProofLength PAAxiom finiteConsistencyFormula n) :
    ProjectLevelCnBoxCollisionChecklist MainRationality
      (CanonicalProofCertificateAccepted bound) bound where
  bound_poly := bound_poly
  sondow_eventual_accepted := accepted
  accepted_transport :=
    acceptedPredicateTransport_refl (CanonicalProofCertificateAccepted bound)
  lower_source := lower_source
  relabeling := relabeling
  length_eq := length_eq

theorem projectLevelChecklist_canonicalAccepted_roundtrip
    {MainRationality : Prop} {bound : Nat → Real}
    (bound_poly : IsPolynomialBound bound)
    (accepted :
      MainAcceptedEventuallyUnderRationality
        MainRationality (CanonicalProofCertificateAccepted bound))
    (lower_source : BussPudlakTheorem5PALowerBoundSource)
    (relabeling :
      SemanticFormulaRelabeling lower_source.box.formula
        (concretePAFormalization
          canonicalPudlakTargetFamilySpec.target
          canonicalPudlakTargetFamilySpec.code).box.formula)
    (length_eq :
      ∀ n : Nat,
        lower_source.pa_length n =
          semanticBAProofLength PAAxiom finiteConsistencyFormula n) :
    (ProjectLevelCnBoxCollisionChecklist.ofCanonicalAccepted
      bound_poly accepted lower_source relabeling length_eq).canonicalAcceptance =
      accepted := by
  rfl

theorem ProjectLevelCnBoxCollisionChecklist.false_of_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxCollisionChecklist
        MainRationality SondowAccepted bound)
    (hmain : MainRationality) :
    False :=
  canonicalCnBox_proof_certificate_collision
    (checklist.toProofCertificateChecklist hmain)

theorem ProjectLevelCnBoxCollisionChecklist.not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxCollisionChecklist
        MainRationality SondowAccepted bound) :
    ¬ MainRationality := by
  intro hmain
  exact checklist.false_of_main_rationality hmain

theorem not_main_rationality_of_project_level_cnbox_collision
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxCollisionChecklist
        MainRationality SondowAccepted bound) :
    ¬ MainRationality :=
  checklist.not_main_rationality

end BoundedProofPredicate
end BoundedArithmeticLab
