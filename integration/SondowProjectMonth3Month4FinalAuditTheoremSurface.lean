/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4PublicAuditIndexSurface
import integration.SondowProjectMonth3Month4VerifiedProjectIndexSurface

/-!
# Month 3/Month 4 final audit theorem surface

This module is the thin top-level theorem surface for the Month 3/Month 4
route.  It does not introduce a new package or a new mathematical endpoint.
It only names the final equivalences between:

* the paper route;
* the public project-level final audit;
* the verified project-level final audit carrying the Month 3 accepted
  proof-predicate witness and the Month 4 theorem-5 audit witness.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4FinalAuditTheoremSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4TheoremIndexSurface
open SondowProjectMonth3Month4PublicAuditIndexSurface
open SondowProjectMonth3Month4VerifiedProjectIndexSurface

abbrev PublicFinalAuditRoute
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real)
    (n : Nat) (haccepted : SondowAccepted n) : Prop :=
  Nonempty (Σ' pkg :
    PublicAuditIndexPackage
      rootSide MainRationality SondowAccepted bounds bound,
    ProjectLevelFinalAudit pkg n haccepted)

abbrev VerifiedDualWitnessFinalAuditRoute
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real)
    (n : Nat) (haccepted : SondowAccepted n) : Prop :=
  Nonempty (Σ' pkg :
    Month3Month4VerifiedProjectInstantiation
      rootSide MainRationality SondowAccepted bounds bound,
    VerifiedProjectLevelFinalAudit pkg n haccepted)

abbrev FinalAuditBridgePair
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real)
    (n : Nat) (haccepted : SondowAccepted n) : Prop :=
  PublicFinalAuditRoute
      rootSide MainRationality SondowAccepted bounds bound n haccepted ∧
    VerifiedDualWitnessFinalAuditRoute
      rootSide MainRationality SondowAccepted bounds bound n haccepted

theorem paper_route_iff_public_final_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      PublicFinalAuditRoute
        rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  paper_route_iff_project_level_final_audit n haccepted

theorem paper_route_iff_verified_dual_witness_final_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      VerifiedDualWitnessFinalAuditRoute
        rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  paper_route_iff_dual_witness_final_audit n haccepted

theorem public_final_audit_iff_verified_dual_witness_final_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    PublicFinalAuditRoute
        rootSide MainRationality SondowAccepted bounds bound n haccepted ↔
      VerifiedDualWitnessFinalAuditRoute
        rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  (paper_route_iff_public_final_audit n haccepted).symm.trans
    (paper_route_iff_verified_dual_witness_final_audit n haccepted)

theorem public_final_audit_to_verified_dual_witness_final_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (audit :
      PublicFinalAuditRoute
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    VerifiedDualWitnessFinalAuditRoute
      rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  (public_final_audit_iff_verified_dual_witness_final_audit
    n haccepted).mp audit

theorem verified_dual_witness_final_audit_to_public_final_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (audit :
      VerifiedDualWitnessFinalAuditRoute
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    PublicFinalAuditRoute
      rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  (public_final_audit_iff_verified_dual_witness_final_audit
    n haccepted).mpr audit

theorem paper_route_iff_final_audit_bridge_pair
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      FinalAuditBridgePair
        rootSide MainRationality SondowAccepted bounds bound n haccepted := by
  constructor
  · intro route
    exact
      ⟨(paper_route_iff_public_final_audit n haccepted).mp route,
        (paper_route_iff_verified_dual_witness_final_audit
          n haccepted).mp route⟩
  · intro pair
    exact (paper_route_iff_public_final_audit n haccepted).mpr pair.1

theorem exactConvention_checklist_iff_final_audit_bridge_pair
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      FinalAuditBridgePair
        h.toPudlakSideInputs MainRationality SondowAccepted
          bounds bound m haccepted :=
  (exactConvention_checklist_iff_paper_route h).trans
    (paper_route_iff_final_audit_bridge_pair m haccepted)

theorem splitMinChecked_checklist_iff_final_audit_bridge_pair
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      FinalAuditBridgePair
        h.toPudlakSideInputs MainRationality SondowAccepted
          bounds bound m haccepted :=
  (splitMinChecked_checklist_iff_paper_route h).trans
    (paper_route_iff_final_audit_bridge_pair m haccepted)

theorem exactFamily_checklist_iff_final_audit_bridge_pair
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      FinalAuditBridgePair
        h.toPudlakSideInputs MainRationality SondowAccepted
          bounds bound m haccepted :=
  (exactFamily_checklist_iff_paper_route h).trans
    (paper_route_iff_final_audit_bridge_pair m haccepted)

end SondowProjectMonth3Month4FinalAuditTheoremSurface
end SondowMainCheckedCodeBridge
