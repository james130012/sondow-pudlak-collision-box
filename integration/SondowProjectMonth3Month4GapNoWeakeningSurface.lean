/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4CanonicalImportSurface
import BoundedArithmeticLab.CnBoxPudlakExternalGapSameObjectBridge

/-!
# Month 3/Month 4 gap no-weakening surface

This module pins the Month 3/Month 4 canonical package to the project-level
external gap criterion.  The gap route exposed here is not a fresh numerical
predicate: it is the projection of the same concrete certificate field index
already consumed by the Month 3/Month 4 bridge-link surface.

The release-facing result is stated with equivalences from the public concrete
checklists to the no-weakening package, so auditors can verify that no weaker
endpoint has been substituted.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4GapNoWeakeningSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4BridgeLinkSurface
open SondowProjectMonth3Month4CanonicalImportSurface

noncomputable def externalGapCriterion
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound) :
    ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  assembly.index.toExternalGapCriterion

noncomputable def canonicalCertificateAt
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :=
  ProjectSourceAssemblyFieldReleaseSurface.field_index_canonical_certificate_at
    assembly.index n haccepted

structure Month3Month4GapNoWeakeningStatement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound) :
    Prop where
  canonical_import :
    Month3Month4CanonicalBridgeLinkStatement assembly
  external_gap_has_criterion :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound
  external_gap_same_object :
    ∀ n : Nat,
      ExternalGapSameObjectBridge.Certificate (externalGapCriterion assembly) n
  external_gap_target_eq_box_formula :
    ∀ n : Nat,
      canonicalPudlakTargetFamilySpec.target n =
        (canonicalPudlakTargetFamilySpec.box n).formula
  external_gap_code_eq_box_formulaCode :
    ∀ n : Nat,
      canonicalPudlakTargetFamilySpec.code
        (canonicalPudlakTargetFamilySpec.target n) =
          (canonicalPudlakTargetFamilySpec.box n).formulaCode
  external_gap_box_code_roundtrip_to_target :
    ∀ n : Nat,
      BoundedArithmeticLab.BAFormula.decode
        (canonicalPudlakTargetFamilySpec.box n).code =
          some (canonicalPudlakTargetFamilySpec.target n)
  external_gap_carries_iff_pa_finite_consistency :
    ∀ n : Nat,
      CnBoxCarriesPAFiniteConsistency
        (canonicalPudlakTargetFamilySpec.box n) ↔
          PAFiniteConsistencyStatement n
  external_gap_lower_length_eq_canonical_length :
    ∀ n : Nat,
      (externalGapCriterion assembly).lower_source.pa_length n =
        canonicalPudlakTargetFamilySpec.length n
  gap_witness_against_declared_bound :
    ∀ N : Nat,
      HasProofLengthGapWitness canonicalCnBoxPABox bound N
  accepted_certificate_conclusion_eq_box_formula :
    ∀ n : Nat, (haccepted : SondowAccepted n) →
      (canonicalCertificateAt assembly n haccepted).proof.conclusion =
        (canonicalPudlakTargetFamilySpec.box n).formula
  accepted_certificate_code_eq_box_formulaCode :
    ∀ n : Nat, (haccepted : SondowAccepted n) →
      canonicalPudlakTargetFamilySpec.code
        ((canonicalCertificateAt assembly n haccepted).proof.conclusion) =
          (canonicalPudlakTargetFamilySpec.box n).formulaCode
  accepted_certificate_box_code_roundtrip_to_conclusion :
    ∀ n : Nat, (haccepted : SondowAccepted n) →
      BoundedArithmeticLab.BAFormula.decode
        (canonicalPudlakTargetFamilySpec.box n).code =
          some
            ((canonicalCertificateAt assembly n haccepted).proof.conclusion)
  not_main_rationality : ¬ MainRationality

theorem statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound) :
    Month3Month4GapNoWeakeningStatement assembly where
  canonical_import :=
    SondowProjectMonth3Month4CanonicalImportSurface.statement assembly
  external_gap_has_criterion := ⟨externalGapCriterion assembly⟩
  external_gap_same_object := by
    intro n
    exact ExternalGapSameObjectBridge.certificate
      (externalGapCriterion assembly) n
  external_gap_target_eq_box_formula := by
    intro n
    exact ExternalGapSameObjectBridge.target_eq_box_formula
      (externalGapCriterion assembly) n
  external_gap_code_eq_box_formulaCode := by
    intro n
    exact ExternalGapSameObjectBridge.code_eq_box_formulaCode
      (externalGapCriterion assembly) n
  external_gap_box_code_roundtrip_to_target := by
    intro n
    exact ExternalGapSameObjectBridge.box_code_roundtrip_to_target
      (externalGapCriterion assembly) n
  external_gap_carries_iff_pa_finite_consistency := by
    intro n
    exact ExternalGapSameObjectBridge.carries_iff_pa_finite_consistency
      (externalGapCriterion assembly) n
  external_gap_lower_length_eq_canonical_length := by
    intro n
    exact ExternalGapSameObjectBridge.lower_length_eq_canonical_length
      (externalGapCriterion assembly) n
  gap_witness_against_declared_bound := by
    intro N
    exact assembly.index.witnessAgainstDeclaredBound N
  accepted_certificate_conclusion_eq_box_formula := by
    intro n haccepted
    exact AcceptedSameObjectBridge.field_index_canonical_certificate_conclusion_eq_box_formula
        assembly.index n haccepted
  accepted_certificate_code_eq_box_formulaCode := by
    intro n haccepted
    exact AcceptedSameObjectBridge.field_index_canonical_certificate_code_eq_box_formulaCode
        assembly.index n haccepted
  accepted_certificate_box_code_roundtrip_to_conclusion := by
    intro n haccepted
    exact AcceptedSameObjectBridge.field_index_canonical_certificate_box_code_roundtrip_to_conclusion
        assembly.index n haccepted
  not_main_rationality :=
    (externalGapCriterion assembly).not_main_rationality

theorem statement_iff_canonical_import_and_external_gap_same_object
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound) :
    Month3Month4GapNoWeakeningStatement assembly ↔
      Month3Month4CanonicalBridgeLinkStatement assembly ∧
        (∀ n : Nat,
          ExternalGapSameObjectBridge.Certificate
            (externalGapCriterion assembly) n) := by
  constructor
  · intro h
    exact ⟨h.canonical_import, h.external_gap_same_object⟩
  · intro _h
    exact statement assembly

structure Month3Month4GapNoWeakeningPackage
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) where
  assembly :
    PowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound
  gap_no_weakening_statement :
    Month3Month4GapNoWeakeningStatement assembly

namespace Month3Month4GapNoWeakeningPackage

def ofAssembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound) :
    Month3Month4GapNoWeakeningPackage
      rootSide MainRationality SondowAccepted bounds bound where
  assembly := assembly
  gap_no_weakening_statement := statement assembly

end Month3Month4GapNoWeakeningPackage

theorem gapNoWeakeningPackage_nonempty_iff_power_scale_assembly_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty
        (Month3Month4GapNoWeakeningPackage
          rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty
        (PowerScaleAssembly
          rootSide MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨pkg⟩
    exact ⟨pkg.assembly⟩
  · intro h
    rcases h with ⟨assembly⟩
    exact ⟨Month3Month4GapNoWeakeningPackage.ofAssembly assembly⟩

theorem canonical_import_iff_gap_no_weakening_package
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty
        (Month3Month4CanonicalPackage
          rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty
        (Month3Month4GapNoWeakeningPackage
          rootSide MainRationality SondowAccepted bounds bound) :=
  SondowProjectMonth3Month4CanonicalImportSurface.package_nonempty_iff_power_scale_assembly_nonempty.trans
      gapNoWeakeningPackage_nonempty_iff_power_scale_assembly_nonempty.symm

theorem exactConvention_checklist_iff_gap_no_weakening_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Nonempty
        (Month3Month4GapNoWeakeningPackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (SondowProjectMonth3Month4CanonicalImportSurface.exactConvention_checklist_iff_canonical_import
    h).trans
      canonical_import_iff_gap_no_weakening_package

theorem splitMinChecked_checklist_iff_gap_no_weakening_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Nonempty
        (Month3Month4GapNoWeakeningPackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (SondowProjectMonth3Month4CanonicalImportSurface.splitMinChecked_checklist_iff_canonical_import
    h).trans
      canonical_import_iff_gap_no_weakening_package

theorem exactFamily_checklist_iff_gap_no_weakening_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Nonempty
        (Month3Month4GapNoWeakeningPackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (SondowProjectMonth3Month4CanonicalImportSurface.exactFamily_checklist_iff_canonical_import
    h).trans
      canonical_import_iff_gap_no_weakening_package

theorem gapNoWeakeningPackage_to_public_gap_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      Month3Month4GapNoWeakeningPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  ExternalGapSameObjectBridge.hasCriterion_to_public_gap_instantiation
    pkg.gap_no_weakening_statement.external_gap_has_criterion

theorem gapNoWeakeningPackage_not_main_rationality
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      Month3Month4GapNoWeakeningPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  pkg.gap_no_weakening_statement.not_main_rationality

theorem exactConvention_checklist_to_public_gap_instantiation
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) := by
  rcases (exactConvention_checklist_iff_gap_no_weakening_package h).1
    checklist with ⟨pkg⟩
  exact gapNoWeakeningPackage_to_public_gap_instantiation pkg

theorem splitMinChecked_checklist_to_public_gap_instantiation
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) := by
  rcases (splitMinChecked_checklist_iff_gap_no_weakening_package h).1
    checklist with ⟨pkg⟩
  exact gapNoWeakeningPackage_to_public_gap_instantiation pkg

theorem exactFamily_checklist_to_public_gap_instantiation
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) := by
  rcases (exactFamily_checklist_iff_gap_no_weakening_package h).1
    checklist with ⟨pkg⟩
  exact gapNoWeakeningPackage_to_public_gap_instantiation pkg

theorem exactConvention_checklist_not_main_rationality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    ¬ MainRationality := by
  rcases (exactConvention_checklist_iff_gap_no_weakening_package h).1
    checklist with ⟨pkg⟩
  exact gapNoWeakeningPackage_not_main_rationality pkg

theorem splitMinChecked_checklist_not_main_rationality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    ¬ MainRationality := by
  rcases (splitMinChecked_checklist_iff_gap_no_weakening_package h).1
    checklist with ⟨pkg⟩
  exact gapNoWeakeningPackage_not_main_rationality pkg

theorem exactFamily_checklist_not_main_rationality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    ¬ MainRationality := by
  rcases (exactFamily_checklist_iff_gap_no_weakening_package h).1
    checklist with ⟨pkg⟩
  exact gapNoWeakeningPackage_not_main_rationality pkg


end SondowProjectMonth3Month4GapNoWeakeningSurface
end SondowMainCheckedCodeBridge
