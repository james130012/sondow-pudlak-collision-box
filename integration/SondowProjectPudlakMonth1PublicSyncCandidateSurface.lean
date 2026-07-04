/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakMonth1CanonicalImportSurface

/-!
# Month 1 public sync candidate surface

This module packages the Month 1 canonical import certificate as a
public-sync candidate.  The candidate is deliberately an equivalence-preserving
wrapper around the canonical certificate, not a new proof route: the main
`↔` theorems show that the candidate is nonempty exactly when the concrete
CnBox/Pudlak checklist is nonempty at each of the three project entry points.

The additional audit endpoint structure records what a public or paper-facing
reviewer should be able to extract from a candidate:

* the CnBox encoding probe;
* the project same-object closure;
* the public gap instantiation and its public collision instantiation;
* the final `¬ MainRationality` endpoint.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakMonth1PublicSyncCandidateSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectPudlakMonth1CanonicalImportSurface

abbrev Month1PublicSyncWitnessPackage
    (root_scale : _root_.LiteraturePudlakTheorem5ScaleData) :=
  Month1CanonicalWitnessPackage root_scale

abbrev Month1PublicSyncEncodingProbe
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (gap_cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (checklist : SondowProjectPudlakConcreteBridgeChecklist
      rootSide gap_cert) :=
  Month1CanonicalEncodingProbe rootSide gap_cert checklist

structure Month1PublicSyncCandidate
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) where
  canonical :
    Month1CanonicalImportCertificate
      rootSide MainRationality SondowAccepted bounds bound

structure Month1PublicSyncAuditEndpoints
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop where
  encoding_probe :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      Σ' checklist :
        SondowProjectPudlakConcreteBridgeChecklist
          rootSide gap_cert,
        Month1PublicSyncEncodingProbe rootSide gap_cert checklist)
  same_object_closure :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)
  public_gap_instantiation :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality)
  public_collision_instantiation :
    Nonempty (BoundedArithmeticLab.PublicCollisionInstantiation
      MainRationality)
  not_main_rationality : ¬ MainRationality

namespace Month1PublicSyncCandidate

def toCanonical
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (candidate : Month1PublicSyncCandidate
      rootSide MainRationality SondowAccepted bounds bound) :
    Month1CanonicalImportCertificate
      rootSide MainRationality SondowAccepted bounds bound :=
  candidate.canonical

def ofCanonical
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (canonical : Month1CanonicalImportCertificate
      rootSide MainRationality SondowAccepted bounds bound) :
    Month1PublicSyncCandidate
      rootSide MainRationality SondowAccepted bounds bound where
  canonical := canonical

def toAuditorAssembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (candidate : Month1PublicSyncCandidate
      rootSide MainRationality SondowAccepted bounds bound) :
    Month1CanonicalAuditorAssembly
      rootSide MainRationality SondowAccepted bounds bound :=
  candidate.canonical.toAuditorAssembly

theorem nonempty_iff_canonical_import
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (Month1PublicSyncCandidate
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (Month1CanonicalImportCertificate
        rootSide MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨candidate⟩
    exact ⟨candidate.toCanonical⟩
  · intro h
    rcases h with ⟨canonical⟩
    exact ⟨ofCanonical canonical⟩

theorem nonempty_iff_auditor_assembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (Month1PublicSyncCandidate
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (Month1CanonicalAuditorAssembly
        rootSide MainRationality SondowAccepted bounds bound) :=
  nonempty_iff_canonical_import.trans
    Month1CanonicalImportCertificate.nonempty_iff_auditor_assembly

theorem nonempty_iff_public_bundle_origin
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (Month1PublicSyncCandidate
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (Σ' bundle : ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakExactInputBridgeReleaseSurface.PublicBundleLowerSourceOrigin
          rootSide bundle) :=
  nonempty_iff_canonical_import.trans
    Month1CanonicalImportCertificate.nonempty_iff_public_bundle_origin

theorem exactConvention_checklist_iff_public_sync_candidate
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
      Nonempty (Month1PublicSyncCandidate
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (Month1CanonicalImportCertificate.exactConvention_checklist_iff_canonical_import
    h).trans
      (nonempty_iff_canonical_import
        (rootSide := h.toPudlakSideInputs)
        (MainRationality := MainRationality)
        (SondowAccepted := SondowAccepted)
        (bounds := bounds)
        (bound := bound)).symm

theorem splitMinChecked_checklist_iff_public_sync_candidate
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
      Nonempty (Month1PublicSyncCandidate
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (Month1CanonicalImportCertificate.splitMinChecked_checklist_iff_canonical_import
    h).trans
      (nonempty_iff_canonical_import
        (rootSide := h.toPudlakSideInputs)
        (MainRationality := MainRationality)
        (SondowAccepted := SondowAccepted)
        (bounds := bounds)
        (bound := bound)).symm

theorem exactFamily_checklist_iff_public_sync_candidate
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
      Nonempty (Month1PublicSyncCandidate
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (Month1CanonicalImportCertificate.exactFamily_checklist_iff_canonical_import
    h).trans
      (nonempty_iff_canonical_import
        (rootSide := h.toPudlakSideInputs)
        (MainRationality := MainRationality)
        (SondowAccepted := SondowAccepted)
        (bounds := bounds)
        (bound := bound)).symm

theorem bounded_scale_eq_power
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (candidate : Month1PublicSyncCandidate
      rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    candidate.toAuditorAssembly.index.lower_source.conditions.scale_data.scale n =
      rootSide.literature_lower_bound.scale_data.time_constructible_bound n ^
        rootSide.literature_lower_bound.scale_data.exponent :=
  Month1CanonicalImportCertificate.bounded_scale_eq_power
    candidate.canonical n

theorem lower_source_scale_eq_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (candidate : Month1PublicSyncCandidate
      rootSide MainRationality SondowAccepted bounds bound) :
    candidate.toAuditorAssembly.index.lower_source.conditions.scale_data.scale =
      rootSide.literature_lower_bound.scale_data.scale :=
  Month1CanonicalImportCertificate.lower_source_scale_eq_root
    candidate.canonical

theorem time_constructible_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (candidate : Month1PublicSyncCandidate
      rootSide MainRationality SondowAccepted bounds bound) :
    candidate.toAuditorAssembly.index.lower_source.conditions.scale_data.time_constructible_statement ↔
      candidate.toAuditorAssembly.literature_witness.time_constructible_statement :=
  Month1CanonicalImportCertificate.time_constructible_iff_literature
    candidate.canonical

theorem eventually_reads_input_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (candidate : Month1PublicSyncCandidate
      rootSide MainRationality SondowAccepted bounds bound) :
    candidate.toAuditorAssembly.index.lower_source.conditions.scale_data.eventually_reads_input_statement ↔
      candidate.toAuditorAssembly.literature_witness.eventually_reads_input_statement :=
  Month1CanonicalImportCertificate.eventually_reads_input_iff_literature
    candidate.canonical

theorem eventually_defined_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (candidate : Month1PublicSyncCandidate
      rootSide MainRationality SondowAccepted bounds bound) :
    candidate.toAuditorAssembly.index.lower_source.conditions.scale_data.eventually_defined_statement ↔
      candidate.toAuditorAssembly.literature_witness.eventually_defined_statement :=
  Month1CanonicalImportCertificate.eventually_defined_iff_literature
    candidate.canonical

theorem dominates_input_length_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (candidate : Month1PublicSyncCandidate
      rootSide MainRationality SondowAccepted bounds bound) :
    candidate.toAuditorAssembly.index.lower_source.conditions.scale_data.dominates_input_length_statement ↔
      candidate.toAuditorAssembly.literature_witness.dominates_input_length_statement :=
  Month1CanonicalImportCertificate.dominates_input_length_iff_literature
    candidate.canonical

theorem root_normalForm_translation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (candidate : Month1PublicSyncCandidate
      rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    RootToBoundedFormulaCode
      ((rootSide.literature_lower_bound.toNormalForm
        rootSide.strengthened_to_partial).code n)
      (BoundedArithmeticLab.rescaledExternalPudlakCode
        candidate.toAuditorAssembly.index.lower_source.conditions.scale_data.scale n) :=
  Month1CanonicalImportCertificate.root_normalForm_translation
    candidate.canonical n

theorem encoding_probe_target_eq_box_formula
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {gap_cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    {checklist : SondowProjectPudlakConcreteBridgeChecklist
      rootSide gap_cert}
    (probe : Month1PublicSyncEncodingProbe rootSide gap_cert checklist)
    (n : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target n =
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box n).formula :=
  Month1CanonicalImportCertificate.encoding_probe_target_eq_box_formula
    probe n

theorem encoding_probe_box_code_roundtrip_to_target
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {gap_cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    {checklist : SondowProjectPudlakConcreteBridgeChecklist
      rootSide gap_cert}
    (probe : Month1PublicSyncEncodingProbe rootSide gap_cert checklist)
    (n : Nat) :
    BoundedArithmeticLab.BAFormula.decode
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box n).code =
        some
          (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target n) :=
  Month1CanonicalImportCertificate.encoding_probe_box_code_roundtrip_to_target
    probe n

theorem encoding_probe_carries_iff_pa_finite_consistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {gap_cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    {checklist : SondowProjectPudlakConcreteBridgeChecklist
      rootSide gap_cert}
    (probe : Month1PublicSyncEncodingProbe rootSide gap_cert checklist)
    (n : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.CnBoxCarriesPAFiniteConsistency
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box n) ↔
        BoundedArithmeticLab.BoundedProofPredicate.PAFiniteConsistencyStatement n :=
  Month1CanonicalImportCertificate.encoding_probe_carries_iff_pa_finite_consistency
    probe n

theorem exactConvention_to_encoding_probe
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
    (candidate : Month1PublicSyncCandidate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      Σ' checklist :
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert,
        Month1PublicSyncEncodingProbe
          h.toPudlakSideInputs gap_cert checklist) :=
  Month1CanonicalImportCertificate.exactConvention_to_encoding_probe
    h candidate.canonical

theorem splitMinChecked_to_encoding_probe
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
    (candidate : Month1PublicSyncCandidate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      Σ' checklist :
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert,
        Month1PublicSyncEncodingProbe
          h.toPudlakSideInputs gap_cert checklist) :=
  Month1CanonicalImportCertificate.splitMinChecked_to_encoding_probe
    h candidate.canonical

theorem exactFamily_to_encoding_probe
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
    (candidate : Month1PublicSyncCandidate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      Σ' checklist :
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert,
        Month1PublicSyncEncodingProbe
          h.toPudlakSideInputs gap_cert checklist) :=
  Month1CanonicalImportCertificate.exactFamily_to_encoding_probe
    h candidate.canonical

theorem exactConvention_to_same_object_closure
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
    (candidate : Month1PublicSyncCandidate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  Month1CanonicalImportCertificate.exactConvention_to_same_object_closure
    h candidate.canonical

theorem splitMinChecked_to_same_object_closure
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
    (candidate : Month1PublicSyncCandidate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  Month1CanonicalImportCertificate.splitMinChecked_to_same_object_closure
    h candidate.canonical

theorem exactFamily_to_same_object_closure
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
    (candidate : Month1PublicSyncCandidate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  Month1CanonicalImportCertificate.exactFamily_to_same_object_closure
    h candidate.canonical

theorem exactConvention_to_public_gap
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
    (candidate : Month1PublicSyncCandidate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  Month1CanonicalImportCertificate.exactConvention_to_public_gap
    h candidate.canonical

theorem splitMinChecked_to_public_gap
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
    (candidate : Month1PublicSyncCandidate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  Month1CanonicalImportCertificate.splitMinChecked_to_public_gap
    h candidate.canonical

theorem exactFamily_to_public_gap
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
    (candidate : Month1PublicSyncCandidate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  Month1CanonicalImportCertificate.exactFamily_to_public_gap
    h candidate.canonical

theorem exactConvention_to_public_collision
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
    (candidate : Month1PublicSyncCandidate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicCollisionInstantiation MainRationality) := by
  rcases exactConvention_to_public_gap h candidate with ⟨gap_inst⟩
  exact ⟨gap_inst.toCollisionInstantiation⟩

theorem splitMinChecked_to_public_collision
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
    (candidate : Month1PublicSyncCandidate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicCollisionInstantiation MainRationality) := by
  rcases splitMinChecked_to_public_gap h candidate with ⟨gap_inst⟩
  exact ⟨gap_inst.toCollisionInstantiation⟩

theorem exactFamily_to_public_collision
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
    (candidate : Month1PublicSyncCandidate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicCollisionInstantiation MainRationality) := by
  rcases exactFamily_to_public_gap h candidate with ⟨gap_inst⟩
  exact ⟨gap_inst.toCollisionInstantiation⟩

theorem exactConvention_not_main_rationality
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
    (candidate : Month1PublicSyncCandidate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  Month1CanonicalImportCertificate.exactConvention_not_main_rationality
    h candidate.canonical

theorem splitMinChecked_not_main_rationality
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
    (candidate : Month1PublicSyncCandidate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  Month1CanonicalImportCertificate.splitMinChecked_not_main_rationality
    h candidate.canonical

theorem exactFamily_not_main_rationality
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
    (candidate : Month1PublicSyncCandidate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  Month1CanonicalImportCertificate.exactFamily_not_main_rationality
    h candidate.canonical

theorem exactConvention_to_audit_endpoints
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
    (candidate : Month1PublicSyncCandidate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Month1PublicSyncAuditEndpoints
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  encoding_probe := exactConvention_to_encoding_probe h candidate
  same_object_closure := exactConvention_to_same_object_closure h candidate
  public_gap_instantiation := exactConvention_to_public_gap h candidate
  public_collision_instantiation := exactConvention_to_public_collision h candidate
  not_main_rationality := exactConvention_not_main_rationality h candidate

theorem splitMinChecked_to_audit_endpoints
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
    (candidate : Month1PublicSyncCandidate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Month1PublicSyncAuditEndpoints
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  encoding_probe := splitMinChecked_to_encoding_probe h candidate
  same_object_closure := splitMinChecked_to_same_object_closure h candidate
  public_gap_instantiation := splitMinChecked_to_public_gap h candidate
  public_collision_instantiation := splitMinChecked_to_public_collision h candidate
  not_main_rationality := splitMinChecked_not_main_rationality h candidate

theorem exactFamily_to_audit_endpoints
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
    (candidate : Month1PublicSyncCandidate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Month1PublicSyncAuditEndpoints
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  encoding_probe := exactFamily_to_encoding_probe h candidate
  same_object_closure := exactFamily_to_same_object_closure h candidate
  public_gap_instantiation := exactFamily_to_public_gap h candidate
  public_collision_instantiation := exactFamily_to_public_collision h candidate
  not_main_rationality := exactFamily_not_main_rationality h candidate

theorem exactConvention_nonempty_to_audit_endpoints
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
    (candidate_nonempty :
      Nonempty (Month1PublicSyncCandidate
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)) :
    Month1PublicSyncAuditEndpoints
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound := by
  rcases candidate_nonempty with ⟨candidate⟩
  exact exactConvention_to_audit_endpoints h candidate

theorem splitMinChecked_nonempty_to_audit_endpoints
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
    (candidate_nonempty :
      Nonempty (Month1PublicSyncCandidate
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)) :
    Month1PublicSyncAuditEndpoints
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound := by
  rcases candidate_nonempty with ⟨candidate⟩
  exact splitMinChecked_to_audit_endpoints h candidate

theorem exactFamily_nonempty_to_audit_endpoints
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
    (candidate_nonempty :
      Nonempty (Month1PublicSyncCandidate
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)) :
    Month1PublicSyncAuditEndpoints
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound := by
  rcases candidate_nonempty with ⟨candidate⟩
  exact exactFamily_to_audit_endpoints h candidate

end Month1PublicSyncCandidate

/-!
Intentional public-sync probes.
-/

#check Month1PublicSyncWitnessPackage
#check Month1PublicSyncEncodingProbe
#check Month1PublicSyncCandidate
#check Month1PublicSyncAuditEndpoints
#check Month1PublicSyncCandidate.nonempty_iff_canonical_import
#check Month1PublicSyncCandidate.nonempty_iff_public_bundle_origin
#check Month1PublicSyncCandidate.exactConvention_checklist_iff_public_sync_candidate
#check Month1PublicSyncCandidate.splitMinChecked_checklist_iff_public_sync_candidate
#check Month1PublicSyncCandidate.exactFamily_checklist_iff_public_sync_candidate
#check Month1PublicSyncCandidate.encoding_probe_box_code_roundtrip_to_target
#check Month1PublicSyncCandidate.encoding_probe_carries_iff_pa_finite_consistency
#check Month1PublicSyncCandidate.exactConvention_to_audit_endpoints
#check Month1PublicSyncCandidate.splitMinChecked_to_audit_endpoints
#check Month1PublicSyncCandidate.exactFamily_to_audit_endpoints
#check Month1PublicSyncCandidate.exactConvention_nonempty_to_audit_endpoints
#check Month1PublicSyncCandidate.splitMinChecked_nonempty_to_audit_endpoints
#check Month1PublicSyncCandidate.exactFamily_nonempty_to_audit_endpoints

end SondowProjectPudlakMonth1PublicSyncCandidateSurface
end SondowMainCheckedCodeBridge
