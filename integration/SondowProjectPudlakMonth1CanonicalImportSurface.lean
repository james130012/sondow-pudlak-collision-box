/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakMonth1ProbeCertificateBundle

/-!
# Month 1 canonical import surface

This module is the stable single-import surface for the Month 1
same-object/public-bridge route.  It imports the probe certificate bundle and
then exposes canonical names for the proof objects and endpoints that an
auditor should check.

The surface is intentionally thin but not merely decorative: it proves the
canonical certificate is equivalent to the probe certificate, the auditor
assembly, and the public bundle origin.  All endpoint theorems are delegated to
the probe certificate bundle, preserving the exact proof route.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakMonth1CanonicalImportSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectPudlakMonth1PublicAuditorEntrySurface
open SondowProjectPudlakMonth1ProbeCertificateBundle

abbrev Month1CanonicalWitnessPackage
    (root_scale : _root_.LiteraturePudlakTheorem5ScaleData) :=
  Month1PublicAuditorWitnessPackage root_scale

abbrev Month1CanonicalAuditorAssembly
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) :=
  Month1PublicAuditorAssembly
    rootSide MainRationality SondowAccepted bounds bound

abbrev Month1CanonicalProbeCertificate
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) :=
  Month1ProbeCertificate
    rootSide MainRationality SondowAccepted bounds bound

abbrev Month1CanonicalEncodingProbe
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (gap_cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (checklist : SondowProjectPudlakConcreteBridgeChecklist
      rootSide gap_cert) :=
  Month1ConcreteChecklistEncodingProbe rootSide gap_cert checklist

structure Month1CanonicalImportCertificate
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) where
  probe :
    Month1CanonicalProbeCertificate
      rootSide MainRationality SondowAccepted bounds bound

namespace Month1CanonicalImportCertificate

def toAuditorAssembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (cert : Month1CanonicalImportCertificate
      rootSide MainRationality SondowAccepted bounds bound) :
    Month1CanonicalAuditorAssembly
      rootSide MainRationality SondowAccepted bounds bound :=
  cert.probe.assembly

def ofAuditorAssembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : Month1CanonicalAuditorAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    Month1CanonicalImportCertificate
      rootSide MainRationality SondowAccepted bounds bound where
  probe := { assembly := assembly }

theorem nonempty_iff_probe_certificate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (Month1CanonicalImportCertificate
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (Month1CanonicalProbeCertificate
        rootSide MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.probe⟩
  · intro h
    rcases h with ⟨probe⟩
    exact ⟨{ probe := probe }⟩

theorem nonempty_iff_auditor_assembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (Month1CanonicalImportCertificate
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (Month1CanonicalAuditorAssembly
        rootSide MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toAuditorAssembly⟩
  · intro h
    rcases h with ⟨assembly⟩
    exact ⟨ofAuditorAssembly assembly⟩

theorem nonempty_iff_public_bundle_origin
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (Month1CanonicalImportCertificate
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (Σ' bundle : ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakExactInputBridgeReleaseSurface.PublicBundleLowerSourceOrigin
          rootSide bundle) :=
  nonempty_iff_auditor_assembly.trans
    month1_auditor_entry_iff_public_bundle_origin

theorem exactConvention_checklist_iff_canonical_import
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
      Nonempty (Month1CanonicalImportCertificate
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactConvention_checklist_iff_month1_auditor_entry h).trans
    nonempty_iff_auditor_assembly.symm

theorem splitMinChecked_checklist_iff_canonical_import
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
      Nonempty (Month1CanonicalImportCertificate
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (splitMinChecked_checklist_iff_month1_auditor_entry h).trans
    nonempty_iff_auditor_assembly.symm

theorem exactFamily_checklist_iff_canonical_import
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
      Nonempty (Month1CanonicalImportCertificate
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactFamily_checklist_iff_month1_auditor_entry h).trans
    nonempty_iff_auditor_assembly.symm

theorem bounded_scale_eq_power
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (cert : Month1CanonicalImportCertificate
      rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    cert.toAuditorAssembly.index.lower_source.conditions.scale_data.scale n =
      rootSide.literature_lower_bound.scale_data.time_constructible_bound n ^
        rootSide.literature_lower_bound.scale_data.exponent :=
  Month1ProbeCertificate.bounded_scale_eq_power cert.probe n

theorem lower_source_scale_eq_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (cert : Month1CanonicalImportCertificate
      rootSide MainRationality SondowAccepted bounds bound) :
    cert.toAuditorAssembly.index.lower_source.conditions.scale_data.scale =
      rootSide.literature_lower_bound.scale_data.scale :=
  Month1ProbeCertificate.lower_source_scale_eq_root cert.probe

theorem time_constructible_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (cert : Month1CanonicalImportCertificate
      rootSide MainRationality SondowAccepted bounds bound) :
    cert.toAuditorAssembly.index.lower_source.conditions.scale_data.time_constructible_statement ↔
      cert.toAuditorAssembly.literature_witness.time_constructible_statement :=
  Month1ProbeCertificate.time_constructible_iff_literature cert.probe

theorem eventually_reads_input_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (cert : Month1CanonicalImportCertificate
      rootSide MainRationality SondowAccepted bounds bound) :
    cert.toAuditorAssembly.index.lower_source.conditions.scale_data.eventually_reads_input_statement ↔
      cert.toAuditorAssembly.literature_witness.eventually_reads_input_statement :=
  Month1ProbeCertificate.eventually_reads_input_iff_literature cert.probe

theorem eventually_defined_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (cert : Month1CanonicalImportCertificate
      rootSide MainRationality SondowAccepted bounds bound) :
    cert.toAuditorAssembly.index.lower_source.conditions.scale_data.eventually_defined_statement ↔
      cert.toAuditorAssembly.literature_witness.eventually_defined_statement :=
  Month1ProbeCertificate.eventually_defined_iff_literature cert.probe

theorem dominates_input_length_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (cert : Month1CanonicalImportCertificate
      rootSide MainRationality SondowAccepted bounds bound) :
    cert.toAuditorAssembly.index.lower_source.conditions.scale_data.dominates_input_length_statement ↔
      cert.toAuditorAssembly.literature_witness.dominates_input_length_statement :=
  Month1ProbeCertificate.dominates_input_length_iff_literature cert.probe

theorem root_normalForm_translation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (cert : Month1CanonicalImportCertificate
      rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    RootToBoundedFormulaCode
      ((rootSide.literature_lower_bound.toNormalForm
        rootSide.strengthened_to_partial).code n)
      (BoundedArithmeticLab.rescaledExternalPudlakCode
        cert.toAuditorAssembly.index.lower_source.conditions.scale_data.scale n) :=
  Month1ProbeCertificate.root_normalForm_translation cert.probe n

theorem encoding_probe_target_eq_box_formula
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {gap_cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    {checklist : SondowProjectPudlakConcreteBridgeChecklist
      rootSide gap_cert}
    (probe : Month1CanonicalEncodingProbe rootSide gap_cert checklist)
    (n : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target n =
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box n).formula :=
  probe.target_eq_box_formula n

theorem encoding_probe_box_code_roundtrip_to_target
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {gap_cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    {checklist : SondowProjectPudlakConcreteBridgeChecklist
      rootSide gap_cert}
    (probe : Month1CanonicalEncodingProbe rootSide gap_cert checklist)
    (n : Nat) :
    BoundedArithmeticLab.BAFormula.decode
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box n).code =
        some
          (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target n) :=
  probe.box_code_roundtrip_to_target n

theorem encoding_probe_carries_iff_pa_finite_consistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {gap_cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    {checklist : SondowProjectPudlakConcreteBridgeChecklist
      rootSide gap_cert}
    (probe : Month1CanonicalEncodingProbe rootSide gap_cert checklist)
    (n : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.CnBoxCarriesPAFiniteConsistency
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box n) ↔
        BoundedArithmeticLab.BoundedProofPredicate.PAFiniteConsistencyStatement n :=
  probe.carries_iff_pa_finite_consistency n

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
    (cert : Month1CanonicalImportCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      Σ' checklist :
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert,
        Month1CanonicalEncodingProbe
          h.toPudlakSideInputs gap_cert checklist) :=
  Month1ProbeCertificate.exactConvention_to_encoding_probe h cert.probe

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
    (cert : Month1CanonicalImportCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      Σ' checklist :
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert,
        Month1CanonicalEncodingProbe
          h.toPudlakSideInputs gap_cert checklist) :=
  Month1ProbeCertificate.splitMinChecked_to_encoding_probe h cert.probe

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
    (cert : Month1CanonicalImportCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      Σ' checklist :
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert,
        Month1CanonicalEncodingProbe
          h.toPudlakSideInputs gap_cert checklist) :=
  Month1ProbeCertificate.exactFamily_to_encoding_probe h cert.probe

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
    (cert : Month1CanonicalImportCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  Month1ProbeCertificate.exactConvention_to_same_object_closure h cert.probe

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
    (cert : Month1CanonicalImportCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  Month1ProbeCertificate.exactConvention_to_public_gap h cert.probe

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
    (cert : Month1CanonicalImportCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  Month1ProbeCertificate.exactConvention_not_main_rationality h cert.probe

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
    (cert : Month1CanonicalImportCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  Month1ProbeCertificate.splitMinChecked_to_same_object_closure h cert.probe

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
    (cert : Month1CanonicalImportCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  Month1ProbeCertificate.splitMinChecked_to_public_gap h cert.probe

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
    (cert : Month1CanonicalImportCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  Month1ProbeCertificate.splitMinChecked_not_main_rationality h cert.probe

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
    (cert : Month1CanonicalImportCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  Month1ProbeCertificate.exactFamily_to_same_object_closure h cert.probe

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
    (cert : Month1CanonicalImportCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  Month1ProbeCertificate.exactFamily_to_public_gap h cert.probe

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
    (cert : Month1CanonicalImportCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  Month1ProbeCertificate.exactFamily_not_main_rationality h cert.probe

end Month1CanonicalImportCertificate

/-!
Intentional import-surface probes.
-/

#check Month1CanonicalWitnessPackage
#check Month1CanonicalAuditorAssembly
#check Month1CanonicalProbeCertificate
#check Month1CanonicalEncodingProbe
#check Month1CanonicalImportCertificate
#check Month1CanonicalImportCertificate.nonempty_iff_probe_certificate
#check Month1CanonicalImportCertificate.nonempty_iff_auditor_assembly
#check Month1CanonicalImportCertificate.nonempty_iff_public_bundle_origin
#check Month1CanonicalImportCertificate.exactConvention_checklist_iff_canonical_import
#check Month1CanonicalImportCertificate.splitMinChecked_checklist_iff_canonical_import
#check Month1CanonicalImportCertificate.exactFamily_checklist_iff_canonical_import
#check Month1CanonicalImportCertificate.bounded_scale_eq_power
#check Month1CanonicalImportCertificate.lower_source_scale_eq_root
#check Month1CanonicalImportCertificate.time_constructible_iff_literature
#check Month1CanonicalImportCertificate.root_normalForm_translation
#check Month1CanonicalImportCertificate.encoding_probe_target_eq_box_formula
#check Month1CanonicalImportCertificate.encoding_probe_box_code_roundtrip_to_target
#check Month1CanonicalImportCertificate.encoding_probe_carries_iff_pa_finite_consistency
#check Month1CanonicalImportCertificate.exactConvention_to_encoding_probe
#check Month1CanonicalImportCertificate.splitMinChecked_to_encoding_probe
#check Month1CanonicalImportCertificate.exactFamily_to_encoding_probe
#check Month1CanonicalImportCertificate.exactConvention_to_same_object_closure
#check Month1CanonicalImportCertificate.exactConvention_to_public_gap
#check Month1CanonicalImportCertificate.exactConvention_not_main_rationality
#check Month1CanonicalImportCertificate.splitMinChecked_to_same_object_closure
#check Month1CanonicalImportCertificate.splitMinChecked_to_public_gap
#check Month1CanonicalImportCertificate.splitMinChecked_not_main_rationality
#check Month1CanonicalImportCertificate.exactFamily_to_same_object_closure
#check Month1CanonicalImportCertificate.exactFamily_to_public_gap
#check Month1CanonicalImportCertificate.exactFamily_not_main_rationality

end SondowProjectPudlakMonth1CanonicalImportSurface
end SondowMainCheckedCodeBridge
