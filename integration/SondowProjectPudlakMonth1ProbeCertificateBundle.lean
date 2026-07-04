/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakMonth1PublicAuditorEntrySurface

/-!
# Month 1 probe certificate bundle

This file is a proof-probe bundle for the Month 1 same-object/public-bridge
closure route.  The public auditor entry surface gives readable endpoints; this
module packages them as a small certificate object and a concrete checklist
encoding probe so a reviewer can type-check one file and see the route from
literature witness compilation to the CnBox/Pudlak same-object facts.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakMonth1ProbeCertificateBundle

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectPudlakMonth1PublicAuditorEntrySurface

structure Month1ConcreteChecklistEncodingProbe
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (checklist : SondowProjectPudlakConcreteBridgeChecklist
      rootSide cert) : Prop where
  target_eq_box_formula :
    ∀ n : Nat,
      BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target n =
        (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box n).formula
  box_code_roundtrip_to_target :
    ∀ n : Nat,
      BoundedArithmeticLab.BAFormula.decode
        (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box n).code =
          some
            (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target n)
  carries_iff_pa_finite_consistency :
    ∀ n : Nat,
      BoundedArithmeticLab.BoundedProofPredicate.CnBoxCarriesPAFiniteConsistency
        (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box n) ↔
          BoundedArithmeticLab.BoundedProofPredicate.PAFiniteConsistencyStatement n

namespace Month1ConcreteChecklistEncodingProbe

def ofChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    (checklist : SondowProjectPudlakConcreteBridgeChecklist
      rootSide cert) :
    Month1ConcreteChecklistEncodingProbe rootSide cert checklist where
  target_eq_box_formula := by
    intro n
    exact
      SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_target_eq_box_formula
        checklist n
  box_code_roundtrip_to_target := by
    intro n
    exact
      SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_box_code_roundtrip_to_target
        checklist n
  carries_iff_pa_finite_consistency := by
    intro n
    exact
      SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_carries_iff_pa_finite_consistency
        checklist n

end Month1ConcreteChecklistEncodingProbe

structure Month1ProbeCertificate
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) where
  assembly :
    Month1PublicAuditorAssembly
      rootSide MainRationality SondowAccepted bounds bound

namespace Month1ProbeCertificate

theorem bounded_scale_eq_power
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (cert : Month1ProbeCertificate
      rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    cert.assembly.index.lower_source.conditions.scale_data.scale n =
      rootSide.literature_lower_bound.scale_data.time_constructible_bound n ^
        rootSide.literature_lower_bound.scale_data.exponent :=
  month1_auditor_entry_bounded_scale_eq_power cert.assembly n

theorem lower_source_scale_eq_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (cert : Month1ProbeCertificate
      rootSide MainRationality SondowAccepted bounds bound) :
    cert.assembly.index.lower_source.conditions.scale_data.scale =
      rootSide.literature_lower_bound.scale_data.scale :=
  month1_auditor_entry_lower_source_scale_eq_root cert.assembly

theorem time_constructible_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (cert : Month1ProbeCertificate
      rootSide MainRationality SondowAccepted bounds bound) :
    cert.assembly.index.lower_source.conditions.scale_data.time_constructible_statement ↔
      cert.assembly.literature_witness.time_constructible_statement :=
  month1_auditor_entry_time_constructible_iff_literature cert.assembly

theorem eventually_reads_input_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (cert : Month1ProbeCertificate
      rootSide MainRationality SondowAccepted bounds bound) :
    cert.assembly.index.lower_source.conditions.scale_data.eventually_reads_input_statement ↔
      cert.assembly.literature_witness.eventually_reads_input_statement :=
  month1_auditor_entry_eventually_reads_input_iff_literature cert.assembly

theorem eventually_defined_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (cert : Month1ProbeCertificate
      rootSide MainRationality SondowAccepted bounds bound) :
    cert.assembly.index.lower_source.conditions.scale_data.eventually_defined_statement ↔
      cert.assembly.literature_witness.eventually_defined_statement :=
  month1_auditor_entry_eventually_defined_iff_literature cert.assembly

theorem dominates_input_length_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (cert : Month1ProbeCertificate
      rootSide MainRationality SondowAccepted bounds bound) :
    cert.assembly.index.lower_source.conditions.scale_data.dominates_input_length_statement ↔
      cert.assembly.literature_witness.dominates_input_length_statement :=
  month1_auditor_entry_dominates_input_length_iff_literature cert.assembly

theorem root_normalForm_translation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (cert : Month1ProbeCertificate
      rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    RootToBoundedFormulaCode
      ((rootSide.literature_lower_bound.toNormalForm
        rootSide.strengthened_to_partial).code n)
      (BoundedArithmeticLab.rescaledExternalPudlakCode
        cert.assembly.index.lower_source.conditions.scale_data.scale n) :=
  cert.assembly.root_normalForm_translation n

theorem exactConvention_to_concrete_checklist
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
    (cert : Month1ProbeCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs gap_cert) :=
  exactConvention_month1_auditor_entry_to_concrete_checklist h cert.assembly

theorem splitMinChecked_to_concrete_checklist
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
    (cert : Month1ProbeCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs gap_cert) :=
  splitMinChecked_month1_auditor_entry_to_concrete_checklist h cert.assembly

theorem exactFamily_to_concrete_checklist
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
    (cert : Month1ProbeCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs gap_cert) :=
  exactFamily_month1_auditor_entry_to_concrete_checklist h cert.assembly

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
    (cert : Month1ProbeCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      Σ' checklist :
        SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs gap_cert,
        Month1ConcreteChecklistEncodingProbe
          h.toPudlakSideInputs gap_cert checklist) := by
  rcases exactConvention_to_concrete_checklist h cert with
    ⟨⟨gap_cert, checklist⟩⟩
  exact ⟨⟨gap_cert,
    ⟨checklist, Month1ConcreteChecklistEncodingProbe.ofChecklist checklist⟩⟩⟩

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
    (cert : Month1ProbeCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      Σ' checklist :
        SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs gap_cert,
        Month1ConcreteChecklistEncodingProbe
          h.toPudlakSideInputs gap_cert checklist) := by
  rcases splitMinChecked_to_concrete_checklist h cert with
    ⟨⟨gap_cert, checklist⟩⟩
  exact ⟨⟨gap_cert,
    ⟨checklist, Month1ConcreteChecklistEncodingProbe.ofChecklist checklist⟩⟩⟩

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
    (cert : Month1ProbeCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      Σ' checklist :
        SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs gap_cert,
        Month1ConcreteChecklistEncodingProbe
          h.toPudlakSideInputs gap_cert checklist) := by
  rcases exactFamily_to_concrete_checklist h cert with
    ⟨⟨gap_cert, checklist⟩⟩
  exact ⟨⟨gap_cert,
    ⟨checklist, Month1ConcreteChecklistEncodingProbe.ofChecklist checklist⟩⟩⟩

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
    (cert : Month1ProbeCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  exactConvention_month1_auditor_entry_to_same_object_closure h cert.assembly

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
    (cert : Month1ProbeCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  exactConvention_month1_auditor_entry_to_public_gap h cert.assembly

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
    (cert : Month1ProbeCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  exactConvention_month1_auditor_entry_not_main_rationality h cert.assembly

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
    (cert : Month1ProbeCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  splitMinChecked_month1_auditor_entry_to_same_object_closure h cert.assembly

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
    (cert : Month1ProbeCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  splitMinChecked_month1_auditor_entry_to_public_gap h cert.assembly

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
    (cert : Month1ProbeCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  splitMinChecked_month1_auditor_entry_not_main_rationality h cert.assembly

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
    (cert : Month1ProbeCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  exactFamily_month1_auditor_entry_to_same_object_closure h cert.assembly

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
    (cert : Month1ProbeCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  exactFamily_month1_auditor_entry_to_public_gap h cert.assembly

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
    (cert : Month1ProbeCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  exactFamily_month1_auditor_entry_not_main_rationality h cert.assembly

end Month1ProbeCertificate

/-!
The following `#check`s are intentional: this file is meant to be run as a
proof probe with `lake env lean`.
-/

#check Month1ConcreteChecklistEncodingProbe
#check Month1ConcreteChecklistEncodingProbe.ofChecklist
#check Month1ProbeCertificate
#check Month1ProbeCertificate.bounded_scale_eq_power
#check Month1ProbeCertificate.lower_source_scale_eq_root
#check Month1ProbeCertificate.time_constructible_iff_literature
#check Month1ProbeCertificate.eventually_reads_input_iff_literature
#check Month1ProbeCertificate.eventually_defined_iff_literature
#check Month1ProbeCertificate.dominates_input_length_iff_literature
#check Month1ProbeCertificate.root_normalForm_translation
#check Month1ProbeCertificate.exactConvention_to_concrete_checklist
#check Month1ProbeCertificate.splitMinChecked_to_concrete_checklist
#check Month1ProbeCertificate.exactFamily_to_concrete_checklist
#check Month1ProbeCertificate.exactConvention_to_encoding_probe
#check Month1ProbeCertificate.splitMinChecked_to_encoding_probe
#check Month1ProbeCertificate.exactFamily_to_encoding_probe
#check Month1ProbeCertificate.exactConvention_to_same_object_closure
#check Month1ProbeCertificate.exactConvention_to_public_gap
#check Month1ProbeCertificate.exactConvention_not_main_rationality
#check Month1ProbeCertificate.splitMinChecked_to_same_object_closure
#check Month1ProbeCertificate.splitMinChecked_to_public_gap
#check Month1ProbeCertificate.splitMinChecked_not_main_rationality
#check Month1ProbeCertificate.exactFamily_to_same_object_closure
#check Month1ProbeCertificate.exactFamily_to_public_gap
#check Month1ProbeCertificate.exactFamily_not_main_rationality

end SondowProjectPudlakMonth1ProbeCertificateBundle
end SondowMainCheckedCodeBridge
