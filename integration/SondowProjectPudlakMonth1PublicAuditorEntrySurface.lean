/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakLiteratureWitnessCompilerReleaseSurface

/-!
# Month 1 public auditor entry surface

This module is a compact audit entry point for the Month 1 same-object/public
bridge closure work.  It re-exports the current strongest Pudlak-side public
route in one place:

* literature Theorem 5 witness compilation;
* power-scale registration;
* time-constructible witness registration;
* concrete CnBox/Pudlak checklist equivalence;
* same-object closure, public-gap instantiation, and contradiction endpoints.

It does not add a new route.  Every public theorem below delegates to the
literature witness compiler release surface, preserving the previously proved
`↔` boundaries rather than replacing them with one-way implications.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakMonth1PublicAuditorEntrySurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectPudlakLiteratureWitnessCompilerReleaseSurface

abbrev Month1PublicAuditorWitnessPackage
    (root_scale : _root_.LiteraturePudlakTheorem5ScaleData) :=
  LiteraturePudlakTheorem5TimeConstructibleWitnessPackage root_scale

abbrev Month1PublicAuditorAssembly
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) :=
  ProjectConcreteFieldLiteratureWitnessAssembly
    rootSide MainRationality SondowAccepted bounds bound

def month1_witness_to_root_data
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness : Month1PublicAuditorWitnessPackage root_scale) :
    SondowProjectPudlakTimeConstructibleWitnessBridgeReleaseSurface.RootTimeConstructibleWitnessData
      root_scale :=
  witness.toRootWitnessData

def month1_witness_to_bounded_scale
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness : Month1PublicAuditorWitnessPackage root_scale) :
    BoundedArithmeticLab.TimeConstructibleScale :=
  witness.toBoundedScale

theorem month1_witness_bounded_scale_eq_power
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness : Month1PublicAuditorWitnessPackage root_scale)
    (n : Nat) :
    witness.toBoundedScale.scale n =
      root_scale.time_constructible_bound n ^ root_scale.exponent :=
  LiteraturePudlakTheorem5TimeConstructibleWitnessPackage.toBoundedScale_pointwise_power
    witness n

theorem month1_witness_time_constructible_iff
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness : Month1PublicAuditorWitnessPackage root_scale) :
    witness.toBoundedScale.time_constructible_statement ↔
      witness.time_constructible_statement :=
  LiteraturePudlakTheorem5TimeConstructibleWitnessPackage.compiled_time_constructible_iff
    witness

theorem month1_witness_eventually_reads_input_iff
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness : Month1PublicAuditorWitnessPackage root_scale) :
    witness.toBoundedScale.eventually_reads_input_statement ↔
      witness.eventually_reads_input_statement :=
  LiteraturePudlakTheorem5TimeConstructibleWitnessPackage.compiled_eventually_reads_input_iff
    witness

theorem month1_witness_eventually_defined_iff
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness : Month1PublicAuditorWitnessPackage root_scale) :
    witness.toBoundedScale.eventually_defined_statement ↔
      witness.eventually_defined_statement :=
  LiteraturePudlakTheorem5TimeConstructibleWitnessPackage.compiled_eventually_defined_iff
    witness

theorem month1_witness_dominates_input_length_iff
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness : Month1PublicAuditorWitnessPackage root_scale) :
    witness.toBoundedScale.dominates_input_length_statement ↔
      witness.dominates_input_length_statement :=
  LiteraturePudlakTheorem5TimeConstructibleWitnessPackage.compiled_dominates_input_length_iff
    witness

theorem month1_auditor_entry_iff_power_scale_assembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (Month1PublicAuditorAssembly
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (SondowProjectPudlakPowerScaleBridgeReleaseSurface.ProjectConcreteFieldPowerScaleAssembly
        rootSide MainRationality SondowAccepted bounds bound) :=
  literatureWitnessAssembly_nonempty_iff_powerScaleAssembly_nonempty

theorem month1_auditor_entry_iff_public_bundle_origin
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (Month1PublicAuditorAssembly
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (Σ' bundle : ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakExactInputBridgeReleaseSurface.PublicBundleLowerSourceOrigin
          rootSide bundle) :=
  literatureWitnessAssembly_nonempty_iff_publicBundleLowerSourceOrigin_nonempty

theorem month1_auditor_entry_bounded_scale_eq_power
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : Month1PublicAuditorAssembly
      rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    assembly.index.lower_source.conditions.scale_data.scale n =
      rootSide.literature_lower_bound.scale_data.time_constructible_bound n ^
        rootSide.literature_lower_bound.scale_data.exponent :=
  assembly.bounded_scale_eq_power n

theorem month1_auditor_entry_lower_source_scale_eq_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : Month1PublicAuditorAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.scale =
      rootSide.literature_lower_bound.scale_data.scale :=
  assembly.lower_source_scale_eq_root

theorem month1_auditor_entry_time_constructible_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : Month1PublicAuditorAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.time_constructible_statement ↔
      assembly.literature_witness.time_constructible_statement :=
  assembly.time_constructible_iff_literature

theorem month1_auditor_entry_eventually_reads_input_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : Month1PublicAuditorAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.eventually_reads_input_statement ↔
      assembly.literature_witness.eventually_reads_input_statement :=
  assembly.eventually_reads_input_iff_literature

theorem month1_auditor_entry_eventually_defined_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : Month1PublicAuditorAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.eventually_defined_statement ↔
      assembly.literature_witness.eventually_defined_statement :=
  assembly.eventually_defined_iff_literature

theorem month1_auditor_entry_dominates_input_length_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : Month1PublicAuditorAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.dominates_input_length_statement ↔
      assembly.literature_witness.dominates_input_length_statement :=
  assembly.dominates_input_length_iff_literature

theorem exactConvention_checklist_iff_month1_auditor_entry
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
    Nonempty (Σ' cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) ↔
      Nonempty (Month1PublicAuditorAssembly
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  exactConvention_checklist_iff_literature_witness_assembly h

theorem splitMinChecked_checklist_iff_month1_auditor_entry
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
    Nonempty (Σ' cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) ↔
      Nonempty (Month1PublicAuditorAssembly
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  splitMinChecked_checklist_iff_literature_witness_assembly h

theorem exactFamily_checklist_iff_month1_auditor_entry
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
    Nonempty (Σ' cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) ↔
      Nonempty (Month1PublicAuditorAssembly
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  exactFamily_checklist_iff_literature_witness_assembly h

theorem exactConvention_month1_auditor_entry_to_concrete_checklist
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
    (assembly : Month1PublicAuditorAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) :=
  exactConvention_to_concrete_checklist_of_literature_witness_assembly
    h assembly

theorem splitMinChecked_month1_auditor_entry_to_concrete_checklist
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
    (assembly : Month1PublicAuditorAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) :=
  (splitMinChecked_checklist_iff_month1_auditor_entry h).2 ⟨assembly⟩

theorem exactFamily_month1_auditor_entry_to_concrete_checklist
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
    (assembly : Month1PublicAuditorAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) :=
  (exactFamily_checklist_iff_month1_auditor_entry h).2 ⟨assembly⟩

theorem exactConvention_month1_auditor_entry_to_same_object_closure
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
    (assembly : Month1PublicAuditorAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  exactConvention_to_same_object_closure_of_literature_witness_assembly
    h assembly

theorem exactConvention_month1_auditor_entry_to_public_gap
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
    (assembly : Month1PublicAuditorAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  exactConvention_to_public_gap_instantiation_of_literature_witness_assembly
    h assembly

theorem exactConvention_month1_auditor_entry_not_main_rationality
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
    (assembly : Month1PublicAuditorAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  exactConvention_not_main_rationality_of_literature_witness_assembly
    h assembly

theorem splitMinChecked_month1_auditor_entry_to_same_object_closure
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
    (assembly : Month1PublicAuditorAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  splitMinChecked_to_same_object_closure_of_literature_witness_assembly
    h assembly

theorem splitMinChecked_month1_auditor_entry_to_public_gap
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
    (assembly : Month1PublicAuditorAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  splitMinChecked_to_public_gap_instantiation_of_literature_witness_assembly
    h assembly

theorem splitMinChecked_month1_auditor_entry_not_main_rationality
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
    (assembly : Month1PublicAuditorAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  splitMinChecked_not_main_rationality_of_literature_witness_assembly
    h assembly

theorem exactFamily_month1_auditor_entry_to_same_object_closure
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
    (assembly : Month1PublicAuditorAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  exactFamily_to_same_object_closure_of_literature_witness_assembly
    h assembly

theorem exactFamily_month1_auditor_entry_to_public_gap
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
    (assembly : Month1PublicAuditorAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  exactFamily_to_public_gap_instantiation_of_literature_witness_assembly
    h assembly

theorem exactFamily_month1_auditor_entry_not_main_rationality
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
    (assembly : Month1PublicAuditorAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  exactFamily_not_main_rationality_of_literature_witness_assembly
    h assembly

end SondowProjectPudlakMonth1PublicAuditorEntrySurface
end SondowMainCheckedCodeBridge
