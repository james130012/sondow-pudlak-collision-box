/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakTimeConstructibleWitnessBridgeReleaseSurface

/-!
# Literature witness compiler release surface

This module exposes the next audit layer above the time-constructible witness
bridge.  The bounded side uses `TimeConstructibleScale`; the project root side
uses `LiteraturePudlakTheorem5ScaleData`; the witness bridge introduced a
root-facing witness record.  Here we add the publication-facing compiler input:
a literature Theorem 5 witness package whose four abstract side-condition
statements compile into the root witness record.

The compiler does not assert new mathematics by fiat.  Its project assembly is
proved equivalent to the already checked constructive power-scale assembly, so
all public checklist and collision consequences still flow through the same
same-object route.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakLiteratureWitnessCompilerReleaseSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectPudlakPowerScaleBridgeReleaseSurface
open SondowProjectPudlakTimeConstructibleWitnessBridgeReleaseSurface

/-- Publication-facing witness package for the side conditions on the
time-constructible rescaling in the Pudlak Theorem 5 input. -/
structure LiteraturePudlakTheorem5TimeConstructibleWitnessPackage
    (_root_scale : _root_.LiteraturePudlakTheorem5ScaleData) where
  time_constructible_statement : Prop
  time_constructible : time_constructible_statement
  eventually_reads_input_statement : Prop
  eventually_reads_input : eventually_reads_input_statement
  eventually_defined_statement : Prop
  eventually_defined : eventually_defined_statement
  dominates_input_length_statement : Prop
  dominates_input_length : dominates_input_length_statement

namespace LiteraturePudlakTheorem5TimeConstructibleWitnessPackage

def toRootWitnessData
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness :
      LiteraturePudlakTheorem5TimeConstructibleWitnessPackage root_scale) :
    RootTimeConstructibleWitnessData root_scale where
  time_constructible_statement := witness.time_constructible_statement
  time_constructible := witness.time_constructible
  eventually_reads_input_statement := witness.eventually_reads_input_statement
  eventually_reads_input := witness.eventually_reads_input
  eventually_defined_statement := witness.eventually_defined_statement
  eventually_defined := witness.eventually_defined
  dominates_input_length_statement :=
    witness.dominates_input_length_statement
  dominates_input_length := witness.dominates_input_length

def ofRootWitnessData
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness : RootTimeConstructibleWitnessData root_scale) :
    LiteraturePudlakTheorem5TimeConstructibleWitnessPackage root_scale where
  time_constructible_statement := witness.time_constructible_statement
  time_constructible := witness.time_constructible
  eventually_reads_input_statement := witness.eventually_reads_input_statement
  eventually_reads_input := witness.eventually_reads_input
  eventually_defined_statement := witness.eventually_defined_statement
  eventually_defined := witness.eventually_defined
  dominates_input_length_statement :=
    witness.dominates_input_length_statement
  dominates_input_length := witness.dominates_input_length

def toBoundedScale
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness :
      LiteraturePudlakTheorem5TimeConstructibleWitnessPackage root_scale) :
    BoundedArithmeticLab.TimeConstructibleScale :=
  witness.toRootWitnessData.toBoundedScale root_scale.scale

@[simp] theorem toRootWitnessData_time_constructible_statement
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness :
      LiteraturePudlakTheorem5TimeConstructibleWitnessPackage root_scale) :
    witness.toRootWitnessData.time_constructible_statement =
      witness.time_constructible_statement := by
  rfl

@[simp] theorem toRootWitnessData_eventually_reads_input_statement
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness :
      LiteraturePudlakTheorem5TimeConstructibleWitnessPackage root_scale) :
    witness.toRootWitnessData.eventually_reads_input_statement =
      witness.eventually_reads_input_statement := by
  rfl

@[simp] theorem toRootWitnessData_eventually_defined_statement
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness :
      LiteraturePudlakTheorem5TimeConstructibleWitnessPackage root_scale) :
    witness.toRootWitnessData.eventually_defined_statement =
      witness.eventually_defined_statement := by
  rfl

@[simp] theorem toRootWitnessData_dominates_input_length_statement
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness :
      LiteraturePudlakTheorem5TimeConstructibleWitnessPackage root_scale) :
    witness.toRootWitnessData.dominates_input_length_statement =
      witness.dominates_input_length_statement := by
  rfl

@[simp] theorem toBoundedScale_scale
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness :
      LiteraturePudlakTheorem5TimeConstructibleWitnessPackage root_scale) :
    witness.toBoundedScale.scale = root_scale.scale := by
  rfl

theorem toBoundedScale_pointwise_power
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness :
      LiteraturePudlakTheorem5TimeConstructibleWitnessPackage root_scale)
    (n : Nat) :
    witness.toBoundedScale.scale n =
      root_scale.time_constructible_bound n ^ root_scale.exponent := by
  change root_scale.scale n =
    root_scale.time_constructible_bound n ^ root_scale.exponent
  exact root_scale.scale_eq n

def toPowerScaleRegistration
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness :
      LiteraturePudlakTheorem5TimeConstructibleWitnessPackage root_scale) :
    RootBoundedPowerScaleRegistration root_scale witness.toBoundedScale where
  bounded_scale_eq_power := witness.toBoundedScale_pointwise_power

def toWitnessBridge
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness :
      LiteraturePudlakTheorem5TimeConstructibleWitnessPackage root_scale) :
    RootBoundedTimeConstructibleWitnessBridge
      witness.toRootWitnessData witness.toBoundedScale :=
  RootBoundedTimeConstructibleWitnessBridge.ofRootBoundedScale
    witness.toRootWitnessData root_scale.scale

def toConstructiveScaleRegistration
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness :
      LiteraturePudlakTheorem5TimeConstructibleWitnessPackage root_scale) :
    RootBoundedConstructiveScaleRegistration
      witness.toRootWitnessData witness.toBoundedScale where
  power_registration := witness.toPowerScaleRegistration
  witness_bridge := witness.toWitnessBridge

theorem compiled_time_constructible_iff
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness :
      LiteraturePudlakTheorem5TimeConstructibleWitnessPackage root_scale) :
    witness.toBoundedScale.time_constructible_statement ↔
      witness.time_constructible_statement :=
  witness.toWitnessBridge.time_constructible_iff

theorem compiled_eventually_reads_input_iff
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness :
      LiteraturePudlakTheorem5TimeConstructibleWitnessPackage root_scale) :
    witness.toBoundedScale.eventually_reads_input_statement ↔
      witness.eventually_reads_input_statement :=
  witness.toWitnessBridge.eventually_reads_input_iff

theorem compiled_eventually_defined_iff
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness :
      LiteraturePudlakTheorem5TimeConstructibleWitnessPackage root_scale) :
    witness.toBoundedScale.eventually_defined_statement ↔
      witness.eventually_defined_statement :=
  witness.toWitnessBridge.eventually_defined_iff

theorem compiled_dominates_input_length_iff
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness :
      LiteraturePudlakTheorem5TimeConstructibleWitnessPackage root_scale) :
    witness.toBoundedScale.dominates_input_length_statement ↔
      witness.dominates_input_length_statement :=
  witness.toWitnessBridge.dominates_input_length_iff

end LiteraturePudlakTheorem5TimeConstructibleWitnessPackage

structure ProjectConcreteFieldLiteratureWitnessAssembly
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) where
  index : ProjectConcreteCertificateFieldIndex
    MainRationality SondowAccepted bounds bound
  literature_witness :
    LiteraturePudlakTheorem5TimeConstructibleWitnessPackage
      rootSide.literature_lower_bound.scale_data
  constructive_registration :
    RootBoundedConstructiveScaleRegistration
      literature_witness.toRootWitnessData
      index.lower_source.conditions.scale_data

namespace ProjectConcreteFieldLiteratureWitnessAssembly

def toConstructivePowerScaleAssembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound where
  index := assembly.index
  root_witness := assembly.literature_witness.toRootWitnessData
  constructive_registration := assembly.constructive_registration

def ofConstructivePowerScaleAssembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    ProjectConcreteFieldLiteratureWitnessAssembly
      rootSide MainRationality SondowAccepted bounds bound := by
  let literature_witness :=
    LiteraturePudlakTheorem5TimeConstructibleWitnessPackage.ofRootWitnessData
      assembly.root_witness
  refine
    { index := assembly.index
      literature_witness := literature_witness
      constructive_registration := ?_ }
  simpa [literature_witness,
    LiteraturePudlakTheorem5TimeConstructibleWitnessPackage.ofRootWitnessData,
    LiteraturePudlakTheorem5TimeConstructibleWitnessPackage.toRootWitnessData]
    using assembly.constructive_registration

def toPowerScaleAssembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    ProjectConcreteFieldPowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound :=
  assembly.toConstructivePowerScaleAssembly.toPowerScaleAssembly

def toPublicBundleLowerSourceOrigin
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    SondowProjectPudlakExactInputBridgeReleaseSurface.PublicBundleLowerSourceOrigin
      rootSide assembly.index.toCertificateBundle :=
  assembly.toConstructivePowerScaleAssembly.toPublicBundleLowerSourceOrigin

theorem bounded_scale_eq_power
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    assembly.index.lower_source.conditions.scale_data.scale n =
      rootSide.literature_lower_bound.scale_data.time_constructible_bound n ^
        rootSide.literature_lower_bound.scale_data.exponent :=
  assembly.constructive_registration.bounded_scale_eq_power n

theorem lower_source_scale_eq_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.scale =
      rootSide.literature_lower_bound.scale_data.scale :=
  assembly.constructive_registration.bounded_scale_eq_root

theorem time_constructible_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.time_constructible_statement ↔
      assembly.literature_witness.time_constructible_statement :=
  assembly.toConstructivePowerScaleAssembly.time_constructible_iff_root

theorem eventually_reads_input_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.eventually_reads_input_statement ↔
      assembly.literature_witness.eventually_reads_input_statement :=
  assembly.toConstructivePowerScaleAssembly.eventually_reads_input_iff_root

theorem eventually_defined_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.eventually_defined_statement ↔
      assembly.literature_witness.eventually_defined_statement :=
  assembly.toConstructivePowerScaleAssembly.eventually_defined_iff_root

theorem dominates_input_length_iff_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.dominates_input_length_statement ↔
      assembly.literature_witness.dominates_input_length_statement :=
  assembly.toConstructivePowerScaleAssembly.dominates_input_length_iff_root

theorem bounded_time_constructible_of_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.time_constructible_statement :=
  assembly.toConstructivePowerScaleAssembly.bounded_time_constructible_of_root

theorem bounded_eventually_reads_input_of_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.eventually_reads_input_statement :=
  assembly.toConstructivePowerScaleAssembly.bounded_eventually_reads_input_of_root

theorem bounded_eventually_defined_of_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.eventually_defined_statement :=
  assembly.toConstructivePowerScaleAssembly.bounded_eventually_defined_of_root

theorem bounded_dominates_input_length_of_literature
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.dominates_input_length_statement :=
  assembly.toConstructivePowerScaleAssembly.bounded_dominates_input_length_of_root

theorem root_normalForm_translation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    RootToBoundedFormulaCode
      ((rootSide.literature_lower_bound.toNormalForm
        rootSide.strengthened_to_partial).code n)
      (BoundedArithmeticLab.rescaledExternalPudlakCode
        assembly.index.lower_source.conditions.scale_data.scale n) :=
  assembly.toConstructivePowerScaleAssembly.root_normalForm_translation n

end ProjectConcreteFieldLiteratureWitnessAssembly

theorem literatureWitnessAssembly_nonempty_iff_constructivePowerScaleAssembly_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (ProjectConcreteFieldLiteratureWitnessAssembly
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectConcreteFieldConstructivePowerScaleAssembly
        rootSide MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨assembly⟩
    exact ⟨assembly.toConstructivePowerScaleAssembly⟩
  · intro h
    rcases h with ⟨assembly⟩
    exact ⟨ProjectConcreteFieldLiteratureWitnessAssembly.ofConstructivePowerScaleAssembly
      assembly⟩

theorem literatureWitnessAssembly_nonempty_iff_powerScaleAssembly_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (ProjectConcreteFieldLiteratureWitnessAssembly
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectConcreteFieldPowerScaleAssembly
        rootSide MainRationality SondowAccepted bounds bound) :=
  literatureWitnessAssembly_nonempty_iff_constructivePowerScaleAssembly_nonempty.trans
    constructivePowerScaleAssembly_nonempty_iff_powerScaleAssembly_nonempty

theorem literatureWitnessAssembly_nonempty_iff_publicBundleLowerSourceOrigin_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (ProjectConcreteFieldLiteratureWitnessAssembly
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (Σ' bundle : ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakExactInputBridgeReleaseSurface.PublicBundleLowerSourceOrigin
          rootSide bundle) :=
  literatureWitnessAssembly_nonempty_iff_constructivePowerScaleAssembly_nonempty.trans
    constructivePowerScaleAssembly_nonempty_iff_publicBundleLowerSourceOrigin_nonempty

theorem exactConvention_checklist_iff_literature_witness_assembly
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
      Nonempty (ProjectConcreteFieldLiteratureWitnessAssembly
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactConvention_checklist_iff_constructive_power_scale_assembly h).trans
    literatureWitnessAssembly_nonempty_iff_constructivePowerScaleAssembly_nonempty.symm

theorem splitMinChecked_checklist_iff_literature_witness_assembly
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
      Nonempty (ProjectConcreteFieldLiteratureWitnessAssembly
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (splitMinChecked_checklist_iff_constructive_power_scale_assembly h).trans
    literatureWitnessAssembly_nonempty_iff_constructivePowerScaleAssembly_nonempty.symm

theorem exactFamily_checklist_iff_literature_witness_assembly
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
      Nonempty (ProjectConcreteFieldLiteratureWitnessAssembly
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactFamily_checklist_iff_constructive_power_scale_assembly h).trans
    literatureWitnessAssembly_nonempty_iff_constructivePowerScaleAssembly_nonempty.symm

theorem exactConvention_to_concrete_checklist_of_literature_witness_assembly
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
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) :=
  exactConvention_to_concrete_checklist_of_constructive_power_scale_assembly
    h assembly.toConstructivePowerScaleAssembly

theorem exactConvention_to_same_object_closure_of_literature_witness_assembly
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
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  exactConvention_to_same_object_closure_of_constructive_power_scale_assembly
    h assembly.toConstructivePowerScaleAssembly

theorem exactConvention_to_public_gap_instantiation_of_literature_witness_assembly
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
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  exactConvention_to_public_gap_instantiation_of_constructive_power_scale_assembly
    h assembly.toConstructivePowerScaleAssembly

theorem exactConvention_not_main_rationality_of_literature_witness_assembly
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
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  exactConvention_not_main_rationality_of_constructive_power_scale_assembly
    h assembly.toConstructivePowerScaleAssembly

theorem splitMinChecked_to_same_object_closure_of_literature_witness_assembly
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
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  splitMinChecked_to_same_object_closure_of_constructive_power_scale_assembly
    h assembly.toConstructivePowerScaleAssembly

theorem splitMinChecked_to_public_gap_instantiation_of_literature_witness_assembly
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
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  splitMinChecked_to_public_gap_instantiation_of_constructive_power_scale_assembly
    h assembly.toConstructivePowerScaleAssembly

theorem splitMinChecked_not_main_rationality_of_literature_witness_assembly
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
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  splitMinChecked_not_main_rationality_of_constructive_power_scale_assembly
    h assembly.toConstructivePowerScaleAssembly

theorem exactFamily_to_same_object_closure_of_literature_witness_assembly
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
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  exactFamily_to_same_object_closure_of_constructive_power_scale_assembly
    h assembly.toConstructivePowerScaleAssembly

theorem exactFamily_to_public_gap_instantiation_of_literature_witness_assembly
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
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  exactFamily_to_public_gap_instantiation_of_constructive_power_scale_assembly
    h assembly.toConstructivePowerScaleAssembly

theorem exactFamily_not_main_rationality_of_literature_witness_assembly
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
    (assembly : ProjectConcreteFieldLiteratureWitnessAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  exactFamily_not_main_rationality_of_constructive_power_scale_assembly
    h assembly.toConstructivePowerScaleAssembly

end SondowProjectPudlakLiteratureWitnessCompilerReleaseSurface
end SondowMainCheckedCodeBridge
