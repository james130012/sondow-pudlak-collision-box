/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakPowerScaleBridgeReleaseSurface

/-!
# Time-constructible witness bridge release surface

The power-scale layer identifies the bounded lower-source scale with the
literature Theorem 5 scale `time_constructible_bound n ^ exponent`.  This file
adds the next audit boundary: the four abstract witness statements carried by
`TimeConstructibleScale`.

The root `LiteraturePudlakTheorem5ScaleData` record does not yet store these
witness statements.  We therefore expose a root-facing witness package and prove
that the stronger constructive interface is equivalent to the already verified
power-scale assembly interface.  Downstream public collision consequences still
flow through the same power-scale assembly, while auditors can now inspect the
exact witness-statement registrations.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakTimeConstructibleWitnessBridgeReleaseSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectPudlakFieldOriginReleaseSurface
open SondowProjectPudlakPowerScaleBridgeReleaseSurface

/-- Root-facing package for the time-constructibility side conditions that are
kept abstract by the bounded lower-source interface. -/
structure RootTimeConstructibleWitnessData
    (_root_scale : _root_.LiteraturePudlakTheorem5ScaleData) where
  time_constructible_statement : Prop
  time_constructible : time_constructible_statement
  eventually_reads_input_statement : Prop
  eventually_reads_input : eventually_reads_input_statement
  eventually_defined_statement : Prop
  eventually_defined : eventually_defined_statement
  dominates_input_length_statement : Prop
  dominates_input_length : dominates_input_length_statement

namespace RootTimeConstructibleWitnessData

def toBoundedScale
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness : RootTimeConstructibleWitnessData root_scale)
    (scale : Nat → Nat) :
    BoundedArithmeticLab.TimeConstructibleScale where
  scale := scale
  time_constructible_statement := witness.time_constructible_statement
  time_constructible := witness.time_constructible
  eventually_reads_input_statement := witness.eventually_reads_input_statement
  eventually_reads_input := witness.eventually_reads_input
  eventually_defined_statement := witness.eventually_defined_statement
  eventually_defined := witness.eventually_defined
  dominates_input_length_statement := witness.dominates_input_length_statement
  dominates_input_length := witness.dominates_input_length

def ofBoundedScale
    (root_scale : _root_.LiteraturePudlakTheorem5ScaleData)
    (bounded_scale : BoundedArithmeticLab.TimeConstructibleScale) :
    RootTimeConstructibleWitnessData root_scale where
  time_constructible_statement :=
    bounded_scale.time_constructible_statement
  time_constructible := bounded_scale.time_constructible
  eventually_reads_input_statement :=
    bounded_scale.eventually_reads_input_statement
  eventually_reads_input := bounded_scale.eventually_reads_input
  eventually_defined_statement := bounded_scale.eventually_defined_statement
  eventually_defined := bounded_scale.eventually_defined
  dominates_input_length_statement :=
    bounded_scale.dominates_input_length_statement
  dominates_input_length := bounded_scale.dominates_input_length

@[simp] theorem toBoundedScale_scale
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (witness : RootTimeConstructibleWitnessData root_scale)
    (scale : Nat → Nat) :
    (witness.toBoundedScale scale).scale = scale := by
  rfl

@[simp] theorem ofBoundedScale_time_constructible_statement
    (root_scale : _root_.LiteraturePudlakTheorem5ScaleData)
    (bounded_scale : BoundedArithmeticLab.TimeConstructibleScale) :
    (RootTimeConstructibleWitnessData.ofBoundedScale
      root_scale bounded_scale).time_constructible_statement =
        bounded_scale.time_constructible_statement := by
  rfl

@[simp] theorem ofBoundedScale_eventually_reads_input_statement
    (root_scale : _root_.LiteraturePudlakTheorem5ScaleData)
    (bounded_scale : BoundedArithmeticLab.TimeConstructibleScale) :
    (RootTimeConstructibleWitnessData.ofBoundedScale
      root_scale bounded_scale).eventually_reads_input_statement =
        bounded_scale.eventually_reads_input_statement := by
  rfl

@[simp] theorem ofBoundedScale_eventually_defined_statement
    (root_scale : _root_.LiteraturePudlakTheorem5ScaleData)
    (bounded_scale : BoundedArithmeticLab.TimeConstructibleScale) :
    (RootTimeConstructibleWitnessData.ofBoundedScale
      root_scale bounded_scale).eventually_defined_statement =
        bounded_scale.eventually_defined_statement := by
  rfl

@[simp] theorem ofBoundedScale_dominates_input_length_statement
    (root_scale : _root_.LiteraturePudlakTheorem5ScaleData)
    (bounded_scale : BoundedArithmeticLab.TimeConstructibleScale) :
    (RootTimeConstructibleWitnessData.ofBoundedScale
      root_scale bounded_scale).dominates_input_length_statement =
        bounded_scale.dominates_input_length_statement := by
  rfl

end RootTimeConstructibleWitnessData

structure RootBoundedTimeConstructibleWitnessBridge
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (root_witness : RootTimeConstructibleWitnessData root_scale)
    (bounded_scale : BoundedArithmeticLab.TimeConstructibleScale) :
    Prop where
  time_constructible_statement_eq :
    bounded_scale.time_constructible_statement =
      root_witness.time_constructible_statement
  eventually_reads_input_statement_eq :
    bounded_scale.eventually_reads_input_statement =
      root_witness.eventually_reads_input_statement
  eventually_defined_statement_eq :
    bounded_scale.eventually_defined_statement =
      root_witness.eventually_defined_statement
  dominates_input_length_statement_eq :
    bounded_scale.dominates_input_length_statement =
      root_witness.dominates_input_length_statement

namespace RootBoundedTimeConstructibleWitnessBridge

theorem time_constructible_iff
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {root_witness : RootTimeConstructibleWitnessData root_scale}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (bridge :
      RootBoundedTimeConstructibleWitnessBridge root_witness bounded_scale) :
    bounded_scale.time_constructible_statement ↔
      root_witness.time_constructible_statement := by
  rw [bridge.time_constructible_statement_eq]

theorem eventually_reads_input_iff
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {root_witness : RootTimeConstructibleWitnessData root_scale}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (bridge :
      RootBoundedTimeConstructibleWitnessBridge root_witness bounded_scale) :
    bounded_scale.eventually_reads_input_statement ↔
      root_witness.eventually_reads_input_statement := by
  rw [bridge.eventually_reads_input_statement_eq]

theorem eventually_defined_iff
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {root_witness : RootTimeConstructibleWitnessData root_scale}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (bridge :
      RootBoundedTimeConstructibleWitnessBridge root_witness bounded_scale) :
    bounded_scale.eventually_defined_statement ↔
      root_witness.eventually_defined_statement := by
  rw [bridge.eventually_defined_statement_eq]

theorem dominates_input_length_iff
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {root_witness : RootTimeConstructibleWitnessData root_scale}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (bridge :
      RootBoundedTimeConstructibleWitnessBridge root_witness bounded_scale) :
    bounded_scale.dominates_input_length_statement ↔
      root_witness.dominates_input_length_statement := by
  rw [bridge.dominates_input_length_statement_eq]

theorem bounded_time_constructible_of_root
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {root_witness : RootTimeConstructibleWitnessData root_scale}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (bridge :
      RootBoundedTimeConstructibleWitnessBridge root_witness bounded_scale) :
    bounded_scale.time_constructible_statement :=
  (bridge.time_constructible_iff).2 root_witness.time_constructible

theorem bounded_eventually_reads_input_of_root
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {root_witness : RootTimeConstructibleWitnessData root_scale}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (bridge :
      RootBoundedTimeConstructibleWitnessBridge root_witness bounded_scale) :
    bounded_scale.eventually_reads_input_statement :=
  (bridge.eventually_reads_input_iff).2 root_witness.eventually_reads_input

theorem bounded_eventually_defined_of_root
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {root_witness : RootTimeConstructibleWitnessData root_scale}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (bridge :
      RootBoundedTimeConstructibleWitnessBridge root_witness bounded_scale) :
    bounded_scale.eventually_defined_statement :=
  (bridge.eventually_defined_iff).2 root_witness.eventually_defined

theorem bounded_dominates_input_length_of_root
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {root_witness : RootTimeConstructibleWitnessData root_scale}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (bridge :
      RootBoundedTimeConstructibleWitnessBridge root_witness bounded_scale) :
    bounded_scale.dominates_input_length_statement :=
  (bridge.dominates_input_length_iff).2 root_witness.dominates_input_length

theorem root_time_constructible_of_bounded
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {root_witness : RootTimeConstructibleWitnessData root_scale}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (bridge :
      RootBoundedTimeConstructibleWitnessBridge root_witness bounded_scale) :
    root_witness.time_constructible_statement :=
  (bridge.time_constructible_iff).1 bounded_scale.time_constructible

theorem root_eventually_reads_input_of_bounded
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {root_witness : RootTimeConstructibleWitnessData root_scale}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (bridge :
      RootBoundedTimeConstructibleWitnessBridge root_witness bounded_scale) :
    root_witness.eventually_reads_input_statement :=
  (bridge.eventually_reads_input_iff).1 bounded_scale.eventually_reads_input

theorem root_eventually_defined_of_bounded
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {root_witness : RootTimeConstructibleWitnessData root_scale}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (bridge :
      RootBoundedTimeConstructibleWitnessBridge root_witness bounded_scale) :
    root_witness.eventually_defined_statement :=
  (bridge.eventually_defined_iff).1 bounded_scale.eventually_defined

theorem root_dominates_input_length_of_bounded
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {root_witness : RootTimeConstructibleWitnessData root_scale}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (bridge :
      RootBoundedTimeConstructibleWitnessBridge root_witness bounded_scale) :
    root_witness.dominates_input_length_statement :=
  (bridge.dominates_input_length_iff).1 bounded_scale.dominates_input_length

def reflOfBoundedScale
    (root_scale : _root_.LiteraturePudlakTheorem5ScaleData)
    (bounded_scale : BoundedArithmeticLab.TimeConstructibleScale) :
    RootBoundedTimeConstructibleWitnessBridge
      (RootTimeConstructibleWitnessData.ofBoundedScale
        root_scale bounded_scale)
      bounded_scale where
  time_constructible_statement_eq := rfl
  eventually_reads_input_statement_eq := rfl
  eventually_defined_statement_eq := rfl
  dominates_input_length_statement_eq := rfl

def ofRootBoundedScale
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (root_witness : RootTimeConstructibleWitnessData root_scale)
    (scale : Nat → Nat) :
    RootBoundedTimeConstructibleWitnessBridge
      root_witness (root_witness.toBoundedScale scale) where
  time_constructible_statement_eq := rfl
  eventually_reads_input_statement_eq := rfl
  eventually_defined_statement_eq := rfl
  dominates_input_length_statement_eq := rfl

end RootBoundedTimeConstructibleWitnessBridge

structure RootBoundedConstructiveScaleRegistration
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    (root_witness : RootTimeConstructibleWitnessData root_scale)
    (bounded_scale : BoundedArithmeticLab.TimeConstructibleScale) :
    Prop where
  power_registration :
    RootBoundedPowerScaleRegistration root_scale bounded_scale
  witness_bridge :
    RootBoundedTimeConstructibleWitnessBridge root_witness bounded_scale

namespace RootBoundedConstructiveScaleRegistration

def toPowerScaleRegistration
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {root_witness : RootTimeConstructibleWitnessData root_scale}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (registration :
      RootBoundedConstructiveScaleRegistration
        root_witness bounded_scale) :
    RootBoundedPowerScaleRegistration root_scale bounded_scale :=
  registration.power_registration

theorem bounded_scale_eq_power
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {root_witness : RootTimeConstructibleWitnessData root_scale}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (registration :
      RootBoundedConstructiveScaleRegistration
        root_witness bounded_scale)
    (n : Nat) :
    bounded_scale.scale n =
      root_scale.time_constructible_bound n ^ root_scale.exponent :=
  registration.power_registration.bounded_scale_eq_power n

theorem bounded_scale_eq_root
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {root_witness : RootTimeConstructibleWitnessData root_scale}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (registration :
      RootBoundedConstructiveScaleRegistration
        root_witness bounded_scale) :
    bounded_scale.scale = root_scale.scale :=
  registration.power_registration.to_scale_eq

def ofPowerScaleRegistration
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (power_registration :
      RootBoundedPowerScaleRegistration root_scale bounded_scale) :
    Σ' root_witness : RootTimeConstructibleWitnessData root_scale,
      RootBoundedConstructiveScaleRegistration
        root_witness bounded_scale :=
  ⟨RootTimeConstructibleWitnessData.ofBoundedScale
      root_scale bounded_scale,
    { power_registration := power_registration
      witness_bridge :=
        RootBoundedTimeConstructibleWitnessBridge.reflOfBoundedScale
          root_scale bounded_scale }⟩

theorem nonempty_iff_power_registration
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale} :
    Nonempty (Σ' root_witness : RootTimeConstructibleWitnessData root_scale,
      RootBoundedConstructiveScaleRegistration
        root_witness bounded_scale) ↔
      RootBoundedPowerScaleRegistration root_scale bounded_scale := by
  constructor
  · intro h
    rcases h with ⟨⟨root_witness, registration⟩⟩
    exact registration.power_registration
  · intro power_registration
    exact ⟨ofPowerScaleRegistration power_registration⟩

end RootBoundedConstructiveScaleRegistration

structure ProjectConcreteFieldConstructivePowerScaleAssembly
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) where
  index : ProjectConcreteCertificateFieldIndex
    MainRationality SondowAccepted bounds bound
  root_witness :
    RootTimeConstructibleWitnessData
      rootSide.literature_lower_bound.scale_data
  constructive_registration :
    RootBoundedConstructiveScaleRegistration
      root_witness index.lower_source.conditions.scale_data

namespace ProjectConcreteFieldConstructivePowerScaleAssembly

def toPowerScaleAssembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    ProjectConcreteFieldPowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound where
  index := assembly.index
  power_registration :=
    assembly.constructive_registration.power_registration

def ofPowerScaleAssembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldPowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound where
  index := assembly.index
  root_witness :=
    RootTimeConstructibleWitnessData.ofBoundedScale
      rootSide.literature_lower_bound.scale_data
      assembly.index.lower_source.conditions.scale_data
  constructive_registration :=
    { power_registration := assembly.power_registration
      witness_bridge :=
        RootBoundedTimeConstructibleWitnessBridge.reflOfBoundedScale
          rootSide.literature_lower_bound.scale_data
          assembly.index.lower_source.conditions.scale_data }

def toScaleDataAssembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    SondowProjectPudlakScaleDataBridgeReleaseSurface.ProjectConcreteFieldScaleDataAssembly
      rootSide MainRationality SondowAccepted bounds bound :=
  assembly.toPowerScaleAssembly.toScaleDataAssembly

def toRootSourceAssembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    SondowProjectPudlakRootSourceAssemblyReleaseSurface.ProjectConcreteFieldRootSourceAssembly
      rootSide MainRationality SondowAccepted bounds bound :=
  assembly.toPowerScaleAssembly.toRootSourceAssembly

def toFieldOrigin
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    ProjectConcreteFieldLowerSourceOrigin rootSide assembly.index :=
  assembly.toPowerScaleAssembly.toFieldOrigin

def toPublicBundleLowerSourceOrigin
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    SondowProjectPudlakExactInputBridgeReleaseSurface.PublicBundleLowerSourceOrigin
      rootSide assembly.index.toCertificateBundle :=
  assembly.toPowerScaleAssembly.toPublicBundleLowerSourceOrigin

theorem bounded_scale_eq_power
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
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
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.scale =
      rootSide.literature_lower_bound.scale_data.scale :=
  assembly.constructive_registration.bounded_scale_eq_root

theorem time_constructible_iff_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.time_constructible_statement ↔
      assembly.root_witness.time_constructible_statement :=
  assembly.constructive_registration.witness_bridge.time_constructible_iff

theorem eventually_reads_input_iff_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.eventually_reads_input_statement ↔
      assembly.root_witness.eventually_reads_input_statement :=
  assembly.constructive_registration.witness_bridge.eventually_reads_input_iff

theorem eventually_defined_iff_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.eventually_defined_statement ↔
      assembly.root_witness.eventually_defined_statement :=
  assembly.constructive_registration.witness_bridge.eventually_defined_iff

theorem dominates_input_length_iff_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.dominates_input_length_statement ↔
      assembly.root_witness.dominates_input_length_statement :=
  assembly.constructive_registration.witness_bridge.dominates_input_length_iff

theorem bounded_time_constructible_of_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.time_constructible_statement :=
  assembly.constructive_registration.witness_bridge.bounded_time_constructible_of_root

theorem bounded_eventually_reads_input_of_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.eventually_reads_input_statement :=
  assembly.constructive_registration.witness_bridge.bounded_eventually_reads_input_of_root

theorem bounded_eventually_defined_of_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.eventually_defined_statement :=
  assembly.constructive_registration.witness_bridge.bounded_eventually_defined_of_root

theorem bounded_dominates_input_length_of_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.dominates_input_length_statement :=
  assembly.constructive_registration.witness_bridge.bounded_dominates_input_length_of_root

theorem root_time_constructible_of_bounded
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.root_witness.time_constructible_statement :=
  assembly.constructive_registration.witness_bridge.root_time_constructible_of_bounded

theorem root_eventually_reads_input_of_bounded
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.root_witness.eventually_reads_input_statement :=
  assembly.constructive_registration.witness_bridge.root_eventually_reads_input_of_bounded

theorem root_eventually_defined_of_bounded
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.root_witness.eventually_defined_statement :=
  assembly.constructive_registration.witness_bridge.root_eventually_defined_of_bounded

theorem root_dominates_input_length_of_bounded
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.root_witness.dominates_input_length_statement :=
  assembly.constructive_registration.witness_bridge.root_dominates_input_length_of_bounded

theorem root_normalForm_translation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    RootToBoundedFormulaCode
      ((rootSide.literature_lower_bound.toNormalForm
        rootSide.strengthened_to_partial).code n)
      (BoundedArithmeticLab.rescaledExternalPudlakCode
        assembly.index.lower_source.conditions.scale_data.scale n) :=
  assembly.toPowerScaleAssembly.root_normalForm_translation n

end ProjectConcreteFieldConstructivePowerScaleAssembly

theorem constructivePowerScaleAssembly_nonempty_iff_powerScaleAssembly_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectConcreteFieldPowerScaleAssembly
        rootSide MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨assembly⟩
    exact ⟨assembly.toPowerScaleAssembly⟩
  · intro h
    rcases h with ⟨assembly⟩
    exact ⟨ProjectConcreteFieldConstructivePowerScaleAssembly.ofPowerScaleAssembly
      assembly⟩

theorem constructivePowerScaleAssembly_nonempty_iff_publicBundleLowerSourceOrigin_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (ProjectConcreteFieldConstructivePowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (Σ' bundle : ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakExactInputBridgeReleaseSurface.PublicBundleLowerSourceOrigin
          rootSide bundle) :=
  constructivePowerScaleAssembly_nonempty_iff_powerScaleAssembly_nonempty.trans
    powerScaleAssembly_nonempty_iff_publicBundleLowerSourceOrigin_nonempty

theorem exactConvention_checklist_iff_constructive_power_scale_assembly
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
      Nonempty (ProjectConcreteFieldConstructivePowerScaleAssembly
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactConvention_checklist_iff_power_scale_assembly h).trans
    constructivePowerScaleAssembly_nonempty_iff_powerScaleAssembly_nonempty.symm

theorem splitMinChecked_checklist_iff_constructive_power_scale_assembly
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
      Nonempty (ProjectConcreteFieldConstructivePowerScaleAssembly
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (splitMinChecked_checklist_iff_power_scale_assembly h).trans
    constructivePowerScaleAssembly_nonempty_iff_powerScaleAssembly_nonempty.symm

theorem exactFamily_checklist_iff_constructive_power_scale_assembly
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
      Nonempty (ProjectConcreteFieldConstructivePowerScaleAssembly
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactFamily_checklist_iff_power_scale_assembly h).trans
    constructivePowerScaleAssembly_nonempty_iff_powerScaleAssembly_nonempty.symm

theorem exactConvention_to_concrete_checklist_of_constructive_power_scale_assembly
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
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) :=
  exactConvention_to_concrete_checklist_of_power_scale_assembly
    h assembly.toPowerScaleAssembly

theorem exactConvention_to_same_object_closure_of_constructive_power_scale_assembly
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
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  exactConvention_to_same_object_closure_of_power_scale_assembly
    h assembly.toPowerScaleAssembly

theorem exactConvention_to_public_gap_instantiation_of_constructive_power_scale_assembly
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
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  exactConvention_to_public_gap_instantiation_of_power_scale_assembly
    h assembly.toPowerScaleAssembly

theorem exactConvention_not_main_rationality_of_constructive_power_scale_assembly
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
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  exactConvention_not_main_rationality_of_power_scale_assembly
    h assembly.toPowerScaleAssembly

theorem splitMinChecked_to_same_object_closure_of_constructive_power_scale_assembly
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
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  splitMinChecked_to_same_object_closure_of_power_scale_assembly
    h assembly.toPowerScaleAssembly

theorem splitMinChecked_to_public_gap_instantiation_of_constructive_power_scale_assembly
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
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  splitMinChecked_to_public_gap_instantiation_of_power_scale_assembly
    h assembly.toPowerScaleAssembly

theorem splitMinChecked_not_main_rationality_of_constructive_power_scale_assembly
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
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  splitMinChecked_not_main_rationality_of_power_scale_assembly
    h assembly.toPowerScaleAssembly

theorem exactFamily_to_same_object_closure_of_constructive_power_scale_assembly
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
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  exactFamily_to_same_object_closure_of_power_scale_assembly
    h assembly.toPowerScaleAssembly

theorem exactFamily_to_public_gap_instantiation_of_constructive_power_scale_assembly
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
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  exactFamily_to_public_gap_instantiation_of_power_scale_assembly
    h assembly.toPowerScaleAssembly

theorem exactFamily_not_main_rationality_of_constructive_power_scale_assembly
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
    (assembly : ProjectConcreteFieldConstructivePowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  exactFamily_not_main_rationality_of_power_scale_assembly
    h assembly.toPowerScaleAssembly

end SondowProjectPudlakTimeConstructibleWitnessBridgeReleaseSurface
end SondowMainCheckedCodeBridge
