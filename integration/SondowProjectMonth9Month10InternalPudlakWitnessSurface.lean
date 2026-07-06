/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth8ProofLengthInstantiationSurface
import EulerLimit.PudlakTheorem5ExactMinimalFieldPackageSurface

/-!
# Month 9-10 internal Pudlak theorem 5 and computable witness surface

This module starts the Month 9-10 replacement of the external Pudlak theorem 5
boundary.  It separates two tasks:

* an internal finite-consistency lower-bound machine that can supply the same
  `PudlakFiniteConsistencyLowerBoundPackage` used by the existing collision
  core, without storing a literature certificate field;
* a computable tail-gap witness layer that turns an upper threshold and a gap
  threshold into the concrete contradiction witness `max upperN gapN`.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth9Month10InternalPudlakWitnessSurface

universe u v w q

open SondowProjectMonth7FinalCollisionSurface
open SondowProjectMonth8ProofLengthInstantiationSurface
open Filter

/-- Month 9 lower-bound machine boundary.  This is intentionally shaped like
the current `PudlakFiniteConsistencyLowerBoundPackage`, but it is not a
`LiteraturePudlakTheorem5LowerBoundCertificate`: the proof-complexity lower
bound is the machine field to be internally re-proved. -/
structure InternalFiniteConsistencyLowerBoundMachine : Type where
  scale : Nat → Nat
  scale_properties : _root_.PolynomialCofinalScale scale
  rescaled_strong_lower_bound :
    _root_.StrongRescaledPartialConsistencyLowerBound scale

namespace InternalFiniteConsistencyLowerBoundMachine

def toPudlakFiniteConsistencyLowerBoundPackage
    (machine : InternalFiniteConsistencyLowerBoundMachine) :
    _root_.PudlakFiniteConsistencyLowerBoundPackage where
  scale := machine.scale
  scale_properties := machine.scale_properties
  rescaled_strong_lower_bound := machine.rescaled_strong_lower_bound

def ofPudlakFiniteConsistencyLowerBoundPackage
    (pkg : _root_.PudlakFiniteConsistencyLowerBoundPackage) :
    InternalFiniteConsistencyLowerBoundMachine where
  scale := pkg.scale
  scale_properties := pkg.scale_properties
  rescaled_strong_lower_bound := pkg.rescaled_strong_lower_bound

theorem toPackage_ofPackage
    (pkg : _root_.PudlakFiniteConsistencyLowerBoundPackage) :
    (ofPudlakFiniteConsistencyLowerBoundPackage pkg).toPudlakFiniteConsistencyLowerBoundPackage =
      pkg := by
  cases pkg
  rfl

theorem ofPackage_toPackage
    (machine : InternalFiniteConsistencyLowerBoundMachine) :
    ofPudlakFiniteConsistencyLowerBoundPackage
        machine.toPudlakFiniteConsistencyLowerBoundPackage =
      machine := by
  cases machine
  rfl

theorem nonempty_iff_pudlak_lower_bound_package :
    Nonempty InternalFiniteConsistencyLowerBoundMachine ↔
      Nonempty _root_.PudlakFiniteConsistencyLowerBoundPackage := by
  constructor
  · intro h
    rcases h with ⟨machine⟩
    exact ⟨machine.toPudlakFiniteConsistencyLowerBoundPackage⟩
  · intro h
    rcases h with ⟨pkg⟩
    exact ⟨ofPudlakFiniteConsistencyLowerBoundPackage pkg⟩

theorem eventualPartialConsistencyLowerBound
    (machine : InternalFiniteConsistencyLowerBoundMachine) :
    _root_.EventualLowerBound _root_.ProofSystem.PA
      _root_.ProofLengthMeasure.symbolSize _root_.partialConsistencyCode :=
  machine.toPudlakFiniteConsistencyLowerBoundPackage.eventualPartialConsistencyLowerBound

theorem strongReflectionGraftLowerBound_of_transfer
    (machine : InternalFiniteConsistencyLowerBoundMachine)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    _root_.StrongProofLengthLowerBound _root_.ProofSystem.PA
      _root_.ProofLengthMeasure.symbolSize _root_.sondowReflectionGraftCode :=
  machine.toPudlakFiniteConsistencyLowerBoundPackage
    |>.strongReflectionGraftLowerBound_of_transfer htransfer

/-- The direct transfer chain from the machine's rescaled lower-bound field to
the reflection-graft family.  This avoids reading the lower bound through the
whole `PudlakFiniteConsistencyLowerBoundPackage`: the only ingredients are the
machine's scale cofinality and the explicit partial-to-graft transfer. -/
def rescaledToReflectionGraftTransfer
    (machine : InternalFiniteConsistencyLowerBoundMachine)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    _root_.StrongLowerBoundTransfer _root_.ProofSystem.PA
      _root_.ProofLengthMeasure.symbolSize
      (_root_.rescaledPartialConsistencyCode machine.scale)
      _root_.sondowReflectionGraftCode :=
  (_root_.rescaled_partial_consistency_transfer_of_polynomial_cofinal_scale
      machine.scale_properties).comp htransfer

/-- Field-level lower-bound route: the reflection-graft strong lower bound can
be obtained directly from `rescaled_strong_lower_bound` by the composed
rescaled-to-partial and partial-to-graft transfer chain. -/
theorem strongReflectionGraftLowerBound_from_rescaled_field
    (machine : InternalFiniteConsistencyLowerBoundMachine)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    _root_.StrongProofLengthLowerBound _root_.ProofSystem.PA
      _root_.ProofLengthMeasure.symbolSize _root_.sondowReflectionGraftCode :=
  machine.rescaled_strong_lower_bound.transfer
    (machine.rescaledToReflectionGraftTransfer htransfer)

theorem eventualReflectionGraftLowerBound_from_rescaled_field
    (machine : InternalFiniteConsistencyLowerBoundMachine)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    _root_.EventualLowerBound _root_.ProofSystem.PA
      _root_.ProofLengthMeasure.symbolSize _root_.sondowReflectionGraftCode :=
  (machine.strongReflectionGraftLowerBound_from_rescaled_field htransfer)
    |>.toEventualLowerBound

theorem reflectionGraftGap_from_rescaled_field
    (machine : InternalFiniteConsistencyLowerBoundMachine)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) :
    _root_.EventualStrictGap U
      (fun n : Nat => sondowProjectLocalPudlakCollisionBox n) :=
  _root_.EventualLowerBound.toProofLengthGap
    (machine.eventualReflectionGraftLowerBound_from_rescaled_field htransfer)
    U hU

theorem reflectionGraftGap_from_rescaled_field_gap_after
    (machine : InternalFiniteConsistencyLowerBoundMachine)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ∃ n : Nat, N ≤ n ∧ U n < sondowProjectLocalPudlakCollisionBox n :=
  (machine.reflectionGraftGap_from_rescaled_field htransfer U hU).gap_after N

/-- Transfer-witness form of the field-level lower route.  For a target upper
bound `U`, the composed rescaled-to-graft transfer supplies a concrete
polynomial source bound `g`; any frequent win over `g` on the rescaled finite
consistency family transfers to a frequent win over `U` on the reflection-graft
family. -/
theorem reflectionGraftGap_from_rescaled_field_transfer_witness
    (machine : InternalFiniteConsistencyLowerBoundMachine)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) :
    ∃ g : Nat → Real,
      _root_.is_polynomial_bound g ∧
        ((∃ᶠ n in atTop,
            _root_.proof_length _root_.ProofSystem.PA
              _root_.ProofLengthMeasure.symbolSize
              (_root_.rescaledPartialConsistencyCode machine.scale n) > g n) →
          ∃ᶠ n in atTop,
            _root_.proof_length _root_.ProofSystem.PA
              _root_.ProofLengthMeasure.symbolSize
              (_root_.sondowReflectionGraftCode n) > U n) :=
  (machine.rescaledToReflectionGraftTransfer htransfer).transfer U hU

/-- Witness-extraction trace for the direct field-level route.  It keeps the
intermediate polynomial `g` produced by the transfer certificate, then uses the
machine's rescaled strong lower-bound field to obtain a concrete tail witness
for the project reflection-graft gap. -/
theorem reflectionGraftGap_from_rescaled_field_gap_after_trace
    (machine : InternalFiniteConsistencyLowerBoundMachine)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ∃ g : Nat → Real,
      _root_.is_polynomial_bound g ∧
        ∃ n : Nat, N ≤ n ∧ U n < sondowProjectLocalPudlakCollisionBox n := by
  rcases machine.reflectionGraftGap_from_rescaled_field_transfer_witness
      htransfer U hU with
    ⟨g, hg, htransfer_g⟩
  have hsource :
      ∃ᶠ n in atTop,
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.rescaledPartialConsistencyCode machine.scale n) > g n :=
    machine.rescaled_strong_lower_bound.frequently_beats_every_polynomial g hg
  have htarget :
      ∃ᶠ n in atTop,
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowReflectionGraftCode n) > U n :=
    htransfer_g hsource
  rcases Filter.frequently_atTop.mp htarget N with ⟨n, hn, hgt⟩
  exact ⟨g, hg, n, hn, by
    simpa [sondowProjectLocalPudlakCollisionBox] using hgt⟩

theorem eventualReflectionGraftLowerBound_of_transfer
    (machine : InternalFiniteConsistencyLowerBoundMachine)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    _root_.EventualLowerBound _root_.ProofSystem.PA
      _root_.ProofLengthMeasure.symbolSize _root_.sondowReflectionGraftCode :=
  machine.toPudlakFiniteConsistencyLowerBoundPackage.eventualReflectionGraftLowerBound_of_transfer
    htransfer

theorem reflectionGraftGap_of_transfer
    (machine : InternalFiniteConsistencyLowerBoundMachine)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) :
    _root_.EventualStrictGap U
      (fun n : Nat => sondowProjectLocalPudlakCollisionBox n) :=
  machine.toPudlakFiniteConsistencyLowerBoundPackage.reflectionGraftGap_of_transfer
    htransfer U hU

theorem eventualReflectionGraftLowerBound_eq_strong_to_eventual
    (machine : InternalFiniteConsistencyLowerBoundMachine)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    machine.eventualReflectionGraftLowerBound_of_transfer htransfer =
      _root_.StrongProofLengthLowerBound.toEventualLowerBound
        (machine.strongReflectionGraftLowerBound_of_transfer htransfer) :=
  rfl

theorem reflectionGraftGap_eq_eventualLowerBound_toGap
    (machine : InternalFiniteConsistencyLowerBoundMachine)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) :
    machine.reflectionGraftGap_of_transfer htransfer U hU =
      _root_.EventualLowerBound.toProofLengthGap
        (machine.eventualReflectionGraftLowerBound_of_transfer htransfer)
        U hU :=
  rfl

theorem reflectionGraftGap_gap_after_from_eventualLowerBound
    (machine : InternalFiniteConsistencyLowerBoundMachine)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ∃ n : Nat, N ≤ n ∧ U n < sondowProjectLocalPudlakCollisionBox n := by
  simpa [reflectionGraftGap_of_transfer,
    sondowProjectLocalPudlakCollisionBox] using
    (machine.eventualReflectionGraftLowerBound_of_transfer htransfer).lower_bound
      U hU N

def toProjectCollisionInputs
    (machine : InternalFiniteConsistencyLowerBoundMachine)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    SondowProjectLocalPudlakCollisionInputs where
  project_upper := project_upper
  pudlak_lower_bound := machine.toPudlakFiniteConsistencyLowerBoundPackage
  transfer_to_graft := htransfer

theorem toProjectCollisionInputs_pudlak_lower_bound
    (machine : InternalFiniteConsistencyLowerBoundMachine)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    (machine.toProjectCollisionInputs project_upper htransfer).pudlak_lower_bound =
      machine.toPudlakFiniteConsistencyLowerBoundPackage :=
  rfl

/-- Same-object lower-route trace for the internal finite-consistency machine.
After the machine is inserted into the project collision inputs, the final
Pudlak gap certificate used by the collision core is exactly the reflection
graft gap generated by this machine and the same transfer certificate. -/
theorem toProjectCollisionInputs_finalGap_eq_machineGap
    (machine : InternalFiniteConsistencyLowerBoundMachine)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) :
    SondowProjectLocalPudlakCollisionInputs.finalPudlakGapCertificate
        (machine.toProjectCollisionInputs project_upper htransfer) U hU =
      machine.reflectionGraftGap_of_transfer htransfer U hU :=
  rfl

/-- Field-level audit for the same lower route: the project checklist keeps the
same project upper source, the same internal-machine lower-bound package, the
same transfer certificate, and the same final gap certificate. -/
theorem toProjectCollisionInputs_full_lower_route_trace
    (machine : InternalFiniteConsistencyLowerBoundMachine)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) :
    (machine.toProjectCollisionInputs project_upper htransfer).project_upper =
        project_upper ∧
      (machine.toProjectCollisionInputs project_upper htransfer).pudlak_lower_bound =
        machine.toPudlakFiniteConsistencyLowerBoundPackage ∧
      (machine.toProjectCollisionInputs project_upper htransfer).transfer_to_graft =
        htransfer ∧
      SondowProjectLocalPudlakCollisionInputs.finalPudlakGapCertificate
          (machine.toProjectCollisionInputs project_upper htransfer) U hU =
        machine.reflectionGraftGap_of_transfer htransfer U hU := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end InternalFiniteConsistencyLowerBoundMachine

/-- Compatibility adapter only: it records how the old literature certificate
can still instantiate the new internal-machine-shaped boundary.  The new
Month 9 work should prove this machine directly rather than using this adapter
as the final source. -/
def internalMachineOfLiteratureCertificate
    (hsource : _root_.LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    InternalFiniteConsistencyLowerBoundMachine :=
  InternalFiniteConsistencyLowerBoundMachine.ofPudlakFiniteConsistencyLowerBoundPackage
    (hsource.toPudlakFiniteConsistencyLowerBoundPackage hpartial)

theorem internalMachineOfLiteratureCertificate_toPackage
    (hsource : _root_.LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    (internalMachineOfLiteratureCertificate hsource hpartial).toPudlakFiniteConsistencyLowerBoundPackage =
      hsource.toPudlakFiniteConsistencyLowerBoundPackage hpartial :=
  InternalFiniteConsistencyLowerBoundMachine.toPackage_ofPackage
    (hsource.toPudlakFiniteConsistencyLowerBoundPackage hpartial)

namespace InternalPudlakTheorem5TransferPieces

def strengthenedToPartialTransferOfConstant
    (projection : _root_.StrengthenedToPartialConsistencyConstantProjection) :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer :=
  _root_.strengthened_to_partial_transfer_of_constant_projection
    projection

def partialToGraftTransferOfConstant
    (projection : _root_.PAConjunctionEliminationConstantCost) :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer :=
  _root_.LinearProofLengthProjection.toStrongLowerBoundTransfer
    (_root_.ConstantProofLengthProjection.toLinearProofLengthProjection
      projection)

end InternalPudlakTheorem5TransferPieces

/-- Intrinsic theorem-5 scale statement used by the Month 9 internalization
route.  It has the same fields as the current literature scale certificate, but
is not itself a literature certificate. -/
structure InternalPudlakTheorem5ScaleData : Type where
  time_constructible_bound : Nat → Nat
  exponent : Nat
  scale : Nat → Nat
  scale_eq :
    ∀ n : Nat, scale n = time_constructible_bound n ^ exponent
  scale_id_le : ∀ n : Nat, n ≤ scale n
  scale_polynomial_bound :
    _root_.is_polynomial_bound (fun n : Nat => (scale n : Real))

namespace InternalPudlakTheorem5ScaleData

def toLiteratureScaleData
    (scale_data : InternalPudlakTheorem5ScaleData) :
    _root_.LiteraturePudlakTheorem5ScaleData where
  time_constructible_bound := scale_data.time_constructible_bound
  exponent := scale_data.exponent
  scale := scale_data.scale
  scale_eq := scale_data.scale_eq
  scale_id_le := scale_data.scale_id_le
  scale_polynomial_bound := scale_data.scale_polynomial_bound

def ofLiteratureScaleData
    (scale_data : _root_.LiteraturePudlakTheorem5ScaleData) :
    InternalPudlakTheorem5ScaleData where
  time_constructible_bound := scale_data.time_constructible_bound
  exponent := scale_data.exponent
  scale := scale_data.scale
  scale_eq := scale_data.scale_eq
  scale_id_le := scale_data.scale_id_le
  scale_polynomial_bound := scale_data.scale_polynomial_bound

theorem toLiterature_ofLiterature
    (scale_data : _root_.LiteraturePudlakTheorem5ScaleData) :
    (ofLiteratureScaleData scale_data).toLiteratureScaleData =
      scale_data := by
  cases scale_data
  rfl

theorem ofLiterature_toLiterature
    (scale_data : InternalPudlakTheorem5ScaleData) :
    ofLiteratureScaleData scale_data.toLiteratureScaleData =
      scale_data := by
  cases scale_data
  rfl

def scaleProperties
    (scale_data : InternalPudlakTheorem5ScaleData) :
    _root_.PolynomialCofinalScale scale_data.scale :=
  scale_data.toLiteratureScaleData.scale_properties

def rawCode
    (_scale_data : InternalPudlakTheorem5ScaleData) :
    Nat → _root_.FormulaCode :=
  _root_.bussPudlakPAFiniteConsistencyRawCode

def rescaledRawCode
    (scale_data : InternalPudlakTheorem5ScaleData) :
    Nat → _root_.FormulaCode :=
  scale_data.toLiteratureScaleData.rescaledRawCode

def powerBoundRawCode
    (scale_data : InternalPudlakTheorem5ScaleData) :
    Nat → _root_.FormulaCode :=
  scale_data.toLiteratureScaleData.powerBoundRawCode

theorem rescaledRawCode_eq_powerBoundRawCode
    (scale_data : InternalPudlakTheorem5ScaleData) (n : Nat) :
    scale_data.rescaledRawCode n =
      scale_data.powerBoundRawCode n :=
  scale_data.toLiteratureScaleData.rescaledRawCode_eq_powerBoundRawCode n

theorem powerBoundRawCode_eq_rescaledPudlak
    (scale_data : InternalPudlakTheorem5ScaleData) (n : Nat) :
    scale_data.powerBoundRawCode n =
      _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
        scale_data.scale n :=
  scale_data.toLiteratureScaleData.powerBoundRawCode_eq_rescaledPudlak n

abbrev PowerBoundLowerBound
    (scale_data : InternalPudlakTheorem5ScaleData) : Prop :=
  _root_.LiteraturePudlakTheorem5PowerBoundLowerBound
    scale_data.toLiteratureScaleData

theorem powerBoundLowerBound_to_rescaledLowerBound
    (scale_data : InternalPudlakTheorem5ScaleData)
    (hlower : scale_data.PowerBoundLowerBound) :
    _root_.StrongRescaledExternalStrengthenedLowerBound
      scale_data.rawCode scale_data.scale :=
  scale_data.toLiteratureScaleData
    |>.powerBoundLowerBound_to_rescaledLowerBound hlower

theorem rescaledLowerBound_to_powerBoundLowerBound
    (scale_data : InternalPudlakTheorem5ScaleData)
    (hlower :
      _root_.StrongRescaledExternalStrengthenedLowerBound
        scale_data.rawCode scale_data.scale) :
    scale_data.PowerBoundLowerBound :=
  scale_data.toLiteratureScaleData
    |>.rescaledLowerBound_to_powerBoundLowerBound hlower

theorem powerBoundLowerBound_iff_rescaledLowerBound
    (scale_data : InternalPudlakTheorem5ScaleData) :
    scale_data.PowerBoundLowerBound ↔
      _root_.StrongRescaledExternalStrengthenedLowerBound
        scale_data.rawCode scale_data.scale :=
  ⟨scale_data.powerBoundLowerBound_to_rescaledLowerBound,
    scale_data.rescaledLowerBound_to_powerBoundLowerBound⟩

end InternalPudlakTheorem5ScaleData

/-- Refined Month 9 theorem-5 machine.  It exposes the exact raw code,
rescaling data, rescaled lower bound, and strengthened-to-partial transfer
needed to build the project lower-bound package.  The lower-bound field is the
piece Month 9 must eventually prove internally. -/
structure InternalPudlakTheorem5Machine : Type where
  scale_data : _root_.LiteraturePudlakTheorem5ScaleData
  rescaled_raw_lower_bound :
    _root_.StrongRescaledExternalStrengthenedLowerBound
      scale_data.rawCode scale_data.scale
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer

namespace InternalPudlakTheorem5Machine

def rawCode (machine : InternalPudlakTheorem5Machine) :
    Nat → _root_.FormulaCode :=
  machine.scale_data.rawCode

def scale (machine : InternalPudlakTheorem5Machine) : Nat → Nat :=
  machine.scale_data.scale

def scaleProperties
    (machine : InternalPudlakTheorem5Machine) :
    _root_.PolynomialCofinalScale machine.scale :=
  machine.scale_data.scale_properties

def toStandardInstance
    (machine : InternalPudlakTheorem5Machine) :
    _root_.LiteraturePudlakTheorem5StandardInstance :=
  machine.scale_data.toStandardInstance machine.rescaled_raw_lower_bound

def toLowerBoundSource
    (machine : InternalPudlakTheorem5Machine) :
    _root_.RescaledRawPudlakStrengthenedLowerBoundSource :=
  machine.scale_data.toLowerBoundSource machine.rescaled_raw_lower_bound

def toNormalForm
    (machine : InternalPudlakTheorem5Machine) :
    _root_.PartialConsistencyLowerBoundNormalForm :=
  machine.scale_data.toNormalForm
    machine.rescaled_raw_lower_bound machine.strengthened_to_partial

theorem normalForm_code_eq_rescaledPudlak
    (machine : InternalPudlakTheorem5Machine) (n : Nat) :
    machine.toNormalForm.code n =
      _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
        machine.scale n := by
  exact
    machine.scale_data.normalForm_code_eq_rescaledPudlak
      machine.rescaled_raw_lower_bound machine.strengthened_to_partial n

def toPudlakFiniteConsistencyLowerBoundPackage
    (machine : InternalPudlakTheorem5Machine) :
    _root_.PudlakFiniteConsistencyLowerBoundPackage :=
  pudlakFiniteConsistencyLowerBoundPackageOfPartialNormalForm
    machine.toNormalForm

def toInternalFiniteConsistencyLowerBoundMachine
    (machine : InternalPudlakTheorem5Machine) :
    InternalFiniteConsistencyLowerBoundMachine :=
  InternalFiniteConsistencyLowerBoundMachine.ofPudlakFiniteConsistencyLowerBoundPackage
    machine.toPudlakFiniteConsistencyLowerBoundPackage

theorem toInternalFiniteConsistencyLowerBoundMachine_toPackage
    (machine : InternalPudlakTheorem5Machine) :
    machine.toInternalFiniteConsistencyLowerBoundMachine.toPudlakFiniteConsistencyLowerBoundPackage =
      machine.toPudlakFiniteConsistencyLowerBoundPackage :=
  InternalFiniteConsistencyLowerBoundMachine.toPackage_ofPackage
    machine.toPudlakFiniteConsistencyLowerBoundPackage

theorem toPackage_scale_eq_id
    (machine : InternalPudlakTheorem5Machine) :
    machine.toPudlakFiniteConsistencyLowerBoundPackage.scale = id := by
  rfl

theorem toPackage_rescaledCode_eq_partialConsistencyCode
    (machine : InternalPudlakTheorem5Machine) (n : Nat) :
    _root_.rescaledPartialConsistencyCode
        machine.toPudlakFiniteConsistencyLowerBoundPackage.scale n =
      _root_.partialConsistencyCode n := by
  rfl

def ofLiteratureCertificate
    (hsource : _root_.LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    InternalPudlakTheorem5Machine where
  scale_data := hsource.scale_data
  rescaled_raw_lower_bound := hsource.rescaled_strong_lower_bound
  strengthened_to_partial := hpartial

theorem ofLiteratureCertificate_toInternalMachine_eq_compat
    (hsource : _root_.LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    (ofLiteratureCertificate hsource hpartial).toInternalFiniteConsistencyLowerBoundMachine =
      internalMachineOfLiteratureCertificate hsource hpartial := by
  rfl

theorem ofLiteratureCertificate_toPackage_eq_compat
    (hsource : _root_.LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    (ofLiteratureCertificate hsource hpartial).toPudlakFiniteConsistencyLowerBoundPackage =
      hsource.toPudlakFiniteConsistencyLowerBoundPackage hpartial := by
  rfl

end InternalPudlakTheorem5Machine

/-- Power-bound presentation of the same refined theorem-5 machine.  This is
the closest Lean statement to the literature's power-bound form; converting it
to the rescaled machine uses the audited power-bound/rescaled equivalence. -/
structure InternalPudlakTheorem5PowerBoundMachine : Type where
  scale_data : _root_.LiteraturePudlakTheorem5ScaleData
  power_bound_lower_bound :
    _root_.LiteraturePudlakTheorem5PowerBoundLowerBound scale_data
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer

namespace InternalPudlakTheorem5PowerBoundMachine

def toLiteratureCertificate
    (machine : InternalPudlakTheorem5PowerBoundMachine) :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate where
  scale_data := machine.scale_data
  power_bound_lower_bound := machine.power_bound_lower_bound

def toRescaledMachine
    (machine : InternalPudlakTheorem5PowerBoundMachine) :
    InternalPudlakTheorem5Machine where
  scale_data := machine.scale_data
  rescaled_raw_lower_bound :=
    machine.scale_data.powerBoundLowerBound_to_rescaledLowerBound
      machine.power_bound_lower_bound
  strengthened_to_partial := machine.strengthened_to_partial

def toInternalFiniteConsistencyLowerBoundMachine
    (machine : InternalPudlakTheorem5PowerBoundMachine) :
    InternalFiniteConsistencyLowerBoundMachine :=
  machine.toRescaledMachine.toInternalFiniteConsistencyLowerBoundMachine

theorem toRescaledMachine_normalForm_code_eq_rescaledPudlak
    (machine : InternalPudlakTheorem5PowerBoundMachine) (n : Nat) :
    machine.toRescaledMachine.toNormalForm.code n =
      _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
        machine.scale_data.scale n :=
  machine.toRescaledMachine.normalForm_code_eq_rescaledPudlak n

def ofLiteratureCertificate
    (hsource : _root_.LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    InternalPudlakTheorem5PowerBoundMachine where
  scale_data := hsource.scale_data
  power_bound_lower_bound := hsource.power_bound_lower_bound
  strengthened_to_partial := hpartial

theorem ofLiteratureCertificate_toLiteratureCertificate
    (hsource : _root_.LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    (ofLiteratureCertificate hsource hpartial).toLiteratureCertificate =
      hsource := by
  cases hsource
  rfl

theorem ofLiteratureCertificate_toRescaledMachine_eq_compat
    (hsource : _root_.LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    (ofLiteratureCertificate hsource hpartial).toRescaledMachine =
      InternalPudlakTheorem5Machine.ofLiteratureCertificate
        hsource hpartial := by
  cases hsource
  rfl

theorem ofLiteratureCertificate_toInternalMachine_eq_compat
    (hsource : _root_.LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    (ofLiteratureCertificate hsource hpartial).toInternalFiniteConsistencyLowerBoundMachine =
      internalMachineOfLiteratureCertificate hsource hpartial := by
  cases hsource
  rfl

theorem nonempty_iff_literature_certificate
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    Nonempty InternalPudlakTheorem5PowerBoundMachine ↔
      Nonempty _root_.LiteraturePudlakTheorem5LowerBoundCertificate := by
  constructor
  · intro h
    rcases h with ⟨machine⟩
    exact ⟨machine.toLiteratureCertificate⟩
  · intro h
    rcases h with ⟨hsource⟩
    exact ⟨ofLiteratureCertificate hsource hpartial⟩

end InternalPudlakTheorem5PowerBoundMachine

/-- Intrinsic power-bound machine: the theorem-5 scale statement is stored in
the internal Month 9 shape, and the lower-bound lemma is stated against that
internal scale data. -/
structure IntrinsicPudlakTheorem5PowerBoundMachine : Type where
  scale_data : InternalPudlakTheorem5ScaleData
  power_bound_lower_bound : scale_data.PowerBoundLowerBound
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer

namespace IntrinsicPudlakTheorem5PowerBoundMachine

def toPowerBoundMachine
    (machine : IntrinsicPudlakTheorem5PowerBoundMachine) :
    InternalPudlakTheorem5PowerBoundMachine where
  scale_data := machine.scale_data.toLiteratureScaleData
  power_bound_lower_bound := machine.power_bound_lower_bound
  strengthened_to_partial := machine.strengthened_to_partial

def toRescaledMachine
    (machine : IntrinsicPudlakTheorem5PowerBoundMachine) :
    InternalPudlakTheorem5Machine :=
  machine.toPowerBoundMachine.toRescaledMachine

def toInternalFiniteConsistencyLowerBoundMachine
    (machine : IntrinsicPudlakTheorem5PowerBoundMachine) :
    InternalFiniteConsistencyLowerBoundMachine :=
  machine.toPowerBoundMachine.toInternalFiniteConsistencyLowerBoundMachine

def ofPowerBoundMachine
    (machine : InternalPudlakTheorem5PowerBoundMachine) :
    IntrinsicPudlakTheorem5PowerBoundMachine where
  scale_data :=
    InternalPudlakTheorem5ScaleData.ofLiteratureScaleData
      machine.scale_data
  power_bound_lower_bound := by
    change _root_.LiteraturePudlakTheorem5PowerBoundLowerBound
      (InternalPudlakTheorem5ScaleData.ofLiteratureScaleData
        machine.scale_data).toLiteratureScaleData
    rw [InternalPudlakTheorem5ScaleData.toLiterature_ofLiterature
      machine.scale_data]
    exact machine.power_bound_lower_bound
  strengthened_to_partial := machine.strengthened_to_partial

theorem toPowerBound_ofPowerBound
    (machine : InternalPudlakTheorem5PowerBoundMachine) :
    (ofPowerBoundMachine machine).toPowerBoundMachine = machine := by
  cases machine
  rfl

theorem ofPowerBound_toPowerBound
    (machine : IntrinsicPudlakTheorem5PowerBoundMachine) :
    ofPowerBoundMachine machine.toPowerBoundMachine = machine := by
  cases machine
  rfl

def ofLiteratureCertificate
    (hsource : _root_.LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    IntrinsicPudlakTheorem5PowerBoundMachine :=
  ofPowerBoundMachine
    (InternalPudlakTheorem5PowerBoundMachine.ofLiteratureCertificate
      hsource hpartial)

theorem ofLiteratureCertificate_toPowerBound_eq_compat
    (hsource : _root_.LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    (ofLiteratureCertificate hsource hpartial).toPowerBoundMachine =
      InternalPudlakTheorem5PowerBoundMachine.ofLiteratureCertificate
        hsource hpartial :=
  toPowerBound_ofPowerBound
    (InternalPudlakTheorem5PowerBoundMachine.ofLiteratureCertificate
      hsource hpartial)

theorem toRescaledMachine_normalForm_code_eq_rescaledPudlak
    (machine : IntrinsicPudlakTheorem5PowerBoundMachine) (n : Nat) :
    machine.toRescaledMachine.toNormalForm.code n =
      _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
        machine.scale_data.scale n :=
  machine.toPowerBoundMachine
    |>.toRescaledMachine_normalForm_code_eq_rescaledPudlak n

end IntrinsicPudlakTheorem5PowerBoundMachine

/-- The exact Month 9 proof-complexity lemma frontier.  Once the project proves
this core internally, the remaining data needed to enter the collision route is
only the already-separated strengthened-to-partial transfer. -/
structure InternalPudlakTheorem5LowerBoundCore : Type where
  scale_data : InternalPudlakTheorem5ScaleData
  power_bound_lower_bound : scale_data.PowerBoundLowerBound

namespace InternalPudlakTheorem5LowerBoundCore

def toIntrinsicPowerBoundMachine
    (core : InternalPudlakTheorem5LowerBoundCore)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    IntrinsicPudlakTheorem5PowerBoundMachine where
  scale_data := core.scale_data
  power_bound_lower_bound := core.power_bound_lower_bound
  strengthened_to_partial := hpartial

def ofIntrinsicPowerBoundMachine
    (machine : IntrinsicPudlakTheorem5PowerBoundMachine) :
    InternalPudlakTheorem5LowerBoundCore where
  scale_data := machine.scale_data
  power_bound_lower_bound := machine.power_bound_lower_bound

theorem of_toIntrinsicPowerBoundMachine
    (core : InternalPudlakTheorem5LowerBoundCore)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    ofIntrinsicPowerBoundMachine
        (core.toIntrinsicPowerBoundMachine hpartial) =
      core := by
  cases core
  rfl

theorem toIntrinsicPowerBoundMachine_toCore
    (machine : IntrinsicPudlakTheorem5PowerBoundMachine) :
    (ofIntrinsicPowerBoundMachine machine).toIntrinsicPowerBoundMachine
        machine.strengthened_to_partial =
      machine := by
  cases machine
  rfl

theorem nonempty_iff_intrinsic_machine
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    Nonempty InternalPudlakTheorem5LowerBoundCore ↔
      Nonempty IntrinsicPudlakTheorem5PowerBoundMachine := by
  constructor
  · intro h
    rcases h with ⟨core⟩
    exact ⟨core.toIntrinsicPowerBoundMachine hpartial⟩
  · intro h
    rcases h with ⟨machine⟩
    exact ⟨ofIntrinsicPowerBoundMachine machine⟩

theorem lowerBound_iff_rescaledLowerBound
    (core : InternalPudlakTheorem5LowerBoundCore) :
    core.scale_data.PowerBoundLowerBound ↔
      _root_.StrongRescaledExternalStrengthenedLowerBound
        core.scale_data.rawCode core.scale_data.scale :=
  core.scale_data.powerBoundLowerBound_iff_rescaledLowerBound

def toInternalFiniteConsistencyLowerBoundMachine
    (core : InternalPudlakTheorem5LowerBoundCore)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    InternalFiniteConsistencyLowerBoundMachine :=
  core.toIntrinsicPowerBoundMachine hpartial
    |>.toInternalFiniteConsistencyLowerBoundMachine

def toPudlakFiniteConsistencyLowerBoundPackage
    (core : InternalPudlakTheorem5LowerBoundCore)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    _root_.PudlakFiniteConsistencyLowerBoundPackage :=
  core.toInternalFiniteConsistencyLowerBoundMachine hpartial
    |>.toPudlakFiniteConsistencyLowerBoundPackage

theorem toPudlakFiniteConsistencyLowerBoundPackage_eq_machine
    (core : InternalPudlakTheorem5LowerBoundCore)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    core.toPudlakFiniteConsistencyLowerBoundPackage hpartial =
      (core.toIntrinsicPowerBoundMachine hpartial
        |>.toRescaledMachine
        |>.toPudlakFiniteConsistencyLowerBoundPackage) :=
  rfl

def toProjectCollisionInputs
    (core : InternalPudlakTheorem5LowerBoundCore)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    SondowProjectLocalPudlakCollisionInputs where
  project_upper := project_upper
  pudlak_lower_bound :=
    core.toPudlakFiniteConsistencyLowerBoundPackage hpartial
  transfer_to_graft := htransfer

theorem toProjectCollisionInputs_pudlak_lower_bound
    (core : InternalPudlakTheorem5LowerBoundCore)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    (core.toProjectCollisionInputs project_upper hpartial htransfer).pudlak_lower_bound =
      core.toPudlakFiniteConsistencyLowerBoundPackage hpartial :=
  rfl

theorem toProjectCollisionInputs_eq_internal_machine_inputs
    (core : InternalPudlakTheorem5LowerBoundCore)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    core.toProjectCollisionInputs project_upper hpartial htransfer =
      (core.toInternalFiniteConsistencyLowerBoundMachine hpartial
        |>.toProjectCollisionInputs project_upper htransfer) :=
  rfl

def toProjectCollisionInputsOfConstantPieces
    (core : InternalPudlakTheorem5LowerBoundCore)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
    SondowProjectLocalPudlakCollisionInputs :=
  core.toProjectCollisionInputs project_upper
    (InternalPudlakTheorem5TransferPieces.strengthenedToPartialTransferOfConstant
      strengthened_to_partial)
    (InternalPudlakTheorem5TransferPieces.partialToGraftTransferOfConstant
      partial_to_graft)

theorem toProjectCollisionInputsOfConstantPieces_pudlak_lower_bound
    (core : InternalPudlakTheorem5LowerBoundCore)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
    (core.toProjectCollisionInputsOfConstantPieces
        project_upper strengthened_to_partial partial_to_graft).pudlak_lower_bound =
      core.toPudlakFiniteConsistencyLowerBoundPackage
        (InternalPudlakTheorem5TransferPieces.strengthenedToPartialTransferOfConstant
          strengthened_to_partial) :=
  rfl

end InternalPudlakTheorem5LowerBoundCore

/-- Project-facing theorem-5 statement map extracted from Pudlak's power-bound
presentation.  This is intentionally not the old literature certificate: it
spells out the scale fields and the proof-length lower-bound target that Month
9-10 consumes internally. -/
structure InternalPudlakTheorem5ProjectPowerBoundStatementMap : Type where
  time_constructible_bound : Nat → Nat
  exponent : Nat
  scale : Nat → Nat
  scale_eq :
    ∀ n : Nat, scale n = time_constructible_bound n ^ exponent
  scale_id_le : ∀ n : Nat, n ≤ scale n
  scale_polynomial_bound :
    _root_.is_polynomial_bound (fun n : Nat => (scale n : Real))
  power_bound_lower_bound :
    _root_.StrongProofLengthLowerBound _root_.ProofSystem.PA
      _root_.ProofLengthMeasure.symbolSize
      (fun n : Nat =>
        _root_.bussPudlakPAFiniteConsistencyRawCode
          (time_constructible_bound n ^ exponent))

namespace InternalPudlakTheorem5ProjectPowerBoundStatementMap

def toScaleData
    (h : InternalPudlakTheorem5ProjectPowerBoundStatementMap) :
    InternalPudlakTheorem5ScaleData where
  time_constructible_bound := h.time_constructible_bound
  exponent := h.exponent
  scale := h.scale
  scale_eq := h.scale_eq
  scale_id_le := h.scale_id_le
  scale_polynomial_bound := h.scale_polynomial_bound

theorem toPowerBoundLowerBound
    (h : InternalPudlakTheorem5ProjectPowerBoundStatementMap) :
    h.toScaleData.PowerBoundLowerBound := by
  change _root_.StrongProofLengthLowerBound _root_.ProofSystem.PA
    _root_.ProofLengthMeasure.symbolSize
    (fun n : Nat =>
      _root_.bussPudlakPAFiniteConsistencyRawCode
        (h.time_constructible_bound n ^ h.exponent))
  exact h.power_bound_lower_bound

def toLowerBoundCore
    (h : InternalPudlakTheorem5ProjectPowerBoundStatementMap) :
    InternalPudlakTheorem5LowerBoundCore where
  scale_data := h.toScaleData
  power_bound_lower_bound := h.toPowerBoundLowerBound

def toInternalFiniteConsistencyLowerBoundMachine
    (h : InternalPudlakTheorem5ProjectPowerBoundStatementMap)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    InternalFiniteConsistencyLowerBoundMachine :=
  h.toLowerBoundCore.toInternalFiniteConsistencyLowerBoundMachine hpartial

def toPudlakFiniteConsistencyLowerBoundPackage
    (h : InternalPudlakTheorem5ProjectPowerBoundStatementMap)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    _root_.PudlakFiniteConsistencyLowerBoundPackage :=
  h.toInternalFiniteConsistencyLowerBoundMachine hpartial
    |>.toPudlakFiniteConsistencyLowerBoundPackage

def ofLowerBoundCore
    (core : InternalPudlakTheorem5LowerBoundCore) :
    InternalPudlakTheorem5ProjectPowerBoundStatementMap where
  time_constructible_bound := core.scale_data.time_constructible_bound
  exponent := core.scale_data.exponent
  scale := core.scale_data.scale
  scale_eq := core.scale_data.scale_eq
  scale_id_le := core.scale_data.scale_id_le
  scale_polynomial_bound := core.scale_data.scale_polynomial_bound
  power_bound_lower_bound := core.power_bound_lower_bound

theorem toLowerBoundCore_ofLowerBoundCore
    (core : InternalPudlakTheorem5LowerBoundCore) :
    (ofLowerBoundCore core).toLowerBoundCore = core := by
  cases core
  rfl

theorem ofLowerBoundCore_toLowerBoundCore
    (h : InternalPudlakTheorem5ProjectPowerBoundStatementMap) :
    ofLowerBoundCore h.toLowerBoundCore = h := by
  cases h
  rfl

theorem nonempty_iff_lower_bound_core :
    Nonempty InternalPudlakTheorem5ProjectPowerBoundStatementMap ↔
      Nonempty InternalPudlakTheorem5LowerBoundCore := by
  constructor
  · intro h
    rcases h with ⟨statement⟩
    exact ⟨statement.toLowerBoundCore⟩
  · intro h
    rcases h with ⟨core⟩
    exact ⟨ofLowerBoundCore core⟩

noncomputable def ofExactMinimalFieldPackage
    (pkg :
      _root_.PudlakTheorem5ExactMinimalFieldPackageSurface.ExactMinimalFieldPackage) :
    InternalPudlakTheorem5ProjectPowerBoundStatementMap where
  time_constructible_bound :=
    _root_.PudlakTheorem5MinimalExternalFieldsSurface.timeConstructibleBound
  exponent :=
    _root_.PudlakTheorem5MinimalExternalFieldsSurface.exponent
  scale :=
    _root_.PudlakTheorem5MinimalExternalFieldsSurface.scale
  scale_eq := pkg.scale_eq_power_bound
  scale_id_le := pkg.scale_id_le
  scale_polynomial_bound := pkg.scale_polynomial_bound
  power_bound_lower_bound := by
    have hrescaled :
        _root_.StrongRescaledExternalStrengthenedLowerBound
          (_root_.PudlakTheorem5MinimalExternalFieldsSurface.scaleData).rawCode
          (_root_.PudlakTheorem5MinimalExternalFieldsSurface.scaleData).scale := by
      simpa [_root_.PudlakTheorem5MinimalExternalFieldsSurface.rawCode,
        _root_.PudlakTheorem5MinimalExternalFieldsSurface.scale]
        using pkg.rescaled_lower_bound
    have hp :
        _root_.LiteraturePudlakTheorem5PowerBoundLowerBound
          _root_.PudlakTheorem5MinimalExternalFieldsSurface.scaleData :=
      pkg.power_bound_iff_rescaled.2 hrescaled
    change _root_.LiteraturePudlakTheorem5PowerBoundLowerBound
      _root_.PudlakTheorem5MinimalExternalFieldsSurface.scaleData
    exact hp

noncomputable def fromExactMinimalFieldPackageStatement
    (h :
      _root_.PudlakTheorem5ExactMinimalFieldPackageSurface.Statement) :
    InternalPudlakTheorem5ProjectPowerBoundStatementMap :=
  ofExactMinimalFieldPackage h.some

theorem exactMinimalFieldPackageStatement_to_nonempty :
    _root_.PudlakTheorem5ExactMinimalFieldPackageSurface.Statement →
      Nonempty InternalPudlakTheorem5ProjectPowerBoundStatementMap := by
  intro h
  exact ⟨fromExactMinimalFieldPackageStatement h⟩

theorem exactMinimalFieldPackageStatement_to_lower_bound_core_nonempty :
    _root_.PudlakTheorem5ExactMinimalFieldPackageSurface.Statement →
      Nonempty InternalPudlakTheorem5LowerBoundCore :=
  nonempty_iff_lower_bound_core.mp ∘
    exactMinimalFieldPackageStatement_to_nonempty

noncomputable def exactMinimalFieldPackageStatement_to_lower_bound_core
    (h :
      _root_.PudlakTheorem5ExactMinimalFieldPackageSurface.Statement) :
    InternalPudlakTheorem5LowerBoundCore :=
  (fromExactMinimalFieldPackageStatement h).toLowerBoundCore

theorem fromExactMinimalFieldPackageStatement_scale_eq
    (h :
      _root_.PudlakTheorem5ExactMinimalFieldPackageSurface.Statement)
    (n : Nat) :
    (fromExactMinimalFieldPackageStatement h).scale n =
      (fromExactMinimalFieldPackageStatement h).time_constructible_bound n ^
        (fromExactMinimalFieldPackageStatement h).exponent :=
  (fromExactMinimalFieldPackageStatement h).scale_eq n

theorem fromExactMinimalFieldPackageStatement_scale_id_le
    (h :
      _root_.PudlakTheorem5ExactMinimalFieldPackageSurface.Statement)
    (n : Nat) :
    n ≤ (fromExactMinimalFieldPackageStatement h).scale n :=
  (fromExactMinimalFieldPackageStatement h).scale_id_le n

theorem fromExactMinimalFieldPackageStatement_powerBoundLowerBound
    (h :
      _root_.PudlakTheorem5ExactMinimalFieldPackageSurface.Statement) :
    (fromExactMinimalFieldPackageStatement h).toScaleData.PowerBoundLowerBound :=
  (fromExactMinimalFieldPackageStatement h).toPowerBoundLowerBound

noncomputable def exactMinimalFieldPackageStatement_toInternalFiniteConsistencyLowerBoundMachine
    (h :
      _root_.PudlakTheorem5ExactMinimalFieldPackageSurface.Statement)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    InternalFiniteConsistencyLowerBoundMachine :=
  (fromExactMinimalFieldPackageStatement h)
    |>.toInternalFiniteConsistencyLowerBoundMachine hpartial

noncomputable def exactMinimalFieldPackageStatement_toPudlakFiniteConsistencyLowerBoundPackage
    (h :
      _root_.PudlakTheorem5ExactMinimalFieldPackageSurface.Statement)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    _root_.PudlakFiniteConsistencyLowerBoundPackage :=
  (exactMinimalFieldPackageStatement_toInternalFiniteConsistencyLowerBoundMachine
      h hpartial).toPudlakFiniteConsistencyLowerBoundPackage

theorem exactMinimalFieldPackageStatement_toPackage_eq_statementMapPackage
    (h :
      _root_.PudlakTheorem5ExactMinimalFieldPackageSurface.Statement)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
  exactMinimalFieldPackageStatement_toPudlakFiniteConsistencyLowerBoundPackage
        h hpartial =
      toPudlakFiniteConsistencyLowerBoundPackage
        (fromExactMinimalFieldPackageStatement h) hpartial :=
  rfl

theorem exactMinimalFieldPackageStatement_internal_machine_gap_after_trace
    (h :
      _root_.PudlakTheorem5ExactMinimalFieldPackageSurface.Statement)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (htransfer :
      _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ∃ g : Nat → Real,
      _root_.is_polynomial_bound g ∧
        ∃ n : Nat, N ≤ n ∧ U n < sondowProjectLocalPudlakCollisionBox n :=
  (exactMinimalFieldPackageStatement_toInternalFiniteConsistencyLowerBoundMachine
      h hpartial).reflectionGraftGap_from_rescaled_field_gap_after_trace
    htransfer U hU N

end InternalPudlakTheorem5ProjectPowerBoundStatementMap

/-- Checked-code version of the theorem-5 power-bound lower bound.  This is the
next internalization target below the abstract `proof_length` statement: prove
that the audited checked length beats every polynomial, then identify global PA
symbol-size proof length with that checked length on the theorem-5 raw family. -/
abbrev InternalPudlakTheorem5CheckedPowerBoundLowerBound
    (_scale_data : InternalPudlakTheorem5ScaleData)
    (checkedLength : Nat → Nat) : Prop :=
  ∀ f : Nat → Real, _root_.is_polynomial_bound f →
    ∃ᶠ n in atTop, (checkedLength n : Real) > f n

/-- The checked-code lower-bound core.  This isolates the exact place where a
future internal proof-complexity argument must work: on concrete checked code
lengths for the theorem-5 power-bound raw formula family. -/
structure InternalPudlakTheorem5CheckedLowerBoundCore : Type where
  scale_data : InternalPudlakTheorem5ScaleData
  checkedLength : Nat → Nat
  checked_lower_bound :
    InternalPudlakTheorem5CheckedPowerBoundLowerBound
      scale_data checkedLength
  proof_length_exact :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode n) =
        (checkedLength n : Real)

namespace InternalPudlakTheorem5CheckedLowerBoundCore

theorem toPowerBoundLowerBound
    (core : InternalPudlakTheorem5CheckedLowerBoundCore) :
    core.scale_data.PowerBoundLowerBound where
  frequently_beats_every_polynomial := by
    intro f hf
    exact
      (core.checked_lower_bound f hf).mono
        (fun n hn => by
          have hexact :
              _root_.proof_length _root_.ProofSystem.PA
                  _root_.ProofLengthMeasure.symbolSize
                  (core.scale_data.toLiteratureScaleData.powerBoundRawCode n) =
                (core.checkedLength n : Real) := by
            simpa [InternalPudlakTheorem5ScaleData.powerBoundRawCode]
              using core.proof_length_exact n
          rw [hexact]
          exact hn)

def toLowerBoundCore
    (core : InternalPudlakTheorem5CheckedLowerBoundCore) :
    InternalPudlakTheorem5LowerBoundCore where
  scale_data := core.scale_data
  power_bound_lower_bound := core.toPowerBoundLowerBound

def toIntrinsicPowerBoundMachine
    (core : InternalPudlakTheorem5CheckedLowerBoundCore)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    IntrinsicPudlakTheorem5PowerBoundMachine :=
  core.toLowerBoundCore.toIntrinsicPowerBoundMachine hpartial

theorem toLowerBoundCore_scale_data_eq
    (core : InternalPudlakTheorem5CheckedLowerBoundCore) :
    core.toLowerBoundCore.scale_data = core.scale_data :=
  rfl

theorem toLowerBoundCore_power_bound_lower_bound_eq
    (core : InternalPudlakTheorem5CheckedLowerBoundCore) :
    core.toLowerBoundCore.power_bound_lower_bound =
      core.toPowerBoundLowerBound :=
  rfl

theorem toIntrinsicPowerBoundMachine_toCore
    (core : InternalPudlakTheorem5CheckedLowerBoundCore)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    InternalPudlakTheorem5LowerBoundCore.ofIntrinsicPowerBoundMachine
        (core.toIntrinsicPowerBoundMachine hpartial) =
      core.toLowerBoundCore := by
  rfl

theorem nonempty_to_lower_bound_core :
    Nonempty InternalPudlakTheorem5CheckedLowerBoundCore →
      Nonempty InternalPudlakTheorem5LowerBoundCore := by
  intro h
  rcases h with ⟨core⟩
  exact ⟨core.toLowerBoundCore⟩

def toInternalFiniteConsistencyLowerBoundMachine
    (core : InternalPudlakTheorem5CheckedLowerBoundCore)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    InternalFiniteConsistencyLowerBoundMachine :=
  core.toLowerBoundCore.toInternalFiniteConsistencyLowerBoundMachine hpartial

def toPudlakFiniteConsistencyLowerBoundPackage
    (core : InternalPudlakTheorem5CheckedLowerBoundCore)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    _root_.PudlakFiniteConsistencyLowerBoundPackage :=
  core.toLowerBoundCore.toPudlakFiniteConsistencyLowerBoundPackage hpartial

def toProjectCollisionInputs
    (core : InternalPudlakTheorem5CheckedLowerBoundCore)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    SondowProjectLocalPudlakCollisionInputs :=
  core.toLowerBoundCore.toProjectCollisionInputs
    project_upper hpartial htransfer

theorem toPudlakFiniteConsistencyLowerBoundPackage_eq_lower_core
    (core : InternalPudlakTheorem5CheckedLowerBoundCore)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    core.toPudlakFiniteConsistencyLowerBoundPackage hpartial =
      core.toLowerBoundCore.toPudlakFiniteConsistencyLowerBoundPackage
        hpartial :=
  rfl

theorem toProjectCollisionInputs_pudlak_lower_bound
    (core : InternalPudlakTheorem5CheckedLowerBoundCore)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    (core.toProjectCollisionInputs project_upper hpartial htransfer).pudlak_lower_bound =
      core.toPudlakFiniteConsistencyLowerBoundPackage hpartial :=
  rfl

def toProjectCollisionInputsOfConstantPieces
    (core : InternalPudlakTheorem5CheckedLowerBoundCore)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
    SondowProjectLocalPudlakCollisionInputs :=
  core.toLowerBoundCore.toProjectCollisionInputsOfConstantPieces
    project_upper strengthened_to_partial partial_to_graft

theorem toProjectCollisionInputsOfConstantPieces_pudlak_lower_bound
    (core : InternalPudlakTheorem5CheckedLowerBoundCore)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
    (core.toProjectCollisionInputsOfConstantPieces
        project_upper strengthened_to_partial partial_to_graft).pudlak_lower_bound =
      core.toPudlakFiniteConsistencyLowerBoundPackage
        (InternalPudlakTheorem5TransferPieces.strengthenedToPartialTransferOfConstant
          strengthened_to_partial) :=
  rfl

end InternalPudlakTheorem5CheckedLowerBoundCore

/-- Relevant-code predicate for the theorem-5 power-bound raw family.  A code
is relevant exactly when it is one of the raw theorem-5 finite-consistency
formulas at the power-bound scale. -/
def InternalPudlakTheorem5PowerBoundRelevantCode
    (scale_data : InternalPudlakTheorem5ScaleData)
    (code : _root_.FormulaCode) : Prop :=
  ∃ n : Nat, code = scale_data.powerBoundRawCode n

/-- Proof-code-semantics version of the theorem-5 lower-bound core.  This is
below checked lengths: the checked length is now the minimum accepted proof-code
size computed by a `ProofCodeSemantics` checker on the theorem-5 raw family. -/
structure InternalPudlakTheorem5ProofCodeSemanticsCore : Type (q + 1) where
  scale_data : InternalPudlakTheorem5ScaleData
  proof_code_semantics :
    _root_.ProofCodeSemantics.{q}
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)
  proof_code_lower_bound :
    ∀ f : Nat → Real, _root_.is_polynomial_bound f →
      ∃ᶠ n in atTop,
        (proof_code_semantics.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n
  proof_length_exact :
    ∀ code : _root_.FormulaCode,
      ∀ hcode : InternalPudlakTheorem5PowerBoundRelevantCode scale_data code,
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize code =
          (proof_code_semantics.minProofCodeSize code hcode : Real)

namespace InternalPudlakTheorem5ProofCodeSemanticsCore

noncomputable def checkedLength
    (core : InternalPudlakTheorem5ProofCodeSemanticsCore) :
    Nat → Nat :=
  fun n =>
    core.proof_code_semantics.minProofCodeSize
      (core.scale_data.powerBoundRawCode n) ⟨n, rfl⟩

theorem checkedLength_eq_minProofCodeSize
    (core : InternalPudlakTheorem5ProofCodeSemanticsCore) (n : Nat) :
    core.checkedLength n =
      core.proof_code_semantics.minProofCodeSize
        (core.scale_data.powerBoundRawCode n) ⟨n, rfl⟩ :=
  rfl

def toCheckedLowerBoundCore
    (core : InternalPudlakTheorem5ProofCodeSemanticsCore) :
    InternalPudlakTheorem5CheckedLowerBoundCore where
  scale_data := core.scale_data
  checkedLength := core.checkedLength
  checked_lower_bound := by
    intro f hf
    simpa [checkedLength] using core.proof_code_lower_bound f hf
  proof_length_exact := by
    intro n
    exact core.proof_length_exact
      (core.scale_data.powerBoundRawCode n) ⟨n, rfl⟩

def toLowerBoundCore
    (core : InternalPudlakTheorem5ProofCodeSemanticsCore) :
    InternalPudlakTheorem5LowerBoundCore :=
  core.toCheckedLowerBoundCore.toLowerBoundCore

theorem toCheckedLowerBoundCore_checkedLength_eq
    (core : InternalPudlakTheorem5ProofCodeSemanticsCore) :
    core.toCheckedLowerBoundCore.checkedLength =
      core.checkedLength :=
  rfl

theorem proof_length_exact_at_powerBoundRawCode
    (core : InternalPudlakTheorem5ProofCodeSemanticsCore) (n : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (core.scale_data.powerBoundRawCode n) =
      (core.checkedLength n : Real) :=
  core.toCheckedLowerBoundCore.proof_length_exact n

theorem nonempty_to_checked_lower_bound_core :
    Nonempty InternalPudlakTheorem5ProofCodeSemanticsCore →
      Nonempty InternalPudlakTheorem5CheckedLowerBoundCore := by
  intro h
  rcases h with ⟨core⟩
  exact ⟨core.toCheckedLowerBoundCore⟩

theorem nonempty_to_lower_bound_core :
    Nonempty InternalPudlakTheorem5ProofCodeSemanticsCore →
      Nonempty InternalPudlakTheorem5LowerBoundCore :=
  InternalPudlakTheorem5CheckedLowerBoundCore.nonempty_to_lower_bound_core ∘
    nonempty_to_checked_lower_bound_core

end InternalPudlakTheorem5ProofCodeSemanticsCore

/-- Proof-length-code-semantics version of the theorem-5 core.  Compared with
`InternalPudlakTheorem5ProofCodeSemanticsCore`, the exactness field is now the
standard `ProofLengthCodeSemantics.Calibration` used elsewhere in the project. -/
structure InternalPudlakTheorem5ProofLengthCodeSemanticsCore : Type (q + 1) where
  scale_data : InternalPudlakTheorem5ScaleData
  proof_length_model :
    _root_.ProofLengthCodeSemantics.{q}
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)
  proof_code_lower_bound :
    ∀ f : Nat → Real, _root_.is_polynomial_bound f →
      ∃ᶠ n in atTop,
        (proof_length_model.proof_code_semantics.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n
  calibration : proof_length_model.Calibration

namespace InternalPudlakTheorem5ProofLengthCodeSemanticsCore

def proof_code_semantics
    (core : InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q}) :
    _root_.ProofCodeSemantics.{q}
      (InternalPudlakTheorem5PowerBoundRelevantCode core.scale_data) :=
  core.proof_length_model.proof_code_semantics

theorem project_length_eq_minProofCodeSize
    (core : InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q})
    (code : _root_.FormulaCode)
    (hcode : InternalPudlakTheorem5PowerBoundRelevantCode
      core.scale_data code) :
    core.proof_length_model.length code =
      core.proof_code_semantics.minProofCodeSize code hcode := by
  simp [_root_.ProofLengthCodeSemantics.length,
    proof_code_semantics,
    _root_.ProofCodeSemantics.semanticProofLength_eq_minProofCodeSize
      core.proof_length_model.proof_code_semantics
      core.proof_length_model.fallback_length hcode]

theorem proof_length_eq_minProofCodeSize
    (core : InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q})
    (code : _root_.FormulaCode)
    (hcode : InternalPudlakTheorem5PowerBoundRelevantCode
      core.scale_data code) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize code =
      (core.proof_code_semantics.minProofCodeSize code hcode : Real) := by
  rw [core.calibration.proof_length_eq_length code hcode]
  exact_mod_cast core.project_length_eq_minProofCodeSize code hcode

def toProofCodeSemanticsCore
    (core : InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q}) :
    InternalPudlakTheorem5ProofCodeSemanticsCore.{q} where
  scale_data := core.scale_data
  proof_code_semantics := core.proof_code_semantics
  proof_code_lower_bound := core.proof_code_lower_bound
  proof_length_exact := core.proof_length_eq_minProofCodeSize

def toCheckedLowerBoundCore
    (core : InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q}) :
    InternalPudlakTheorem5CheckedLowerBoundCore :=
  core.toProofCodeSemanticsCore.toCheckedLowerBoundCore

def toLowerBoundCore
    (core : InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q}) :
    InternalPudlakTheorem5LowerBoundCore :=
  core.toProofCodeSemanticsCore.toLowerBoundCore

theorem toProofCodeSemanticsCore_scale_data_eq
    (core : InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q}) :
    core.toProofCodeSemanticsCore.scale_data = core.scale_data :=
  rfl

theorem toProofCodeSemanticsCore_checkedLength_eq_minProofCodeSize
    (core : InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q})
    (n : Nat) :
    core.toProofCodeSemanticsCore.checkedLength n =
      core.proof_code_semantics.minProofCodeSize
        (core.scale_data.powerBoundRawCode n) ⟨n, rfl⟩ :=
  rfl

theorem nonempty_to_proof_code_semantics_core :
    Nonempty InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q} →
      Nonempty InternalPudlakTheorem5ProofCodeSemanticsCore.{q} := by
  intro h
  rcases h with ⟨core⟩
  exact ⟨core.toProofCodeSemanticsCore⟩

theorem nonempty_to_lower_bound_core :
    Nonempty InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q} →
      Nonempty InternalPudlakTheorem5LowerBoundCore :=
  InternalPudlakTheorem5ProofCodeSemanticsCore.nonempty_to_lower_bound_core ∘
    nonempty_to_proof_code_semantics_core

end InternalPudlakTheorem5ProofLengthCodeSemanticsCore

/-- No-small-proof-code form of the theorem-5 lower-bound task.  This is the
usual counting frontier: for every polynomial bound, frequently every accepted
proof code for the theorem-5 raw formula has size above that bound. -/
abbrev InternalPudlakTheorem5NoSmallProofCodes
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) : Prop :=
  ∀ f : Nat → Real, _root_.is_polynomial_bound f →
    ∃ᶠ n in atTop,
      ∀ c : sem.Code,
        sem.checks c (scale_data.powerBoundRawCode n) →
          f n < (sem.size c : Real)

namespace InternalPudlakTheorem5NoSmallProofCodes

theorem toProofCodeLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (hno : InternalPudlakTheorem5NoSmallProofCodes scale_data sem) :
    ∀ f : Nat → Real, _root_.is_polynomial_bound f →
      ∃ᶠ n in atTop,
        (sem.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n := by
  intro f hf
  exact
    (hno f hf).mono
      (fun n hsmall => by
        rcases sem.hasProofCodeOfSize_minProofCodeSize
            (code := scale_data.powerBoundRawCode n) ⟨n, rfl⟩ with
          ⟨c, hchecks, hsize_le⟩
        have hlt_size : f n < (sem.size c : Real) :=
          hsmall c hchecks
        have hsize_le_min :
            (sem.size c : Real) ≤
              (sem.minProofCodeSize
                (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) := by
          exact_mod_cast hsize_le
        exact lt_of_lt_of_le hlt_size hsize_le_min)

end InternalPudlakTheorem5NoSmallProofCodes

/-- A finite-search interface for small proof codes.  For each formula index
`n` and size cutoff `K`, `candidates n K` is an auditable finite list that is
complete for all accepted proof codes of size `< K`. -/
structure InternalPudlakTheorem5SmallCodeSearch
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    Type (q + 1) where
  candidates : Nat → Nat → List sem.Code
  complete :
    ∀ n K : Nat, ∀ c : sem.Code,
      sem.checks c (scale_data.powerBoundRawCode n) →
        sem.size c < K →
          c ∈ candidates n K

/-- Finite-search version of the theorem-5 no-small-code task.  For every
polynomial bound, frequently there is a cutoff `K > f n` such that every
candidate in the finite search list is rejected by the checker. -/
abbrev InternalPudlakTheorem5FiniteSearchExclusion
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (search : InternalPudlakTheorem5SmallCodeSearch scale_data sem) : Prop :=
  ∀ f : Nat → Real, _root_.is_polynomial_bound f →
    ∃ᶠ n in atTop,
      ∃ K : Nat,
        f n < (K : Real) ∧
          ∀ c : sem.Code, c ∈ search.candidates n K →
            ¬ sem.checks c (scale_data.powerBoundRawCode n)

namespace InternalPudlakTheorem5FiniteSearchExclusion

theorem toNoSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (hexcl :
      InternalPudlakTheorem5FiniteSearchExclusion scale_data sem search) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data sem := by
  intro f hf
  exact
    (hexcl f hf).mono
      (fun n hn c hchecks => by
        rcases hn with ⟨K, hf_lt_K, hrejected⟩
        by_contra hnot_lt
        have hsize_le_f : (sem.size c : Real) ≤ f n :=
          le_of_not_gt hnot_lt
        have hsize_lt_K_real : (sem.size c : Real) < (K : Real) :=
          lt_of_le_of_lt hsize_le_f hf_lt_K
        have hsize_lt_K : sem.size c < K := by
          exact_mod_cast hsize_lt_K_real
        have hmem : c ∈ search.candidates n K :=
          search.complete n K c hchecks hsize_lt_K
        exact (hrejected c hmem hchecks))

end InternalPudlakTheorem5FiniteSearchExclusion

/-- The theorem-5 proof-length-code core with the lower-bound field expressed
as a no-small-proof-code/counting statement.  This is narrower than a direct
`proof_code_lower_bound` field and is the next real target for internalizing
Pudlak's proof-complexity argument. -/
structure InternalPudlakTheorem5NoSmallCodeSemanticsCore : Type (q + 1) where
  scale_data : InternalPudlakTheorem5ScaleData
  proof_length_model :
    _root_.ProofLengthCodeSemantics.{q}
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)
  no_small_proof_codes :
    InternalPudlakTheorem5NoSmallProofCodes
      scale_data proof_length_model.proof_code_semantics
  calibration : proof_length_model.Calibration

namespace InternalPudlakTheorem5NoSmallCodeSemanticsCore

def proof_code_semantics
    (core : InternalPudlakTheorem5NoSmallCodeSemanticsCore.{q}) :
    _root_.ProofCodeSemantics.{q}
      (InternalPudlakTheorem5PowerBoundRelevantCode core.scale_data) :=
  core.proof_length_model.proof_code_semantics

theorem proof_code_lower_bound
    (core : InternalPudlakTheorem5NoSmallCodeSemanticsCore.{q}) :
    ∀ f : Nat → Real, _root_.is_polynomial_bound f →
      ∃ᶠ n in atTop,
        (core.proof_code_semantics.minProofCodeSize
          (core.scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n :=
  InternalPudlakTheorem5NoSmallProofCodes.toProofCodeLowerBound
    core.no_small_proof_codes

def toProofLengthCodeSemanticsCore
    (core : InternalPudlakTheorem5NoSmallCodeSemanticsCore.{q}) :
    InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q} where
  scale_data := core.scale_data
  proof_length_model := core.proof_length_model
  proof_code_lower_bound := core.proof_code_lower_bound
  calibration := core.calibration

def toProofCodeSemanticsCore
    (core : InternalPudlakTheorem5NoSmallCodeSemanticsCore.{q}) :
    InternalPudlakTheorem5ProofCodeSemanticsCore.{q} :=
  core.toProofLengthCodeSemanticsCore.toProofCodeSemanticsCore

def toLowerBoundCore
    (core : InternalPudlakTheorem5NoSmallCodeSemanticsCore.{q}) :
    InternalPudlakTheorem5LowerBoundCore :=
  core.toProofLengthCodeSemanticsCore.toLowerBoundCore

theorem toProofLengthCodeSemanticsCore_model_eq
    (core : InternalPudlakTheorem5NoSmallCodeSemanticsCore.{q}) :
    core.toProofLengthCodeSemanticsCore.proof_length_model =
      core.proof_length_model :=
  rfl

theorem toProofLengthCodeSemanticsCore_lower_bound_eq
    (core : InternalPudlakTheorem5NoSmallCodeSemanticsCore.{q}) :
    core.toProofLengthCodeSemanticsCore.proof_code_lower_bound =
      core.proof_code_lower_bound :=
  rfl

theorem nonempty_to_proof_length_code_semantics_core :
    Nonempty InternalPudlakTheorem5NoSmallCodeSemanticsCore.{q} →
      Nonempty InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q} := by
  intro h
  rcases h with ⟨core⟩
  exact ⟨core.toProofLengthCodeSemanticsCore⟩

theorem nonempty_to_lower_bound_core :
    Nonempty InternalPudlakTheorem5NoSmallCodeSemanticsCore.{q} →
      Nonempty InternalPudlakTheorem5LowerBoundCore :=
  InternalPudlakTheorem5ProofLengthCodeSemanticsCore.nonempty_to_lower_bound_core ∘
    nonempty_to_proof_length_code_semantics_core

end InternalPudlakTheorem5NoSmallCodeSemanticsCore

/-- Finite-search/counting version of the theorem-5 no-small-code core.  This
is the next proof target below `NoSmallCodeSemanticsCore`: an actual checker
only has to enumerate all proof codes below a cutoff and prove that every
enumerated candidate is rejected. -/
structure InternalPudlakTheorem5FiniteSearchNoSmallCore : Type (q + 1) where
  scale_data : InternalPudlakTheorem5ScaleData
  proof_length_model :
    _root_.ProofLengthCodeSemantics.{q}
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)
  small_code_search :
    InternalPudlakTheorem5SmallCodeSearch
      scale_data proof_length_model.proof_code_semantics
  finite_search_exclusion :
    InternalPudlakTheorem5FiniteSearchExclusion
      scale_data proof_length_model.proof_code_semantics small_code_search
  calibration : proof_length_model.Calibration

namespace InternalPudlakTheorem5FiniteSearchNoSmallCore

def proof_code_semantics
    (core : InternalPudlakTheorem5FiniteSearchNoSmallCore.{q}) :
    _root_.ProofCodeSemantics.{q}
      (InternalPudlakTheorem5PowerBoundRelevantCode core.scale_data) :=
  core.proof_length_model.proof_code_semantics

theorem no_small_proof_codes
    (core : InternalPudlakTheorem5FiniteSearchNoSmallCore.{q}) :
    InternalPudlakTheorem5NoSmallProofCodes
      core.scale_data core.proof_code_semantics :=
  InternalPudlakTheorem5FiniteSearchExclusion.toNoSmallProofCodes
    core.finite_search_exclusion

def toNoSmallCodeSemanticsCore
    (core : InternalPudlakTheorem5FiniteSearchNoSmallCore.{q}) :
    InternalPudlakTheorem5NoSmallCodeSemanticsCore.{q} where
  scale_data := core.scale_data
  proof_length_model := core.proof_length_model
  no_small_proof_codes := core.no_small_proof_codes
  calibration := core.calibration

def toProofLengthCodeSemanticsCore
    (core : InternalPudlakTheorem5FiniteSearchNoSmallCore.{q}) :
    InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q} :=
  core.toNoSmallCodeSemanticsCore.toProofLengthCodeSemanticsCore

def toLowerBoundCore
    (core : InternalPudlakTheorem5FiniteSearchNoSmallCore.{q}) :
    InternalPudlakTheorem5LowerBoundCore :=
  core.toProofLengthCodeSemanticsCore.toLowerBoundCore

theorem toNoSmallCodeSemanticsCore_model_eq
    (core : InternalPudlakTheorem5FiniteSearchNoSmallCore.{q}) :
    core.toNoSmallCodeSemanticsCore.proof_length_model =
      core.proof_length_model :=
  rfl

theorem finite_search_exclusion_to_no_small
    (core : InternalPudlakTheorem5FiniteSearchNoSmallCore.{q}) :
    core.toNoSmallCodeSemanticsCore.no_small_proof_codes =
      core.no_small_proof_codes :=
  rfl

theorem nonempty_to_no_small_code_semantics_core :
    Nonempty InternalPudlakTheorem5FiniteSearchNoSmallCore.{q} →
      Nonempty InternalPudlakTheorem5NoSmallCodeSemanticsCore.{q} := by
  intro h
  rcases h with ⟨core⟩
  exact ⟨core.toNoSmallCodeSemanticsCore⟩

theorem nonempty_to_lower_bound_core :
    Nonempty InternalPudlakTheorem5FiniteSearchNoSmallCore.{q} →
      Nonempty InternalPudlakTheorem5LowerBoundCore :=
  InternalPudlakTheorem5NoSmallCodeSemanticsCore.nonempty_to_lower_bound_core ∘
    nonempty_to_no_small_code_semantics_core

end InternalPudlakTheorem5FiniteSearchNoSmallCore

/-- Computable finite-search exclusion.  Instead of a bare `∃ᶠ`, this stores a
witness extractor: for every polynomial bound and every lower threshold `N`, it
returns a concrete index `n ≥ N`, a cutoff `K`, and a finite rejection proof for
all enumerated candidate proof codes below `K`. -/
structure InternalPudlakTheorem5ComputableFiniteSearchExclusion
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (search : InternalPudlakTheorem5SmallCodeSearch scale_data sem) :
    Type (q + 1) where
  witness : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  cutoff : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  witness_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ witness f hf N
  cutoff_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (witness f hf N) < (cutoff f hf N : Real)
  rejects_candidates :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      ∀ c : sem.Code, c ∈ search.candidates (witness f hf N) (cutoff f hf N) →
        ¬ sem.checks c (scale_data.powerBoundRawCode (witness f hf N))

/-- A concrete lower-search witness extracted from the computable theorem-5
search certificate for a specific polynomial bound `f` and lower threshold
`N`.  It stores the searched index, the finite cutoff, the candidate rejection
proof at that index, and the resulting `minProofCodeSize` inequality. -/
structure InternalPudlakTheorem5ComputedLowerSearchWitness
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (search : InternalPudlakTheorem5SmallCodeSearch scale_data sem)
    (f : Nat → Real) (_hf : _root_.is_polynomial_bound f) (N : Nat) :
    Type (q + 1) where
  n : Nat
  K : Nat
  n_ge : N ≤ n
  cutoff_gt : f n < (K : Real)
  rejects_candidates :
    ∀ c : sem.Code, c ∈ search.candidates n K →
      ¬ sem.checks c (scale_data.powerBoundRawCode n)
  no_small_at_n :
    ∀ c : sem.Code, sem.checks c (scale_data.powerBoundRawCode n) →
      f n < (sem.size c : Real)
  minProofCodeSize_gt :
    (sem.minProofCodeSize (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ :
      Real) > f n

/-- Exact same-object calibration between the theorem-5 proof-code checker and
the project collision box.  This is intentionally an explicit residual
certificate: without it, a lower-search witness for `powerBoundRawCode n` cannot
honestly be read as a gap for `sondowProjectLocalPudlakCollisionBox n`. -/
structure InternalPudlakTheorem5ProjectBoxAlignment
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    Type (q + 1) where
  project_box_eq_minProofCodeSize :
    ∀ n : Nat,
      sondowProjectLocalPudlakCollisionBox n =
        (sem.minProofCodeSize (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ :
          Real)

namespace InternalPudlakTheorem5ProjectBoxAlignment

theorem project_box_gt_of_lower_search
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    {U : Nat → Real} {hU : _root_.is_polynomial_bound U} {N : Nat}
    (align : InternalPudlakTheorem5ProjectBoxAlignment scale_data sem)
    (w :
      InternalPudlakTheorem5ComputedLowerSearchWitness
        scale_data sem search U hU N) :
    U w.n < sondowProjectLocalPudlakCollisionBox w.n := by
  rw [align.project_box_eq_minProofCodeSize w.n]
  exact w.minProofCodeSize_gt

end InternalPudlakTheorem5ProjectBoxAlignment

namespace InternalPudlakTheorem5ComputableFiniteSearchExclusion

theorem noSmallAtWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    ∀ c : sem.Code,
      sem.checks c (scale_data.powerBoundRawCode (cert.witness f hf N)) →
        f (cert.witness f hf N) < (sem.size c : Real) := by
  intro c hchecks
  by_contra hnot_lt
  have hsize_le_f : (sem.size c : Real) ≤ f (cert.witness f hf N) :=
    le_of_not_gt hnot_lt
  have hsize_lt_K_real :
      (sem.size c : Real) < (cert.cutoff f hf N : Real) :=
    lt_of_le_of_lt hsize_le_f (cert.cutoff_gt f hf N)
  have hsize_lt_K : sem.size c < cert.cutoff f hf N := by
    exact_mod_cast hsize_lt_K_real
  have hmem :
      c ∈ search.candidates (cert.witness f hf N) (cert.cutoff f hf N) :=
    search.complete (cert.witness f hf N) (cert.cutoff f hf N)
      c hchecks hsize_lt_K
  exact (cert.rejects_candidates f hf N c hmem hchecks)

theorem minProofCodeSize_gt_at_witness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    (sem.minProofCodeSize
      (scale_data.powerBoundRawCode (cert.witness f hf N))
      ⟨cert.witness f hf N, rfl⟩ : Real) >
      f (cert.witness f hf N) := by
  rcases sem.hasProofCodeOfSize_minProofCodeSize
      (code := scale_data.powerBoundRawCode (cert.witness f hf N))
      ⟨cert.witness f hf N, rfl⟩ with
    ⟨c, hchecks, hsize_le⟩
  have hlt_size :
      f (cert.witness f hf N) < (sem.size c : Real) :=
    cert.noSmallAtWitness f hf N c hchecks
  have hsize_le_min :
      (sem.size c : Real) ≤
        (sem.minProofCodeSize
          (scale_data.powerBoundRawCode (cert.witness f hf N))
          ⟨cert.witness f hf N, rfl⟩ : Real) := by
    exact_mod_cast hsize_le
  exact lt_of_lt_of_le hlt_size hsize_le_min

def computedLowerSearchWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    InternalPudlakTheorem5ComputedLowerSearchWitness
      scale_data sem search f hf N where
  n := cert.witness f hf N
  K := cert.cutoff f hf N
  n_ge := cert.witness_ge f hf N
  cutoff_gt := cert.cutoff_gt f hf N
  rejects_candidates := fun c hmem =>
    cert.rejects_candidates f hf N c hmem
  no_small_at_n := cert.noSmallAtWitness f hf N
  minProofCodeSize_gt := cert.minProofCodeSize_gt_at_witness f hf N

theorem computedLowerSearchWitness_full_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    let w := cert.computedLowerSearchWitness f hf N
    w.n = cert.witness f hf N ∧
      w.K = cert.cutoff f hf N ∧
      N ≤ w.n ∧
      f w.n < (w.K : Real) ∧
      (∀ c : sem.Code, c ∈ search.candidates w.n w.K →
        ¬ sem.checks c (scale_data.powerBoundRawCode w.n)) ∧
      (∀ c : sem.Code, sem.checks c (scale_data.powerBoundRawCode w.n) →
        f w.n < (sem.size c : Real)) ∧
      (sem.minProofCodeSize (scale_data.powerBoundRawCode w.n)
        ⟨w.n, rfl⟩ : Real) > f w.n := by
  dsimp [computedLowerSearchWitness]
  exact
    ⟨rfl, rfl,
      cert.witness_ge f hf N,
      cert.cutoff_gt f hf N,
      fun c hmem => cert.rejects_candidates f hf N c hmem,
      cert.noSmallAtWitness f hf N,
      cert.minProofCodeSize_gt_at_witness f hf N⟩

theorem toFiniteSearchExclusion
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search) :
    InternalPudlakTheorem5FiniteSearchExclusion scale_data sem search := by
  intro f hf
  exact
    Filter.frequently_atTop.2
      (fun N =>
        ⟨cert.witness f hf N,
          cert.witness_ge f hf N,
          cert.cutoff f hf N,
          cert.cutoff_gt f hf N,
          fun c hmem => cert.rejects_candidates f hf N c hmem⟩)

theorem toNoSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data sem :=
  cert.toFiniteSearchExclusion.toNoSmallProofCodes

end InternalPudlakTheorem5ComputableFiniteSearchExclusion

/-- Computable version of the finite-search no-small-code core.  This is the
first internal theorem-5 surface where the proof-complexity witness is not just
an existence/frequency statement: it carries an explicit extractor for the
lower-bound index used against an upper threshold. -/
structure InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore :
    Type (q + 1) where
  scale_data : InternalPudlakTheorem5ScaleData
  proof_length_model :
    _root_.ProofLengthCodeSemantics.{q}
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)
  small_code_search :
    InternalPudlakTheorem5SmallCodeSearch
      scale_data proof_length_model.proof_code_semantics
  computable_search_exclusion :
    InternalPudlakTheorem5ComputableFiniteSearchExclusion
      scale_data proof_length_model.proof_code_semantics small_code_search
  calibration : proof_length_model.Calibration

namespace InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore

def proof_code_semantics
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}) :
    _root_.ProofCodeSemantics.{q}
      (InternalPudlakTheorem5PowerBoundRelevantCode core.scale_data) :=
  core.proof_length_model.proof_code_semantics

theorem finite_search_exclusion
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}) :
    InternalPudlakTheorem5FiniteSearchExclusion
      core.scale_data core.proof_code_semantics core.small_code_search :=
  core.computable_search_exclusion.toFiniteSearchExclusion

theorem no_small_proof_codes
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}) :
    InternalPudlakTheorem5NoSmallProofCodes
      core.scale_data core.proof_code_semantics :=
  core.computable_search_exclusion.toNoSmallProofCodes

def toFiniteSearchNoSmallCore
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}) :
    InternalPudlakTheorem5FiniteSearchNoSmallCore.{q} where
  scale_data := core.scale_data
  proof_length_model := core.proof_length_model
  small_code_search := core.small_code_search
  finite_search_exclusion := core.finite_search_exclusion
  calibration := core.calibration

def toNoSmallCodeSemanticsCore
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}) :
    InternalPudlakTheorem5NoSmallCodeSemanticsCore.{q} :=
  core.toFiniteSearchNoSmallCore.toNoSmallCodeSemanticsCore

def toProofLengthCodeSemanticsCore
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}) :
    InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q} :=
  core.toNoSmallCodeSemanticsCore.toProofLengthCodeSemanticsCore

def toLowerBoundCore
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}) :
    InternalPudlakTheorem5LowerBoundCore :=
  core.toProofLengthCodeSemanticsCore.toLowerBoundCore

theorem witness_ge
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    N ≤ core.computable_search_exclusion.witness f hf N :=
  core.computable_search_exclusion.witness_ge f hf N

theorem cutoff_gt_at_witness
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    f (core.computable_search_exclusion.witness f hf N) <
      (core.computable_search_exclusion.cutoff f hf N : Real) :=
  core.computable_search_exclusion.cutoff_gt f hf N

theorem rejects_candidates_at_witness
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat)
    (c : core.proof_code_semantics.Code)
    (hmem :
      c ∈ core.small_code_search.candidates
        (core.computable_search_exclusion.witness f hf N)
        (core.computable_search_exclusion.cutoff f hf N)) :
    ¬ core.proof_code_semantics.checks c
      (core.scale_data.powerBoundRawCode
        (core.computable_search_exclusion.witness f hf N)) :=
  core.computable_search_exclusion.rejects_candidates f hf N c hmem

theorem proof_length_gt_at_computedLowerSearchWitness
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    let w :=
      core.computable_search_exclusion
        |>.computedLowerSearchWitness f hf N
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (core.scale_data.powerBoundRawCode w.n) > f w.n := by
  let w :=
    core.computable_search_exclusion
      |>.computedLowerSearchWitness f hf N
  have hexact :
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (core.scale_data.powerBoundRawCode w.n) =
        (core.proof_code_semantics.minProofCodeSize
          (core.scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩ : Real) :=
    core.toProofLengthCodeSemanticsCore.proof_length_eq_minProofCodeSize
      (core.scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩
  change
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (core.scale_data.powerBoundRawCode w.n) > f w.n
  rw [hexact]
  exact w.minProofCodeSize_gt

theorem toPowerBoundLowerBound_direct
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}) :
    core.scale_data.PowerBoundLowerBound where
  frequently_beats_every_polynomial := by
    intro f hf
    refine Filter.frequently_atTop.2 ?_
    intro N
    let w :=
      core.computable_search_exclusion
        |>.computedLowerSearchWitness f hf N
    refine ⟨w.n, w.n_ge, ?_⟩
    simpa [InternalPudlakTheorem5ScaleData.powerBoundRawCode] using
      core.proof_length_gt_at_computedLowerSearchWitness f hf N

theorem toPowerBoundLowerBound_direct_eq_wrapped
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}) :
    core.toPowerBoundLowerBound_direct =
      core.toLowerBoundCore.power_bound_lower_bound := by
  rfl

theorem toRescaledLowerBound_direct
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}) :
    _root_.StrongRescaledExternalStrengthenedLowerBound
      core.scale_data.rawCode core.scale_data.scale :=
  core.scale_data.powerBoundLowerBound_to_rescaledLowerBound
    core.toPowerBoundLowerBound_direct

def toLowerBoundCore_direct
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}) :
    InternalPudlakTheorem5LowerBoundCore where
  scale_data := core.scale_data
  power_bound_lower_bound := core.toPowerBoundLowerBound_direct

theorem toLowerBoundCore_direct_eq_wrapped
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}) :
    core.toLowerBoundCore_direct = core.toLowerBoundCore := by
  rfl

def toIntrinsicPowerBoundMachine_direct
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    IntrinsicPudlakTheorem5PowerBoundMachine where
  scale_data := core.scale_data
  power_bound_lower_bound := core.toPowerBoundLowerBound_direct
  strengthened_to_partial := hpartial

theorem toIntrinsicPowerBoundMachine_direct_eq_wrapped
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    core.toIntrinsicPowerBoundMachine_direct hpartial =
      core.toLowerBoundCore.toIntrinsicPowerBoundMachine hpartial := by
  rfl

def toInternalFiniteConsistencyLowerBoundMachine_direct
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    InternalFiniteConsistencyLowerBoundMachine :=
  (core.toIntrinsicPowerBoundMachine_direct hpartial)
    |>.toInternalFiniteConsistencyLowerBoundMachine

theorem toInternalFiniteConsistencyLowerBoundMachine_direct_eq_wrapped
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    core.toInternalFiniteConsistencyLowerBoundMachine_direct hpartial =
      core.toLowerBoundCore.toInternalFiniteConsistencyLowerBoundMachine
        hpartial := by
  rfl

theorem direct_internal_machine_gap_after_trace
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ∃ g : Nat → Real,
      _root_.is_polynomial_bound g ∧
        ∃ n : Nat, N ≤ n ∧ U n < sondowProjectLocalPudlakCollisionBox n :=
  (core.toInternalFiniteConsistencyLowerBoundMachine_direct hpartial)
    |>.reflectionGraftGap_from_rescaled_field_gap_after_trace
      htransfer U hU N

theorem nonempty_to_finite_search_no_small_core :
    Nonempty InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} →
      Nonempty InternalPudlakTheorem5FiniteSearchNoSmallCore.{q} := by
  intro h
  rcases h with ⟨core⟩
  exact ⟨core.toFiniteSearchNoSmallCore⟩

theorem nonempty_to_lower_bound_core :
    Nonempty InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} →
      Nonempty InternalPudlakTheorem5LowerBoundCore :=
  InternalPudlakTheorem5FiniteSearchNoSmallCore.nonempty_to_lower_bound_core ∘
    nonempty_to_finite_search_no_small_core

end InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore

/-- A tail-form strict gap.  Unlike `EventualStrictGap`, this certificate
stores a threshold, so the final contradiction witness is the computable
number `max upperN threshold`. -/
structure TailStrictGapCertificate (U L : Nat → Real) : Type where
  threshold : Nat
  strict_after : ∀ n : Nat, threshold ≤ n → U n < L n

namespace TailStrictGapCertificate

variable {U measured : Nat → Real}

def witness (gap : TailStrictGapCertificate U measured) (upperN : Nat) : Nat :=
  max upperN gap.threshold

theorem witness_ge_upper
    (gap : TailStrictGapCertificate U measured) (upperN : Nat) :
    upperN ≤ gap.witness upperN := by
  exact Nat.le_max_left upperN gap.threshold

theorem witness_ge_gap
    (gap : TailStrictGapCertificate U measured) (upperN : Nat) :
    gap.threshold ≤ gap.witness upperN := by
  exact Nat.le_max_right upperN gap.threshold

theorem strict_at_witness
    (gap : TailStrictGapCertificate U measured) (upperN : Nat) :
    U (gap.witness upperN) < measured (gap.witness upperN) :=
  gap.strict_after (gap.witness upperN) (gap.witness_ge_gap upperN)

def toEventualStrictGap
    (gap : TailStrictGapCertificate U measured) :
    _root_.EventualStrictGap U measured where
  gap_after := by
    intro N
    exact
      ⟨gap.witness N, gap.witness_ge_upper N,
        gap.strict_at_witness N⟩

noncomputable def ofEventuallyAtTop
    (h : ∀ᶠ n in Filter.atTop, U n < measured n) :
    TailStrictGapCertificate U measured where
  threshold := Classical.choose (Filter.eventually_atTop.mp h)
  strict_after := by
    intro n hn
    exact (Classical.choose_spec (Filter.eventually_atTop.mp h)) n hn

theorem ofEventuallyAtTop_strict_after
    (h : ∀ᶠ n in Filter.atTop, U n < measured n)
    (n : Nat)
    (hn : (ofEventuallyAtTop h).threshold ≤ n) :
    U n < measured n :=
  (ofEventuallyAtTop h).strict_after n hn

theorem computed_witness_contradiction
    (gap : TailStrictGapCertificate U measured)
    (upperN : Nat)
    (hupper : ∀ n : Nat, upperN ≤ n → measured n ≤ U n) :
    False := by
  exact
    (not_lt_of_ge
      (hupper (gap.witness upperN) (gap.witness_ge_upper upperN)))
      (gap.strict_at_witness upperN)

end TailStrictGapCertificate

/-- Search-form strict gap.  This is weaker and closer to proof-complexity
lower bounds than a tail gap: for every requested lower threshold `N`, it
computes a witness `n ≥ N` where `U n < measured n`. -/
structure SearchStrictGapCertificate (U measured : Nat → Real) : Type where
  witness : Nat → Nat
  witness_ge : ∀ N : Nat, N ≤ witness N
  strict_at_witness : ∀ N : Nat, U (witness N) < measured (witness N)

namespace SearchStrictGapCertificate

variable {U measured : Nat → Real}

def toEventualStrictGap
    (gap : SearchStrictGapCertificate U measured) :
    _root_.EventualStrictGap U measured where
  gap_after := by
    intro N
    exact ⟨gap.witness N, gap.witness_ge N, gap.strict_at_witness N⟩

theorem computed_witness_contradiction
    (gap : SearchStrictGapCertificate U measured)
    (upperN : Nat)
    (hupper : ∀ n : Nat, upperN ≤ n → measured n ≤ U n) :
    False := by
  exact
    (not_lt_of_ge
      (hupper (gap.witness upperN) (gap.witness_ge upperN)))
      (gap.strict_at_witness upperN)

end SearchStrictGapCertificate

/-- A computed collision witness driven by a search-style lower gap.  The final
index is the lower search result for the upper route's threshold, not a `max`
of two tail thresholds. -/
structure ComputedSearchCollisionWitness (U measured : Nat → Real) : Type where
  upperN : Nat
  n : Nat
  n_ge_upper : upperN ≤ n
  upper_at_n : measured n ≤ U n
  lower_at_n : U n < measured n

namespace ComputedSearchCollisionWitness

variable {U measured : Nat → Real}

theorem contradiction
    (witness : ComputedSearchCollisionWitness U measured) :
    False :=
  (not_lt_of_ge witness.upper_at_n) witness.lower_at_n

end ComputedSearchCollisionWitness

namespace SearchStrictGapCertificate

variable {U measured : Nat → Real}

def toComputedSearchCollisionWitness
    (gap : SearchStrictGapCertificate U measured)
    (upperN : Nat)
    (hupper : ∀ n : Nat, upperN ≤ n → measured n ≤ U n) :
    ComputedSearchCollisionWitness U measured where
  upperN := upperN
  n := gap.witness upperN
  n_ge_upper := gap.witness_ge upperN
  upper_at_n := hupper (gap.witness upperN) (gap.witness_ge upperN)
  lower_at_n := gap.strict_at_witness upperN

theorem toComputedSearchCollisionWitness_n_eq
    (gap : SearchStrictGapCertificate U measured)
    (upperN : Nat)
    (hupper : ∀ n : Nat, upperN ≤ n → measured n ≤ U n) :
    (gap.toComputedSearchCollisionWitness upperN hupper).n =
      gap.witness upperN :=
  rfl

theorem toComputedSearchCollisionWitness_contradiction
    (gap : SearchStrictGapCertificate U measured)
    (upperN : Nat)
    (hupper : ∀ n : Nat, upperN ≤ n → measured n ≤ U n) :
    False :=
  (gap.toComputedSearchCollisionWitness upperN hupper).contradiction

end SearchStrictGapCertificate

namespace TailStrictGapCertificate

variable {U measured : Nat → Real}

def toSearchStrictGapCertificate
    (gap : TailStrictGapCertificate U measured) :
    SearchStrictGapCertificate U measured where
  witness := gap.witness
  witness_ge := gap.witness_ge_upper
  strict_at_witness := gap.strict_at_witness

end TailStrictGapCertificate

namespace InternalPudlakTheorem5ProjectBoxAlignment

def toSearchStrictGapCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (align : InternalPudlakTheorem5ProjectBoxAlignment scale_data sem)
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) :
    SearchStrictGapCertificate U sondowProjectLocalPudlakCollisionBox where
  witness := fun N => (cert.computedLowerSearchWitness U hU N).n
  witness_ge := fun N => (cert.computedLowerSearchWitness U hU N).n_ge
  strict_at_witness := fun N =>
    align.project_box_gt_of_lower_search
      (cert.computedLowerSearchWitness U hU N)

theorem toSearchStrictGapCertificate_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (align : InternalPudlakTheorem5ProjectBoxAlignment scale_data sem)
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (align.toSearchStrictGapCertificate cert U hU).witness N =
      (cert.computedLowerSearchWitness U hU N).n :=
  rfl

theorem computed_project_lower_search_full_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (align : InternalPudlakTheorem5ProjectBoxAlignment scale_data sem)
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    let w := cert.computedLowerSearchWitness U hU N
    w.n = cert.witness U hU N ∧
      w.K = cert.cutoff U hU N ∧
      N ≤ w.n ∧
      U w.n < (w.K : Real) ∧
      (∀ c : sem.Code, c ∈ search.candidates w.n w.K →
        ¬ sem.checks c (scale_data.powerBoundRawCode w.n)) ∧
      (∀ c : sem.Code, sem.checks c (scale_data.powerBoundRawCode w.n) →
        U w.n < (sem.size c : Real)) ∧
      (sem.minProofCodeSize (scale_data.powerBoundRawCode w.n)
        ⟨w.n, rfl⟩ : Real) > U w.n ∧
      U w.n < sondowProjectLocalPudlakCollisionBox w.n := by
  dsimp [InternalPudlakTheorem5ComputableFiniteSearchExclusion.computedLowerSearchWitness]
  exact
    ⟨rfl, rfl,
      cert.witness_ge U hU N,
      cert.cutoff_gt U hU N,
      fun c hmem => cert.rejects_candidates U hU N c hmem,
      cert.noSmallAtWitness U hU N,
      cert.minProofCodeSize_gt_at_witness U hU N,
      by
        rw [align.project_box_eq_minProofCodeSize (cert.witness U hU N)]
        exact cert.minProofCodeSize_gt_at_witness U hU N⟩

end InternalPudlakTheorem5ProjectBoxAlignment

/-- Tail upper-bound witness extracted from a rationality upper route.  It
records the actual polynomial upper function and the threshold after which the
measured sequence stays below it. -/
structure PolynomialUpperTailCertificate (measured : Nat → Real) : Type where
  U : Nat → Real
  polynomial : _root_.is_polynomial_bound U
  upperN : Nat
  upper_after : ∀ n : Nat, upperN ≤ n → measured n ≤ U n

/-- The explicit collision witness computed from an upper threshold and a
strict-gap threshold.  The witness number is definitionally `max upperN gapN`.
The two inequality fields are intentionally contradictory; the theorem
`ComputedCollisionWitness.contradiction` performs the final elimination. -/
structure ComputedCollisionWitness (U measured : Nat → Real) : Type where
  upperN : Nat
  gapN : Nat
  n : Nat
  n_eq : n = max upperN gapN
  upper_at_n : measured n ≤ U n
  lower_at_n : U n < measured n

namespace ComputedCollisionWitness

variable {U measured : Nat → Real}

theorem contradiction
    (witness : ComputedCollisionWitness U measured) :
    False :=
  (not_lt_of_ge witness.upper_at_n) witness.lower_at_n

end ComputedCollisionWitness

namespace TailStrictGapCertificate

variable {U measured : Nat → Real}

def toComputedCollisionWitness
    (gap : TailStrictGapCertificate U measured)
    (upperN : Nat)
    (hupper : ∀ n : Nat, upperN ≤ n → measured n ≤ U n) :
    ComputedCollisionWitness U measured where
  upperN := upperN
  gapN := gap.threshold
  n := gap.witness upperN
  n_eq := rfl
  upper_at_n := hupper (gap.witness upperN) (gap.witness_ge_upper upperN)
  lower_at_n := gap.strict_at_witness upperN

theorem toComputedCollisionWitness_n_eq
    (gap : TailStrictGapCertificate U measured)
    (upperN : Nat)
    (hupper : ∀ n : Nat, upperN ≤ n → measured n ≤ U n) :
    (gap.toComputedCollisionWitness upperN hupper).n =
      max upperN gap.threshold := by
  rfl

theorem toComputedCollisionWitness_contradiction
    (gap : TailStrictGapCertificate U measured)
    (upperN : Nat)
    (hupper : ∀ n : Nat, upperN ≤ n → measured n ≤ U n) :
    False :=
  (gap.toComputedCollisionWitness upperN hupper).contradiction

end TailStrictGapCertificate

namespace PolynomialUpperTailCertificate

variable {measured : Nat → Real}

def computedWitness
    (upper : PolynomialUpperTailCertificate measured)
    (gap : TailStrictGapCertificate upper.U measured) :
    ComputedCollisionWitness upper.U measured :=
  gap.toComputedCollisionWitness upper.upperN upper.upper_after

theorem computedWitness_n_eq
    (upper : PolynomialUpperTailCertificate measured)
    (gap : TailStrictGapCertificate upper.U measured) :
    (upper.computedWitness gap).n =
      max upper.upperN gap.threshold := by
  rfl

theorem computedWitness_contradiction
    (upper : PolynomialUpperTailCertificate measured)
    (gap : TailStrictGapCertificate upper.U measured) :
    False :=
  (upper.computedWitness gap).contradiction

end PolynomialUpperTailCertificate

namespace PolynomialUpperTailCertificate

variable {measured : Nat → Real}

def computedSearchWitness
    (upper : PolynomialUpperTailCertificate measured)
    (gap : SearchStrictGapCertificate upper.U measured) :
    ComputedSearchCollisionWitness upper.U measured :=
  gap.toComputedSearchCollisionWitness upper.upperN upper.upper_after

theorem computedSearchWitness_n_eq
    (upper : PolynomialUpperTailCertificate measured)
    (gap : SearchStrictGapCertificate upper.U measured) :
    (upper.computedSearchWitness gap).n =
      gap.witness upper.upperN :=
  rfl

theorem computedSearchWitness_contradiction
    (upper : PolynomialUpperTailCertificate measured)
    (gap : SearchStrictGapCertificate upper.U measured) :
    False :=
  (upper.computedSearchWitness gap).contradiction

end PolynomialUpperTailCertificate

/-- Computable search-gap provider for every polynomial upper function.  This
is the weaker, proof-complexity-native Month 10 target: for each upper function
it provides an algorithmic lower witness beyond any requested threshold. -/
structure ComputableSearchGapCertificate (measured : Nat → Real) : Type where
  gap_for_polynomial_upper :
    ∀ U : Nat → Real, _root_.is_polynomial_bound U →
      SearchStrictGapCertificate U measured

namespace ComputableSearchGapCertificate

def collisionWitness
    {measured : Nat → Real}
    (gap : ComputableSearchGapCertificate measured)
    (upper : PolynomialUpperTailCertificate measured) :
    ComputedSearchCollisionWitness upper.U measured :=
  upper.computedSearchWitness
    (gap.gap_for_polynomial_upper upper.U upper.polynomial)

theorem collisionWitness_n_eq
    {measured : Nat → Real}
    (gap : ComputableSearchGapCertificate measured)
    (upper : PolynomialUpperTailCertificate measured) :
    (gap.collisionWitness upper).n =
      (gap.gap_for_polynomial_upper upper.U upper.polynomial).witness
        upper.upperN :=
  rfl

theorem collisionWitness_contradiction
    {measured : Nat → Real}
    (gap : ComputableSearchGapCertificate measured)
    (upper : PolynomialUpperTailCertificate measured) :
    False :=
  (gap.collisionWitness upper).contradiction

def toGenericRationalCollisionInputs
    {measured : Nat → Real}
    (gap : ComputableSearchGapCertificate measured)
    (upper_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n → measured n ≤ U n) :
    GenericRationalCollisionInputs where
  measured := measured
  upper_under_rationality := upper_under_rationality
  gap_for_polynomial_upper := fun U hU =>
    (gap.gap_for_polynomial_upper U hU).toEventualStrictGap

noncomputable def upperTailCertificateOfRationality
    {measured : Nat → Real}
    (_gap : ComputableSearchGapCertificate measured)
    (upper_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n → measured n ≤ U n)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate measured :=
  let hex := upper_under_rationality hrat
  let U := Classical.choose hex
  let hU_tail := Classical.choose_spec hex
  let upperN := Classical.choose hU_tail.2
  {
    U := U
    polynomial := hU_tail.1
    upperN := upperN
    upper_after := Classical.choose_spec hU_tail.2 }

noncomputable def collisionWitnessOfRationality
    {measured : Nat → Real}
    (gap : ComputableSearchGapCertificate measured)
    (upper_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n → measured n ≤ U n)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ComputedSearchCollisionWitness
      (gap.upperTailCertificateOfRationality
        upper_under_rationality hrat).U measured :=
  gap.collisionWitness
    (gap.upperTailCertificateOfRationality
      upper_under_rationality hrat)

theorem computed_search_n_contradiction
    {measured : Nat → Real}
    (gap : ComputableSearchGapCertificate measured)
    (upper_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n → measured n ≤ U n)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False := by
  rcases upper_under_rationality hrat with
    ⟨U, hU, upperN, hupper⟩
  exact
    (gap.gap_for_polynomial_upper U hU).computed_witness_contradiction
      upperN hupper

theorem not_rational
    {measured : Nat → Real}
    (gap : ComputableSearchGapCertificate measured)
    (upper_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n → measured n ≤ U n) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat => gap.computed_search_n_contradiction upper_under_rationality hrat

theorem not_rational_eq_generic_core
    {measured : Nat → Real}
    (gap : ComputableSearchGapCertificate measured)
    (upper_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n → measured n ≤ U n) :
    gap.not_rational upper_under_rationality =
      GenericRationalCollisionInputs.not_rational
        (gap.toGenericRationalCollisionInputs upper_under_rationality) := by
  rfl

end ComputableSearchGapCertificate

/-- Computable transfer from the internal theorem-5 finite-search witness to the
project collision box.  This is deliberately weaker than asserting that the
theorem-5 `powerBoundRawCode` family is definitionally the same object as the
project box: it records the exact certificate needed to turn each source-side
search lower witness into a project-level search gap. -/
structure InternalPudlakTheorem5ComputableProjectGapTransfer
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (search : InternalPudlakTheorem5SmallCodeSearch scale_data sem) :
    Type (q + 1) where
  project_gap_for_polynomial_upper :
    InternalPudlakTheorem5ComputableFiniteSearchExclusion scale_data sem search →
      ∀ U : Nat → Real, _root_.is_polynomial_bound U →
        SearchStrictGapCertificate U sondowProjectLocalPudlakCollisionBox

namespace InternalPudlakTheorem5ComputableProjectGapTransfer

def toComputableSearchGapCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (transfer :
      InternalPudlakTheorem5ComputableProjectGapTransfer
        scale_data sem search)
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search) :
    ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox where
  gap_for_polynomial_upper := fun U hU =>
    transfer.project_gap_for_polynomial_upper cert U hU

theorem toComputableSearchGapCertificate_witness_ge
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (transfer :
      InternalPudlakTheorem5ComputableProjectGapTransfer
        scale_data sem search)
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    N ≤ ((transfer.toComputableSearchGapCertificate cert)
      |>.gap_for_polynomial_upper U hU).witness N :=
  ((transfer.toComputableSearchGapCertificate cert)
    |>.gap_for_polynomial_upper U hU).witness_ge N

theorem toComputableSearchGapCertificate_strict_at_witness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (transfer :
      InternalPudlakTheorem5ComputableProjectGapTransfer
        scale_data sem search)
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    U (((transfer.toComputableSearchGapCertificate cert)
        |>.gap_for_polynomial_upper U hU).witness N) <
      sondowProjectLocalPudlakCollisionBox
        (((transfer.toComputableSearchGapCertificate cert)
          |>.gap_for_polynomial_upper U hU).witness N) :=
  ((transfer.toComputableSearchGapCertificate cert)
    |>.gap_for_polynomial_upper U hU).strict_at_witness N

end InternalPudlakTheorem5ComputableProjectGapTransfer

/-- Additive projection from the theorem-5 source minimum into the project box.
If the source proof-code minimum is at most the project box plus a fixed
overhead `D`, then a source search against `U + D` computes a project gap
against `U`. -/
structure InternalPudlakTheorem5AdditiveProjectBoxProjection
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    Type (q + 1) where
  overhead : Real
  overhead_nonneg : 0 ≤ overhead
  source_le_project_add :
    ∀ n : Nat,
      (sem.minProofCodeSize (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ :
        Real) ≤
        sondowProjectLocalPudlakCollisionBox n + overhead

namespace InternalPudlakTheorem5AdditiveProjectBoxProjection

def shiftedUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data sem)
    (U : Nat → Real) : Nat → Real :=
  fun n => U n + projection.overhead

theorem shiftedUpper_polynomial
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data sem)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) :
    _root_.is_polynomial_bound (projection.shiftedUpper U) :=
  _root_.is_polynomial_bound_add_const hU projection.overhead_nonneg

def toComputableProjectGapTransfer
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data sem) :
    InternalPudlakTheorem5ComputableProjectGapTransfer
      scale_data sem search where
  project_gap_for_polynomial_upper := by
    intro cert U hU
    exact
      { witness := fun N =>
          (cert.computedLowerSearchWitness
            (projection.shiftedUpper U)
            (projection.shiftedUpper_polynomial U hU) N).n
        witness_ge := fun N =>
          (cert.computedLowerSearchWitness
            (projection.shiftedUpper U)
            (projection.shiftedUpper_polynomial U hU) N).n_ge
        strict_at_witness := by
          intro N
          have hsource :=
            (cert.computedLowerSearchWitness
              (projection.shiftedUpper U)
              (projection.shiftedUpper_polynomial U hU) N).minProofCodeSize_gt
          have hle :=
            projection.source_le_project_add
              (cert.computedLowerSearchWitness
                (projection.shiftedUpper U)
                (projection.shiftedUpper_polynomial U hU) N).n
          dsimp [shiftedUpper] at hsource
          nlinarith }

theorem toComputableProjectGapTransfer_witness_eq_shifted_source
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data sem)
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((projection.toComputableProjectGapTransfer
      |>.project_gap_for_polynomial_upper cert U hU).witness N) =
      (cert.computedLowerSearchWitness
        (projection.shiftedUpper U)
        (projection.shiftedUpper_polynomial U hU) N).n :=
  rfl

end InternalPudlakTheorem5AdditiveProjectBoxProjection

/-- Scaled additive projection from the theorem-5 source minimum into the project
box.  This is the route matching the power-bound theorem-5 shape: a source
witness at index `n` may become a project collision witness at
`projectIndex n`, usually `scale n`. -/
structure InternalPudlakTheorem5ScaledAdditiveProjectBoxProjection
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    Type (q + 1) where
  projectIndex : Nat → Nat
  projectIndex_ge_source : ∀ n : Nat, n ≤ projectIndex n
  projectIndex_polynomial :
    _root_.is_polynomial_bound (fun n : Nat => (projectIndex n : Real))
  overhead : Real
  overhead_nonneg : 0 ≤ overhead
  source_le_project_add :
    ∀ n : Nat,
      (sem.minProofCodeSize (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ :
        Real) ≤
        sondowProjectLocalPudlakCollisionBox (projectIndex n) + overhead

namespace InternalPudlakTheorem5ScaledAdditiveProjectBoxProjection

def indexedShiftedUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5ScaledAdditiveProjectBoxProjection scale_data sem)
    (U : Nat → Real) : Nat → Real :=
  fun n => U (projection.projectIndex n) + projection.overhead

theorem indexedShiftedUpper_polynomial
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5ScaledAdditiveProjectBoxProjection scale_data sem)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) :
    _root_.is_polynomial_bound (projection.indexedShiftedUpper U) :=
  _root_.is_polynomial_bound_add_const
    (hU.comp_nat projection.projectIndex_polynomial)
    projection.overhead_nonneg

def toComputableProjectGapTransfer
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (projection :
      InternalPudlakTheorem5ScaledAdditiveProjectBoxProjection scale_data sem) :
    InternalPudlakTheorem5ComputableProjectGapTransfer
      scale_data sem search where
  project_gap_for_polynomial_upper := by
    intro cert U hU
    exact
      { witness := fun N =>
          projection.projectIndex
            (cert.computedLowerSearchWitness
              (projection.indexedShiftedUpper U)
              (projection.indexedShiftedUpper_polynomial U hU) N).n
        witness_ge := by
          intro N
          let w :=
            cert.computedLowerSearchWitness
              (projection.indexedShiftedUpper U)
              (projection.indexedShiftedUpper_polynomial U hU) N
          exact le_trans w.n_ge (projection.projectIndex_ge_source w.n)
        strict_at_witness := by
          intro N
          let w :=
            cert.computedLowerSearchWitness
              (projection.indexedShiftedUpper U)
              (projection.indexedShiftedUpper_polynomial U hU) N
          have hsource :
              projection.indexedShiftedUpper U w.n <
                (sem.minProofCodeSize
                  (scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩ : Real) :=
            w.minProofCodeSize_gt
          have hle := projection.source_le_project_add w.n
          dsimp [indexedShiftedUpper] at hsource
          nlinarith }

theorem toComputableProjectGapTransfer_witness_eq_scaled_source
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (projection :
      InternalPudlakTheorem5ScaledAdditiveProjectBoxProjection scale_data sem)
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((projection.toComputableProjectGapTransfer
      |>.project_gap_for_polynomial_upper cert U hU).witness N) =
      projection.projectIndex
        (cert.computedLowerSearchWitness
          (projection.indexedShiftedUpper U)
          (projection.indexedShiftedUpper_polynomial U hU) N).n :=
  rfl

end InternalPudlakTheorem5ScaledAdditiveProjectBoxProjection

/-- Global proof-length projection from the theorem-5 source family to the
project collision box.  This is the reusable proof-complexity bridge: combine
exact recognition of the source checker minimum by PA `proof_length` with a
constant-overhead projection from the theorem-5 source code family to the
reflection-graft family measured by the project box. -/
structure InternalPudlakTheorem5ProofLengthProjectBoxProjection
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    Type (q + 1) where
  source_exact :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (sem.minProofCodeSize (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ :
          Real)
  constant_projection :
    _root_.ConstantProofLengthProjection
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      scale_data.powerBoundRawCode _root_.sondowReflectionGraftCode

namespace InternalPudlakTheorem5ProofLengthProjectBoxProjection

def toAdditiveProjectBoxProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5ProofLengthProjectBoxProjection scale_data sem) :
    InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data sem where
  overhead := projection.constant_projection.D
  overhead_nonneg := projection.constant_projection.D_nonneg
  source_le_project_add := by
    intro n
    have hproj := projection.constant_projection.source_le_target_add n
    rw [← projection.source_exact n]
    simpa [sondowProjectLocalPudlakCollisionBox] using hproj

def toComputableProjectGapTransfer
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (projection :
      InternalPudlakTheorem5ProofLengthProjectBoxProjection scale_data sem) :
    InternalPudlakTheorem5ComputableProjectGapTransfer
      scale_data sem search :=
  projection.toAdditiveProjectBoxProjection.toComputableProjectGapTransfer

end InternalPudlakTheorem5ProofLengthProjectBoxProjection

/-- Scaled proof-length projection from theorem-5 source codes to the project box.
The target family is `sondowReflectionGraftCode (projectIndex n)`, so this
supports the realistic power-bound route where the final collision witness is a
scaled index. -/
structure InternalPudlakTheorem5ScaledProofLengthProjectBoxProjection
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    Type (q + 1) where
  projectIndex : Nat → Nat
  projectIndex_ge_source : ∀ n : Nat, n ≤ projectIndex n
  projectIndex_polynomial :
    _root_.is_polynomial_bound (fun n : Nat => (projectIndex n : Real))
  source_exact :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (sem.minProofCodeSize (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ :
          Real)
  constant_projection :
    _root_.ConstantProofLengthProjection
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      scale_data.powerBoundRawCode
      (fun n : Nat => _root_.sondowReflectionGraftCode (projectIndex n))

namespace InternalPudlakTheorem5ScaledProofLengthProjectBoxProjection

def toScaledAdditiveProjectBoxProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5ScaledProofLengthProjectBoxProjection
        scale_data sem) :
    InternalPudlakTheorem5ScaledAdditiveProjectBoxProjection scale_data sem where
  projectIndex := projection.projectIndex
  projectIndex_ge_source := projection.projectIndex_ge_source
  projectIndex_polynomial := projection.projectIndex_polynomial
  overhead := projection.constant_projection.D
  overhead_nonneg := projection.constant_projection.D_nonneg
  source_le_project_add := by
    intro n
    have hproj := projection.constant_projection.source_le_target_add n
    rw [← projection.source_exact n]
    simpa [sondowProjectLocalPudlakCollisionBox] using hproj

def toComputableProjectGapTransfer
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (projection :
      InternalPudlakTheorem5ScaledProofLengthProjectBoxProjection
        scale_data sem) :
    InternalPudlakTheorem5ComputableProjectGapTransfer
      scale_data sem search :=
  projection.toScaledAdditiveProjectBoxProjection.toComputableProjectGapTransfer

end InternalPudlakTheorem5ScaledProofLengthProjectBoxProjection

namespace InternalPudlakTheorem5ConstantProjection

def ofPointwiseEq
    {T : _root_.ProofSystem} {measure : _root_.ProofLengthMeasure}
    {source target : Nat → _root_.FormulaCode}
    (hcode : ∀ n : Nat, source n = target n) :
    _root_.ConstantProofLengthProjection T measure source target where
  D := 0
  D_nonneg := by norm_num
  source_le_target_add := by
    intro n
    rw [hcode n]
    simp

def reindex
    {T : _root_.ProofSystem} {measure : _root_.ProofLengthMeasure}
    {source target : Nat → _root_.FormulaCode}
    (ρ : Nat → Nat)
    (projection :
      _root_.ConstantProofLengthProjection T measure source target) :
    _root_.ConstantProofLengthProjection
      T measure (fun n : Nat => source (ρ n)) (fun n : Nat => target (ρ n)) where
  D := projection.D
  D_nonneg := projection.D_nonneg
  source_le_target_add := by
    intro n
    exact projection.source_le_target_add (ρ n)

def comp
    {T : _root_.ProofSystem} {measure : _root_.ProofLengthMeasure}
    {source middle target : Nat → _root_.FormulaCode}
    (left :
      _root_.ConstantProofLengthProjection T measure source middle)
    (right :
      _root_.ConstantProofLengthProjection T measure middle target) :
    _root_.ConstantProofLengthProjection T measure source target where
  D := left.D + right.D
  D_nonneg := add_nonneg left.D_nonneg right.D_nonneg
  source_le_target_add := by
    intro n
    have hleft := left.source_le_target_add n
    have hright := right.source_le_target_add n
    nlinarith

end InternalPudlakTheorem5ConstantProjection

namespace InternalPudlakTheorem5ScaleData

theorem powerBoundRawCode_eq_scaled_strengthened
    (scale_data : InternalPudlakTheorem5ScaleData) (n : Nat) :
    scale_data.powerBoundRawCode n =
      _root_.strengthenedPartialConsistencyCode (scale_data.scale n) := by
  simpa [_root_.rescaledPudlakStrengthenedFiniteConsistencyCode,
    _root_.pudlakStrengthenedFiniteConsistencyCode]
    using powerBoundRawCode_eq_rescaledPudlak scale_data n

def powerBoundToScaledStrengthenedConstantProjection
    (scale_data : InternalPudlakTheorem5ScaleData) :
    _root_.ConstantProofLengthProjection
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      scale_data.powerBoundRawCode
      (fun n : Nat =>
        _root_.strengthenedPartialConsistencyCode (scale_data.scale n)) :=
  InternalPudlakTheorem5ConstantProjection.ofPointwiseEq
    (powerBoundRawCode_eq_scaled_strengthened scale_data)

def strengthenedToPartialScaledConstantProjection
    (scale_data : InternalPudlakTheorem5ScaleData)
    (projection : _root_.StrengthenedToPartialConsistencyConstantProjection) :
    _root_.ConstantProofLengthProjection
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      (fun n : Nat =>
        _root_.strengthenedPartialConsistencyCode (scale_data.scale n))
      (fun n : Nat =>
        _root_.partialConsistencyCode (scale_data.scale n)) :=
  InternalPudlakTheorem5ConstantProjection.reindex
    scale_data.scale projection

def partialToReflectionGraftScaledConstantProjection
    (scale_data : InternalPudlakTheorem5ScaleData)
    (projection : _root_.PAConjunctionEliminationConstantCost) :
    _root_.ConstantProofLengthProjection
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      (fun n : Nat =>
        _root_.partialConsistencyCode (scale_data.scale n))
      (fun n : Nat =>
        _root_.sondowReflectionGraftCode (scale_data.scale n)) :=
  InternalPudlakTheorem5ConstantProjection.reindex
    scale_data.scale projection

def powerBoundToScaledReflectionGraftConstantProjection
    (scale_data : InternalPudlakTheorem5ScaleData)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
    _root_.ConstantProofLengthProjection
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      scale_data.powerBoundRawCode
      (fun n : Nat =>
        _root_.sondowReflectionGraftCode (scale_data.scale n)) :=
  InternalPudlakTheorem5ConstantProjection.comp
    (InternalPudlakTheorem5ConstantProjection.comp
      (scale_data.powerBoundToScaledStrengthenedConstantProjection)
      (scale_data.strengthenedToPartialScaledConstantProjection
        strengthened_to_partial))
    (scale_data.partialToReflectionGraftScaledConstantProjection
      partial_to_graft)

end InternalPudlakTheorem5ScaleData

/-- Abstract theorem-5 checker semantics.  This is the Month 9-10 side of the
PA/Hilbert checker handoff: Month 11 can instantiate this structure without
creating a reverse import from Month 9-10 to the concrete PA/Hilbert surface. -/
structure InternalPudlakTheorem5CheckerSemantics
    (scale_data : InternalPudlakTheorem5ScaleData) : Type (q + 1) where
  Code : Type q
  checks : Code → _root_.FormulaCode → Prop
  size : Code → Nat
  complete_at_powerBoundRawCode :
    ∀ n : Nat, ∃ c : Code, checks c (scale_data.powerBoundRawCode n)

namespace InternalPudlakTheorem5CheckerSemantics

def toProofCodeSemantics
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data) :
    _root_.ProofCodeSemantics.{q}
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data) where
  Code := checker.Code
  checks := checker.checks
  size := checker.size
  complete := by
    intro code hcode
    rcases hcode with ⟨n, hcode_eq⟩
    rcases checker.complete_at_powerBoundRawCode n with ⟨c, hchecks⟩
    exact ⟨c, by simpa [hcode_eq] using hchecks⟩

theorem toProofCodeSemantics_checks_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data)
    (c : checker.Code) (code : _root_.FormulaCode) :
    checker.toProofCodeSemantics.checks c code = checker.checks c code :=
  rfl

theorem toProofCodeSemantics_size_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data)
    (c : checker.Code) :
    checker.toProofCodeSemantics.size c = checker.size c :=
  rfl

noncomputable def minProofCodeSizeAt
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data)
    (n : Nat) : Nat :=
  checker.toProofCodeSemantics.minProofCodeSize
    (scale_data.powerBoundRawCode n) ⟨n, rfl⟩

theorem minProofCodeSizeAt_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data)
    (n : Nat) :
    checker.minProofCodeSizeAt n =
      checker.toProofCodeSemantics.minProofCodeSize
        (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ :=
  rfl

def toProofLengthCodeSemantics
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data) :
    _root_.ProofLengthCodeSemantics.{q}
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data) where
  proof_code_semantics := checker.toProofCodeSemantics
  fallback_length := fun _ => 0

theorem toProofLengthCodeSemantics_proof_code_semantics_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data) :
    checker.toProofLengthCodeSemantics.proof_code_semantics =
      checker.toProofCodeSemantics :=
  rfl

end InternalPudlakTheorem5CheckerSemantics

/-- Checker-native finite enumeration for small proof codes.  This keeps the
Month 11 PA/Hilbert checker handoff concrete: the concrete checker only has to
provide a finite candidate list that is complete for accepted codes below each
cutoff. -/
structure InternalPudlakTheorem5CheckerFiniteEnumeration
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data) :
    Type (q + 1) where
  candidates : Nat → Nat → List checker.Code
  complete :
    ∀ n K : Nat, ∀ c : checker.Code,
      checker.checks c (scale_data.powerBoundRawCode n) →
        checker.size c < K →
          c ∈ candidates n K

namespace InternalPudlakTheorem5CheckerFiniteEnumeration

def toSmallCodeSearch
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    (enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker) :
    InternalPudlakTheorem5SmallCodeSearch
      scale_data checker.toProofCodeSemantics where
  candidates := enumeration.candidates
  complete := by
    intro n K c hchecks hsize
    exact enumeration.complete n K c hchecks hsize

theorem toSmallCodeSearch_candidates_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    (enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker)
    (n K : Nat) :
    enumeration.toSmallCodeSearch.candidates n K =
      enumeration.candidates n K :=
  rfl

end InternalPudlakTheorem5CheckerFiniteEnumeration

/-- Computable checker-native rejection extractor.  It is the theorem-5
finite-search certificate in the shape produced by a concrete executable
checker: choose a witness index and cutoff, then reject every enumerated
candidate for that index/cutoff. -/
structure InternalPudlakTheorem5CheckerComputableRejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data)
    (enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker) :
    Type (q + 1) where
  witness : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  cutoff : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  witness_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ witness f hf N
  cutoff_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (witness f hf N) < (cutoff f hf N : Real)
  rejects_candidates :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      ∀ c : checker.Code,
        c ∈ enumeration.candidates (witness f hf N) (cutoff f hf N) →
          ¬ checker.checks c (scale_data.powerBoundRawCode (witness f hf N))

namespace InternalPudlakTheorem5CheckerComputableRejectionExtractor

def toComputableFiniteSearchExclusion
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration) :
    InternalPudlakTheorem5ComputableFiniteSearchExclusion
      scale_data checker.toProofCodeSemantics enumeration.toSmallCodeSearch where
  witness := extractor.witness
  cutoff := extractor.cutoff
  witness_ge := extractor.witness_ge
  cutoff_gt := extractor.cutoff_gt
  rejects_candidates := by
    intro f hf N c hmem
    exact extractor.rejects_candidates f hf N c hmem

theorem toComputableFiniteSearchExclusion_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    extractor.toComputableFiniteSearchExclusion.witness f hf N =
      extractor.witness f hf N :=
  rfl

theorem toComputableFiniteSearchExclusion_cutoff_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    extractor.toComputableFiniteSearchExclusion.cutoff f hf N =
      extractor.cutoff f hf N :=
  rfl

end InternalPudlakTheorem5CheckerComputableRejectionExtractor

/-- Exactness certificate connecting the abstract project-level `proof_length`
to the checker minimum on exactly the theorem-5 relevant family.  This is the
residual that a concrete PA/Hilbert checker must discharge; the computable
finite-search layer below it is proof-length-free. -/
structure InternalPudlakTheorem5CheckerProofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data) :
    Prop where
  proof_length_eq_minProofCodeSize :
    ∀ code : _root_.FormulaCode,
      ∀ hcode : InternalPudlakTheorem5PowerBoundRelevantCode scale_data code,
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize code =
          (checker.toProofCodeSemantics.minProofCodeSize code hcode : Real)

namespace InternalPudlakTheorem5CheckerProofLengthExactness

theorem at_powerBoundRawCode
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness checker)
    (n : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
      (scale_data.powerBoundRawCode n) =
      (checker.minProofCodeSizeAt n : Real) :=
  exactness.proof_length_eq_minProofCodeSize
    (scale_data.powerBoundRawCode n) ⟨n, rfl⟩

theorem toProofLengthCodeSemantics_calibration
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness checker) :
    checker.toProofLengthCodeSemantics.Calibration where
  proof_length_eq_length := by
    intro code hcode
    rw [exactness.proof_length_eq_minProofCodeSize code hcode]
    change
      (checker.toProofCodeSemantics.minProofCodeSize code hcode : Real) =
        (checker.toProofCodeSemantics.semanticProofLength (fun _ => 0) code : Real)
    exact_mod_cast
        (checker.toProofCodeSemantics.semanticProofLength_eq_minProofCodeSize
        (fun _ => 0) hcode).symm

end InternalPudlakTheorem5CheckerProofLengthExactness

/-- Family-shaped version of checker proof-length exactness.  This is the
natural target for a concrete PA/Hilbert checker: prove exactness on the
theorem-5 formula family `powerBoundRawCode n`, then the generic relevant-code
statement follows by eliminating the existential relevant-code witness. -/
structure InternalPudlakTheorem5CheckerProofLengthFamilyExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data) :
    Prop where
  proof_length_eq_minProofCodeSizeAt :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode n) =
        (checker.minProofCodeSizeAt n : Real)

namespace InternalPudlakTheorem5CheckerProofLengthFamilyExactness

theorem ofCheckerProofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness checker) :
    InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker where
  proof_length_eq_minProofCodeSizeAt :=
    exactness.at_powerBoundRawCode

theorem toCheckerProofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker) :
    InternalPudlakTheorem5CheckerProofLengthExactness checker where
  proof_length_eq_minProofCodeSize := by
    intro code hcode
    rcases hcode with ⟨n, rfl⟩
    exact family.proof_length_eq_minProofCodeSizeAt n

theorem checkerProofLengthExactness_iff_familyExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data) :
    Nonempty (InternalPudlakTheorem5CheckerProofLengthExactness checker) ↔
      Nonempty
        (InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker) := by
  constructor
  · intro h
    rcases h with ⟨exactness⟩
    exact ⟨ofCheckerProofLengthExactness exactness⟩
  · intro h
    rcases h with ⟨family⟩
    exact ⟨family.toCheckerProofLengthExactness⟩

theorem toCheckerProofLengthExactness_at_powerBoundRawCode
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker)
    (n : Nat) :
    family.toCheckerProofLengthExactness.at_powerBoundRawCode n =
      family.proof_length_eq_minProofCodeSizeAt n :=
  rfl

end InternalPudlakTheorem5CheckerProofLengthFamilyExactness

/-- Split form of checker family proof-length exactness.  A concrete checker
can expose a canonical length family and prove separately that PA `proof_length`
and the checker minimum both compute that same length. -/
structure InternalPudlakTheorem5CheckerFamilyLengthCalibration
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data) :
    Type where
  family_length : Nat → Nat
  proof_length_eq_family_length :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode n) =
        (family_length n : Real)
  minProofCodeSizeAt_eq_family_length :
    ∀ n : Nat,
      checker.minProofCodeSizeAt n = family_length n

namespace InternalPudlakTheorem5CheckerFamilyLengthCalibration

theorem proof_length_eq_minProofCodeSizeAt
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    (cal :
      InternalPudlakTheorem5CheckerFamilyLengthCalibration checker)
    (n : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
      (scale_data.powerBoundRawCode n) =
      (checker.minProofCodeSizeAt n : Real) := by
  calc
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode n)
        = (cal.family_length n : Real) :=
          cal.proof_length_eq_family_length n
    _ = (checker.minProofCodeSizeAt n : Real) := by
          exact_mod_cast (cal.minProofCodeSizeAt_eq_family_length n).symm

def toFamilyExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    (cal :
      InternalPudlakTheorem5CheckerFamilyLengthCalibration checker) :
    InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker where
  proof_length_eq_minProofCodeSizeAt :=
    cal.proof_length_eq_minProofCodeSizeAt

def ofFamilyExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker) :
    InternalPudlakTheorem5CheckerFamilyLengthCalibration checker where
  family_length := checker.minProofCodeSizeAt
  proof_length_eq_family_length :=
    family.proof_length_eq_minProofCodeSizeAt
  minProofCodeSizeAt_eq_family_length := by
    intro n
    rfl

theorem nonempty_iff_familyExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data) :
    Nonempty
        (InternalPudlakTheorem5CheckerFamilyLengthCalibration checker) ↔
      Nonempty
        (InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker) := by
  constructor
  · intro h
    rcases h with ⟨cal⟩
    exact ⟨cal.toFamilyExactness⟩
  · intro h
    rcases h with ⟨family⟩
    exact ⟨ofFamilyExactness family⟩

theorem toFamilyExactness_proof_length_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    (cal :
      InternalPudlakTheorem5CheckerFamilyLengthCalibration checker)
    (n : Nat) :
    cal.toFamilyExactness.proof_length_eq_minProofCodeSizeAt n =
      cal.proof_length_eq_minProofCodeSizeAt n :=
  rfl

end InternalPudlakTheorem5CheckerFamilyLengthCalibration

/-- Proof-length-free no-small-code checker profile.  The only mathematical
content here is the lower-bound/counting statement over checker-accepted codes;
the `proof_length` exactness certificate is supplied separately. -/
structure InternalPudlakTheorem5CheckerNoSmallProfile
    (scale_data : InternalPudlakTheorem5ScaleData) : Type (q + 1) where
  checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data
  no_small_proof_codes :
    InternalPudlakTheorem5NoSmallProofCodes
      scale_data checker.toProofCodeSemantics

namespace InternalPudlakTheorem5CheckerNoSmallProfile

def proof_code_semantics
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerNoSmallProfile.{q} scale_data) :
    _root_.ProofCodeSemantics.{q}
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data) :=
  profile.checker.toProofCodeSemantics

theorem proof_code_lower_bound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerNoSmallProfile.{q} scale_data) :
    ∀ f : Nat → Real, _root_.is_polynomial_bound f →
      ∃ᶠ n in atTop,
        (profile.proof_code_semantics.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n :=
  InternalPudlakTheorem5NoSmallProofCodes.toProofCodeLowerBound
    profile.no_small_proof_codes

def toProofCodeSemanticsCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerNoSmallProfile.{q} scale_data)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness profile.checker) :
    InternalPudlakTheorem5ProofCodeSemanticsCore.{q} where
  scale_data := scale_data
  proof_code_semantics := profile.proof_code_semantics
  proof_code_lower_bound := profile.proof_code_lower_bound
  proof_length_exact := exactness.proof_length_eq_minProofCodeSize

def toCheckedLowerBoundCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerNoSmallProfile.{q} scale_data)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness profile.checker) :
    InternalPudlakTheorem5CheckedLowerBoundCore :=
  (profile.toProofCodeSemanticsCore exactness).toCheckedLowerBoundCore

def toLowerBoundCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerNoSmallProfile.{q} scale_data)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness profile.checker) :
    InternalPudlakTheorem5LowerBoundCore :=
  (profile.toProofCodeSemanticsCore exactness).toLowerBoundCore

end InternalPudlakTheorem5CheckerNoSmallProfile

/-- Proof-length-free finite-search checker profile.  This is the abstract
target that a PA/Hilbert executable checker must instantiate: a finite search
over small proof codes plus rejection of every enumerated candidate. -/
structure InternalPudlakTheorem5CheckerComputableSearchProfile
    (scale_data : InternalPudlakTheorem5ScaleData) : Type (q + 1) where
  checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data
  small_code_search :
    InternalPudlakTheorem5SmallCodeSearch
      scale_data checker.toProofCodeSemantics
  computable_search_exclusion :
    InternalPudlakTheorem5ComputableFiniteSearchExclusion
      scale_data checker.toProofCodeSemantics small_code_search

namespace InternalPudlakTheorem5CheckerComputableRejectionExtractor

def toCheckerComputableSearchProfile
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration) :
    InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data where
  checker := checker
  small_code_search := enumeration.toSmallCodeSearch
  computable_search_exclusion := extractor.toComputableFiniteSearchExclusion

theorem toCheckerComputableSearchProfile_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    (extractor.toCheckerComputableSearchProfile.computable_search_exclusion.witness f hf N) =
        extractor.witness f hf N :=
  rfl

end InternalPudlakTheorem5CheckerComputableRejectionExtractor

namespace InternalPudlakTheorem5CheckerComputableSearchProfile

def proof_code_semantics
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data) :
    _root_.ProofCodeSemantics.{q}
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data) :=
  profile.checker.toProofCodeSemantics

theorem finite_search_exclusion
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data) :
    InternalPudlakTheorem5FiniteSearchExclusion
      scale_data profile.proof_code_semantics profile.small_code_search :=
  profile.computable_search_exclusion.toFiniteSearchExclusion

theorem no_small_proof_codes
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data) :
    InternalPudlakTheorem5NoSmallProofCodes
      scale_data profile.proof_code_semantics :=
  profile.computable_search_exclusion.toNoSmallProofCodes

def toNoSmallProfile
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data) :
    InternalPudlakTheorem5CheckerNoSmallProfile.{q} scale_data where
  checker := profile.checker
  no_small_proof_codes := profile.no_small_proof_codes

def toProofCodeSemanticsCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness profile.checker) :
    InternalPudlakTheorem5ProofCodeSemanticsCore.{q} :=
  profile.toNoSmallProfile.toProofCodeSemanticsCore exactness

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness profile.checker) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} where
  scale_data := scale_data
  proof_length_model := profile.checker.toProofLengthCodeSemantics
  small_code_search := profile.small_code_search
  computable_search_exclusion := profile.computable_search_exclusion
  calibration := exactness.toProofLengthCodeSemantics_calibration

def toProofCodeSemanticsCoreOfFamilyExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data)
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness profile.checker) :
    InternalPudlakTheorem5ProofCodeSemanticsCore.{q} :=
  profile.toProofCodeSemanticsCore family.toCheckerProofLengthExactness

def toComputableFiniteSearchNoSmallCoreOfFamilyExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data)
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness profile.checker) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} :=
  profile.toComputableFiniteSearchNoSmallCore
    family.toCheckerProofLengthExactness

theorem toComputableFiniteSearchNoSmallCoreOfFamilyExactness_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data)
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness profile.checker)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    (profile.toComputableFiniteSearchNoSmallCoreOfFamilyExactness family).computable_search_exclusion.witness f hf N =
      profile.computable_search_exclusion.witness f hf N :=
  rfl

theorem toComputableFiniteSearchNoSmallCore_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness profile.checker)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    (profile.toComputableFiniteSearchNoSmallCore exactness).computable_search_exclusion.witness f hf N =
      profile.computable_search_exclusion.witness f hf N :=
  rfl

theorem toComputableFiniteSearchNoSmallCore_same_search
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness profile.checker) :
    (profile.toComputableFiniteSearchNoSmallCore exactness).small_code_search =
      profile.small_code_search :=
  rfl

def toCheckedLowerBoundCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness profile.checker) :
    InternalPudlakTheorem5CheckedLowerBoundCore :=
  (profile.toProofCodeSemanticsCore exactness).toCheckedLowerBoundCore

def toLowerBoundCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness profile.checker) :
    InternalPudlakTheorem5LowerBoundCore :=
  (profile.toProofCodeSemanticsCore exactness).toLowerBoundCore

def toScaledAdditiveProjectBoxProjectionOfConstantProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness profile.checker)
    (projectIndex : Nat → Nat)
    (projectIndex_ge_source : ∀ n : Nat, n ≤ projectIndex n)
    (projectIndex_polynomial :
      _root_.is_polynomial_bound (fun n : Nat => (projectIndex n : Real)))
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        scale_data.powerBoundRawCode
        (fun n : Nat => _root_.sondowReflectionGraftCode (projectIndex n))) :
    InternalPudlakTheorem5ScaledAdditiveProjectBoxProjection
      scale_data profile.proof_code_semantics where
  projectIndex := projectIndex
  projectIndex_ge_source := projectIndex_ge_source
  projectIndex_polynomial := projectIndex_polynomial
  overhead := projection.D
  overhead_nonneg := projection.D_nonneg
  source_le_project_add := by
    intro n
    have hproj := projection.source_le_target_add n
    rw [exactness.proof_length_eq_minProofCodeSize
      (scale_data.powerBoundRawCode n) ⟨n, rfl⟩] at hproj
    simpa [proof_code_semantics, sondowProjectLocalPudlakCollisionBox]
      using hproj

def toScaledComputableProjectGapTransferOfConstantProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness profile.checker)
    (projectIndex : Nat → Nat)
    (projectIndex_ge_source : ∀ n : Nat, n ≤ projectIndex n)
    (projectIndex_polynomial :
      _root_.is_polynomial_bound (fun n : Nat => (projectIndex n : Real)))
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        scale_data.powerBoundRawCode
        (fun n : Nat => _root_.sondowReflectionGraftCode (projectIndex n))) :
    InternalPudlakTheorem5ComputableProjectGapTransfer
      scale_data profile.proof_code_semantics profile.small_code_search :=
  (profile.toScaledAdditiveProjectBoxProjectionOfConstantProjection
    exactness projectIndex projectIndex_ge_source projectIndex_polynomial
    projection).toComputableProjectGapTransfer

def toScaleComputableProjectGapTransferOfConstantPieces
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness profile.checker)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
    InternalPudlakTheorem5ComputableProjectGapTransfer
      scale_data profile.proof_code_semantics profile.small_code_search :=
  profile.toScaledComputableProjectGapTransferOfConstantProjection
    exactness
    scale_data.scale
    scale_data.scale_id_le
    scale_data.scale_polynomial_bound
    (scale_data.powerBoundToScaledReflectionGraftConstantProjection
      strengthened_to_partial partial_to_graft)

def toProjectCollisionInputsOfConstantPieces
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness profile.checker)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
    SondowProjectLocalPudlakCollisionInputs :=
  (profile.toLowerBoundCore exactness)
    |>.toProjectCollisionInputsOfConstantPieces
      project_upper strengthened_to_partial partial_to_graft

theorem same_constant_pieces_feed_lower_inputs_and_gap_transfer
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness profile.checker)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
      Nonempty
        (InternalPudlakTheorem5ComputableProjectGapTransfer
          scale_data profile.proof_code_semantics
          profile.small_code_search) ∧
      ((profile.toProjectCollisionInputsOfConstantPieces
          exactness project_upper strengthened_to_partial partial_to_graft).transfer_to_graft =
        InternalPudlakTheorem5TransferPieces.partialToGraftTransferOfConstant
          partial_to_graft) :=
  ⟨⟨profile.toScaleComputableProjectGapTransferOfConstantPieces
      exactness strengthened_to_partial partial_to_graft⟩,
    rfl⟩

def toScaleComputableProjectGapTransferOfConstantPiecesOfFamilyExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data)
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness profile.checker)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
    InternalPudlakTheorem5ComputableProjectGapTransfer
      scale_data profile.proof_code_semantics profile.small_code_search :=
  profile.toScaleComputableProjectGapTransferOfConstantPieces
    family.toCheckerProofLengthExactness
    strengthened_to_partial partial_to_graft

theorem same_constant_pieces_feed_lower_inputs_and_gap_transfer_of_family_exactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{q} scale_data)
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness profile.checker)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
      Nonempty
        (InternalPudlakTheorem5ComputableProjectGapTransfer
          scale_data profile.proof_code_semantics
          profile.small_code_search) ∧
      ((profile.toProjectCollisionInputsOfConstantPieces
          family.toCheckerProofLengthExactness
          project_upper strengthened_to_partial partial_to_graft).transfer_to_graft =
        InternalPudlakTheorem5TransferPieces.partialToGraftTransferOfConstant
          partial_to_graft) :=
  profile.same_constant_pieces_feed_lower_inputs_and_gap_transfer
    family.toCheckerProofLengthExactness
    project_upper strengthened_to_partial partial_to_graft

end InternalPudlakTheorem5CheckerComputableSearchProfile

namespace InternalPudlakTheorem5CheckerComputableRejectionExtractor

def computedLowerSearchWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    InternalPudlakTheorem5ComputedLowerSearchWitness
      scale_data checker.toProofCodeSemantics enumeration.toSmallCodeSearch
      f hf N :=
  extractor.toComputableFiniteSearchExclusion
    |>.computedLowerSearchWitness f hf N

theorem computedLowerSearchWitness_n_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    (extractor.computedLowerSearchWitness f hf N).n =
      extractor.witness f hf N :=
  rfl

theorem computedLowerSearchWitness_K_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    (extractor.computedLowerSearchWitness f hf N).K =
      extractor.cutoff f hf N :=
  rfl

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness checker) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} :=
  extractor.toCheckerComputableSearchProfile
    |>.toComputableFiniteSearchNoSmallCore exactness

def toComputableFiniteSearchNoSmallCoreOfFamilyExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} :=
  extractor.toComputableFiniteSearchNoSmallCore
    family.toCheckerProofLengthExactness

theorem toComputableFiniteSearchNoSmallCore_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness checker)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    (extractor.toComputableFiniteSearchNoSmallCore exactness).computable_search_exclusion.witness f hf N =
      extractor.witness f hf N :=
  rfl

theorem toComputableFiniteSearchNoSmallCoreOfFamilyExactness_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    (extractor.toComputableFiniteSearchNoSmallCoreOfFamilyExactness family).computable_search_exclusion.witness f hf N =
      extractor.witness f hf N :=
  rfl

def toScaleComputableProjectGapTransferOfConstantPieces
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness checker)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
    InternalPudlakTheorem5ComputableProjectGapTransfer
      scale_data checker.toProofCodeSemantics enumeration.toSmallCodeSearch :=
  extractor.toCheckerComputableSearchProfile
    |>.toScaleComputableProjectGapTransferOfConstantPieces
      exactness strengthened_to_partial partial_to_graft

def toScaleComputableProjectGapTransferOfConstantPiecesOfFamilyExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
    InternalPudlakTheorem5ComputableProjectGapTransfer
      scale_data checker.toProofCodeSemantics enumeration.toSmallCodeSearch :=
  extractor.toScaleComputableProjectGapTransferOfConstantPieces
    family.toCheckerProofLengthExactness
    strengthened_to_partial partial_to_graft

theorem same_constant_pieces_feed_checker_extractor_core_and_gap_transfer
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness checker)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
      Nonempty
        (InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}) ∧
      Nonempty
        (InternalPudlakTheorem5ComputableProjectGapTransfer
          scale_data checker.toProofCodeSemantics
          enumeration.toSmallCodeSearch) :=
  ⟨⟨extractor.toComputableFiniteSearchNoSmallCore exactness⟩,
    ⟨extractor.toScaleComputableProjectGapTransferOfConstantPieces
      exactness strengthened_to_partial partial_to_graft⟩⟩

theorem same_constant_pieces_feed_checker_extractor_core_and_gap_transfer_of_family_exactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
      Nonempty
        (InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}) ∧
      Nonempty
        (InternalPudlakTheorem5ComputableProjectGapTransfer
          scale_data checker.toProofCodeSemantics
          enumeration.toSmallCodeSearch) :=
  extractor.same_constant_pieces_feed_checker_extractor_core_and_gap_transfer
    family.toCheckerProofLengthExactness
    strengthened_to_partial partial_to_graft

end InternalPudlakTheorem5CheckerComputableRejectionExtractor

namespace InternalPudlakTheorem5ProofLengthCodeSemanticsCore

def toProofLengthProjectBoxProjection
    (core : InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q})
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        core.scale_data.powerBoundRawCode _root_.sondowReflectionGraftCode) :
    InternalPudlakTheorem5ProofLengthProjectBoxProjection
      core.scale_data core.proof_code_semantics where
  source_exact := by
    intro n
    exact core.proof_length_eq_minProofCodeSize
      (core.scale_data.powerBoundRawCode n) ⟨n, rfl⟩
  constant_projection := projection

def toAdditiveProjectBoxProjectionOfConstantProjection
    (core : InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q})
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        core.scale_data.powerBoundRawCode _root_.sondowReflectionGraftCode) :
    InternalPudlakTheorem5AdditiveProjectBoxProjection
      core.scale_data core.proof_code_semantics :=
  (core.toProofLengthProjectBoxProjection projection).toAdditiveProjectBoxProjection

def toComputableProjectGapTransferOfConstantProjection
    (core : InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q})
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        core.scale_data.powerBoundRawCode _root_.sondowReflectionGraftCode)
    (search :
      InternalPudlakTheorem5SmallCodeSearch
        core.scale_data core.proof_code_semantics) :
    InternalPudlakTheorem5ComputableProjectGapTransfer
      core.scale_data core.proof_code_semantics search :=
  (core.toProofLengthProjectBoxProjection projection).toComputableProjectGapTransfer

def toScaledProofLengthProjectBoxProjection
    (core : InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q})
    (projectIndex : Nat → Nat)
    (projectIndex_ge_source : ∀ n : Nat, n ≤ projectIndex n)
    (projectIndex_polynomial :
      _root_.is_polynomial_bound (fun n : Nat => (projectIndex n : Real)))
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        core.scale_data.powerBoundRawCode
        (fun n : Nat => _root_.sondowReflectionGraftCode (projectIndex n))) :
    InternalPudlakTheorem5ScaledProofLengthProjectBoxProjection
      core.scale_data core.proof_code_semantics where
  projectIndex := projectIndex
  projectIndex_ge_source := projectIndex_ge_source
  projectIndex_polynomial := projectIndex_polynomial
  source_exact := by
    intro n
    exact core.proof_length_eq_minProofCodeSize
      (core.scale_data.powerBoundRawCode n) ⟨n, rfl⟩
  constant_projection := projection

def toScaledAdditiveProjectBoxProjectionOfConstantProjection
    (core : InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q})
    (projectIndex : Nat → Nat)
    (projectIndex_ge_source : ∀ n : Nat, n ≤ projectIndex n)
    (projectIndex_polynomial :
      _root_.is_polynomial_bound (fun n : Nat => (projectIndex n : Real)))
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        core.scale_data.powerBoundRawCode
        (fun n : Nat => _root_.sondowReflectionGraftCode (projectIndex n))) :
    InternalPudlakTheorem5ScaledAdditiveProjectBoxProjection
      core.scale_data core.proof_code_semantics :=
  (core.toScaledProofLengthProjectBoxProjection
    projectIndex projectIndex_ge_source projectIndex_polynomial projection)
    |>.toScaledAdditiveProjectBoxProjection

def toScaledComputableProjectGapTransferOfConstantProjection
    (core : InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q})
    (projectIndex : Nat → Nat)
    (projectIndex_ge_source : ∀ n : Nat, n ≤ projectIndex n)
    (projectIndex_polynomial :
      _root_.is_polynomial_bound (fun n : Nat => (projectIndex n : Real)))
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        core.scale_data.powerBoundRawCode
        (fun n : Nat => _root_.sondowReflectionGraftCode (projectIndex n)))
    (search :
      InternalPudlakTheorem5SmallCodeSearch
        core.scale_data core.proof_code_semantics) :
    InternalPudlakTheorem5ComputableProjectGapTransfer
      core.scale_data core.proof_code_semantics search :=
  (core.toScaledProofLengthProjectBoxProjection
    projectIndex projectIndex_ge_source projectIndex_polynomial projection)
    |>.toComputableProjectGapTransfer

end InternalPudlakTheorem5ProofLengthCodeSemanticsCore

namespace InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore

def toProofLengthProjectBoxProjection
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        core.scale_data.powerBoundRawCode _root_.sondowReflectionGraftCode) :
    InternalPudlakTheorem5ProofLengthProjectBoxProjection
      core.scale_data core.proof_code_semantics :=
  core.toProofLengthCodeSemanticsCore.toProofLengthProjectBoxProjection
    projection

def toAdditiveProjectBoxProjectionOfConstantProjection
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        core.scale_data.powerBoundRawCode _root_.sondowReflectionGraftCode) :
    InternalPudlakTheorem5AdditiveProjectBoxProjection
      core.scale_data core.proof_code_semantics :=
  (core.toProofLengthProjectBoxProjection projection).toAdditiveProjectBoxProjection

def toComputableProjectGapTransferOfConstantProjection
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        core.scale_data.powerBoundRawCode _root_.sondowReflectionGraftCode) :
    InternalPudlakTheorem5ComputableProjectGapTransfer
      core.scale_data core.proof_code_semantics core.small_code_search :=
  (core.toProofLengthProjectBoxProjection projection).toComputableProjectGapTransfer

def toScaledProofLengthProjectBoxProjection
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (projectIndex : Nat → Nat)
    (projectIndex_ge_source : ∀ n : Nat, n ≤ projectIndex n)
    (projectIndex_polynomial :
      _root_.is_polynomial_bound (fun n : Nat => (projectIndex n : Real)))
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        core.scale_data.powerBoundRawCode
        (fun n : Nat => _root_.sondowReflectionGraftCode (projectIndex n))) :
    InternalPudlakTheorem5ScaledProofLengthProjectBoxProjection
      core.scale_data core.proof_code_semantics :=
  core.toProofLengthCodeSemanticsCore.toScaledProofLengthProjectBoxProjection
    projectIndex projectIndex_ge_source projectIndex_polynomial projection

def toScaledAdditiveProjectBoxProjectionOfConstantProjection
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (projectIndex : Nat → Nat)
    (projectIndex_ge_source : ∀ n : Nat, n ≤ projectIndex n)
    (projectIndex_polynomial :
      _root_.is_polynomial_bound (fun n : Nat => (projectIndex n : Real)))
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        core.scale_data.powerBoundRawCode
        (fun n : Nat => _root_.sondowReflectionGraftCode (projectIndex n))) :
    InternalPudlakTheorem5ScaledAdditiveProjectBoxProjection
      core.scale_data core.proof_code_semantics :=
  (core.toScaledProofLengthProjectBoxProjection
    projectIndex projectIndex_ge_source projectIndex_polynomial projection)
    |>.toScaledAdditiveProjectBoxProjection

def toScaledComputableProjectGapTransferOfConstantProjection
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (projectIndex : Nat → Nat)
    (projectIndex_ge_source : ∀ n : Nat, n ≤ projectIndex n)
    (projectIndex_polynomial :
      _root_.is_polynomial_bound (fun n : Nat => (projectIndex n : Real)))
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        core.scale_data.powerBoundRawCode
        (fun n : Nat => _root_.sondowReflectionGraftCode (projectIndex n))) :
    InternalPudlakTheorem5ComputableProjectGapTransfer
      core.scale_data core.proof_code_semantics core.small_code_search :=
  (core.toScaledProofLengthProjectBoxProjection
    projectIndex projectIndex_ge_source projectIndex_polynomial projection)
    |>.toComputableProjectGapTransfer

def additiveProjectSearchCollisionWitness
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.proof_code_semantics)
    (upper : PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox) :
    ComputedSearchCollisionWitness upper.U sondowProjectLocalPudlakCollisionBox :=
  ((projection.toComputableProjectGapTransfer
      (search := core.small_code_search))
    |>.toComputableSearchGapCertificate core.computable_search_exclusion)
    |>.collisionWitness upper

theorem additiveProjectSearchCollisionWitness_n_eq_shifted_source_search
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.proof_code_semantics)
    (upper : PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox) :
    (core.additiveProjectSearchCollisionWitness projection upper).n =
      (core.computable_search_exclusion
        |>.computedLowerSearchWitness
          (projection.shiftedUpper upper.U)
          (projection.shiftedUpper_polynomial upper.U upper.polynomial)
          upper.upperN).n := by
  rfl

/-- Payload-free additive projection endpoint.  This is the replacement target
for the old local-Hilbert projection route: once the source checker minimum is
known to be at most the project box plus a fixed overhead, the computed witness
is the finite-search witness for the shifted upper bound `U + overhead`. -/
theorem additiveProjectSearchCollisionWitness_full_trace
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.proof_code_semantics)
    (upper : PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox) :
    let shiftedUpper := projection.shiftedUpper upper.U
    let hshifted :=
      projection.shiftedUpper_polynomial upper.U upper.polynomial
    let w :=
      core.computable_search_exclusion
        |>.computedLowerSearchWitness shiftedUpper hshifted upper.upperN
    let witness := core.additiveProjectSearchCollisionWitness projection upper
    witness.n = w.n ∧
      upper.upperN ≤ witness.n ∧
        shiftedUpper w.n < (w.K : Real) ∧
          (∀ c : core.proof_code_semantics.Code,
            c ∈ core.small_code_search.candidates w.n w.K →
              ¬ core.proof_code_semantics.checks c
                (core.scale_data.powerBoundRawCode w.n)) ∧
          (core.proof_code_semantics.minProofCodeSize
              (core.scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩ :
              Real) > shiftedUpper w.n ∧
          upper.U witness.n < sondowProjectLocalPudlakCollisionBox witness.n ∧
          sondowProjectLocalPudlakCollisionBox witness.n ≤ upper.U witness.n ∧
          False := by
  let shiftedUpper := projection.shiftedUpper upper.U
  let hshifted :=
    projection.shiftedUpper_polynomial upper.U upper.polynomial
  let w :=
    core.computable_search_exclusion
      |>.computedLowerSearchWitness shiftedUpper hshifted upper.upperN
  let witness := core.additiveProjectSearchCollisionWitness projection upper
  exact
    ⟨rfl,
      witness.n_ge_upper,
      w.cutoff_gt,
      w.rejects_candidates,
      w.minProofCodeSize_gt,
      witness.lower_at_n,
      witness.upper_at_n,
      witness.contradiction⟩

def scaledAdditiveProjectSearchCollisionWitness
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (projection :
      InternalPudlakTheorem5ScaledAdditiveProjectBoxProjection
        core.scale_data core.proof_code_semantics)
    (upper : PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox) :
    ComputedSearchCollisionWitness upper.U sondowProjectLocalPudlakCollisionBox :=
  ((projection.toComputableProjectGapTransfer
      (search := core.small_code_search))
    |>.toComputableSearchGapCertificate core.computable_search_exclusion)
    |>.collisionWitness upper

theorem scaledAdditiveProjectSearchCollisionWitness_n_eq_indexed_source_search
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (projection :
      InternalPudlakTheorem5ScaledAdditiveProjectBoxProjection
        core.scale_data core.proof_code_semantics)
    (upper : PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox) :
    (core.scaledAdditiveProjectSearchCollisionWitness projection upper).n =
      projection.projectIndex
        (core.computable_search_exclusion
          |>.computedLowerSearchWitness
            (projection.indexedShiftedUpper upper.U)
            (projection.indexedShiftedUpper_polynomial
              upper.U upper.polynomial)
            upper.upperN).n := by
  rfl

/-- Payload-free scaled projection endpoint.  This is the theorem-5 shaped
version of the additive endpoint: the project collision witness is the scaled
project index of the source finite-search witness. -/
theorem scaledAdditiveProjectSearchCollisionWitness_full_trace
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (projection :
      InternalPudlakTheorem5ScaledAdditiveProjectBoxProjection
        core.scale_data core.proof_code_semantics)
    (upper : PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox) :
    let indexedUpper := projection.indexedShiftedUpper upper.U
    let hindexed :=
      projection.indexedShiftedUpper_polynomial upper.U upper.polynomial
    let w :=
      core.computable_search_exclusion
        |>.computedLowerSearchWitness indexedUpper hindexed upper.upperN
    let witness := core.scaledAdditiveProjectSearchCollisionWitness projection upper
    witness.n = projection.projectIndex w.n ∧
      upper.upperN ≤ witness.n ∧
        indexedUpper w.n < (w.K : Real) ∧
          (∀ c : core.proof_code_semantics.Code,
            c ∈ core.small_code_search.candidates w.n w.K →
              ¬ core.proof_code_semantics.checks c
                (core.scale_data.powerBoundRawCode w.n)) ∧
          (core.proof_code_semantics.minProofCodeSize
              (core.scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩ :
              Real) > indexedUpper w.n ∧
          upper.U witness.n < sondowProjectLocalPudlakCollisionBox witness.n ∧
          sondowProjectLocalPudlakCollisionBox witness.n ≤ upper.U witness.n ∧
          False := by
  let indexedUpper := projection.indexedShiftedUpper upper.U
  let hindexed :=
    projection.indexedShiftedUpper_polynomial upper.U upper.polynomial
  let w :=
    core.computable_search_exclusion
      |>.computedLowerSearchWitness indexedUpper hindexed upper.upperN
  let witness := core.scaledAdditiveProjectSearchCollisionWitness projection upper
  exact
    ⟨rfl,
      witness.n_ge_upper,
      w.cutoff_gt,
      w.rejects_candidates,
      w.minProofCodeSize_gt,
      witness.lower_at_n,
      witness.upper_at_n,
      witness.contradiction⟩

end InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore

/-- Local-Hilbert instantiation of the additive project-box projection.  This is
the bridge that makes the existing `LocalHilbertProofCodeProjectionModel` usable
for Month 9-10: once theorem-5 `powerBoundRawCode` is identified with the local
source family and the project box is identified with the local reflection-graft
target minimum, the local `+2` projection yields the additive transfer. -/
structure InternalPudlakTheorem5LocalHilbertProjectBoxProjection
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) where
  local_projection :
    _root_.MiniHilbert.LocalHilbertProofCodeProjectionModel interp
  theorem5_source_eq_local_source :
    ∀ m : Nat,
      sem.minProofCodeSize (scale_data.powerBoundRawCode m) ⟨m, rfl⟩ =
        interp.localHilbertProofCodeSemantics.minProofCodeSize
          (_root_.partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)
  project_box_eq_local_target :
    ∀ m : Nat,
      sondowProjectLocalPudlakCollisionBox m =
        (interp.localHilbertProofCodeSemantics.minProofCodeSize
          (_root_.sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩) :
          Real)

namespace InternalPudlakTheorem5LocalHilbertProjectBoxProjection

def toAdditiveProjectBoxProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (h :
      InternalPudlakTheorem5LocalHilbertProjectBoxProjection
        scale_data sem interp) :
    InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data sem where
  overhead := 2
  overhead_nonneg := by norm_num
  source_le_project_add := by
    intro m
    have hlocal :
        (interp.localHilbertProofCodeSemantics.minProofCodeSize
          (_root_.partialConsistencyCode m) (Or.inl ⟨m, rfl⟩) : Real) ≤
          (interp.localHilbertProofCodeSemantics.minProofCodeSize
            (_root_.sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩) : Real) +
            2 := by
      exact_mod_cast h.local_projection.source_le_target_add_two m
    rw [h.theorem5_source_eq_local_source m]
    rw [h.project_box_eq_local_target m]
    exact hlocal

def toComputableProjectGapTransfer
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (h :
      InternalPudlakTheorem5LocalHilbertProjectBoxProjection
        scale_data sem interp) :
    InternalPudlakTheorem5ComputableProjectGapTransfer
      scale_data sem search :=
  h.toAdditiveProjectBoxProjection.toComputableProjectGapTransfer

end InternalPudlakTheorem5LocalHilbertProjectBoxProjection

/-- Payload-free replacement for the legacy local-Hilbert projection bridge.  The
old `LocalHilbertProofCodeProjectionModel` routes the same `source ≤ target + 2`
fact through `FormulaCodeHilbertInterpretation.localHilbertProofCodeSemantics`,
whose current construction still unfolds payload certificates.  This structure
keeps only the theorem-5 source minimum, the project collision box, and the
scaled project index needed by the finite-search route. -/
structure InternalPudlakTheorem5PayloadFreeLocalHilbertProjectionModel
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    Type (q + 1) where
  projectIndex : Nat → Nat
  projectIndex_ge_source : ∀ m : Nat, m ≤ projectIndex m
  projectIndex_polynomial :
    _root_.is_polynomial_bound (fun m : Nat => (projectIndex m : Real))
  source_le_target_add_two :
    ∀ m : Nat,
      (sem.minProofCodeSize (scale_data.powerBoundRawCode m) ⟨m, rfl⟩ :
        Real) ≤
        sondowProjectLocalPudlakCollisionBox (projectIndex m) + 2

namespace InternalPudlakTheorem5PayloadFreeLocalHilbertProjectionModel

def toScaledAdditiveProjectBoxProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (h :
      InternalPudlakTheorem5PayloadFreeLocalHilbertProjectionModel
        scale_data sem) :
    InternalPudlakTheorem5ScaledAdditiveProjectBoxProjection
      scale_data sem where
  projectIndex := h.projectIndex
  projectIndex_ge_source := h.projectIndex_ge_source
  projectIndex_polynomial := h.projectIndex_polynomial
  overhead := 2
  overhead_nonneg := by norm_num
  source_le_project_add := h.source_le_target_add_two

theorem toScaledAdditiveProjectBoxProjection_source_le_target_add_two
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (h :
      InternalPudlakTheorem5PayloadFreeLocalHilbertProjectionModel
        scale_data sem)
    (m : Nat) :
    (h.toScaledAdditiveProjectBoxProjection.source_le_project_add m) =
      h.source_le_target_add_two m := by
  rfl

end InternalPudlakTheorem5PayloadFreeLocalHilbertProjectionModel

namespace InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore

def payloadFreeLocalHilbertProjectSearchCollisionWitness
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (projection :
      InternalPudlakTheorem5PayloadFreeLocalHilbertProjectionModel
        core.scale_data core.proof_code_semantics)
    (upper : PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox) :
    ComputedSearchCollisionWitness upper.U sondowProjectLocalPudlakCollisionBox :=
  core.scaledAdditiveProjectSearchCollisionWitness
    projection.toScaledAdditiveProjectBoxProjection upper

theorem payloadFreeLocalHilbertProjectSearchCollisionWitness_n_eq_indexed_source_search
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (projection :
      InternalPudlakTheorem5PayloadFreeLocalHilbertProjectionModel
        core.scale_data core.proof_code_semantics)
    (upper : PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox) :
    (core.payloadFreeLocalHilbertProjectSearchCollisionWitness
      projection upper).n =
      projection.projectIndex
        (core.computable_search_exclusion
          |>.computedLowerSearchWitness
            (projection.toScaledAdditiveProjectBoxProjection.indexedShiftedUpper
              upper.U)
            (projection.toScaledAdditiveProjectBoxProjection
              |>.indexedShiftedUpper_polynomial upper.U upper.polynomial)
            upper.upperN).n := by
  rfl

/-- Payload-free Local-Hilbert-shaped endpoint trace.  The final collision index
is the clean project index applied to the source finite-search witness; no
`partial_consistency_payload` or strengthened payload axiom is mentioned. -/
theorem payloadFreeLocalHilbertProjectSearchCollisionWitness_full_trace
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (projection :
      InternalPudlakTheorem5PayloadFreeLocalHilbertProjectionModel
        core.scale_data core.proof_code_semantics)
    (upper : PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox) :
    let scaledProjection := projection.toScaledAdditiveProjectBoxProjection
    let indexedUpper := scaledProjection.indexedShiftedUpper upper.U
    let hindexed :=
      scaledProjection.indexedShiftedUpper_polynomial upper.U upper.polynomial
    let w :=
      core.computable_search_exclusion
        |>.computedLowerSearchWitness indexedUpper hindexed upper.upperN
    let witness :=
      core.payloadFreeLocalHilbertProjectSearchCollisionWitness projection upper
    witness.n = projection.projectIndex w.n ∧
      upper.upperN ≤ witness.n ∧
        indexedUpper w.n < (w.K : Real) ∧
          (∀ c : core.proof_code_semantics.Code,
            c ∈ core.small_code_search.candidates w.n w.K →
              ¬ core.proof_code_semantics.checks c
                (core.scale_data.powerBoundRawCode w.n)) ∧
          (core.proof_code_semantics.minProofCodeSize
              (core.scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩ :
              Real) > indexedUpper w.n ∧
          upper.U witness.n < sondowProjectLocalPudlakCollisionBox witness.n ∧
          sondowProjectLocalPudlakCollisionBox witness.n ≤ upper.U witness.n ∧
          False := by
  exact
    scaledAdditiveProjectSearchCollisionWitness_full_trace
      core projection.toScaledAdditiveProjectBoxProjection upper

def localHilbertProjectSearchCollisionWitness
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (projection :
      InternalPudlakTheorem5LocalHilbertProjectBoxProjection
        core.scale_data core.proof_code_semantics interp)
    (upper : PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox) :
    ComputedSearchCollisionWitness upper.U sondowProjectLocalPudlakCollisionBox :=
  ((projection.toComputableProjectGapTransfer
      (search := core.small_code_search))
    |>.toComputableSearchGapCertificate core.computable_search_exclusion)
    |>.collisionWitness upper

theorem localHilbertProjectSearchCollisionWitness_n_eq_source_search
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (projection :
      InternalPudlakTheorem5LocalHilbertProjectBoxProjection
        core.scale_data core.proof_code_semantics interp)
    (upper : PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox) :
    (core.localHilbertProjectSearchCollisionWitness projection upper).n =
      (core.computable_search_exclusion
        |>.computedLowerSearchWitness
          (projection.toAdditiveProjectBoxProjection.shiftedUpper upper.U)
          (projection.toAdditiveProjectBoxProjection.shiftedUpper_polynomial
            upper.U upper.polynomial)
          upper.upperN).n := by
  rfl

/-- Core-level Local-Hilbert endpoint trace.  Unlike the project checklist
wrappers, this statement depends only on the computable finite-search core, the
local Hilbert projection, and a Sondow upper-tail certificate. -/
theorem localHilbertProjectSearchCollisionWitness_full_trace
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (projection :
      InternalPudlakTheorem5LocalHilbertProjectBoxProjection
        core.scale_data core.proof_code_semantics interp)
    (upper : PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox) :
    let w :=
      core.computable_search_exclusion
        |>.computedLowerSearchWitness
          (projection.toAdditiveProjectBoxProjection.shiftedUpper upper.U)
          (projection.toAdditiveProjectBoxProjection.shiftedUpper_polynomial
            upper.U upper.polynomial)
          upper.upperN
    let witness :=
      core.localHilbertProjectSearchCollisionWitness projection upper
    witness.n = w.n ∧
      upper.upperN ≤ witness.n ∧
        upper.U witness.n < sondowProjectLocalPudlakCollisionBox witness.n ∧
          sondowProjectLocalPudlakCollisionBox witness.n ≤ upper.U witness.n ∧
            False := by
  let witness := core.localHilbertProjectSearchCollisionWitness projection upper
  exact
    ⟨rfl,
      witness.n_ge_upper,
      witness.lower_at_n,
      witness.upper_at_n,
      witness.contradiction⟩

end InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore

namespace InternalPudlakTheorem5ProjectBoxAlignment

def toComputableSearchGapCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (align : InternalPudlakTheorem5ProjectBoxAlignment scale_data sem)
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search) :
    ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox where
  gap_for_polynomial_upper := fun U hU =>
    align.toSearchStrictGapCertificate cert U hU

def toComputableProjectGapTransfer
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (align : InternalPudlakTheorem5ProjectBoxAlignment scale_data sem) :
    InternalPudlakTheorem5ComputableProjectGapTransfer
      scale_data sem search where
  project_gap_for_polynomial_upper := fun cert U hU =>
    align.toSearchStrictGapCertificate cert U hU

theorem toComputableSearchGapCertificate_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (align : InternalPudlakTheorem5ProjectBoxAlignment scale_data sem)
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((align.toComputableSearchGapCertificate cert).gap_for_polynomial_upper
        U hU).witness N =
      (cert.computedLowerSearchWitness U hU N).n :=
  rfl

/-- Full source-to-project search trace for a project-box alignment.  It exposes
that the project computable gap uses exactly the finite-search lower witness, and
keeps the cutoff, finite rejection, no-small proof-code statement, and
minimum-size inequality available for audit. -/
theorem toComputableSearchGapCertificate_full_lower_search_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{q}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (align : InternalPudlakTheorem5ProjectBoxAlignment scale_data sem)
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    let gap := align.toComputableSearchGapCertificate cert
    let w := cert.computedLowerSearchWitness U hU N
    ((gap.gap_for_polynomial_upper U hU).witness N = w.n) ∧
      N ≤ w.n ∧
        U w.n < (w.K : Real) ∧
          (∀ c : sem.Code, c ∈ search.candidates w.n w.K →
            ¬ sem.checks c (scale_data.powerBoundRawCode w.n)) ∧
          (∀ c : sem.Code,
            sem.checks c (scale_data.powerBoundRawCode w.n) →
              U w.n < (sem.size c : Real)) ∧
          (sem.minProofCodeSize (scale_data.powerBoundRawCode w.n)
            ⟨w.n, rfl⟩ : Real) > U w.n ∧
          U ((gap.gap_for_polynomial_upper U hU).witness N) <
            sondowProjectLocalPudlakCollisionBox
              ((gap.gap_for_polynomial_upper U hU).witness N) := by
  let gap := align.toComputableSearchGapCertificate cert
  let w := cert.computedLowerSearchWitness U hU N
  exact
    ⟨rfl,
      w.n_ge,
      w.cutoff_gt,
      w.rejects_candidates,
      w.no_small_at_n,
      w.minProofCodeSize_gt,
      (gap.gap_for_polynomial_upper U hU).strict_at_witness N⟩

end InternalPudlakTheorem5ProjectBoxAlignment

/-- A computable gap provider for every polynomial upper function.  This is the
Month 10 target shape replacing a merely eventual gap package. -/
structure ComputableGapCertificate (measured : Nat → Real) : Type where
  gap_for_polynomial_upper :
    ∀ U : Nat → Real, _root_.is_polynomial_bound U →
      TailStrictGapCertificate U measured

namespace ComputableGapCertificate

def toComputableSearchGapCertificate
    {measured : Nat → Real}
    (gap : ComputableGapCertificate measured) :
    ComputableSearchGapCertificate measured where
  gap_for_polynomial_upper := fun U hU =>
    (gap.gap_for_polynomial_upper U hU).toSearchStrictGapCertificate

noncomputable def ofEventuallyStrict
    {measured : Nat → Real}
    (h :
      ∀ U : Nat → Real, _root_.is_polynomial_bound U →
        ∀ᶠ n in Filter.atTop, U n < measured n) :
    ComputableGapCertificate measured where
  gap_for_polynomial_upper := fun U hU =>
    TailStrictGapCertificate.ofEventuallyAtTop (h U hU)

theorem ofEventuallyStrict_strict_after
    {measured : Nat → Real}
    (h :
      ∀ U : Nat → Real, _root_.is_polynomial_bound U →
        ∀ᶠ n in Filter.atTop, U n < measured n)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U)
    (n : Nat)
    (hn :
      ((ofEventuallyStrict h).gap_for_polynomial_upper U hU).threshold ≤ n) :
    U n < measured n :=
  ((ofEventuallyStrict h).gap_for_polynomial_upper U hU).strict_after n hn

def collisionWitness
    {measured : Nat → Real}
    (gap : ComputableGapCertificate measured)
    (upper : PolynomialUpperTailCertificate measured) :
    ComputedCollisionWitness upper.U measured :=
  upper.computedWitness
    (gap.gap_for_polynomial_upper upper.U upper.polynomial)

theorem collisionWitness_n_eq
    {measured : Nat → Real}
    (gap : ComputableGapCertificate measured)
    (upper : PolynomialUpperTailCertificate measured) :
    (gap.collisionWitness upper).n =
      max upper.upperN
        (gap.gap_for_polynomial_upper upper.U upper.polynomial).threshold := by
  rfl

theorem collisionWitness_contradiction
    {measured : Nat → Real}
    (gap : ComputableGapCertificate measured)
    (upper : PolynomialUpperTailCertificate measured) :
    False :=
  (gap.collisionWitness upper).contradiction

noncomputable def upperTailCertificateOfRationality
    {measured : Nat → Real}
    (_gap : ComputableGapCertificate measured)
    (upper_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n → measured n ≤ U n)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate measured :=
  let hex := upper_under_rationality hrat
  let U := Classical.choose hex
  let hU_tail := Classical.choose_spec hex
  let upperN := Classical.choose hU_tail.2
  {
    U := U
    polynomial := hU_tail.1
    upperN := upperN
    upper_after := Classical.choose_spec hU_tail.2 }

noncomputable def collisionWitnessOfRationality
    {measured : Nat → Real}
    (gap : ComputableGapCertificate measured)
    (upper_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n → measured n ≤ U n)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ComputedCollisionWitness
      (gap.upperTailCertificateOfRationality
        upper_under_rationality hrat).U measured :=
  gap.collisionWitness
    (gap.upperTailCertificateOfRationality
      upper_under_rationality hrat)

theorem collisionWitnessOfRationality_contradiction
    {measured : Nat → Real}
    (gap : ComputableGapCertificate measured)
    (upper_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n → measured n ≤ U n)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (gap.collisionWitnessOfRationality
    upper_under_rationality hrat).contradiction

def toGenericRationalCollisionInputs
    {measured : Nat → Real}
    (gap : ComputableGapCertificate measured)
    (upper_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n → measured n ≤ U n) :
    GenericRationalCollisionInputs where
  measured := measured
  upper_under_rationality := upper_under_rationality
  gap_for_polynomial_upper := fun U hU =>
    (gap.gap_for_polynomial_upper U hU).toEventualStrictGap

theorem computed_n_contradiction
    {measured : Nat → Real}
    (gap : ComputableGapCertificate measured)
    (upper_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n → measured n ≤ U n)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False := by
  rcases upper_under_rationality hrat with
    ⟨U, hU, upperN, hupper⟩
  exact
    (gap.gap_for_polynomial_upper U hU).computed_witness_contradiction
      upperN hupper

theorem not_rational
    {measured : Nat → Real}
    (gap : ComputableGapCertificate measured)
    (upper_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n → measured n ≤ U n) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat => gap.computed_n_contradiction upper_under_rationality hrat

theorem not_rational_eq_generic_core
    {measured : Nat → Real}
    (gap : ComputableGapCertificate measured)
    (upper_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n → measured n ≤ U n) :
    gap.not_rational upper_under_rationality =
      GenericRationalCollisionInputs.not_rational
        (gap.toGenericRationalCollisionInputs upper_under_rationality) := by
  rfl

end ComputableGapCertificate

/-- First Month 9-10 checklist.  It keeps the internal lower-bound machine and
the computable witness layer separate, so the theorem 5 internalization can
advance without changing the collision witness API. -/
structure Month9Month10InternalPudlakWitnessChecklist : Type where
  lower_machine : InternalFiniteConsistencyLowerBoundMachine
  transfer_to_graft :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer
  computable_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox

namespace Month9Month10InternalPudlakWitnessChecklist

def lowerPackage
    (h : Month9Month10InternalPudlakWitnessChecklist) :
    _root_.PudlakFiniteConsistencyLowerBoundPackage :=
  h.lower_machine.toPudlakFiniteConsistencyLowerBoundPackage

theorem eventualReflectionGraftLowerBound
    (h : Month9Month10InternalPudlakWitnessChecklist) :
    _root_.EventualLowerBound _root_.ProofSystem.PA
      _root_.ProofLengthMeasure.symbolSize _root_.sondowReflectionGraftCode :=
  h.lower_machine.eventualReflectionGraftLowerBound_of_transfer
    h.transfer_to_graft

theorem eventual_gap_from_internal_machine
    (h : Month9Month10InternalPudlakWitnessChecklist)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) :
    _root_.EventualStrictGap U sondowProjectLocalPudlakCollisionBox :=
  h.lower_machine.reflectionGraftGap_of_transfer
    h.transfer_to_graft U hU

theorem computable_gap_refines_eventual_gap
    (h : Month9Month10InternalPudlakWitnessChecklist)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) :
    _root_.EventualStrictGap U sondowProjectLocalPudlakCollisionBox :=
  (h.computable_gap.gap_for_polynomial_upper U hU).toEventualStrictGap

theorem computed_n_contradiction
    (h : Month9Month10InternalPudlakWitnessChecklist)
    (upper_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n →
              sondowProjectLocalPudlakCollisionBox n ≤ U n)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.computable_gap.computed_n_contradiction
    upper_under_rationality hrat

noncomputable def collisionWitnessOfRationality
    (h : Month9Month10InternalPudlakWitnessChecklist)
    (upper_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n →
              sondowProjectLocalPudlakCollisionBox n ≤ U n)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ComputedCollisionWitness
      (h.computable_gap.upperTailCertificateOfRationality
        upper_under_rationality hrat).U
      sondowProjectLocalPudlakCollisionBox :=
  h.computable_gap.collisionWitnessOfRationality
    upper_under_rationality hrat

theorem collisionWitnessOfRationality_contradiction
    (h : Month9Month10InternalPudlakWitnessChecklist)
    (upper_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n →
              sondowProjectLocalPudlakCollisionBox n ≤ U n)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.collisionWitnessOfRationality
    upper_under_rationality hrat).contradiction

theorem not_rational
    (h : Month9Month10InternalPudlakWitnessChecklist)
    (upper_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n →
              sondowProjectLocalPudlakCollisionBox n ≤ U n) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.computable_gap.not_rational upper_under_rationality

theorem not_rational_eq_generic_core
    (h : Month9Month10InternalPudlakWitnessChecklist)
    (upper_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n →
              sondowProjectLocalPudlakCollisionBox n ≤ U n) :
    h.not_rational upper_under_rationality =
      GenericRationalCollisionInputs.not_rational
        (h.computable_gap.toGenericRationalCollisionInputs
          upper_under_rationality) :=
  h.computable_gap.not_rational_eq_generic_core
    upper_under_rationality

end Month9Month10InternalPudlakWitnessChecklist

theorem month9_month10_initial_closure
    (h : Month9Month10InternalPudlakWitnessChecklist) :
    Nonempty _root_.PudlakFiniteConsistencyLowerBoundPackage ∧
      (∀ U : Nat → Real, _root_.is_polynomial_bound U →
        _root_.EventualStrictGap U sondowProjectLocalPudlakCollisionBox) ∧
        Nonempty (ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox) ∧
          (∀ U : Nat → Real, _root_.is_polynomial_bound U →
            Nonempty (SearchStrictGapCertificate U sondowProjectLocalPudlakCollisionBox)) ∧
            (∀ U : Nat → Real, _root_.is_polynomial_bound U →
              Nonempty (TailStrictGapCertificate U sondowProjectLocalPudlakCollisionBox)) :=
  ⟨⟨h.lowerPackage⟩,
    h.computable_gap_refines_eventual_gap,
    ⟨h.computable_gap.toComputableSearchGapCertificate⟩,
    fun U hU =>
      ⟨(h.computable_gap.gap_for_polynomial_upper U hU).toSearchStrictGapCertificate⟩,
    fun U hU => ⟨h.computable_gap.gap_for_polynomial_upper U hU⟩⟩

/-- Project-level Month 9-10 checklist: the Sondow upper route is now bundled
with the internal lower-bound machine and the computable gap witness layer. -/
structure Month9Month10ProjectCollisionChecklist : Type where
  witness_checklist : Month9Month10InternalPudlakWitnessChecklist
  project_upper : SondowProjectLocalS21CollapseConclusion

namespace Month9Month10ProjectCollisionChecklist

def toProjectCollisionInputs
    (h : Month9Month10ProjectCollisionChecklist) :
    SondowProjectLocalPudlakCollisionInputs :=
  h.witness_checklist.lower_machine.toProjectCollisionInputs
    h.project_upper h.witness_checklist.transfer_to_graft

def upperUnderRationality
    (h : Month9Month10ProjectCollisionChecklist) :
    _root_.is_rational _root_.euler_mascheroni →
      ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
        ∃ upperN : Nat,
          ∀ n : Nat, upperN ≤ n →
            sondowProjectLocalPudlakCollisionBox n ≤ U n :=
  h.toProjectCollisionInputs.upperBoundUnderRationality

def toGenericCollisionInputs
    (h : Month9Month10ProjectCollisionChecklist) :
    GenericRationalCollisionInputs :=
  h.witness_checklist.computable_gap.toGenericRationalCollisionInputs
    h.upperUnderRationality

noncomputable def upperTailOfRationality
    (h : Month9Month10ProjectCollisionChecklist)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox :=
  h.witness_checklist.computable_gap.upperTailCertificateOfRationality
    h.upperUnderRationality hrat

noncomputable def projectCollisionWitnessOfRationality
    (h : Month9Month10ProjectCollisionChecklist)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ComputedCollisionWitness
      (h.upperTailOfRationality hrat).U
      sondowProjectLocalPudlakCollisionBox :=
  h.witness_checklist.computable_gap.collisionWitness
    (h.upperTailOfRationality hrat)

theorem projectCollisionWitness_n_eq_max
    (h : Month9Month10ProjectCollisionChecklist)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.projectCollisionWitnessOfRationality hrat).n =
      max (h.upperTailOfRationality hrat).upperN
        (h.witness_checklist.computable_gap.gap_for_polynomial_upper
          (h.upperTailOfRationality hrat).U
          (h.upperTailOfRationality hrat).polynomial).threshold := by
  rfl

theorem projectCollisionWitness_contradiction
    (h : Month9Month10ProjectCollisionChecklist)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.projectCollisionWitnessOfRationality hrat).contradiction

theorem computed_n_contradiction
    (h : Month9Month10ProjectCollisionChecklist)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.witness_checklist.computed_n_contradiction
    h.upperUnderRationality hrat

theorem not_rational
    (h : Month9Month10ProjectCollisionChecklist) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat => h.computed_n_contradiction hrat

theorem not_rational_eq_generic_core
    (h : Month9Month10ProjectCollisionChecklist) :
    h.not_rational =
      GenericRationalCollisionInputs.not_rational h.toGenericCollisionInputs :=
  h.witness_checklist.not_rational_eq_generic_core
    h.upperUnderRationality

theorem project_collision_inputs_use_internal_lower_package
    (h : Month9Month10ProjectCollisionChecklist) :
    h.toProjectCollisionInputs.pudlak_lower_bound =
      h.witness_checklist.lower_machine.toPudlakFiniteConsistencyLowerBoundPackage :=
  rfl

theorem computed_gap_refines_project_eventual_gap
    (h : Month9Month10ProjectCollisionChecklist)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) :
    _root_.EventualStrictGap U sondowProjectLocalPudlakCollisionBox :=
  h.witness_checklist.computable_gap_refines_eventual_gap U hU

def toComputableSearchGapCertificate
    (h : Month9Month10ProjectCollisionChecklist) :
    ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox :=
  h.witness_checklist.computable_gap.toComputableSearchGapCertificate

def toSearchGenericCollisionInputs
    (h : Month9Month10ProjectCollisionChecklist) :
    GenericRationalCollisionInputs :=
  h.toComputableSearchGapCertificate.toGenericRationalCollisionInputs
    h.upperUnderRationality

noncomputable def projectSearchCollisionWitnessOfRationality
    (h : Month9Month10ProjectCollisionChecklist)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ComputedSearchCollisionWitness
      (h.upperTailOfRationality hrat).U
      sondowProjectLocalPudlakCollisionBox :=
  h.toComputableSearchGapCertificate.collisionWitness
    (h.upperTailOfRationality hrat)

theorem projectSearchCollisionWitness_n_eq_search
    (h : Month9Month10ProjectCollisionChecklist)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.projectSearchCollisionWitnessOfRationality hrat).n =
      ((h.toComputableSearchGapCertificate.gap_for_polynomial_upper
        (h.upperTailOfRationality hrat).U
        (h.upperTailOfRationality hrat).polynomial).witness
          (h.upperTailOfRationality hrat).upperN) := by
  rfl

theorem projectSearchCollisionWitness_ge_upper
    (h : Month9Month10ProjectCollisionChecklist)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.upperTailOfRationality hrat).upperN ≤
      (h.projectSearchCollisionWitnessOfRationality hrat).n :=
  (h.projectSearchCollisionWitnessOfRationality hrat).n_ge_upper

theorem projectSearchCollisionWitness_contradiction
    (h : Month9Month10ProjectCollisionChecklist)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.projectSearchCollisionWitnessOfRationality hrat).contradiction

theorem computed_search_n_contradiction
    (h : Month9Month10ProjectCollisionChecklist)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.toComputableSearchGapCertificate.computed_search_n_contradiction
    h.upperUnderRationality hrat

theorem search_not_rational
    (h : Month9Month10ProjectCollisionChecklist) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat => h.computed_search_n_contradiction hrat

theorem search_not_rational_eq_generic_core
    (h : Month9Month10ProjectCollisionChecklist) :
    h.search_not_rational =
      GenericRationalCollisionInputs.not_rational h.toSearchGenericCollisionInputs :=
  h.toComputableSearchGapCertificate.not_rational_eq_generic_core
    h.upperUnderRationality

end Month9Month10ProjectCollisionChecklist

theorem month9_month10_project_search_gap_closure
    (h : Month9Month10ProjectCollisionChecklist) :
    Nonempty (ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox) ∧
      (∀ U : Nat → Real, _root_.is_polynomial_bound U →
        Nonempty (SearchStrictGapCertificate U sondowProjectLocalPudlakCollisionBox)) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (h.upperTailOfRationality hrat).upperN ≤
            (h.projectSearchCollisionWitnessOfRationality hrat).n) ∧
          h.search_not_rational =
            GenericRationalCollisionInputs.not_rational h.toSearchGenericCollisionInputs :=
  ⟨⟨h.toComputableSearchGapCertificate⟩,
    fun U hU => ⟨h.toComputableSearchGapCertificate.gap_for_polynomial_upper U hU⟩,
    h.projectSearchCollisionWitness_ge_upper,
    h.search_not_rational_eq_generic_core⟩

/-- Refined Month 9 checklist.  This removes the package-shaped lower-machine
field and stores the theorem-5 raw/rescaled machine directly. -/
structure Month9Month10RefinedTheorem5Checklist : Type where
  theorem5_machine : InternalPudlakTheorem5Machine
  transfer_to_graft :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer
  computable_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox

namespace Month9Month10RefinedTheorem5Checklist

def toWitnessChecklist
    (h : Month9Month10RefinedTheorem5Checklist) :
    Month9Month10InternalPudlakWitnessChecklist where
  lower_machine := h.theorem5_machine.toInternalFiniteConsistencyLowerBoundMachine
  transfer_to_graft := h.transfer_to_graft
  computable_gap := h.computable_gap

theorem witnessChecklist_lowerMachine_eq
    (h : Month9Month10RefinedTheorem5Checklist) :
    h.toWitnessChecklist.lower_machine =
      h.theorem5_machine.toInternalFiniteConsistencyLowerBoundMachine :=
  rfl

def lowerPackage
    (h : Month9Month10RefinedTheorem5Checklist) :
    _root_.PudlakFiniteConsistencyLowerBoundPackage :=
  h.theorem5_machine.toPudlakFiniteConsistencyLowerBoundPackage

theorem lowerPackage_eq_witnessChecklist_lowerPackage
    (h : Month9Month10RefinedTheorem5Checklist) :
    h.lowerPackage = h.toWitnessChecklist.lowerPackage := by
  rfl

theorem normalForm_code_eq_rescaledPudlak
    (h : Month9Month10RefinedTheorem5Checklist) (n : Nat) :
    h.theorem5_machine.toNormalForm.code n =
      _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
        h.theorem5_machine.scale n :=
  h.theorem5_machine.normalForm_code_eq_rescaledPudlak n

theorem eventual_gap_from_refined_theorem5
    (h : Month9Month10RefinedTheorem5Checklist)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) :
    _root_.EventualStrictGap U sondowProjectLocalPudlakCollisionBox :=
  h.toWitnessChecklist.eventual_gap_from_internal_machine U hU

theorem computable_gap_refines_refined_theorem5_gap
    (h : Month9Month10RefinedTheorem5Checklist)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) :
    _root_.EventualStrictGap U sondowProjectLocalPudlakCollisionBox :=
  h.toWitnessChecklist.computable_gap_refines_eventual_gap U hU

theorem computed_n_contradiction
    (h : Month9Month10RefinedTheorem5Checklist)
    (upper_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n →
              sondowProjectLocalPudlakCollisionBox n ≤ U n)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.toWitnessChecklist.computed_n_contradiction
    upper_under_rationality hrat

def toProjectChecklist
    (h : Month9Month10RefinedTheorem5Checklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10ProjectCollisionChecklist where
  witness_checklist := h.toWitnessChecklist
  project_upper := project_upper

theorem project_computed_n_contradiction
    (h : Month9Month10RefinedTheorem5Checklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.toProjectChecklist project_upper).computed_n_contradiction hrat

theorem project_not_rational_eq_generic_core
    (h : Month9Month10RefinedTheorem5Checklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (h.toProjectChecklist project_upper).not_rational =
      GenericRationalCollisionInputs.not_rational
        (h.toProjectChecklist project_upper).toGenericCollisionInputs :=
  (h.toProjectChecklist project_upper).not_rational_eq_generic_core

end Month9Month10RefinedTheorem5Checklist

/-- Power-bound version of the refined checklist.  This is the audit-facing
entry point closest to the theorem-5 statement, while the rescaled checklist is
what the existing collision route consumes. -/
structure Month9Month10PowerBoundTheorem5Checklist : Type where
  theorem5_machine : InternalPudlakTheorem5PowerBoundMachine
  transfer_to_graft :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer
  computable_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox

namespace Month9Month10PowerBoundTheorem5Checklist

def toRefinedChecklist
    (h : Month9Month10PowerBoundTheorem5Checklist) :
    Month9Month10RefinedTheorem5Checklist where
  theorem5_machine := h.theorem5_machine.toRescaledMachine
  transfer_to_graft := h.transfer_to_graft
  computable_gap := h.computable_gap

def toWitnessChecklist
    (h : Month9Month10PowerBoundTheorem5Checklist) :
    Month9Month10InternalPudlakWitnessChecklist :=
  h.toRefinedChecklist.toWitnessChecklist

theorem powerBound_normalForm_code_eq_rescaledPudlak
    (h : Month9Month10PowerBoundTheorem5Checklist) (n : Nat) :
    h.theorem5_machine.toRescaledMachine.toNormalForm.code n =
      _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
        h.theorem5_machine.scale_data.scale n :=
  h.theorem5_machine.toRescaledMachine_normalForm_code_eq_rescaledPudlak n

def toProjectChecklist
    (h : Month9Month10PowerBoundTheorem5Checklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10ProjectCollisionChecklist :=
  h.toRefinedChecklist.toProjectChecklist project_upper

theorem project_computed_n_contradiction
    (h : Month9Month10PowerBoundTheorem5Checklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.toProjectChecklist project_upper).computed_n_contradiction hrat

theorem project_not_rational_eq_generic_core
    (h : Month9Month10PowerBoundTheorem5Checklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (h.toProjectChecklist project_upper).not_rational =
      GenericRationalCollisionInputs.not_rational
        (h.toProjectChecklist project_upper).toGenericCollisionInputs :=
  (h.toProjectChecklist project_upper).not_rational_eq_generic_core

end Month9Month10PowerBoundTheorem5Checklist

theorem month9_month10_project_closure
    (h : Month9Month10ProjectCollisionChecklist) :
    Nonempty _root_.PudlakFiniteConsistencyLowerBoundPackage ∧
      h.toProjectCollisionInputs.pudlak_lower_bound =
        h.witness_checklist.lower_machine.toPudlakFiniteConsistencyLowerBoundPackage ∧
        h.not_rational =
          GenericRationalCollisionInputs.not_rational h.toGenericCollisionInputs :=
  ⟨⟨h.witness_checklist.lowerPackage⟩,
    h.project_collision_inputs_use_internal_lower_package,
    h.not_rational_eq_generic_core⟩

theorem month9_month10_refined_theorem5_closure
    (h : Month9Month10RefinedTheorem5Checklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty InternalPudlakTheorem5Machine ∧
      Nonempty _root_.PudlakFiniteConsistencyLowerBoundPackage ∧
        (∀ n : Nat,
          h.theorem5_machine.toNormalForm.code n =
            _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
              h.theorem5_machine.scale n) ∧
          (h.toProjectChecklist project_upper).not_rational =
            GenericRationalCollisionInputs.not_rational
              (h.toProjectChecklist project_upper).toGenericCollisionInputs :=
  ⟨⟨h.theorem5_machine⟩,
    ⟨h.lowerPackage⟩,
    h.normalForm_code_eq_rescaledPudlak,
    h.project_not_rational_eq_generic_core project_upper⟩

theorem month9_month10_power_bound_theorem5_closure
    (h : Month9Month10PowerBoundTheorem5Checklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty InternalPudlakTheorem5PowerBoundMachine ∧
      Nonempty InternalPudlakTheorem5Machine ∧
        Nonempty _root_.PudlakFiniteConsistencyLowerBoundPackage ∧
          (∀ n : Nat,
            h.theorem5_machine.toRescaledMachine.toNormalForm.code n =
              _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
                h.theorem5_machine.scale_data.scale n) ∧
            (h.toProjectChecklist project_upper).not_rational =
              GenericRationalCollisionInputs.not_rational
                (h.toProjectChecklist project_upper).toGenericCollisionInputs :=
  ⟨⟨h.theorem5_machine⟩,
    ⟨h.theorem5_machine.toRescaledMachine⟩,
    ⟨h.toRefinedChecklist.lowerPackage⟩,
    h.powerBound_normalForm_code_eq_rescaledPudlak,
    h.project_not_rational_eq_generic_core project_upper⟩

/-- Intrinsic Month 9-10 checklist.  This is the preferred public-facing
internal theorem-5 entry point: its theorem-5 machine is no longer a literature
certificate wrapper. -/
structure Month9Month10IntrinsicTheorem5Checklist : Type where
  theorem5_machine : IntrinsicPudlakTheorem5PowerBoundMachine
  transfer_to_graft :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer
  computable_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox

namespace Month9Month10IntrinsicTheorem5Checklist

def toPowerBoundChecklist
    (h : Month9Month10IntrinsicTheorem5Checklist) :
    Month9Month10PowerBoundTheorem5Checklist where
  theorem5_machine := h.theorem5_machine.toPowerBoundMachine
  transfer_to_graft := h.transfer_to_graft
  computable_gap := h.computable_gap

def toRefinedChecklist
    (h : Month9Month10IntrinsicTheorem5Checklist) :
    Month9Month10RefinedTheorem5Checklist :=
  h.toPowerBoundChecklist.toRefinedChecklist

def toProjectChecklist
    (h : Month9Month10IntrinsicTheorem5Checklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10ProjectCollisionChecklist :=
  h.toPowerBoundChecklist.toProjectChecklist project_upper

theorem intrinsic_normalForm_code_eq_rescaledPudlak
    (h : Month9Month10IntrinsicTheorem5Checklist) (n : Nat) :
    h.theorem5_machine.toRescaledMachine.toNormalForm.code n =
      _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
        h.theorem5_machine.scale_data.scale n :=
  h.theorem5_machine.toRescaledMachine_normalForm_code_eq_rescaledPudlak n

theorem project_computed_n_contradiction
    (h : Month9Month10IntrinsicTheorem5Checklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.toProjectChecklist project_upper).computed_n_contradiction hrat

theorem project_collision_witness_n_eq_max
    (h : Month9Month10IntrinsicTheorem5Checklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((h.toProjectChecklist project_upper).projectCollisionWitnessOfRationality
      hrat).n =
      max ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).upperN
        ((h.toProjectChecklist project_upper).witness_checklist.computable_gap
          |>.gap_for_polynomial_upper
            ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).U
            ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).polynomial
          |>.threshold) := by
  exact
    (h.toProjectChecklist project_upper).projectCollisionWitness_n_eq_max hrat

theorem project_not_rational_eq_generic_core
    (h : Month9Month10IntrinsicTheorem5Checklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (h.toProjectChecklist project_upper).not_rational =
      GenericRationalCollisionInputs.not_rational
        (h.toProjectChecklist project_upper).toGenericCollisionInputs :=
  (h.toProjectChecklist project_upper).not_rational_eq_generic_core

end Month9Month10IntrinsicTheorem5Checklist

/-- Checklist with the theorem-5 lower-bound core isolated as the only
proof-complexity lemma field. -/
structure Month9Month10LowerBoundCoreChecklist : Type where
  theorem5_core : InternalPudlakTheorem5LowerBoundCore
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  transfer_to_graft :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer
  computable_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox

namespace Month9Month10LowerBoundCoreChecklist

def toIntrinsicChecklist
    (h : Month9Month10LowerBoundCoreChecklist) :
    Month9Month10IntrinsicTheorem5Checklist where
  theorem5_machine :=
    h.theorem5_core.toIntrinsicPowerBoundMachine
      h.strengthened_to_partial
  transfer_to_graft := h.transfer_to_graft
  computable_gap := h.computable_gap

def toProjectChecklist
    (h : Month9Month10LowerBoundCoreChecklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10ProjectCollisionChecklist :=
  h.toIntrinsicChecklist.toProjectChecklist project_upper

theorem core_normalForm_code_eq_rescaledPudlak
    (h : Month9Month10LowerBoundCoreChecklist) (n : Nat) :
    h.toIntrinsicChecklist.theorem5_machine.toRescaledMachine.toNormalForm.code n =
      _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
        h.theorem5_core.scale_data.scale n :=
  h.toIntrinsicChecklist.intrinsic_normalForm_code_eq_rescaledPudlak n

theorem project_collision_witness_n_eq_max
    (h : Month9Month10LowerBoundCoreChecklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((h.toProjectChecklist project_upper).projectCollisionWitnessOfRationality
      hrat).n =
      max ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).upperN
        ((h.toProjectChecklist project_upper).witness_checklist.computable_gap
          |>.gap_for_polynomial_upper
            ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).U
            ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).polynomial
          |>.threshold) := by
  exact
    (h.toProjectChecklist project_upper).projectCollisionWitness_n_eq_max hrat

theorem project_computed_n_contradiction
    (h : Month9Month10LowerBoundCoreChecklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.toProjectChecklist project_upper).computed_n_contradiction hrat

theorem project_not_rational_eq_generic_core
    (h : Month9Month10LowerBoundCoreChecklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (h.toProjectChecklist project_upper).not_rational =
      GenericRationalCollisionInputs.not_rational
        (h.toProjectChecklist project_upper).toGenericCollisionInputs :=
  (h.toProjectChecklist project_upper).not_rational_eq_generic_core

end Month9Month10LowerBoundCoreChecklist

/-- Checked-code version of the Month 9-10 lower-bound checklist.  This is one
level closer to a real internal proof of Pudlak theorem 5: the theorem-5 lower
bound is supplied as a checked-code lower bound plus exactness, not as an
abstract global proof-length lower bound. -/
structure Month9Month10CheckedLowerBoundCoreChecklist : Type where
  theorem5_checked_core : InternalPudlakTheorem5CheckedLowerBoundCore
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  transfer_to_graft :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer
  computable_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox

namespace Month9Month10CheckedLowerBoundCoreChecklist

def toLowerBoundCoreChecklist
    (h : Month9Month10CheckedLowerBoundCoreChecklist) :
    Month9Month10LowerBoundCoreChecklist where
  theorem5_core := h.theorem5_checked_core.toLowerBoundCore
  strengthened_to_partial := h.strengthened_to_partial
  transfer_to_graft := h.transfer_to_graft
  computable_gap := h.computable_gap

def toProjectChecklist
    (h : Month9Month10CheckedLowerBoundCoreChecklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10ProjectCollisionChecklist :=
  h.toLowerBoundCoreChecklist.toProjectChecklist project_upper

theorem checked_exactness
    (h : Month9Month10CheckedLowerBoundCoreChecklist) (n : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (h.theorem5_checked_core.scale_data.powerBoundRawCode n) =
      (h.theorem5_checked_core.checkedLength n : Real) :=
  h.theorem5_checked_core.proof_length_exact n

theorem checked_core_refines_lower_bound_core
    (h : Month9Month10CheckedLowerBoundCoreChecklist) :
    h.toLowerBoundCoreChecklist.theorem5_core =
      h.theorem5_checked_core.toLowerBoundCore :=
  rfl

theorem core_normalForm_code_eq_rescaledPudlak
    (h : Month9Month10CheckedLowerBoundCoreChecklist) (n : Nat) :
    (h.toLowerBoundCoreChecklist.toIntrinsicChecklist.theorem5_machine
        |>.toRescaledMachine
        |>.toNormalForm).code n =
      _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
        h.theorem5_checked_core.scale_data.scale n :=
  h.toLowerBoundCoreChecklist.core_normalForm_code_eq_rescaledPudlak n

theorem project_collision_witness_n_eq_max
    (h : Month9Month10CheckedLowerBoundCoreChecklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((h.toProjectChecklist project_upper).projectCollisionWitnessOfRationality
      hrat).n =
      max ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).upperN
        ((h.toProjectChecklist project_upper).witness_checklist.computable_gap
          |>.gap_for_polynomial_upper
            ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).U
            ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).polynomial
          |>.threshold) :=
  h.toLowerBoundCoreChecklist.project_collision_witness_n_eq_max
    project_upper hrat

theorem project_computed_n_contradiction
    (h : Month9Month10CheckedLowerBoundCoreChecklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.toProjectChecklist project_upper).computed_n_contradiction hrat

theorem project_not_rational_eq_generic_core
    (h : Month9Month10CheckedLowerBoundCoreChecklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (h.toProjectChecklist project_upper).not_rational =
      GenericRationalCollisionInputs.not_rational
        (h.toProjectChecklist project_upper).toGenericCollisionInputs :=
  (h.toProjectChecklist project_upper).not_rational_eq_generic_core

end Month9Month10CheckedLowerBoundCoreChecklist

/-- Proof-code-semantics version of the Month 9-10 checklist.  This is the
current narrowest internalization frontier: the theorem-5 lower bound is now a
lower bound for the checker-computed `minProofCodeSize` on the theorem-5 raw
family, plus exact recognition by PA symbol-size `proof_length`. -/
structure Month9Month10ProofCodeSemanticsCoreChecklist : Type (q + 1) where
  theorem5_proof_code_core :
    InternalPudlakTheorem5ProofCodeSemanticsCore.{q}
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  transfer_to_graft :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer
  computable_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox

namespace Month9Month10ProofCodeSemanticsCoreChecklist

def toCheckedLowerBoundCoreChecklist
    (h : Month9Month10ProofCodeSemanticsCoreChecklist.{q}) :
    Month9Month10CheckedLowerBoundCoreChecklist where
  theorem5_checked_core :=
    h.theorem5_proof_code_core.toCheckedLowerBoundCore
  strengthened_to_partial := h.strengthened_to_partial
  transfer_to_graft := h.transfer_to_graft
  computable_gap := h.computable_gap

def toProjectChecklist
    (h : Month9Month10ProofCodeSemanticsCoreChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10ProjectCollisionChecklist :=
  h.toCheckedLowerBoundCoreChecklist.toProjectChecklist project_upper

theorem checkedLength_eq_minProofCodeSize
    (h : Month9Month10ProofCodeSemanticsCoreChecklist.{q}) (n : Nat) :
    h.toCheckedLowerBoundCoreChecklist.theorem5_checked_core.checkedLength n =
      h.theorem5_proof_code_core.proof_code_semantics.minProofCodeSize
        (h.theorem5_proof_code_core.scale_data.powerBoundRawCode n)
        ⟨n, rfl⟩ :=
  rfl

theorem proof_length_exact_at_powerBoundRawCode
    (h : Month9Month10ProofCodeSemanticsCoreChecklist.{q}) (n : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (h.theorem5_proof_code_core.scale_data.powerBoundRawCode n) =
      (h.theorem5_proof_code_core.checkedLength n : Real) :=
  h.theorem5_proof_code_core.proof_length_exact_at_powerBoundRawCode n

theorem project_collision_witness_n_eq_max
    (h : Month9Month10ProofCodeSemanticsCoreChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((h.toProjectChecklist project_upper).projectCollisionWitnessOfRationality
      hrat).n =
      max ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).upperN
        ((h.toProjectChecklist project_upper).witness_checklist.computable_gap
          |>.gap_for_polynomial_upper
            ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).U
            ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).polynomial
          |>.threshold) :=
  h.toCheckedLowerBoundCoreChecklist.project_collision_witness_n_eq_max
    project_upper hrat

theorem project_computed_n_contradiction
    (h : Month9Month10ProofCodeSemanticsCoreChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.toProjectChecklist project_upper).computed_n_contradiction hrat

theorem project_not_rational_eq_generic_core
    (h : Month9Month10ProofCodeSemanticsCoreChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (h.toProjectChecklist project_upper).not_rational =
      GenericRationalCollisionInputs.not_rational
        (h.toProjectChecklist project_upper).toGenericCollisionInputs :=
  (h.toProjectChecklist project_upper).not_rational_eq_generic_core

end Month9Month10ProofCodeSemanticsCoreChecklist

/-- Proof-length-code-semantics checklist.  This is the version aligned with the
project's reusable proof-length calibration interface: a concrete checker model
plus a `Calibration` field replaces ad-hoc exactness equations. -/
structure Month9Month10ProofLengthCodeSemanticsCoreChecklist : Type (q + 1) where
  theorem5_proof_length_code_core :
    InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q}
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  transfer_to_graft :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer
  computable_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox

namespace Month9Month10ProofLengthCodeSemanticsCoreChecklist

def toProofCodeSemanticsCoreChecklist
    (h : Month9Month10ProofLengthCodeSemanticsCoreChecklist.{q}) :
    Month9Month10ProofCodeSemanticsCoreChecklist.{q} where
  theorem5_proof_code_core :=
    h.theorem5_proof_length_code_core.toProofCodeSemanticsCore
  strengthened_to_partial := h.strengthened_to_partial
  transfer_to_graft := h.transfer_to_graft
  computable_gap := h.computable_gap

def toProjectChecklist
    (h : Month9Month10ProofLengthCodeSemanticsCoreChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10ProjectCollisionChecklist :=
  h.toProofCodeSemanticsCoreChecklist.toProjectChecklist project_upper

theorem calibration_project_length_eq_minProofCodeSize
    (h : Month9Month10ProofLengthCodeSemanticsCoreChecklist.{q})
    (code : _root_.FormulaCode)
    (hcode :
      InternalPudlakTheorem5PowerBoundRelevantCode
        h.theorem5_proof_length_code_core.scale_data code) :
    h.theorem5_proof_length_code_core.proof_length_model.length code =
      h.theorem5_proof_length_code_core.proof_code_semantics.minProofCodeSize
        code hcode :=
  h.theorem5_proof_length_code_core.project_length_eq_minProofCodeSize
    code hcode

theorem proof_length_exact_at_powerBoundRawCode
    (h : Month9Month10ProofLengthCodeSemanticsCoreChecklist.{q})
    (n : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (h.theorem5_proof_length_code_core.scale_data.powerBoundRawCode n) =
      (h.theorem5_proof_length_code_core.toProofCodeSemanticsCore.checkedLength n :
        Real) :=
  h.theorem5_proof_length_code_core
    |>.toProofCodeSemanticsCore
    |>.proof_length_exact_at_powerBoundRawCode n

theorem project_collision_witness_n_eq_max
    (h : Month9Month10ProofLengthCodeSemanticsCoreChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((h.toProjectChecklist project_upper).projectCollisionWitnessOfRationality
      hrat).n =
      max ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).upperN
        ((h.toProjectChecklist project_upper).witness_checklist.computable_gap
          |>.gap_for_polynomial_upper
            ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).U
            ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).polynomial
          |>.threshold) :=
  h.toProofCodeSemanticsCoreChecklist.project_collision_witness_n_eq_max
    project_upper hrat

theorem project_computed_n_contradiction
    (h : Month9Month10ProofLengthCodeSemanticsCoreChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.toProjectChecklist project_upper).computed_n_contradiction hrat

theorem project_not_rational_eq_generic_core
    (h : Month9Month10ProofLengthCodeSemanticsCoreChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (h.toProjectChecklist project_upper).not_rational =
      GenericRationalCollisionInputs.not_rational
        (h.toProjectChecklist project_upper).toGenericCollisionInputs :=
  (h.toProjectChecklist project_upper).not_rational_eq_generic_core

end Month9Month10ProofLengthCodeSemanticsCoreChecklist

/-- No-small-code checklist.  This is the current most concrete Month 9
proof-complexity frontier: theorem 5 is reduced to excluding all polynomially
small accepted proof codes for the power-bound finite-consistency raw family,
plus the standard proof-length-code calibration. -/
structure Month9Month10NoSmallCodeSemanticsCoreChecklist : Type (q + 1) where
  theorem5_no_small_code_core :
    InternalPudlakTheorem5NoSmallCodeSemanticsCore.{q}
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  transfer_to_graft :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer
  computable_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox

namespace Month9Month10NoSmallCodeSemanticsCoreChecklist

def toProofLengthCodeSemanticsCoreChecklist
    (h : Month9Month10NoSmallCodeSemanticsCoreChecklist.{q}) :
    Month9Month10ProofLengthCodeSemanticsCoreChecklist.{q} where
  theorem5_proof_length_code_core :=
    h.theorem5_no_small_code_core.toProofLengthCodeSemanticsCore
  strengthened_to_partial := h.strengthened_to_partial
  transfer_to_graft := h.transfer_to_graft
  computable_gap := h.computable_gap

def toProjectChecklist
    (h : Month9Month10NoSmallCodeSemanticsCoreChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10ProjectCollisionChecklist :=
  h.toProofLengthCodeSemanticsCoreChecklist.toProjectChecklist project_upper

theorem no_small_codes_to_minProofCodeSize_lower_bound
    (h : Month9Month10NoSmallCodeSemanticsCoreChecklist.{q}) :
    ∀ f : Nat → Real, _root_.is_polynomial_bound f →
      ∃ᶠ n in atTop,
        (h.theorem5_no_small_code_core.proof_code_semantics.minProofCodeSize
          (h.theorem5_no_small_code_core.scale_data.powerBoundRawCode n)
          ⟨n, rfl⟩ : Real) > f n :=
  h.theorem5_no_small_code_core.proof_code_lower_bound

theorem calibration_proof_length_eq_minProofCodeSize
    (h : Month9Month10NoSmallCodeSemanticsCoreChecklist.{q})
    (code : _root_.FormulaCode)
    (hcode :
      InternalPudlakTheorem5PowerBoundRelevantCode
        h.theorem5_no_small_code_core.scale_data code) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize code =
      (h.theorem5_no_small_code_core.proof_code_semantics.minProofCodeSize
        code hcode : Real) :=
  h.theorem5_no_small_code_core
    |>.toProofLengthCodeSemanticsCore
    |>.proof_length_eq_minProofCodeSize code hcode

theorem project_collision_witness_n_eq_max
    (h : Month9Month10NoSmallCodeSemanticsCoreChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((h.toProjectChecklist project_upper).projectCollisionWitnessOfRationality
      hrat).n =
      max ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).upperN
        ((h.toProjectChecklist project_upper).witness_checklist.computable_gap
          |>.gap_for_polynomial_upper
            ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).U
            ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).polynomial
          |>.threshold) :=
  h.toProofLengthCodeSemanticsCoreChecklist.project_collision_witness_n_eq_max
    project_upper hrat

theorem project_computed_n_contradiction
    (h : Month9Month10NoSmallCodeSemanticsCoreChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.toProjectChecklist project_upper).computed_n_contradiction hrat

theorem project_not_rational_eq_generic_core
    (h : Month9Month10NoSmallCodeSemanticsCoreChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (h.toProjectChecklist project_upper).not_rational =
      GenericRationalCollisionInputs.not_rational
        (h.toProjectChecklist project_upper).toGenericCollisionInputs :=
  (h.toProjectChecklist project_upper).not_rational_eq_generic_core

end Month9Month10NoSmallCodeSemanticsCoreChecklist

/-- Finite-search/no-small-code checklist.  This is stricter than the
`NoSmallCodeSemanticsCore` checklist: the lower-bound input is now a finite
enumeration of all proof codes below a cutoff, plus a checker rejection proof
for every enumerated candidate. -/
structure Month9Month10FiniteSearchNoSmallCodeChecklist : Type (q + 1) where
  theorem5_finite_search_core :
    InternalPudlakTheorem5FiniteSearchNoSmallCore.{q}
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  transfer_to_graft :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer
  computable_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox

namespace Month9Month10FiniteSearchNoSmallCodeChecklist

def toNoSmallCodeSemanticsCoreChecklist
    (h : Month9Month10FiniteSearchNoSmallCodeChecklist.{q}) :
    Month9Month10NoSmallCodeSemanticsCoreChecklist.{q} where
  theorem5_no_small_code_core :=
    h.theorem5_finite_search_core.toNoSmallCodeSemanticsCore
  strengthened_to_partial := h.strengthened_to_partial
  transfer_to_graft := h.transfer_to_graft
  computable_gap := h.computable_gap

def toProofLengthCodeSemanticsCoreChecklist
    (h : Month9Month10FiniteSearchNoSmallCodeChecklist.{q}) :
    Month9Month10ProofLengthCodeSemanticsCoreChecklist.{q} :=
  h.toNoSmallCodeSemanticsCoreChecklist
    |>.toProofLengthCodeSemanticsCoreChecklist

def toProjectChecklist
    (h : Month9Month10FiniteSearchNoSmallCodeChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10ProjectCollisionChecklist :=
  h.toNoSmallCodeSemanticsCoreChecklist.toProjectChecklist project_upper

theorem finite_search_exclusion_statement
    (h : Month9Month10FiniteSearchNoSmallCodeChecklist.{q}) :
    InternalPudlakTheorem5FiniteSearchExclusion
      h.theorem5_finite_search_core.scale_data
      h.theorem5_finite_search_core.proof_code_semantics
      h.theorem5_finite_search_core.small_code_search :=
  h.theorem5_finite_search_core.finite_search_exclusion

theorem finite_search_exclusion_to_no_small
    (h : Month9Month10FiniteSearchNoSmallCodeChecklist.{q}) :
    InternalPudlakTheorem5NoSmallProofCodes
      h.theorem5_finite_search_core.scale_data
      h.theorem5_finite_search_core.proof_code_semantics :=
  h.theorem5_finite_search_core.no_small_proof_codes

theorem small_code_search_complete
    (h : Month9Month10FiniteSearchNoSmallCodeChecklist.{q}) :
    ∀ n K : Nat, ∀ c : h.theorem5_finite_search_core.proof_code_semantics.Code,
      h.theorem5_finite_search_core.proof_code_semantics.checks c
        (h.theorem5_finite_search_core.scale_data.powerBoundRawCode n) →
        h.theorem5_finite_search_core.proof_code_semantics.size c < K →
          c ∈ h.theorem5_finite_search_core.small_code_search.candidates n K :=
  h.theorem5_finite_search_core.small_code_search.complete

theorem no_small_codes_to_minProofCodeSize_lower_bound
    (h : Month9Month10FiniteSearchNoSmallCodeChecklist.{q}) :
    ∀ f : Nat → Real, _root_.is_polynomial_bound f →
      ∃ᶠ n in atTop,
        (h.theorem5_finite_search_core.proof_code_semantics.minProofCodeSize
          (h.theorem5_finite_search_core.scale_data.powerBoundRawCode n)
          ⟨n, rfl⟩ : Real) > f n :=
  h.theorem5_finite_search_core
    |>.toNoSmallCodeSemanticsCore
    |>.proof_code_lower_bound

theorem calibration_proof_length_eq_minProofCodeSize
    (h : Month9Month10FiniteSearchNoSmallCodeChecklist.{q})
    (code : _root_.FormulaCode)
    (hcode :
      InternalPudlakTheorem5PowerBoundRelevantCode
        h.theorem5_finite_search_core.scale_data code) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize code =
      (h.theorem5_finite_search_core.proof_code_semantics.minProofCodeSize
        code hcode : Real) :=
  h.theorem5_finite_search_core
    |>.toNoSmallCodeSemanticsCore
    |>.toProofLengthCodeSemanticsCore
    |>.proof_length_eq_minProofCodeSize code hcode

theorem project_collision_witness_n_eq_max
    (h : Month9Month10FiniteSearchNoSmallCodeChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((h.toProjectChecklist project_upper).projectCollisionWitnessOfRationality
      hrat).n =
      max ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).upperN
        ((h.toProjectChecklist project_upper).witness_checklist.computable_gap
          |>.gap_for_polynomial_upper
            ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).U
            ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).polynomial
          |>.threshold) :=
  h.toNoSmallCodeSemanticsCoreChecklist.project_collision_witness_n_eq_max
    project_upper hrat

theorem project_computed_n_contradiction
    (h : Month9Month10FiniteSearchNoSmallCodeChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.toProjectChecklist project_upper).computed_n_contradiction hrat

theorem project_not_rational_eq_generic_core
    (h : Month9Month10FiniteSearchNoSmallCodeChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (h.toProjectChecklist project_upper).not_rational =
      GenericRationalCollisionInputs.not_rational
        (h.toProjectChecklist project_upper).toGenericCollisionInputs :=
  (h.toProjectChecklist project_upper).not_rational_eq_generic_core

end Month9Month10FiniteSearchNoSmallCodeChecklist

/-- Computable finite-search checklist.  This strengthens the finite-search
frontier by exposing the lower-bound witness extractor `witness f hf N`, so the
project can compute an index beyond any requested threshold before forming the
final collision witness. -/
structure Month9Month10ComputableFiniteSearchNoSmallCodeChecklist :
    Type (q + 1) where
  theorem5_computable_search_core :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  transfer_to_graft :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer
  computable_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox

namespace Month9Month10ComputableFiniteSearchNoSmallCodeChecklist

def toFiniteSearchNoSmallCodeChecklist
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q}) :
    Month9Month10FiniteSearchNoSmallCodeChecklist.{q} where
  theorem5_finite_search_core :=
    h.theorem5_computable_search_core.toFiniteSearchNoSmallCore
  strengthened_to_partial := h.strengthened_to_partial
  transfer_to_graft := h.transfer_to_graft
  computable_gap := h.computable_gap

def toNoSmallCodeSemanticsCoreChecklist
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q}) :
    Month9Month10NoSmallCodeSemanticsCoreChecklist.{q} :=
  h.toFiniteSearchNoSmallCodeChecklist
    |>.toNoSmallCodeSemanticsCoreChecklist

def toProjectChecklist
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10ProjectCollisionChecklist :=
  h.toFiniteSearchNoSmallCodeChecklist.toProjectChecklist project_upper

theorem computable_search_to_finite_search_exclusion
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q}) :
    InternalPudlakTheorem5FiniteSearchExclusion
      h.theorem5_computable_search_core.scale_data
      h.theorem5_computable_search_core.proof_code_semantics
      h.theorem5_computable_search_core.small_code_search :=
  h.theorem5_computable_search_core.finite_search_exclusion

theorem computable_search_witness_ge
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    N ≤ h.theorem5_computable_search_core.computable_search_exclusion.witness f hf N :=
  h.theorem5_computable_search_core.witness_ge f hf N

theorem computable_search_cutoff_gt_at_witness
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    f (h.theorem5_computable_search_core.computable_search_exclusion.witness f hf N) <
      (h.theorem5_computable_search_core.computable_search_exclusion.cutoff f hf N :
        Real) :=
  h.theorem5_computable_search_core.cutoff_gt_at_witness f hf N

theorem computable_search_rejects_candidates_at_witness
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat)
    (c : h.theorem5_computable_search_core.proof_code_semantics.Code)
    (hmem :
      c ∈ h.theorem5_computable_search_core.small_code_search.candidates
        (h.theorem5_computable_search_core.computable_search_exclusion.witness f hf N)
        (h.theorem5_computable_search_core.computable_search_exclusion.cutoff f hf N)) :
    ¬ h.theorem5_computable_search_core.proof_code_semantics.checks c
      (h.theorem5_computable_search_core.scale_data.powerBoundRawCode
        (h.theorem5_computable_search_core.computable_search_exclusion.witness f hf N)) :=
  h.theorem5_computable_search_core.rejects_candidates_at_witness f hf N c hmem

def computedLowerSearchWitness
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    InternalPudlakTheorem5ComputedLowerSearchWitness
      h.theorem5_computable_search_core.scale_data
      h.theorem5_computable_search_core.proof_code_semantics
      h.theorem5_computable_search_core.small_code_search f hf N :=
  h.theorem5_computable_search_core.computable_search_exclusion
    |>.computedLowerSearchWitness f hf N

theorem computed_lower_search_witness_ge
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    N ≤ (h.computedLowerSearchWitness f hf N).n :=
  (h.computedLowerSearchWitness f hf N).n_ge

theorem computed_lower_search_cutoff_gt
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    f (h.computedLowerSearchWitness f hf N).n <
      ((h.computedLowerSearchWitness f hf N).K : Real) :=
  (h.computedLowerSearchWitness f hf N).cutoff_gt

theorem computed_lower_search_minProofCodeSize_gt
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    (h.theorem5_computable_search_core.proof_code_semantics.minProofCodeSize
      (h.theorem5_computable_search_core.scale_data.powerBoundRawCode
        (h.computedLowerSearchWitness f hf N).n)
      ⟨(h.computedLowerSearchWitness f hf N).n, rfl⟩ : Real) >
      f (h.computedLowerSearchWitness f hf N).n :=
  (h.computedLowerSearchWitness f hf N).minProofCodeSize_gt

theorem computed_lower_search_nonempty
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q}) :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      Nonempty
        (InternalPudlakTheorem5ComputedLowerSearchWitness
          h.theorem5_computable_search_core.scale_data
          h.theorem5_computable_search_core.proof_code_semantics
          h.theorem5_computable_search_core.small_code_search f hf N) := by
  intro f hf N
  exact ⟨h.computedLowerSearchWitness f hf N⟩

theorem no_small_codes_to_minProofCodeSize_lower_bound
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q}) :
    ∀ f : Nat → Real, _root_.is_polynomial_bound f →
      ∃ᶠ n in atTop,
        (h.theorem5_computable_search_core.proof_code_semantics.minProofCodeSize
          (h.theorem5_computable_search_core.scale_data.powerBoundRawCode n)
          ⟨n, rfl⟩ : Real) > f n :=
  h.theorem5_computable_search_core
    |>.toNoSmallCodeSemanticsCore
    |>.proof_code_lower_bound

theorem direct_powerBoundLowerBound_from_computable_search
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q}) :
    h.theorem5_computable_search_core.scale_data.PowerBoundLowerBound :=
  h.theorem5_computable_search_core.toPowerBoundLowerBound_direct

theorem direct_rescaledLowerBound_from_computable_search
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q}) :
    _root_.StrongRescaledExternalStrengthenedLowerBound
      h.theorem5_computable_search_core.scale_data.rawCode
      h.theorem5_computable_search_core.scale_data.scale :=
  h.theorem5_computable_search_core.toRescaledLowerBound_direct

def directLowerBoundCore
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q}) :
    InternalPudlakTheorem5LowerBoundCore :=
  h.theorem5_computable_search_core.toLowerBoundCore_direct

theorem directLowerBoundCore_eq_wrapped
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q}) :
    h.directLowerBoundCore =
      h.theorem5_computable_search_core.toLowerBoundCore := by
  rfl

def directInternalFiniteConsistencyLowerBoundMachine
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q}) :
    InternalFiniteConsistencyLowerBoundMachine :=
  h.theorem5_computable_search_core
    |>.toInternalFiniteConsistencyLowerBoundMachine_direct
        h.strengthened_to_partial

theorem directInternalFiniteConsistencyLowerBoundMachine_eq_wrapped
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q}) :
    h.directInternalFiniteConsistencyLowerBoundMachine =
      InternalPudlakTheorem5LowerBoundCore.toInternalFiniteConsistencyLowerBoundMachine
        h.theorem5_computable_search_core.toLowerBoundCore
        h.strengthened_to_partial := by
  rfl

theorem direct_internal_machine_gap_after_trace
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ∃ g : Nat → Real,
      _root_.is_polynomial_bound g ∧
        ∃ n : Nat, N ≤ n ∧ U n < sondowProjectLocalPudlakCollisionBox n :=
  h.theorem5_computable_search_core.direct_internal_machine_gap_after_trace
    h.strengthened_to_partial h.transfer_to_graft U hU N

theorem project_collision_witness_n_eq_max
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((h.toProjectChecklist project_upper).projectCollisionWitnessOfRationality
      hrat).n =
      max ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).upperN
        ((h.toProjectChecklist project_upper).witness_checklist.computable_gap
          |>.gap_for_polynomial_upper
            ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).U
            ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).polynomial
          |>.threshold) :=
  h.toFiniteSearchNoSmallCodeChecklist.project_collision_witness_n_eq_max
    project_upper hrat

def projectLowerSearchWitnessOfRationality
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    InternalPudlakTheorem5ComputedLowerSearchWitness
      h.theorem5_computable_search_core.scale_data
      h.theorem5_computable_search_core.proof_code_semantics
      h.theorem5_computable_search_core.small_code_search
      ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).U
      ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).polynomial
      ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).upperN :=
  h.computedLowerSearchWitness
    ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).U
    ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).polynomial
    ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).upperN

theorem project_lower_search_witness_ge_upperN
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).upperN ≤
      (h.projectLowerSearchWitnessOfRationality project_upper hrat).n :=
  (h.projectLowerSearchWitnessOfRationality project_upper hrat).n_ge

theorem project_lower_search_minProofCodeSize_gt_upper
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.theorem5_computable_search_core.proof_code_semantics.minProofCodeSize
      (h.theorem5_computable_search_core.scale_data.powerBoundRawCode
        (h.projectLowerSearchWitnessOfRationality project_upper hrat).n)
      ⟨(h.projectLowerSearchWitnessOfRationality project_upper hrat).n, rfl⟩ :
        Real) >
      ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).U
        (h.projectLowerSearchWitnessOfRationality project_upper hrat).n :=
  (h.projectLowerSearchWitnessOfRationality project_upper hrat).minProofCodeSize_gt

theorem project_lower_search_rejects_candidates
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni)
    (c : h.theorem5_computable_search_core.proof_code_semantics.Code)
    (hmem :
      c ∈ h.theorem5_computable_search_core.small_code_search.candidates
        (h.projectLowerSearchWitnessOfRationality project_upper hrat).n
        (h.projectLowerSearchWitnessOfRationality project_upper hrat).K) :
    ¬ h.theorem5_computable_search_core.proof_code_semantics.checks c
      (h.theorem5_computable_search_core.scale_data.powerBoundRawCode
        (h.projectLowerSearchWitnessOfRationality project_upper hrat).n) :=
  (h.projectLowerSearchWitnessOfRationality project_upper hrat).rejects_candidates c hmem

theorem project_computed_n_contradiction
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.toProjectChecklist project_upper).computed_n_contradiction hrat

theorem project_not_rational_eq_generic_core
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (h.toProjectChecklist project_upper).not_rational =
      GenericRationalCollisionInputs.not_rational
        (h.toProjectChecklist project_upper).toGenericCollisionInputs :=
  (h.toProjectChecklist project_upper).not_rational_eq_generic_core

end Month9Month10ComputableFiniteSearchNoSmallCodeChecklist

/-- Project-box-aligned computable search checklist.  This is the point where
the Month 10 computable theorem-5 search witness is allowed to become a project
collision witness: it carries the explicit same-object alignment from the
theorem-5 `powerBoundRawCode` checker to `sondowProjectLocalPudlakCollisionBox`.
-/
structure Month9Month10ProjectBoxAlignedComputableSearchChecklist :
    Type (q + 1) where
  computable_search_checklist :
    Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q}
  project_box_alignment :
    InternalPudlakTheorem5ProjectBoxAlignment
      computable_search_checklist.theorem5_computable_search_core.scale_data
      computable_search_checklist.theorem5_computable_search_core.proof_code_semantics

namespace Month9Month10ProjectBoxAlignedComputableSearchChecklist

def theorem5_computable_search_core
    (h : Month9Month10ProjectBoxAlignedComputableSearchChecklist.{q}) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} :=
  h.computable_search_checklist.theorem5_computable_search_core

def theorem5_search_exclusion
    (h : Month9Month10ProjectBoxAlignedComputableSearchChecklist.{q}) :
    InternalPudlakTheorem5ComputableFiniteSearchExclusion
      h.theorem5_computable_search_core.scale_data
      h.theorem5_computable_search_core.proof_code_semantics
      h.theorem5_computable_search_core.small_code_search :=
  h.theorem5_computable_search_core.computable_search_exclusion

def toComputableSearchGapCertificate
    (h : Month9Month10ProjectBoxAlignedComputableSearchChecklist.{q}) :
    ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox :=
  h.project_box_alignment.toComputableSearchGapCertificate
    h.theorem5_search_exclusion

def toProjectChecklist
    (h : Month9Month10ProjectBoxAlignedComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10ProjectCollisionChecklist :=
  h.computable_search_checklist.toProjectChecklist project_upper

def upperUnderRationality
    (h : Month9Month10ProjectBoxAlignedComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    _root_.is_rational _root_.euler_mascheroni →
      ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
        ∃ upperN : Nat,
          ∀ n : Nat, upperN ≤ n →
            sondowProjectLocalPudlakCollisionBox n ≤ U n :=
  (h.toProjectChecklist project_upper).upperUnderRationality

def toSearchGenericCollisionInputs
    (h : Month9Month10ProjectBoxAlignedComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    GenericRationalCollisionInputs :=
  h.toComputableSearchGapCertificate.toGenericRationalCollisionInputs
    (h.upperUnderRationality project_upper)

noncomputable def upperTailOfRationality
    (h : Month9Month10ProjectBoxAlignedComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox :=
  (h.toProjectChecklist project_upper).upperTailOfRationality hrat

noncomputable def projectSearchCollisionWitnessOfRationality
    (h : Month9Month10ProjectBoxAlignedComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ComputedSearchCollisionWitness
      (h.upperTailOfRationality project_upper hrat).U
      sondowProjectLocalPudlakCollisionBox :=
  h.toComputableSearchGapCertificate.collisionWitness
    (h.upperTailOfRationality project_upper hrat)

theorem project_search_witness_eq_lower_search
    (h : Month9Month10ProjectBoxAlignedComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n =
      (h.computable_search_checklist.projectLowerSearchWitnessOfRationality
        project_upper hrat).n := by
  rfl

/-- Full same-witness audit for the project-box-aligned search route.  The
project collision witness is definitionally the finite-search lower witness, and
the latter still carries the cutoff, finite candidate rejection, no-small proof
code statement, checked minimum-size lower bound, and final contradiction. -/
theorem project_search_witness_full_lower_search_trace
    (h : Month9Month10ProjectBoxAlignedComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let upper := h.upperTailOfRationality project_upper hrat
    let w :=
      h.computable_search_checklist.projectLowerSearchWitnessOfRationality
        project_upper hrat
    (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n =
        w.n ∧
      upper.upperN ≤ w.n ∧
        upper.U w.n < (w.K : Real) ∧
          (∀ c : h.theorem5_computable_search_core.proof_code_semantics.Code,
            c ∈ h.theorem5_computable_search_core.small_code_search.candidates
              w.n w.K →
              ¬ h.theorem5_computable_search_core.proof_code_semantics.checks c
                (h.theorem5_computable_search_core.scale_data.powerBoundRawCode
                  w.n)) ∧
          (∀ c : h.theorem5_computable_search_core.proof_code_semantics.Code,
            h.theorem5_computable_search_core.proof_code_semantics.checks c
              (h.theorem5_computable_search_core.scale_data.powerBoundRawCode
                w.n) →
              upper.U w.n <
                (h.theorem5_computable_search_core.proof_code_semantics.size c :
                  Real)) ∧
          (h.theorem5_computable_search_core.proof_code_semantics.minProofCodeSize
              (h.theorem5_computable_search_core.scale_data.powerBoundRawCode
                w.n) ⟨w.n, rfl⟩ : Real) >
            upper.U w.n ∧
          upper.U
              (h.projectSearchCollisionWitnessOfRationality
                project_upper hrat).n <
            sondowProjectLocalPudlakCollisionBox
              (h.projectSearchCollisionWitnessOfRationality
                project_upper hrat).n ∧
          sondowProjectLocalPudlakCollisionBox
              (h.projectSearchCollisionWitnessOfRationality
                project_upper hrat).n ≤
            upper.U
              (h.projectSearchCollisionWitnessOfRationality
                project_upper hrat).n ∧
          False := by
  let upper := h.upperTailOfRationality project_upper hrat
  let w :=
    h.computable_search_checklist.projectLowerSearchWitnessOfRationality
      project_upper hrat
  exact
    ⟨rfl,
      w.n_ge,
      w.cutoff_gt,
      w.rejects_candidates,
      w.no_small_at_n,
      w.minProofCodeSize_gt,
      (h.projectSearchCollisionWitnessOfRationality
        project_upper hrat).lower_at_n,
      (h.projectSearchCollisionWitnessOfRationality
        project_upper hrat).upper_at_n,
      (h.projectSearchCollisionWitnessOfRationality
        project_upper hrat).contradiction⟩

theorem project_search_witness_ge_upperN
    (h : Month9Month10ProjectBoxAlignedComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.upperTailOfRationality project_upper hrat).upperN ≤
      (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n :=
  (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n_ge_upper

theorem project_search_gap_at_witness
    (h : Month9Month10ProjectBoxAlignedComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.upperTailOfRationality project_upper hrat).U
        (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n <
      sondowProjectLocalPudlakCollisionBox
        (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n :=
  (h.projectSearchCollisionWitnessOfRationality project_upper hrat).lower_at_n

theorem project_search_upper_at_witness
    (h : Month9Month10ProjectBoxAlignedComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    sondowProjectLocalPudlakCollisionBox
        (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n ≤
      (h.upperTailOfRationality project_upper hrat).U
        (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n :=
  (h.projectSearchCollisionWitnessOfRationality project_upper hrat).upper_at_n

theorem project_search_computed_n_contradiction
    (h : Month9Month10ProjectBoxAlignedComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.projectSearchCollisionWitnessOfRationality project_upper hrat).contradiction

theorem search_not_rational
    (h : Month9Month10ProjectBoxAlignedComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat => h.project_search_computed_n_contradiction project_upper hrat

theorem search_not_rational_eq_generic_core
    (h : Month9Month10ProjectBoxAlignedComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    h.search_not_rational project_upper =
      GenericRationalCollisionInputs.not_rational
        (h.toSearchGenericCollisionInputs project_upper) :=
  h.toComputableSearchGapCertificate.not_rational_eq_generic_core
    (h.upperUnderRationality project_upper)

end Month9Month10ProjectBoxAlignedComputableSearchChecklist

/-- Transfer-based computable project-search checklist.  Unlike
`Month9Month10ProjectBoxAlignedComputableSearchChecklist`, this layer does not
require direct equality between the theorem-5 code family and the project box;
it asks for the exact computable transfer certificate needed by the collision
core. -/
structure Month9Month10ProjectGapTransferComputableSearchChecklist :
    Type (q + 1) where
  computable_search_checklist :
    Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q}
  project_gap_transfer :
    InternalPudlakTheorem5ComputableProjectGapTransfer
      computable_search_checklist.theorem5_computable_search_core.scale_data
      computable_search_checklist.theorem5_computable_search_core.proof_code_semantics
      computable_search_checklist.theorem5_computable_search_core.small_code_search

namespace Month9Month10ProjectGapTransferComputableSearchChecklist

def theorem5_computable_search_core
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q}) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} :=
  h.computable_search_checklist.theorem5_computable_search_core

def theorem5_search_exclusion
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q}) :
    InternalPudlakTheorem5ComputableFiniteSearchExclusion
      h.theorem5_computable_search_core.scale_data
      h.theorem5_computable_search_core.proof_code_semantics
      h.theorem5_computable_search_core.small_code_search :=
  h.theorem5_computable_search_core.computable_search_exclusion

def toComputableSearchGapCertificate
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q}) :
    ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox :=
  h.project_gap_transfer.toComputableSearchGapCertificate
    h.theorem5_search_exclusion

def toProjectChecklist
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10ProjectCollisionChecklist :=
  h.computable_search_checklist.toProjectChecklist project_upper

def upperUnderRationality
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    _root_.is_rational _root_.euler_mascheroni →
      ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
        ∃ upperN : Nat,
          ∀ n : Nat, upperN ≤ n →
            sondowProjectLocalPudlakCollisionBox n ≤ U n :=
  (h.toProjectChecklist project_upper).upperUnderRationality

def toSearchGenericCollisionInputs
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    GenericRationalCollisionInputs :=
  h.toComputableSearchGapCertificate.toGenericRationalCollisionInputs
    (h.upperUnderRationality project_upper)

def projectSearchCollisionWitness
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q})
    (upper : PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox) :
    ComputedSearchCollisionWitness upper.U
      sondowProjectLocalPudlakCollisionBox :=
  h.toComputableSearchGapCertificate.collisionWitness upper

theorem project_search_witness_eq_gap_transfer_witness_for_upper
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q})
    (upper : PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox) :
    (h.projectSearchCollisionWitness upper).n =
      ((h.toComputableSearchGapCertificate.gap_for_polynomial_upper
          upper.U upper.polynomial).witness upper.upperN) :=
  rfl

/-- Payload-free calculation trace once the Sondow side has already supplied a
polynomial upper-tail certificate.  This is the exact computation core for the
final printed witness number: the witness is the project-gap-transfer search
result at `upper.upperN`, and the two certified inequalities contradict. -/
theorem project_gap_transfer_computed_witness_for_upper_full_trace
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q})
    (upper : PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox) :
    let gap :=
      h.toComputableSearchGapCertificate.gap_for_polynomial_upper
        upper.U upper.polynomial
    let witness := h.projectSearchCollisionWitness upper
    witness.n = gap.witness upper.upperN ∧
      upper.upperN ≤ witness.n ∧
        upper.U witness.n < sondowProjectLocalPudlakCollisionBox witness.n ∧
          sondowProjectLocalPudlakCollisionBox witness.n ≤ upper.U witness.n ∧
            False := by
  let witness := h.projectSearchCollisionWitness upper
  exact
    ⟨rfl,
      witness.n_ge_upper,
      witness.lower_at_n,
      witness.upper_at_n,
      witness.contradiction⟩

noncomputable def upperTailOfRationality
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox :=
  (h.toProjectChecklist project_upper).upperTailOfRationality hrat

noncomputable def projectSearchCollisionWitnessOfRationality
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ComputedSearchCollisionWitness
      (h.upperTailOfRationality project_upper hrat).U
      sondowProjectLocalPudlakCollisionBox :=
  h.toComputableSearchGapCertificate.collisionWitness
    (h.upperTailOfRationality project_upper hrat)

theorem project_search_witness_eq_gap_transfer_witness
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n =
      ((h.toComputableSearchGapCertificate.gap_for_polynomial_upper
          (h.upperTailOfRationality project_upper hrat).U
          (h.upperTailOfRationality project_upper hrat).polynomial).witness
        (h.upperTailOfRationality project_upper hrat).upperN) :=
  rfl

/-- Endpoint trace for the project-gap-transfer search route.  This is the
calculation shape the evaluator has to expose: the final contradiction witness
is exactly the lower gap witness returned by the computable project transfer at
the upper route's threshold. -/
theorem project_gap_transfer_computed_witness_full_trace
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let upper := h.upperTailOfRationality project_upper hrat
    let gap :=
      h.toComputableSearchGapCertificate.gap_for_polynomial_upper
        upper.U upper.polynomial
    let witness := h.projectSearchCollisionWitnessOfRationality project_upper hrat
    witness.n = gap.witness upper.upperN ∧
      upper.upperN ≤ witness.n ∧
        upper.U witness.n < sondowProjectLocalPudlakCollisionBox witness.n ∧
          sondowProjectLocalPudlakCollisionBox witness.n ≤ upper.U witness.n ∧
            False := by
  let upper := h.upperTailOfRationality project_upper hrat
  let witness := h.projectSearchCollisionWitnessOfRationality project_upper hrat
  exact
    ⟨rfl,
      witness.n_ge_upper,
      witness.lower_at_n,
      witness.upper_at_n,
      witness.contradiction⟩

theorem project_search_witness_ge_upperN
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.upperTailOfRationality project_upper hrat).upperN ≤
      (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n :=
  (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n_ge_upper

theorem project_search_gap_at_witness
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.upperTailOfRationality project_upper hrat).U
        (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n <
      sondowProjectLocalPudlakCollisionBox
        (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n :=
  (h.projectSearchCollisionWitnessOfRationality project_upper hrat).lower_at_n

theorem project_search_upper_at_witness
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    sondowProjectLocalPudlakCollisionBox
        (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n ≤
      (h.upperTailOfRationality project_upper hrat).U
        (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n :=
  (h.projectSearchCollisionWitnessOfRationality project_upper hrat).upper_at_n

theorem project_search_computed_n_contradiction
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.projectSearchCollisionWitnessOfRationality project_upper hrat).contradiction

theorem search_not_rational
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat => h.project_search_computed_n_contradiction project_upper hrat

theorem search_not_rational_eq_generic_core
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    h.search_not_rational project_upper =
      GenericRationalCollisionInputs.not_rational
        (h.toSearchGenericCollisionInputs project_upper) :=
  h.toComputableSearchGapCertificate.not_rational_eq_generic_core
    (h.upperUnderRationality project_upper)

end Month9Month10ProjectGapTransferComputableSearchChecklist

namespace Month9Month10ComputableFiniteSearchNoSmallCodeChecklist

def toProjectCollisionInputsOfConstantPieces
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
    SondowProjectLocalPudlakCollisionInputs :=
  h.theorem5_computable_search_core.toLowerBoundCore
    |>.toProjectCollisionInputsOfConstantPieces
      project_upper strengthened_to_partial partial_to_graft

theorem toProjectCollisionInputsOfConstantPieces_pudlak_lower_bound
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
    (h.toProjectCollisionInputsOfConstantPieces
        project_upper strengthened_to_partial partial_to_graft).pudlak_lower_bound =
      (h.theorem5_computable_search_core.toLowerBoundCore
        |>.toPudlakFiniteConsistencyLowerBoundPackage
          (InternalPudlakTheorem5TransferPieces.strengthenedToPartialTransferOfConstant
            strengthened_to_partial)) :=
  rfl

theorem toProjectCollisionInputsOfConstantPieces_transfer_to_graft
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
    (h.toProjectCollisionInputsOfConstantPieces
        project_upper strengthened_to_partial partial_to_graft).transfer_to_graft =
      InternalPudlakTheorem5TransferPieces.partialToGraftTransferOfConstant
        partial_to_graft :=
  rfl

theorem scale_projection_pieces_same_constant_certificates_as_project_inputs
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
    Nonempty
        (_root_.ConstantProofLengthProjection
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          h.theorem5_computable_search_core.scale_data.powerBoundRawCode
          (fun n : Nat =>
            _root_.sondowReflectionGraftCode
              (h.theorem5_computable_search_core.scale_data.scale n))) ∧
      (h.toProjectCollisionInputsOfConstantPieces
          project_upper strengthened_to_partial partial_to_graft).transfer_to_graft =
        InternalPudlakTheorem5TransferPieces.partialToGraftTransferOfConstant
          partial_to_graft :=
  ⟨⟨h.theorem5_computable_search_core.scale_data
      |>.powerBoundToScaledReflectionGraftConstantProjection
        strengthened_to_partial partial_to_graft⟩,
    h.toProjectCollisionInputsOfConstantPieces_transfer_to_graft
      project_upper strengthened_to_partial partial_to_graft⟩

def toProjectGapTransferChecklistOfAdditiveProjection
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        h.theorem5_computable_search_core.scale_data
        h.theorem5_computable_search_core.proof_code_semantics) :
    Month9Month10ProjectGapTransferComputableSearchChecklist.{q} where
  computable_search_checklist := h
  project_gap_transfer := projection.toComputableProjectGapTransfer

def toProjectGapTransferChecklistOfLocalHilbertProjection
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (projection :
      InternalPudlakTheorem5LocalHilbertProjectBoxProjection
        h.theorem5_computable_search_core.scale_data
        h.theorem5_computable_search_core.proof_code_semantics
        interp) :
    Month9Month10ProjectGapTransferComputableSearchChecklist.{q} :=
  h.toProjectGapTransferChecklistOfAdditiveProjection
    projection.toAdditiveProjectBoxProjection

/-- Local-Hilbert witness equation.  The project gap witness produced by the
local `+2` projection is exactly the source finite-search witness for the
shifted upper bound `U + 2`. -/
theorem project_gap_witness_eq_local_hilbert_source_search
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (projection :
      InternalPudlakTheorem5LocalHilbertProjectBoxProjection
        h.theorem5_computable_search_core.scale_data
        h.theorem5_computable_search_core.proof_code_semantics
        interp)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (((h.toProjectGapTransferChecklistOfLocalHilbertProjection projection)
      |>.toComputableSearchGapCertificate
      |>.gap_for_polynomial_upper U hU).witness N) =
      (h.theorem5_computable_search_core.computable_search_exclusion
        |>.computedLowerSearchWitness
          (projection.toAdditiveProjectBoxProjection.shiftedUpper U)
          (projection.toAdditiveProjectBoxProjection.shiftedUpper_polynomial
            U hU)
          N).n := by
  rfl

def projectSearchCollisionWitnessOfLocalHilbertProjection
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (projection :
      InternalPudlakTheorem5LocalHilbertProjectBoxProjection
        h.theorem5_computable_search_core.scale_data
        h.theorem5_computable_search_core.proof_code_semantics
        interp)
    (upper : PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox) :
    ComputedSearchCollisionWitness upper.U sondowProjectLocalPudlakCollisionBox :=
  (h.toProjectGapTransferChecklistOfLocalHilbertProjection projection)
    |>.projectSearchCollisionWitness upper

theorem project_search_witness_n_eq_local_hilbert_source_search
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (projection :
      InternalPudlakTheorem5LocalHilbertProjectBoxProjection
        h.theorem5_computable_search_core.scale_data
        h.theorem5_computable_search_core.proof_code_semantics
        interp)
    (upper : PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox) :
    (h.projectSearchCollisionWitnessOfLocalHilbertProjection
      projection upper).n =
      (h.theorem5_computable_search_core.computable_search_exclusion
        |>.computedLowerSearchWitness
          (projection.toAdditiveProjectBoxProjection.shiftedUpper upper.U)
          (projection.toAdditiveProjectBoxProjection.shiftedUpper_polynomial
            upper.U upper.polynomial)
          upper.upperN).n := by
  rfl

/-- Payload-free endpoint trace for the local-Hilbert projection route.  Once
the Sondow side supplies an upper-tail certificate, the final collision witness
is exactly the lower finite-search witness for the shifted upper bound induced
by the local Hilbert `+2` projection. -/
theorem project_local_hilbert_computed_witness_for_upper_full_trace
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (projection :
      InternalPudlakTheorem5LocalHilbertProjectBoxProjection
        h.theorem5_computable_search_core.scale_data
        h.theorem5_computable_search_core.proof_code_semantics
        interp)
    (upper : PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox) :
    let w :=
      h.theorem5_computable_search_core.computable_search_exclusion
        |>.computedLowerSearchWitness
          (projection.toAdditiveProjectBoxProjection.shiftedUpper upper.U)
          (projection.toAdditiveProjectBoxProjection.shiftedUpper_polynomial
            upper.U upper.polynomial)
          upper.upperN
    let witness :=
      h.projectSearchCollisionWitnessOfLocalHilbertProjection projection upper
    witness.n = w.n ∧
      upper.upperN ≤ witness.n ∧
        upper.U witness.n < sondowProjectLocalPudlakCollisionBox witness.n ∧
          sondowProjectLocalPudlakCollisionBox witness.n ≤ upper.U witness.n ∧
            False := by
  let witness :=
    h.projectSearchCollisionWitnessOfLocalHilbertProjection projection upper
  exact
    ⟨rfl,
      witness.n_ge_upper,
      witness.lower_at_n,
      witness.upper_at_n,
      witness.contradiction⟩

def toProjectGapTransferChecklistOfConstantProjection
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        h.theorem5_computable_search_core.scale_data.powerBoundRawCode
        _root_.sondowReflectionGraftCode) :
    Month9Month10ProjectGapTransferComputableSearchChecklist.{q} where
  computable_search_checklist := h
  project_gap_transfer :=
    h.theorem5_computable_search_core
      |>.toComputableProjectGapTransferOfConstantProjection projection

def toProjectGapTransferChecklistOfScaledConstantProjection
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (projectIndex : Nat → Nat)
    (projectIndex_ge_source : ∀ n : Nat, n ≤ projectIndex n)
    (projectIndex_polynomial :
      _root_.is_polynomial_bound (fun n : Nat => (projectIndex n : Real)))
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        h.theorem5_computable_search_core.scale_data.powerBoundRawCode
        (fun n : Nat => _root_.sondowReflectionGraftCode (projectIndex n))) :
    Month9Month10ProjectGapTransferComputableSearchChecklist.{q} where
  computable_search_checklist := h
  project_gap_transfer :=
    h.theorem5_computable_search_core
      |>.toScaledComputableProjectGapTransferOfConstantProjection
        projectIndex projectIndex_ge_source projectIndex_polynomial projection

def toProjectGapTransferChecklistOfScaleConstantProjection
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        h.theorem5_computable_search_core.scale_data.powerBoundRawCode
        (fun n : Nat =>
          _root_.sondowReflectionGraftCode
            (h.theorem5_computable_search_core.scale_data.scale n))) :
    Month9Month10ProjectGapTransferComputableSearchChecklist.{q} :=
  h.toProjectGapTransferChecklistOfScaledConstantProjection
    h.theorem5_computable_search_core.scale_data.scale
    h.theorem5_computable_search_core.scale_data.scale_id_le
    h.theorem5_computable_search_core.scale_data.scale_polynomial_bound
    projection

def toProjectGapTransferChecklistOfScaleProjectionPieces
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
    Month9Month10ProjectGapTransferComputableSearchChecklist.{q} :=
  h.toProjectGapTransferChecklistOfScaleConstantProjection
    (h.theorem5_computable_search_core.scale_data
      |>.powerBoundToScaledReflectionGraftConstantProjection
        strengthened_to_partial partial_to_graft)

def scaleProjectionPiecesConstantProjection
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
    _root_.ConstantProofLengthProjection
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      h.theorem5_computable_search_core.scale_data.powerBoundRawCode
      (fun n : Nat =>
        _root_.sondowReflectionGraftCode
          (h.theorem5_computable_search_core.scale_data.scale n)) :=
  h.theorem5_computable_search_core.scale_data
    |>.powerBoundToScaledReflectionGraftConstantProjection
      strengthened_to_partial partial_to_graft

def scaleProjectionPiecesScaledAdditiveProjection
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
    InternalPudlakTheorem5ScaledAdditiveProjectBoxProjection
      h.theorem5_computable_search_core.scale_data
      h.theorem5_computable_search_core.proof_code_semantics :=
  h.theorem5_computable_search_core
    |>.toScaledAdditiveProjectBoxProjectionOfConstantProjection
      h.theorem5_computable_search_core.scale_data.scale
      h.theorem5_computable_search_core.scale_data.scale_id_le
      h.theorem5_computable_search_core.scale_data.scale_polynomial_bound
      (h.scaleProjectionPiecesConstantProjection
        strengthened_to_partial partial_to_graft)

theorem project_gap_witness_eq_scaled_source_search_of_scale_projection_pieces
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (((h.toProjectGapTransferChecklistOfScaleProjectionPieces
        strengthened_to_partial partial_to_graft)
      |>.toComputableSearchGapCertificate
      |>.gap_for_polynomial_upper U hU).witness N) =
      h.theorem5_computable_search_core.scale_data.scale
        ((h.theorem5_computable_search_core.computable_search_exclusion
          |>.computedLowerSearchWitness
            ((h.scaleProjectionPiecesScaledAdditiveProjection
                strengthened_to_partial partial_to_graft)
              |>.indexedShiftedUpper U)
            ((h.scaleProjectionPiecesScaledAdditiveProjection
                strengthened_to_partial partial_to_graft)
              |>.indexedShiftedUpper_polynomial U hU)
            N).n) := by
  rfl

noncomputable def projectSearchCollisionWitnessOfScaleProjectionPieces
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ComputedSearchCollisionWitness
      ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
          strengthened_to_partial partial_to_graft
        |>.upperTailOfRationality project_upper hrat).U)
      sondowProjectLocalPudlakCollisionBox :=
  h.toProjectGapTransferChecklistOfScaleProjectionPieces
    strengthened_to_partial partial_to_graft
    |>.projectSearchCollisionWitnessOfRationality project_upper hrat

theorem project_search_witness_n_eq_scaled_source_search_of_scale_projection_pieces
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.projectSearchCollisionWitnessOfScaleProjectionPieces
      strengthened_to_partial partial_to_graft project_upper hrat).n =
      h.theorem5_computable_search_core.scale_data.scale
        ((h.theorem5_computable_search_core.computable_search_exclusion
          |>.computedLowerSearchWitness
            ((h.scaleProjectionPiecesScaledAdditiveProjection
                strengthened_to_partial partial_to_graft)
              |>.indexedShiftedUpper
                ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
                    strengthened_to_partial partial_to_graft)
                  |>.upperTailOfRationality project_upper hrat).U)
            ((h.scaleProjectionPiecesScaledAdditiveProjection
                strengthened_to_partial partial_to_graft)
              |>.indexedShiftedUpper_polynomial
                ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
                    strengthened_to_partial partial_to_graft)
                  |>.upperTailOfRationality project_upper hrat).U
                ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
                    strengthened_to_partial partial_to_graft)
                  |>.upperTailOfRationality project_upper hrat).polynomial)
            ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
                strengthened_to_partial partial_to_graft)
              |>.upperTailOfRationality project_upper hrat).upperN).n) := by
  rfl

theorem project_search_witness_ge_upperN_of_scale_projection_pieces
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.toProjectGapTransferChecklistOfScaleProjectionPieces
        strengthened_to_partial partial_to_graft
      |>.upperTailOfRationality project_upper hrat).upperN ≤
      (h.projectSearchCollisionWitnessOfScaleProjectionPieces
        strengthened_to_partial partial_to_graft project_upper hrat).n :=
  (h.toProjectGapTransferChecklistOfScaleProjectionPieces
    strengthened_to_partial partial_to_graft)
    |>.project_search_witness_ge_upperN project_upper hrat

theorem project_search_gap_at_witness_of_scale_projection_pieces
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.toProjectGapTransferChecklistOfScaleProjectionPieces
        strengthened_to_partial partial_to_graft
      |>.upperTailOfRationality project_upper hrat).U
        (h.projectSearchCollisionWitnessOfScaleProjectionPieces
          strengthened_to_partial partial_to_graft project_upper hrat).n <
      sondowProjectLocalPudlakCollisionBox
        (h.projectSearchCollisionWitnessOfScaleProjectionPieces
          strengthened_to_partial partial_to_graft project_upper hrat).n :=
  (h.toProjectGapTransferChecklistOfScaleProjectionPieces
    strengthened_to_partial partial_to_graft)
    |>.project_search_gap_at_witness project_upper hrat

theorem project_search_upper_at_witness_of_scale_projection_pieces
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    sondowProjectLocalPudlakCollisionBox
        (h.projectSearchCollisionWitnessOfScaleProjectionPieces
          strengthened_to_partial partial_to_graft project_upper hrat).n ≤
      (h.toProjectGapTransferChecklistOfScaleProjectionPieces
          strengthened_to_partial partial_to_graft
        |>.upperTailOfRationality project_upper hrat).U
        (h.projectSearchCollisionWitnessOfScaleProjectionPieces
          strengthened_to_partial partial_to_graft project_upper hrat).n :=
  (h.toProjectGapTransferChecklistOfScaleProjectionPieces
    strengthened_to_partial partial_to_graft)
    |>.project_search_upper_at_witness project_upper hrat

theorem project_search_computed_n_contradiction_of_scale_projection_pieces
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.toProjectGapTransferChecklistOfScaleProjectionPieces
    strengthened_to_partial partial_to_graft)
    |>.project_search_computed_n_contradiction project_upper hrat

theorem search_not_rational_of_scale_projection_pieces
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat =>
    h.project_search_computed_n_contradiction_of_scale_projection_pieces
      strengthened_to_partial partial_to_graft project_upper hrat

end Month9Month10ComputableFiniteSearchNoSmallCodeChecklist

/-- Project-level checklist whose theorem-5 lower-bound side is supplied by the
checker-native finite enumeration and rejection extractor.  This is the direct
handoff target for the PA/Hilbert checker work: once it supplies a checker,
complete finite enumeration, computable rejection extractor, and proof-length
exactness certificate, the existing Month 9-10 computable collision machinery
can be reused without changing the project collision core. -/
structure Month9Month10CheckerExtractorComputableSearchChecklist :
    Type (q + 1) where
  scale_data : InternalPudlakTheorem5ScaleData
  checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data
  enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker
  extractor :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      checker enumeration
  exactness : InternalPudlakTheorem5CheckerProofLengthExactness checker
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  transfer_to_graft :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer
  computable_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox

namespace Month9Month10CheckerExtractorComputableSearchChecklist

def ofFamilyExactness
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data)
    (enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (transfer_to_graft :
      _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox) :
    Month9Month10CheckerExtractorComputableSearchChecklist.{q} where
  scale_data := scale_data
  checker := checker
  enumeration := enumeration
  extractor := extractor
  exactness := family.toCheckerProofLengthExactness
  strengthened_to_partial := strengthened_to_partial
  transfer_to_graft := transfer_to_graft
  computable_gap := computable_gap

theorem ofFamilyExactness_exactness_iff_family
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data)
    (enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (transfer_to_graft :
      _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox) :
    Nonempty
        (InternalPudlakTheorem5CheckerProofLengthExactness
          (ofFamilyExactness scale_data checker enumeration extractor family
            strengthened_to_partial transfer_to_graft computable_gap).checker) ↔
      Nonempty
        (InternalPudlakTheorem5CheckerProofLengthFamilyExactness
          (ofFamilyExactness scale_data checker enumeration extractor family
            strengthened_to_partial transfer_to_graft computable_gap).checker) :=
  InternalPudlakTheorem5CheckerProofLengthFamilyExactness.checkerProofLengthExactness_iff_familyExactness
    checker

def proof_code_semantics
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q}) :
    _root_.ProofCodeSemantics.{q}
      (InternalPudlakTheorem5PowerBoundRelevantCode h.scale_data) :=
  h.checker.toProofCodeSemantics

def small_code_search
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q}) :
    InternalPudlakTheorem5SmallCodeSearch
      h.scale_data h.proof_code_semantics :=
  h.enumeration.toSmallCodeSearch

def theorem5_computable_search_core
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q}) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} :=
  h.extractor.toComputableFiniteSearchNoSmallCore h.exactness

def toComputableFiniteSearchNoSmallCodeChecklist
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q}) :
    Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q} where
  theorem5_computable_search_core := h.theorem5_computable_search_core
  strengthened_to_partial := h.strengthened_to_partial
  transfer_to_graft := h.transfer_to_graft
  computable_gap := h.computable_gap

def computedLowerSearchWitness
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    InternalPudlakTheorem5ComputedLowerSearchWitness
      h.scale_data h.proof_code_semantics h.small_code_search f hf N :=
  h.extractor.computedLowerSearchWitness f hf N

theorem computedLowerSearchWitness_n_eq_extractor
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    (h.computedLowerSearchWitness f hf N).n =
      h.extractor.witness f hf N :=
  rfl

theorem computedLowerSearchWitness_K_eq_extractor
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    (h.computedLowerSearchWitness f hf N).K =
      h.extractor.cutoff f hf N :=
  rfl

theorem computable_checklist_witness_eq_extractor
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    h.toComputableFiniteSearchNoSmallCodeChecklist.theorem5_computable_search_core.computable_search_exclusion.witness f hf N =
      h.extractor.witness f hf N :=
  rfl

def toProjectChecklist
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10ProjectCollisionChecklist :=
  h.toComputableFiniteSearchNoSmallCodeChecklist.toProjectChecklist project_upper

theorem project_collision_witness_n_eq_max
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((h.toProjectChecklist project_upper).projectCollisionWitnessOfRationality
      hrat).n =
      max ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).upperN
        ((h.toProjectChecklist project_upper).witness_checklist.computable_gap
          |>.gap_for_polynomial_upper
            ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).U
            ((h.toProjectChecklist project_upper).upperTailOfRationality hrat).polynomial
          |>.threshold) :=
  h.toComputableFiniteSearchNoSmallCodeChecklist
    |>.project_collision_witness_n_eq_max project_upper hrat

theorem project_computed_n_contradiction
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.toComputableFiniteSearchNoSmallCodeChecklist
    |>.project_computed_n_contradiction project_upper hrat

theorem search_not_rational
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat => h.project_computed_n_contradiction project_upper hrat

theorem search_not_rational_eq_generic_core
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    h.search_not_rational project_upper =
      GenericRationalCollisionInputs.not_rational
        (h.toProjectChecklist project_upper).toGenericCollisionInputs :=
  h.toComputableFiniteSearchNoSmallCodeChecklist
    |>.project_not_rational_eq_generic_core project_upper

def toProjectGapTransferChecklistOfScaleProjectionPieces
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost) :
    Month9Month10ProjectGapTransferComputableSearchChecklist.{q} :=
  h.toComputableFiniteSearchNoSmallCodeChecklist
    |>.toProjectGapTransferChecklistOfScaleProjectionPieces
      strengthened_to_partial partial_to_graft

noncomputable def projectSearchCollisionWitnessOfScaleProjectionPieces
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ComputedSearchCollisionWitness
      ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
          strengthened_to_partial partial_to_graft
        |>.upperTailOfRationality project_upper hrat).U)
      sondowProjectLocalPudlakCollisionBox :=
  h.toComputableFiniteSearchNoSmallCodeChecklist
    |>.projectSearchCollisionWitnessOfScaleProjectionPieces
      strengthened_to_partial partial_to_graft project_upper hrat

theorem project_gap_witness_eq_scaled_extractor_witness_of_scale_projection_pieces
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (((h.toProjectGapTransferChecklistOfScaleProjectionPieces
        strengthened_to_partial partial_to_graft)
      |>.toComputableSearchGapCertificate
      |>.gap_for_polynomial_upper U hU).witness N) =
      h.scale_data.scale
        (h.extractor.witness
          ((h.toComputableFiniteSearchNoSmallCodeChecklist
              |>.scaleProjectionPiecesScaledAdditiveProjection
                strengthened_to_partial partial_to_graft)
            |>.indexedShiftedUpper U)
          ((h.toComputableFiniteSearchNoSmallCodeChecklist
              |>.scaleProjectionPiecesScaledAdditiveProjection
                strengthened_to_partial partial_to_graft)
            |>.indexedShiftedUpper_polynomial U hU)
          N) := by
  rfl

theorem project_search_witness_n_eq_scaled_extractor_witness_of_scale_projection_pieces
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.projectSearchCollisionWitnessOfScaleProjectionPieces
      strengthened_to_partial partial_to_graft project_upper hrat).n =
      h.scale_data.scale
        (h.extractor.witness
          ((h.toComputableFiniteSearchNoSmallCodeChecklist
              |>.scaleProjectionPiecesScaledAdditiveProjection
                strengthened_to_partial partial_to_graft)
            |>.indexedShiftedUpper
              ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
                  strengthened_to_partial partial_to_graft)
                |>.upperTailOfRationality project_upper hrat).U)
          ((h.toComputableFiniteSearchNoSmallCodeChecklist
              |>.scaleProjectionPiecesScaledAdditiveProjection
                strengthened_to_partial partial_to_graft)
            |>.indexedShiftedUpper_polynomial
              ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
                  strengthened_to_partial partial_to_graft)
                |>.upperTailOfRationality project_upper hrat).U
              ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
                  strengthened_to_partial partial_to_graft)
                |>.upperTailOfRationality project_upper hrat).polynomial)
          ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
              strengthened_to_partial partial_to_graft)
            |>.upperTailOfRationality project_upper hrat).upperN) := by
  rfl

theorem project_search_scaled_extractor_witness_audit_of_scale_projection_pieces
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.projectSearchCollisionWitnessOfScaleProjectionPieces
        strengthened_to_partial partial_to_graft project_upper hrat).n =
        h.scale_data.scale
          (h.extractor.witness
            ((h.toComputableFiniteSearchNoSmallCodeChecklist
                |>.scaleProjectionPiecesScaledAdditiveProjection
                  strengthened_to_partial partial_to_graft)
              |>.indexedShiftedUpper
                ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
                    strengthened_to_partial partial_to_graft)
                  |>.upperTailOfRationality project_upper hrat).U)
            ((h.toComputableFiniteSearchNoSmallCodeChecklist
                |>.scaleProjectionPiecesScaledAdditiveProjection
                  strengthened_to_partial partial_to_graft)
              |>.indexedShiftedUpper_polynomial
                ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
                    strengthened_to_partial partial_to_graft)
                  |>.upperTailOfRationality project_upper hrat).U
                ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
                    strengthened_to_partial partial_to_graft)
                  |>.upperTailOfRationality project_upper hrat).polynomial)
            ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
                strengthened_to_partial partial_to_graft)
              |>.upperTailOfRationality project_upper hrat).upperN) ∧
      (h.toProjectGapTransferChecklistOfScaleProjectionPieces
          strengthened_to_partial partial_to_graft
        |>.upperTailOfRationality project_upper hrat).upperN ≤
        (h.projectSearchCollisionWitnessOfScaleProjectionPieces
          strengthened_to_partial partial_to_graft project_upper hrat).n ∧
      (h.toProjectGapTransferChecklistOfScaleProjectionPieces
          strengthened_to_partial partial_to_graft
        |>.upperTailOfRationality project_upper hrat).U
          (h.projectSearchCollisionWitnessOfScaleProjectionPieces
            strengthened_to_partial partial_to_graft project_upper hrat).n <
        sondowProjectLocalPudlakCollisionBox
          (h.projectSearchCollisionWitnessOfScaleProjectionPieces
            strengthened_to_partial partial_to_graft project_upper hrat).n ∧
      sondowProjectLocalPudlakCollisionBox
          (h.projectSearchCollisionWitnessOfScaleProjectionPieces
            strengthened_to_partial partial_to_graft project_upper hrat).n ≤
        (h.toProjectGapTransferChecklistOfScaleProjectionPieces
            strengthened_to_partial partial_to_graft
          |>.upperTailOfRationality project_upper hrat).U
          (h.projectSearchCollisionWitnessOfScaleProjectionPieces
            strengthened_to_partial partial_to_graft project_upper hrat).n :=
  ⟨h.project_search_witness_n_eq_scaled_extractor_witness_of_scale_projection_pieces
      strengthened_to_partial partial_to_graft project_upper hrat,
    h.toComputableFiniteSearchNoSmallCodeChecklist
      |>.project_search_witness_ge_upperN_of_scale_projection_pieces
        strengthened_to_partial partial_to_graft project_upper hrat,
    h.toComputableFiniteSearchNoSmallCodeChecklist
      |>.project_search_gap_at_witness_of_scale_projection_pieces
        strengthened_to_partial partial_to_graft project_upper hrat,
    h.toComputableFiniteSearchNoSmallCodeChecklist
      |>.project_search_upper_at_witness_of_scale_projection_pieces
        strengthened_to_partial partial_to_graft project_upper hrat⟩

/-- Endpoint certificate for the final computed collision index.  It records
the actual project index, the fact that it is the scaled checker-extractor
witness, both inequalities at that same index, and the resulting
contradiction. -/
structure ScaledExtractorProjectCollisionEndpoint
    (U : Nat → Real) (computedN : Nat) : Type where
  n : Nat
  n_eq_computed : n = computedN
  lower_at_n : U n < sondowProjectLocalPudlakCollisionBox n
  upper_at_n : sondowProjectLocalPudlakCollisionBox n ≤ U n
  contradiction : False

def scaledExtractorProjectCollisionEndpointOfScaleProjectionPieces
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ScaledExtractorProjectCollisionEndpoint
      ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
          strengthened_to_partial partial_to_graft
        |>.upperTailOfRationality project_upper hrat).U)
      (h.scale_data.scale
        (h.extractor.witness
          ((h.toComputableFiniteSearchNoSmallCodeChecklist
              |>.scaleProjectionPiecesScaledAdditiveProjection
                strengthened_to_partial partial_to_graft)
            |>.indexedShiftedUpper
              ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
                  strengthened_to_partial partial_to_graft)
                |>.upperTailOfRationality project_upper hrat).U)
          ((h.toComputableFiniteSearchNoSmallCodeChecklist
              |>.scaleProjectionPiecesScaledAdditiveProjection
                strengthened_to_partial partial_to_graft)
            |>.indexedShiftedUpper_polynomial
              ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
                  strengthened_to_partial partial_to_graft)
                |>.upperTailOfRationality project_upper hrat).U
              ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
                  strengthened_to_partial partial_to_graft)
                |>.upperTailOfRationality project_upper hrat).polynomial)
          ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
              strengthened_to_partial partial_to_graft)
            |>.upperTailOfRationality project_upper hrat).upperN)) where
  n :=
    (h.projectSearchCollisionWitnessOfScaleProjectionPieces
      strengthened_to_partial partial_to_graft project_upper hrat).n
  n_eq_computed :=
    h.project_search_witness_n_eq_scaled_extractor_witness_of_scale_projection_pieces
      strengthened_to_partial partial_to_graft project_upper hrat
  lower_at_n :=
    (h.toComputableFiniteSearchNoSmallCodeChecklist
      |>.project_search_gap_at_witness_of_scale_projection_pieces
        strengthened_to_partial partial_to_graft project_upper hrat)
  upper_at_n :=
    (h.toComputableFiniteSearchNoSmallCodeChecklist
      |>.project_search_upper_at_witness_of_scale_projection_pieces
        strengthened_to_partial partial_to_graft project_upper hrat)
  contradiction :=
    (h.projectSearchCollisionWitnessOfScaleProjectionPieces
      strengthened_to_partial partial_to_graft project_upper hrat).contradiction

theorem scaledExtractorProjectCollisionEndpoint_n_eq_computed
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.scaledExtractorProjectCollisionEndpointOfScaleProjectionPieces
      strengthened_to_partial partial_to_graft project_upper hrat).n =
      h.scale_data.scale
        (h.extractor.witness
          ((h.toComputableFiniteSearchNoSmallCodeChecklist
              |>.scaleProjectionPiecesScaledAdditiveProjection
                strengthened_to_partial partial_to_graft)
            |>.indexedShiftedUpper
              ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
                  strengthened_to_partial partial_to_graft)
                |>.upperTailOfRationality project_upper hrat).U)
          ((h.toComputableFiniteSearchNoSmallCodeChecklist
              |>.scaleProjectionPiecesScaledAdditiveProjection
                strengthened_to_partial partial_to_graft)
            |>.indexedShiftedUpper_polynomial
              ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
                  strengthened_to_partial partial_to_graft)
                |>.upperTailOfRationality project_upper hrat).U
              ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
                  strengthened_to_partial partial_to_graft)
                |>.upperTailOfRationality project_upper hrat).polynomial)
          ((h.toProjectGapTransferChecklistOfScaleProjectionPieces
              strengthened_to_partial partial_to_graft)
            |>.upperTailOfRationality project_upper hrat).upperN) :=
  (h.scaledExtractorProjectCollisionEndpointOfScaleProjectionPieces
    strengthened_to_partial partial_to_graft project_upper hrat).n_eq_computed

theorem scaledExtractorProjectCollisionEndpoint_contradiction
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.scaledExtractorProjectCollisionEndpointOfScaleProjectionPieces
    strengthened_to_partial partial_to_graft project_upper hrat).contradiction

theorem project_search_computed_n_contradiction_of_scale_projection_pieces
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.scaledExtractorProjectCollisionEndpoint_contradiction
    strengthened_to_partial partial_to_graft project_upper hrat

theorem search_not_rational_of_scale_projection_pieces
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat =>
    h.project_search_computed_n_contradiction_of_scale_projection_pieces
      strengthened_to_partial partial_to_graft project_upper hrat

end Month9Month10CheckerExtractorComputableSearchChecklist

/-- Minimal project endpoint input for the checker-extractor route.  It keeps
the theorem-5 checker payload, the two constant-cost projections, and the
Sondow upper route in one auditable object. -/
structure Month9Month10CheckerExtractorProjectEndpointInputs :
    Type (q + 1) where
  checker_checklist :
    Month9Month10CheckerExtractorComputableSearchChecklist.{q}
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyConstantProjection
  partial_to_graft : _root_.PAConjunctionEliminationConstantCost
  project_upper : SondowProjectLocalS21CollapseConclusion

namespace Month9Month10CheckerExtractorProjectEndpointInputs

def toProjectGapTransferChecklist
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q}) :
    Month9Month10ProjectGapTransferComputableSearchChecklist.{q} :=
  h.checker_checklist.toProjectGapTransferChecklistOfScaleProjectionPieces
    h.strengthened_to_partial h.partial_to_graft

noncomputable def projectSearchCollisionWitnessOfRationality
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ComputedSearchCollisionWitness
      ((h.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).U)
      sondowProjectLocalPudlakCollisionBox :=
  h.checker_checklist.projectSearchCollisionWitnessOfScaleProjectionPieces
    h.strengthened_to_partial h.partial_to_graft h.project_upper hrat

noncomputable def computedCollisionNOfRationality
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  (h.projectSearchCollisionWitnessOfRationality hrat).n

noncomputable def endpointOfRationality
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :=
  h.checker_checklist.scaledExtractorProjectCollisionEndpointOfScaleProjectionPieces
    h.strengthened_to_partial h.partial_to_graft h.project_upper hrat

theorem endpoint_n_eq_computedCollisionN
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.endpointOfRationality hrat).n =
      h.computedCollisionNOfRationality hrat :=
  rfl

theorem computedCollisionN_eq_searchGapWitness
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    h.computedCollisionNOfRationality hrat =
      ((h.toProjectGapTransferChecklist.toComputableSearchGapCertificate
          |>.gap_for_polynomial_upper
            (h.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).U
            (h.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).polynomial)
        |>.witness
          (h.toProjectGapTransferChecklist
            |>.upperTailOfRationality h.project_upper hrat).upperN) :=
  rfl

theorem computedCollisionN_ge_upperN
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).upperN ≤
      h.computedCollisionNOfRationality hrat :=
  (h.projectSearchCollisionWitnessOfRationality hrat).n_ge_upper

theorem endpoint_lower_at_computedCollisionN
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).U
        (h.computedCollisionNOfRationality hrat) <
      sondowProjectLocalPudlakCollisionBox
        (h.computedCollisionNOfRationality hrat) :=
  (h.endpointOfRationality hrat).lower_at_n

theorem endpoint_upper_at_computedCollisionN
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    sondowProjectLocalPudlakCollisionBox
        (h.computedCollisionNOfRationality hrat) ≤
      (h.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).U
        (h.computedCollisionNOfRationality hrat) :=
  (h.endpointOfRationality hrat).upper_at_n

theorem endpoint_contradiction
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.endpointOfRationality hrat).contradiction

theorem not_rational
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q}) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat => h.endpoint_contradiction hrat

/-- Auditable closure summary for the compressed project endpoint input. -/
structure Audit
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q}) : Prop where
  strengthenedToPartialProjection :
    Nonempty _root_.StrengthenedToPartialConsistencyConstantProjection
  partialToGraftProjection :
    Nonempty _root_.PAConjunctionEliminationConstantCost
  scaledConstantProjection :
    Nonempty
      (_root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        h.checker_checklist.scale_data.powerBoundRawCode
        (fun n : Nat =>
          _root_.sondowReflectionGraftCode
            (h.checker_checklist.scale_data.scale n)))
  projectCollisionInputs_transfer_to_graft :
    (h.checker_checklist.toComputableFiniteSearchNoSmallCodeChecklist
      |>.toProjectCollisionInputsOfConstantPieces
        h.project_upper h.strengthened_to_partial
        h.partial_to_graft).transfer_to_graft =
      InternalPudlakTheorem5TransferPieces.partialToGraftTransferOfConstant
        h.partial_to_graft
  enumeration :
    Nonempty
      (InternalPudlakTheorem5CheckerFiniteEnumeration
        h.checker_checklist.checker)
  extractor :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableRejectionExtractor
        h.checker_checklist.checker h.checker_checklist.enumeration)
  exactness :
    Nonempty
      (InternalPudlakTheorem5CheckerProofLengthExactness
        h.checker_checklist.checker)
  familyExactness :
    Nonempty
      (InternalPudlakTheorem5CheckerProofLengthFamilyExactness
        h.checker_checklist.checker)
  computableFiniteSearchCore :
    Nonempty InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}
  computableProjectGapTransfer :
    Nonempty
      (InternalPudlakTheorem5ComputableProjectGapTransfer
        h.checker_checklist.scale_data
        h.checker_checklist.proof_code_semantics
        h.checker_checklist.small_code_search)
  computableGap :
    Nonempty
      (ComputableSearchGapCertificate
        sondowProjectLocalPudlakCollisionBox)
  witness_eq_extractor :
    ∀ f : Nat → Real,
      ∀ hf : _root_.is_polynomial_bound f,
        ∀ N : Nat,
          (h.checker_checklist.computedLowerSearchWitness f hf N).n =
            h.checker_checklist.extractor.witness f hf N
  cutoff_eq_extractor :
    ∀ f : Nat → Real,
      ∀ hf : _root_.is_polynomial_bound f,
        ∀ N : Nat,
          (h.checker_checklist.computedLowerSearchWitness f hf N).K =
            h.checker_checklist.extractor.cutoff f hf N
  computed_n_eq_searchGapWitness :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      h.computedCollisionNOfRationality hrat =
        ((h.toProjectGapTransferChecklist.toComputableSearchGapCertificate
            |>.gap_for_polynomial_upper
              (h.toProjectGapTransferChecklist
                |>.upperTailOfRationality h.project_upper hrat).U
              (h.toProjectGapTransferChecklist
                |>.upperTailOfRationality h.project_upper hrat).polynomial)
          |>.witness
            (h.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).upperN)
  computed_n_ge_upperN :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (h.toProjectGapTransferChecklist
          |>.upperTailOfRationality h.project_upper hrat).upperN ≤
        h.computedCollisionNOfRationality hrat
  lower_at_computed_n :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (h.toProjectGapTransferChecklist
          |>.upperTailOfRationality h.project_upper hrat).U
          (h.computedCollisionNOfRationality hrat) <
        sondowProjectLocalPudlakCollisionBox
          (h.computedCollisionNOfRationality hrat)
  upper_at_computed_n :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      sondowProjectLocalPudlakCollisionBox
          (h.computedCollisionNOfRationality hrat) ≤
        (h.toProjectGapTransferChecklist
          |>.upperTailOfRationality h.project_upper hrat).U
          (h.computedCollisionNOfRationality hrat)
  contradiction_at_computed_n :
    ∀ _ : _root_.is_rational _root_.euler_mascheroni,
      False
  not_rational : ¬ _root_.is_rational _root_.euler_mascheroni

theorem audit
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q}) :
    Audit h := by
  exact
    { strengthenedToPartialProjection := ⟨h.strengthened_to_partial⟩
      partialToGraftProjection := ⟨h.partial_to_graft⟩
      scaledConstantProjection :=
        ⟨h.checker_checklist.toComputableFiniteSearchNoSmallCodeChecklist
          |>.scaleProjectionPiecesConstantProjection
            h.strengthened_to_partial h.partial_to_graft⟩
      projectCollisionInputs_transfer_to_graft :=
        h.checker_checklist.toComputableFiniteSearchNoSmallCodeChecklist
          |>.toProjectCollisionInputsOfConstantPieces_transfer_to_graft
            h.project_upper h.strengthened_to_partial h.partial_to_graft
      enumeration := ⟨h.checker_checklist.enumeration⟩
      extractor := ⟨h.checker_checklist.extractor⟩
      exactness := ⟨h.checker_checklist.exactness⟩
      familyExactness :=
        ⟨InternalPudlakTheorem5CheckerProofLengthFamilyExactness.ofCheckerProofLengthExactness
          h.checker_checklist.exactness⟩
      computableFiniteSearchCore :=
        ⟨h.checker_checklist.theorem5_computable_search_core⟩
      computableProjectGapTransfer :=
        ⟨h.toProjectGapTransferChecklist.project_gap_transfer⟩
      computableGap :=
        ⟨h.toProjectGapTransferChecklist.toComputableSearchGapCertificate⟩
      witness_eq_extractor :=
        h.checker_checklist.computedLowerSearchWitness_n_eq_extractor
      cutoff_eq_extractor :=
        h.checker_checklist.computedLowerSearchWitness_K_eq_extractor
      computed_n_eq_searchGapWitness :=
        h.computedCollisionN_eq_searchGapWitness
      computed_n_ge_upperN := h.computedCollisionN_ge_upperN
      lower_at_computed_n := h.endpoint_lower_at_computedCollisionN
      upper_at_computed_n := h.endpoint_upper_at_computedCollisionN
      contradiction_at_computed_n := fun hrat => h.endpoint_contradiction hrat
      not_rational := h.not_rational }

theorem audit_not_rational
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q}) :
    (h.audit).not_rational = h.not_rational :=
  rfl

theorem audit_proof_length_exactness_iff_family
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q}) :
    Nonempty
        (InternalPudlakTheorem5CheckerProofLengthExactness
          h.checker_checklist.checker) ↔
      Nonempty
        (InternalPudlakTheorem5CheckerProofLengthFamilyExactness
          h.checker_checklist.checker) :=
  InternalPudlakTheorem5CheckerProofLengthFamilyExactness.checkerProofLengthExactness_iff_familyExactness
    h.checker_checklist.checker

/-- Frontier statement for the Month 9-10 endpoint: from these compressed
inputs the project-level computed contradiction is closed.  What remains for
full internalization is upstream construction of the checker checklist and the
two constant projection certificates, not any additional collision-core
argument. -/
structure EndpointFrontier
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q}) : Prop where
  endpointInputs :
    Nonempty Month9Month10CheckerExtractorProjectEndpointInputs.{q}
  checkerChecklist :
    Nonempty Month9Month10CheckerExtractorComputableSearchChecklist.{q}
  checkerRejectionExtractor :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableRejectionExtractor
        h.checker_checklist.checker h.checker_checklist.enumeration)
  proofLengthExactnessField :
    Nonempty
      (InternalPudlakTheorem5CheckerProofLengthExactness
        h.checker_checklist.checker)
  proofLengthFamilyExactnessField :
    Nonempty
      (InternalPudlakTheorem5CheckerProofLengthFamilyExactness
        h.checker_checklist.checker)
  computedWitness :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      Nonempty
        (ComputedSearchCollisionWitness
          ((h.toProjectGapTransferChecklist
            |>.upperTailOfRationality h.project_upper hrat).U)
          sondowProjectLocalPudlakCollisionBox)
  computed_n_formula :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      h.computedCollisionNOfRationality hrat =
        ((h.toProjectGapTransferChecklist.toComputableSearchGapCertificate
            |>.gap_for_polynomial_upper
              (h.toProjectGapTransferChecklist
                |>.upperTailOfRationality h.project_upper hrat).U
              (h.toProjectGapTransferChecklist
                |>.upperTailOfRationality h.project_upper hrat).polynomial)
          |>.witness
            (h.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).upperN)
  contradiction_at_computed_n :
    ∀ _ : _root_.is_rational _root_.euler_mascheroni,
      False
  not_rational : ¬ _root_.is_rational _root_.euler_mascheroni

theorem endpoint_frontier
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q}) :
    EndpointFrontier h where
  endpointInputs := ⟨h⟩
  checkerChecklist := ⟨h.checker_checklist⟩
  checkerRejectionExtractor := ⟨h.checker_checklist.extractor⟩
  proofLengthExactnessField := ⟨h.checker_checklist.exactness⟩
  proofLengthFamilyExactnessField :=
    ⟨InternalPudlakTheorem5CheckerProofLengthFamilyExactness.ofCheckerProofLengthExactness
      h.checker_checklist.exactness⟩
  computedWitness := fun hrat =>
    ⟨h.projectSearchCollisionWitnessOfRationality hrat⟩
  computed_n_formula := h.computedCollisionN_eq_searchGapWitness
  contradiction_at_computed_n := h.endpoint_contradiction
  not_rational := h.not_rational

theorem endpoint_frontier_contradiction
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q})
    (frontier : EndpointFrontier h)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  frontier.contradiction_at_computed_n hrat

theorem endpoint_frontier_to_not_rational
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q})
    (frontier : EndpointFrontier h) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  frontier.not_rational

theorem endpoint_frontier_not_rational
    (h : Month9Month10CheckerExtractorProjectEndpointInputs.{q}) :
    (h.endpoint_frontier).not_rational = h.not_rational :=
  rfl

def ofFamilyExactness
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data)
    (enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker)
    (strengthened_to_partial_transfer :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (transfer_to_graft :
      _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (strengthened_to_partial_projection :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft_projection :
      _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10CheckerExtractorProjectEndpointInputs.{q} where
  checker_checklist :=
    Month9Month10CheckerExtractorComputableSearchChecklist.ofFamilyExactness
      scale_data checker enumeration extractor family
      strengthened_to_partial_transfer transfer_to_graft computable_gap
  strengthened_to_partial := strengthened_to_partial_projection
  partial_to_graft := partial_to_graft_projection
  project_upper := project_upper

theorem ofFamilyExactness_endpoint_frontier
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data)
    (enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker)
    (strengthened_to_partial_transfer :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (transfer_to_graft :
      _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (strengthened_to_partial_projection :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft_projection :
      _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    EndpointFrontier
      (ofFamilyExactness scale_data checker enumeration extractor family
        strengthened_to_partial_transfer transfer_to_graft computable_gap
        strengthened_to_partial_projection partial_to_graft_projection
        project_upper) :=
  (ofFamilyExactness scale_data checker enumeration extractor family
    strengthened_to_partial_transfer transfer_to_graft computable_gap
    strengthened_to_partial_projection partial_to_graft_projection
    project_upper).endpoint_frontier

theorem ofFamilyExactness_not_rational
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data)
    (enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker)
    (strengthened_to_partial_transfer :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (transfer_to_graft :
      _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (strengthened_to_partial_projection :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft_projection :
      _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  (ofFamilyExactness scale_data checker enumeration extractor family
    strengthened_to_partial_transfer transfer_to_graft computable_gap
    strengthened_to_partial_projection partial_to_graft_projection
    project_upper).not_rational

end Month9Month10CheckerExtractorProjectEndpointInputs

/-- The narrowest current project endpoint input for the checker-extractor
route.  It asks the concrete checker line for the family-shaped proof-length
exactness statement and the two constant projections; the corresponding lower
bound transfer certificates are derived internally from those projections. -/
structure Month9Month10CheckerExtractorFamilyEndpointInputs :
    Type (q + 1) where
  scale_data : InternalPudlakTheorem5ScaleData
  checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data
  enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker
  extractor :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      checker enumeration
  family_exactness :
    InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker
  strengthened_to_partial_projection :
    _root_.StrengthenedToPartialConsistencyConstantProjection
  partial_to_graft_projection :
    _root_.PAConjunctionEliminationConstantCost
  computable_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox
  project_upper : SondowProjectLocalS21CollapseConclusion

namespace Month9Month10CheckerExtractorFamilyEndpointInputs

def strengthened_to_partial_transfer
    (h : Month9Month10CheckerExtractorFamilyEndpointInputs.{q}) :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer :=
  InternalPudlakTheorem5TransferPieces.strengthenedToPartialTransferOfConstant
    h.strengthened_to_partial_projection

def transfer_to_graft
    (h : Month9Month10CheckerExtractorFamilyEndpointInputs.{q}) :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer :=
  InternalPudlakTheorem5TransferPieces.partialToGraftTransferOfConstant
    h.partial_to_graft_projection

def toProjectEndpointInputs
    (h : Month9Month10CheckerExtractorFamilyEndpointInputs.{q}) :
    Month9Month10CheckerExtractorProjectEndpointInputs.{q} :=
  Month9Month10CheckerExtractorProjectEndpointInputs.ofFamilyExactness
    h.scale_data h.checker h.enumeration h.extractor h.family_exactness
    h.strengthened_to_partial_transfer h.transfer_to_graft h.computable_gap
    h.strengthened_to_partial_projection h.partial_to_graft_projection
    h.project_upper

theorem transfer_to_graft_eq_projection_transfer
    (h : Month9Month10CheckerExtractorFamilyEndpointInputs.{q}) :
    h.transfer_to_graft =
      InternalPudlakTheorem5TransferPieces.partialToGraftTransferOfConstant
        h.partial_to_graft_projection :=
  rfl

theorem strengthened_to_partial_transfer_eq_projection_transfer
    (h : Month9Month10CheckerExtractorFamilyEndpointInputs.{q}) :
    h.strengthened_to_partial_transfer =
      InternalPudlakTheorem5TransferPieces.strengthenedToPartialTransferOfConstant
        h.strengthened_to_partial_projection :=
  rfl

theorem endpoint_frontier
    (h : Month9Month10CheckerExtractorFamilyEndpointInputs.{q}) :
    h.toProjectEndpointInputs.EndpointFrontier :=
  h.toProjectEndpointInputs.endpoint_frontier

theorem not_rational
    (h : Month9Month10CheckerExtractorFamilyEndpointInputs.{q}) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toProjectEndpointInputs.not_rational

noncomputable def computedCollisionNOfRationality
    (h : Month9Month10CheckerExtractorFamilyEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  h.toProjectEndpointInputs.computedCollisionNOfRationality hrat

theorem computedCollisionN_eq_searchGapWitness
    (h : Month9Month10CheckerExtractorFamilyEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    h.computedCollisionNOfRationality hrat =
      ((h.toProjectEndpointInputs.toProjectGapTransferChecklist
          |>.toComputableSearchGapCertificate
          |>.gap_for_polynomial_upper
            (h.toProjectEndpointInputs.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).U
            (h.toProjectEndpointInputs.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).polynomial)
        |>.witness
          (h.toProjectEndpointInputs.toProjectGapTransferChecklist
            |>.upperTailOfRationality h.project_upper hrat).upperN) :=
  h.toProjectEndpointInputs.computedCollisionN_eq_searchGapWitness hrat

theorem endpoint_n_eq_computedCollisionN
    (h : Month9Month10CheckerExtractorFamilyEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.toProjectEndpointInputs.endpointOfRationality hrat).n =
      h.computedCollisionNOfRationality hrat :=
  h.toProjectEndpointInputs.endpoint_n_eq_computedCollisionN hrat

theorem computedCollisionN_ge_upperN
    (h : Month9Month10CheckerExtractorFamilyEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.toProjectEndpointInputs.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).upperN ≤
      h.computedCollisionNOfRationality hrat :=
  h.toProjectEndpointInputs.computedCollisionN_ge_upperN hrat

theorem endpoint_lower_at_computedCollisionN
    (h : Month9Month10CheckerExtractorFamilyEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.toProjectEndpointInputs.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).U
        (h.computedCollisionNOfRationality hrat) <
      sondowProjectLocalPudlakCollisionBox
        (h.computedCollisionNOfRationality hrat) :=
  h.toProjectEndpointInputs.endpoint_lower_at_computedCollisionN hrat

theorem endpoint_upper_at_computedCollisionN
    (h : Month9Month10CheckerExtractorFamilyEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    sondowProjectLocalPudlakCollisionBox
        (h.computedCollisionNOfRationality hrat) ≤
      (h.toProjectEndpointInputs.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).U
        (h.computedCollisionNOfRationality hrat) :=
  h.toProjectEndpointInputs.endpoint_upper_at_computedCollisionN hrat

theorem endpoint_contradiction
    (h : Month9Month10CheckerExtractorFamilyEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.toProjectEndpointInputs.endpoint_contradiction hrat

theorem endpoint_frontier_to_not_rational
    (h : Month9Month10CheckerExtractorFamilyEndpointInputs.{q})
    (frontier : h.toProjectEndpointInputs.EndpointFrontier) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toProjectEndpointInputs.endpoint_frontier_to_not_rational frontier

/-- Audit summary for the family-shaped endpoint input.  This is the current
minimal handoff target for the concrete PA/Hilbert checker line: no full
proof-length exactness field is supplied by hand, and no separate lower-bound
transfer certificates are supplied by hand. -/
structure Audit
    (h : Month9Month10CheckerExtractorFamilyEndpointInputs.{q}) : Prop where
  familyExactness :
    Nonempty
      (InternalPudlakTheorem5CheckerProofLengthFamilyExactness h.checker)
  fullExactnessRecovered :
    Nonempty
      (InternalPudlakTheorem5CheckerProofLengthExactness h.checker)
  strengthenedTransferDerived :
    h.strengthened_to_partial_transfer =
      InternalPudlakTheorem5TransferPieces.strengthenedToPartialTransferOfConstant
        h.strengthened_to_partial_projection
  graftTransferDerived :
    h.transfer_to_graft =
      InternalPudlakTheorem5TransferPieces.partialToGraftTransferOfConstant
        h.partial_to_graft_projection
  endpointFrontier :
    h.toProjectEndpointInputs.EndpointFrontier
  computed_n_eq_searchGapWitness :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      h.computedCollisionNOfRationality hrat =
        ((h.toProjectEndpointInputs.toProjectGapTransferChecklist
            |>.toComputableSearchGapCertificate
            |>.gap_for_polynomial_upper
              (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                |>.upperTailOfRationality h.project_upper hrat).U
              (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                |>.upperTailOfRationality h.project_upper hrat).polynomial)
          |>.witness
            (h.toProjectEndpointInputs.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).upperN)
  computed_n_ge_upperN :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (h.toProjectEndpointInputs.toProjectGapTransferChecklist
          |>.upperTailOfRationality h.project_upper hrat).upperN ≤
        h.computedCollisionNOfRationality hrat
  lower_at_computed_n :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (h.toProjectEndpointInputs.toProjectGapTransferChecklist
          |>.upperTailOfRationality h.project_upper hrat).U
          (h.computedCollisionNOfRationality hrat) <
        sondowProjectLocalPudlakCollisionBox
          (h.computedCollisionNOfRationality hrat)
  upper_at_computed_n :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      sondowProjectLocalPudlakCollisionBox
          (h.computedCollisionNOfRationality hrat) ≤
        (h.toProjectEndpointInputs.toProjectGapTransferChecklist
          |>.upperTailOfRationality h.project_upper hrat).U
          (h.computedCollisionNOfRationality hrat)
  contradiction_at_computed_n :
    ∀ _ : _root_.is_rational _root_.euler_mascheroni,
      False
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem audit
    (h : Month9Month10CheckerExtractorFamilyEndpointInputs.{q}) :
    Audit h where
  familyExactness := ⟨h.family_exactness⟩
  fullExactnessRecovered :=
    ⟨h.family_exactness.toCheckerProofLengthExactness⟩
  strengthenedTransferDerived :=
    h.strengthened_to_partial_transfer_eq_projection_transfer
  graftTransferDerived :=
    h.transfer_to_graft_eq_projection_transfer
  endpointFrontier := h.endpoint_frontier
  computed_n_eq_searchGapWitness := h.computedCollisionN_eq_searchGapWitness
  computed_n_ge_upperN := h.computedCollisionN_ge_upperN
  lower_at_computed_n := h.endpoint_lower_at_computedCollisionN
  upper_at_computed_n := h.endpoint_upper_at_computedCollisionN
  contradiction_at_computed_n := fun hrat => h.endpoint_contradiction hrat
  endpointNotRational := h.not_rational

theorem audit_not_rational
    (h : Month9Month10CheckerExtractorFamilyEndpointInputs.{q}) :
    (h.audit).endpointNotRational = h.not_rational :=
  rfl

end Month9Month10CheckerExtractorFamilyEndpointInputs

/-- Endpoint input whose proof-length side is split through an explicit length
family.  This is the most concrete Month 9-10 handoff shape before importing a
particular PA/Hilbert checker implementation. -/
structure Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs :
    Type (q + 1) where
  scale_data : InternalPudlakTheorem5ScaleData
  checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data
  enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker
  extractor :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      checker enumeration
  length_calibration :
    InternalPudlakTheorem5CheckerFamilyLengthCalibration checker
  strengthened_to_partial_projection :
    _root_.StrengthenedToPartialConsistencyConstantProjection
  partial_to_graft_projection :
    _root_.PAConjunctionEliminationConstantCost
  computable_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox
  project_upper : SondowProjectLocalS21CollapseConclusion

namespace Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs

def family_exactness
    (h : Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs.{q}) :
    InternalPudlakTheorem5CheckerProofLengthFamilyExactness h.checker :=
  h.length_calibration.toFamilyExactness

def toFamilyEndpointInputs
    (h : Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs.{q}) :
    Month9Month10CheckerExtractorFamilyEndpointInputs.{q} where
  scale_data := h.scale_data
  checker := h.checker
  enumeration := h.enumeration
  extractor := h.extractor
  family_exactness := h.family_exactness
  strengthened_to_partial_projection :=
    h.strengthened_to_partial_projection
  partial_to_graft_projection := h.partial_to_graft_projection
  computable_gap := h.computable_gap
  project_upper := h.project_upper

def toProjectEndpointInputs
    (h : Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs.{q}) :
    Month9Month10CheckerExtractorProjectEndpointInputs.{q} :=
  h.toFamilyEndpointInputs.toProjectEndpointInputs

theorem endpoint_frontier
    (h : Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs.{q}) :
    h.toProjectEndpointInputs.EndpointFrontier :=
  h.toProjectEndpointInputs.endpoint_frontier

theorem not_rational
    (h : Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs.{q}) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toProjectEndpointInputs.not_rational

noncomputable def computedCollisionNOfRationality
    (h : Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  h.toProjectEndpointInputs.computedCollisionNOfRationality hrat

theorem computedCollisionN_eq_searchGapWitness
    (h : Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    h.computedCollisionNOfRationality hrat =
      ((h.toProjectEndpointInputs.toProjectGapTransferChecklist
          |>.toComputableSearchGapCertificate
          |>.gap_for_polynomial_upper
            (h.toProjectEndpointInputs.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).U
            (h.toProjectEndpointInputs.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).polynomial)
        |>.witness
          (h.toProjectEndpointInputs.toProjectGapTransferChecklist
            |>.upperTailOfRationality h.project_upper hrat).upperN) :=
  h.toProjectEndpointInputs.computedCollisionN_eq_searchGapWitness hrat

theorem endpoint_n_eq_computedCollisionN
    (h : Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.toProjectEndpointInputs.endpointOfRationality hrat).n =
      h.computedCollisionNOfRationality hrat :=
  h.toProjectEndpointInputs.endpoint_n_eq_computedCollisionN hrat

theorem computedCollisionN_ge_upperN
    (h : Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.toProjectEndpointInputs.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).upperN ≤
      h.computedCollisionNOfRationality hrat :=
  h.toProjectEndpointInputs.computedCollisionN_ge_upperN hrat

theorem endpoint_lower_at_computedCollisionN
    (h : Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.toProjectEndpointInputs.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).U
        (h.computedCollisionNOfRationality hrat) <
      sondowProjectLocalPudlakCollisionBox
        (h.computedCollisionNOfRationality hrat) :=
  h.toProjectEndpointInputs.endpoint_lower_at_computedCollisionN hrat

theorem endpoint_upper_at_computedCollisionN
    (h : Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    sondowProjectLocalPudlakCollisionBox
        (h.computedCollisionNOfRationality hrat) ≤
      (h.toProjectEndpointInputs.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).U
        (h.computedCollisionNOfRationality hrat) :=
  h.toProjectEndpointInputs.endpoint_upper_at_computedCollisionN hrat

theorem endpoint_contradiction
    (h : Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.toProjectEndpointInputs.endpoint_contradiction hrat

/-- Audit summary for the calibrated family endpoint.  It records the two
length-identification obligations separately and the resulting endpoint
closure. -/
structure Audit
    (h : Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs.{q}) :
    Prop where
  lengthFamily :
    Nonempty (Nat → Nat)
  proofLengthRecognizesFamily :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
        (h.scale_data.powerBoundRawCode n) =
        (h.length_calibration.family_length n : Real)
  checkerMinRecognizesFamily :
    ∀ n : Nat,
      h.checker.minProofCodeSizeAt n =
        h.length_calibration.family_length n
  familyExactnessRecovered :
    Nonempty
      (InternalPudlakTheorem5CheckerProofLengthFamilyExactness h.checker)
  endpointFrontier :
    h.toProjectEndpointInputs.EndpointFrontier
  computed_n_eq_searchGapWitness :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      h.computedCollisionNOfRationality hrat =
        ((h.toProjectEndpointInputs.toProjectGapTransferChecklist
            |>.toComputableSearchGapCertificate
            |>.gap_for_polynomial_upper
              (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                |>.upperTailOfRationality h.project_upper hrat).U
              (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                |>.upperTailOfRationality h.project_upper hrat).polynomial)
          |>.witness
            (h.toProjectEndpointInputs.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).upperN)
  computed_n_ge_upperN :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (h.toProjectEndpointInputs.toProjectGapTransferChecklist
          |>.upperTailOfRationality h.project_upper hrat).upperN ≤
        h.computedCollisionNOfRationality hrat
  lower_at_computed_n :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (h.toProjectEndpointInputs.toProjectGapTransferChecklist
          |>.upperTailOfRationality h.project_upper hrat).U
          (h.computedCollisionNOfRationality hrat) <
        sondowProjectLocalPudlakCollisionBox
          (h.computedCollisionNOfRationality hrat)
  upper_at_computed_n :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      sondowProjectLocalPudlakCollisionBox
          (h.computedCollisionNOfRationality hrat) ≤
        (h.toProjectEndpointInputs.toProjectGapTransferChecklist
          |>.upperTailOfRationality h.project_upper hrat).U
          (h.computedCollisionNOfRationality hrat)
  contradiction_at_computed_n :
    ∀ _ : _root_.is_rational _root_.euler_mascheroni,
      False
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem audit
    (h : Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs.{q}) :
    Audit h where
  lengthFamily := ⟨h.length_calibration.family_length⟩
  proofLengthRecognizesFamily :=
    h.length_calibration.proof_length_eq_family_length
  checkerMinRecognizesFamily :=
    h.length_calibration.minProofCodeSizeAt_eq_family_length
  familyExactnessRecovered := ⟨h.family_exactness⟩
  endpointFrontier := h.endpoint_frontier
  computed_n_eq_searchGapWitness := h.computedCollisionN_eq_searchGapWitness
  computed_n_ge_upperN := h.computedCollisionN_ge_upperN
  lower_at_computed_n := h.endpoint_lower_at_computedCollisionN
  upper_at_computed_n := h.endpoint_upper_at_computedCollisionN
  contradiction_at_computed_n := fun hrat => h.endpoint_contradiction hrat
  endpointNotRational := h.not_rational

theorem audit_not_rational
    (h : Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs.{q}) :
    (h.audit).endpointNotRational = h.not_rational :=
  rfl

end Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs

theorem month9_month10_calibrated_family_endpoint_closure
    (h : Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs.{q}) :
    Nonempty
        (InternalPudlakTheorem5CheckerFamilyLengthCalibration h.checker) ∧
      Nonempty
        (InternalPudlakTheorem5CheckerProofLengthFamilyExactness h.checker) ∧
        Nonempty Month9Month10CheckerExtractorFamilyEndpointInputs.{q} ∧
          Nonempty Month9Month10CheckerExtractorProjectEndpointInputs.{q} ∧
            h.toProjectEndpointInputs.EndpointFrontier ∧
              (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                h.computedCollisionNOfRationality hrat =
                  ((h.toProjectEndpointInputs.toProjectGapTransferChecklist
                      |>.toComputableSearchGapCertificate
                      |>.gap_for_polynomial_upper
                        (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                          |>.upperTailOfRationality h.project_upper hrat).U
                        (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                          |>.upperTailOfRationality h.project_upper hrat).polynomial)
                    |>.witness
                      (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                        |>.upperTailOfRationality h.project_upper hrat).upperN)) ∧
                (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                  (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                      |>.upperTailOfRationality h.project_upper hrat).upperN ≤
                    h.computedCollisionNOfRationality hrat) ∧
                  (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                    (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                        |>.upperTailOfRationality h.project_upper hrat).U
                        (h.computedCollisionNOfRationality hrat) <
                      sondowProjectLocalPudlakCollisionBox
                        (h.computedCollisionNOfRationality hrat)) ∧
                    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                      sondowProjectLocalPudlakCollisionBox
                          (h.computedCollisionNOfRationality hrat) ≤
                        (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                          |>.upperTailOfRationality h.project_upper hrat).U
                          (h.computedCollisionNOfRationality hrat)) ∧
                      (∀ _ : _root_.is_rational _root_.euler_mascheroni,
                        False) ∧
                        ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact
    ⟨⟨h.length_calibration⟩,
      ⟨h.family_exactness⟩,
      ⟨h.toFamilyEndpointInputs⟩,
      ⟨h.toProjectEndpointInputs⟩,
      h.endpoint_frontier,
      h.computedCollisionN_eq_searchGapWitness,
      h.computedCollisionN_ge_upperN,
      h.endpoint_lower_at_computedCollisionN,
      h.endpoint_upper_at_computedCollisionN,
      (fun hrat => h.endpoint_contradiction hrat),
      h.not_rational⟩

/-- Structured Sondow upper-route input for the Month 9-10 endpoint.  The
ordinary partial-consistency payload is no longer supplied as a raw truth
block here: it enters through the existing project-local payload specification
certificate and the reflection-graft verifier. -/
structure Month9Month10PayloadSpecUpperInputs : Type where
  verifier : SondowProjectLocalReflectionGraftVerifier
  payload_spec : PartialConsistencyPayloadSpecCertificate

namespace Month9Month10PayloadSpecUpperInputs

def toProjectUpper
    (h : Month9Month10PayloadSpecUpperInputs) :
    SondowProjectLocalS21CollapseConclusion :=
  verifierAndPayloadSpecCertificate_nonempty_to_projectCollapseConclusion
    ⟨⟨h.verifier⟩, ⟨h.payload_spec⟩⟩

theorem verifier_nonempty
    (h : Month9Month10PayloadSpecUpperInputs) :
    Nonempty SondowProjectLocalReflectionGraftVerifier :=
  ⟨h.verifier⟩

theorem payloadSpec_nonempty
    (h : Month9Month10PayloadSpecUpperInputs) :
    Nonempty PartialConsistencyPayloadSpecCertificate :=
  ⟨h.payload_spec⟩

theorem payloadTruth_nonempty
    (h : Month9Month10PayloadSpecUpperInputs) :
    Nonempty _root_.PartialConsistencyPayloadTruth :=
  partialConsistencyPayloadTruth_nonempty_ofPayloadSpecCertificate
    h.payloadSpec_nonempty

theorem acceptedTruth_nonempty
    (h : Month9Month10PayloadSpecUpperInputs) :
    Nonempty _root_.PartialConsistencyAcceptedTruth :=
  ⟨h.payload_spec.toAcceptedTruth⟩

structure Audit
    (h : Month9Month10PayloadSpecUpperInputs) : Prop where
  verifier :
    Nonempty SondowProjectLocalReflectionGraftVerifier
  payloadSpec :
    Nonempty PartialConsistencyPayloadSpecCertificate
  acceptedTruth :
    Nonempty _root_.PartialConsistencyAcceptedTruth
  payloadTruth :
    Nonempty _root_.PartialConsistencyPayloadTruth
  projectUpper :
    SondowProjectLocalS21CollapseConclusion

theorem audit
    (h : Month9Month10PayloadSpecUpperInputs) :
    Audit h where
  verifier := h.verifier_nonempty
  payloadSpec := h.payloadSpec_nonempty
  acceptedTruth := h.acceptedTruth_nonempty
  payloadTruth := h.payloadTruth_nonempty
  projectUpper := h.toProjectUpper

theorem audit_projectUpper
    (h : Month9Month10PayloadSpecUpperInputs) :
    (h.audit).projectUpper = h.toProjectUpper :=
  rfl

end Month9Month10PayloadSpecUpperInputs

/-- Strengthened finite-consistency payload specification for the Month 9-10
lower-route frontier.  It mirrors the ordinary partial payload spec, but is
kept local to this surface until the strengthened checker realization is moved
to a shared lower-level module. -/
structure Month9Month10StrengthenedPayloadSpecCertificate : Type where
  code_family : Nat → _root_.FormulaCode
  code_family_eq : code_family = _root_.strengthenedPartialConsistencyCode
  accepted_iff_payload :
    ∀ n : Nat,
      _root_.accepted_certificate (code_family n) ↔
        _root_.strengthened_partial_consistency_payload n
  payload_truth : _root_.StrengthenedPartialConsistencyPayloadTruth

namespace Month9Month10StrengthenedPayloadSpecCertificate

def standard
    (htruth : _root_.StrengthenedPartialConsistencyPayloadTruth) :
    Month9Month10StrengthenedPayloadSpecCertificate where
  code_family := _root_.strengthenedPartialConsistencyCode
  code_family_eq := rfl
  accepted_iff_payload := by
    intro n
    rfl
  payload_truth := htruth

def ofAcceptedTruth
    (haccepted : _root_.StrengthenedPartialConsistencyAcceptedTruth) :
    Month9Month10StrengthenedPayloadSpecCertificate :=
  standard haccepted.toPayloadTruth

theorem toPayloadTruth
    (h : Month9Month10StrengthenedPayloadSpecCertificate) :
    _root_.StrengthenedPartialConsistencyPayloadTruth :=
  h.payload_truth

theorem toAcceptedTruth
    (h : Month9Month10StrengthenedPayloadSpecCertificate) :
    _root_.StrengthenedPartialConsistencyAcceptedTruth :=
  h.payload_truth.toAcceptedTruth

theorem accepted_standard_iff
    (h : Month9Month10StrengthenedPayloadSpecCertificate)
    (n : Nat) :
    _root_.accepted_certificate
        (_root_.strengthenedPartialConsistencyCode n) ↔
      _root_.strengthened_partial_consistency_payload n := by
  rw [← h.code_family_eq]
  exact h.accepted_iff_payload n

theorem accepted_standard
    (h : Month9Month10StrengthenedPayloadSpecCertificate)
    (n : Nat) :
    _root_.accepted_certificate
      (_root_.strengthenedPartialConsistencyCode n) :=
  (h.accepted_standard_iff n).2 (h.payload_truth.true_all n)

theorem payload_of_accepted_standard
    (h : Month9Month10StrengthenedPayloadSpecCertificate)
    {n : Nat}
    (haccepted :
      _root_.accepted_certificate
        (_root_.strengthenedPartialConsistencyCode n)) :
    _root_.strengthened_partial_consistency_payload n :=
  (h.accepted_standard_iff n).1 haccepted

theorem nonempty_iff_payloadTruth :
    Nonempty Month9Month10StrengthenedPayloadSpecCertificate ↔
      _root_.StrengthenedPartialConsistencyPayloadTruth := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact cert.toPayloadTruth
  · intro htruth
    exact ⟨standard htruth⟩

theorem nonempty_iff_acceptedTruth :
    Nonempty Month9Month10StrengthenedPayloadSpecCertificate ↔
      _root_.StrengthenedPartialConsistencyAcceptedTruth := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact cert.toAcceptedTruth
  · intro haccepted
    exact ⟨ofAcceptedTruth haccepted⟩

def toAcceptedProjectionPackage
    (h : Month9Month10StrengthenedPayloadSpecCertificate)
    (hprinciple : _root_.PAProofLengthProjectionPrinciple) :
    _root_.StrengthenedToPartialAcceptedProjectionPackage :=
  _root_.StrengthenedToPartialAcceptedProjectionPackage.ofStrengthenedAcceptedTruth
    hprinciple h.toAcceptedTruth

theorem toAcceptedProjectionPackage_transfer
    (h : Month9Month10StrengthenedPayloadSpecCertificate)
    (hprinciple : _root_.PAProofLengthProjectionPrinciple) :
    (h.toAcceptedProjectionPackage hprinciple).toTransfer =
      (h.toAcceptedProjectionPackage hprinciple).toCalibration.toTransfer :=
  rfl

structure Audit
    (h : Month9Month10StrengthenedPayloadSpecCertificate) : Prop where
  payloadTruth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  acceptedTruth :
    _root_.StrengthenedPartialConsistencyAcceptedTruth
  standardAcceptedAll :
    ∀ n : Nat,
      _root_.accepted_certificate
        (_root_.strengthenedPartialConsistencyCode n)
  standardAcceptedIffPayload :
    ∀ n : Nat,
      _root_.accepted_certificate
          (_root_.strengthenedPartialConsistencyCode n) ↔
        _root_.strengthened_partial_consistency_payload n

theorem audit
    (h : Month9Month10StrengthenedPayloadSpecCertificate) :
    Audit h where
  payloadTruth := h.toPayloadTruth
  acceptedTruth := h.toAcceptedTruth
  standardAcceptedAll := h.accepted_standard
  standardAcceptedIffPayload := h.accepted_standard_iff

end Month9Month10StrengthenedPayloadSpecCertificate

/-- Lower-route payload/projection frontier.  The strengthened payload semantics
is represented by a structured spec certificate; the current constant
projection remains a separate proof-length transfer obligation. -/
structure Month9Month10StrengthenedPayloadLowerInputs : Type where
  strengthened_spec :
    Month9Month10StrengthenedPayloadSpecCertificate
  strengthened_to_partial_projection :
    _root_.StrengthenedToPartialConsistencyConstantProjection

namespace Month9Month10StrengthenedPayloadLowerInputs

theorem strengthenedPayloadTruth
    (h : Month9Month10StrengthenedPayloadLowerInputs) :
    _root_.StrengthenedPartialConsistencyPayloadTruth :=
  h.strengthened_spec.toPayloadTruth

theorem strengthenedAcceptedTruth
    (h : Month9Month10StrengthenedPayloadLowerInputs) :
    _root_.StrengthenedPartialConsistencyAcceptedTruth :=
  h.strengthened_spec.toAcceptedTruth

theorem strengthenedSpec_nonempty
    (h : Month9Month10StrengthenedPayloadLowerInputs) :
    Nonempty Month9Month10StrengthenedPayloadSpecCertificate :=
  ⟨h.strengthened_spec⟩

theorem constantProjection_nonempty
    (h : Month9Month10StrengthenedPayloadLowerInputs) :
    Nonempty _root_.StrengthenedToPartialConsistencyConstantProjection :=
  ⟨h.strengthened_to_partial_projection⟩

def strengthened_to_partial_transfer
    (h : Month9Month10StrengthenedPayloadLowerInputs) :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer :=
  InternalPudlakTheorem5TransferPieces.strengthenedToPartialTransferOfConstant
    h.strengthened_to_partial_projection

theorem strengthened_to_partial_transfer_eq_projection_transfer
    (h : Month9Month10StrengthenedPayloadLowerInputs) :
    h.strengthened_to_partial_transfer =
      InternalPudlakTheorem5TransferPieces.strengthenedToPartialTransferOfConstant
        h.strengthened_to_partial_projection :=
  rfl

structure Audit
    (h : Month9Month10StrengthenedPayloadLowerInputs) : Prop where
  strengthenedSpec :
    Nonempty Month9Month10StrengthenedPayloadSpecCertificate
  strengthenedPayloadTruth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  strengthenedAcceptedTruth :
    _root_.StrengthenedPartialConsistencyAcceptedTruth
  constantProjection :
    Nonempty _root_.StrengthenedToPartialConsistencyConstantProjection
  transferDerived :
    h.strengthened_to_partial_transfer =
      InternalPudlakTheorem5TransferPieces.strengthenedToPartialTransferOfConstant
        h.strengthened_to_partial_projection

theorem audit
    (h : Month9Month10StrengthenedPayloadLowerInputs) :
    Audit h where
  strengthenedSpec := h.strengthenedSpec_nonempty
  strengthenedPayloadTruth := h.strengthenedPayloadTruth
  strengthenedAcceptedTruth := h.strengthenedAcceptedTruth
  constantProjection := h.constantProjection_nonempty
  transferDerived :=
    h.strengthened_to_partial_transfer_eq_projection_transfer

end Month9Month10StrengthenedPayloadLowerInputs

/-- Split audit for the strengthened-to-partial handoff.  The lower endpoint
still uses the constant projection for the computable gap overhead, but this
surface also records the weaker accepted-projection calibration that is enough
for the lower-bound transfer itself. -/
structure Month9Month10StrengthenedPayloadProjectionSplitInputs : Type where
  lower_inputs : Month9Month10StrengthenedPayloadLowerInputs
  accepted_projection_package :
    _root_.StrengthenedToPartialAcceptedProjectionPackage
  accepted_projection_eq :
    accepted_projection_package.accepted_projection =
      _root_.PartialToStrengthenedAcceptedProjection.ofStrengthenedAcceptedTruth
        lower_inputs.strengthenedAcceptedTruth

namespace Month9Month10StrengthenedPayloadProjectionSplitInputs

def ofProjectionPrinciple
    (lower_inputs : Month9Month10StrengthenedPayloadLowerInputs)
    (hprinciple : _root_.PAProofLengthProjectionPrinciple) :
    Month9Month10StrengthenedPayloadProjectionSplitInputs where
  lower_inputs := lower_inputs
  accepted_projection_package :=
    lower_inputs.strengthened_spec.toAcceptedProjectionPackage hprinciple
  accepted_projection_eq := rfl

theorem strengthenedPayloadTruth
    (h : Month9Month10StrengthenedPayloadProjectionSplitInputs) :
    _root_.StrengthenedPartialConsistencyPayloadTruth :=
  h.lower_inputs.strengthenedPayloadTruth

theorem strengthenedAcceptedTruth
    (h : Month9Month10StrengthenedPayloadProjectionSplitInputs) :
    _root_.StrengthenedPartialConsistencyAcceptedTruth :=
  h.lower_inputs.strengthenedAcceptedTruth

theorem lowerInputs_nonempty
    (h : Month9Month10StrengthenedPayloadProjectionSplitInputs) :
    Nonempty Month9Month10StrengthenedPayloadLowerInputs :=
  ⟨h.lower_inputs⟩

theorem acceptedProjectionPackage_nonempty
    (h : Month9Month10StrengthenedPayloadProjectionSplitInputs) :
    Nonempty _root_.StrengthenedToPartialAcceptedProjectionPackage :=
  ⟨h.accepted_projection_package⟩

theorem constantProjection_nonempty
    (h : Month9Month10StrengthenedPayloadProjectionSplitInputs) :
    Nonempty _root_.StrengthenedToPartialConsistencyConstantProjection :=
  h.lower_inputs.constantProjection_nonempty

def accepted_projection_transfer
    (h : Month9Month10StrengthenedPayloadProjectionSplitInputs) :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer :=
  h.accepted_projection_package.toTransfer

def constant_projection_transfer
    (h : Month9Month10StrengthenedPayloadProjectionSplitInputs) :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer :=
  h.lower_inputs.strengthened_to_partial_transfer

theorem acceptedProjectionTransfer_nonempty
    (h : Month9Month10StrengthenedPayloadProjectionSplitInputs) :
    Nonempty _root_.StrengthenedToPartialConsistencyLowerBoundTransfer :=
  ⟨h.accepted_projection_transfer⟩

theorem constantProjectionTransfer_nonempty
    (h : Month9Month10StrengthenedPayloadProjectionSplitInputs) :
    Nonempty _root_.StrengthenedToPartialConsistencyLowerBoundTransfer :=
  ⟨h.constant_projection_transfer⟩

theorem accepted_projection_transfer_eq_package_transfer
    (h : Month9Month10StrengthenedPayloadProjectionSplitInputs) :
    h.accepted_projection_transfer =
      h.accepted_projection_package.toTransfer :=
  rfl

theorem constant_projection_transfer_eq_lower_inputs_transfer
    (h : Month9Month10StrengthenedPayloadProjectionSplitInputs) :
    h.constant_projection_transfer =
      h.lower_inputs.strengthened_to_partial_transfer :=
  rfl

theorem accepted_projection_matches_spec
    (h : Month9Month10StrengthenedPayloadProjectionSplitInputs) :
    h.accepted_projection_package.accepted_projection =
      _root_.PartialToStrengthenedAcceptedProjection.ofStrengthenedAcceptedTruth
        h.lower_inputs.strengthenedAcceptedTruth :=
  h.accepted_projection_eq

structure Audit
    (h : Month9Month10StrengthenedPayloadProjectionSplitInputs) : Prop where
  lowerAudit :
    h.lower_inputs.Audit
  acceptedProjectionPackage :
    Nonempty _root_.StrengthenedToPartialAcceptedProjectionPackage
  acceptedProjectionMatchesSpec :
    h.accepted_projection_package.accepted_projection =
      _root_.PartialToStrengthenedAcceptedProjection.ofStrengthenedAcceptedTruth
        h.lower_inputs.strengthenedAcceptedTruth
  acceptedTransfer :
    Nonempty _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  constantProjection :
    Nonempty _root_.StrengthenedToPartialConsistencyConstantProjection
  constantTransfer :
    Nonempty _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  acceptedTransferDerived :
    h.accepted_projection_transfer =
      h.accepted_projection_package.toTransfer
  constantTransferDerived :
    h.constant_projection_transfer =
      h.lower_inputs.strengthened_to_partial_transfer

theorem audit
    (h : Month9Month10StrengthenedPayloadProjectionSplitInputs) :
    Audit h where
  lowerAudit := h.lower_inputs.audit
  acceptedProjectionPackage := h.acceptedProjectionPackage_nonempty
  acceptedProjectionMatchesSpec := h.accepted_projection_matches_spec
  acceptedTransfer := h.acceptedProjectionTransfer_nonempty
  constantProjection := h.constantProjection_nonempty
  constantTransfer := h.constantProjectionTransfer_nonempty
  acceptedTransferDerived :=
    h.accepted_projection_transfer_eq_package_transfer
  constantTransferDerived :=
    h.constant_projection_transfer_eq_lower_inputs_transfer

end Month9Month10StrengthenedPayloadProjectionSplitInputs

theorem month9_month10_strengthened_payload_projection_split_closure
    (h : Month9Month10StrengthenedPayloadProjectionSplitInputs) :
    Nonempty Month9Month10StrengthenedPayloadLowerInputs ∧
      Nonempty _root_.StrengthenedToPartialAcceptedProjectionPackage ∧
        _root_.StrengthenedPartialConsistencyAcceptedTruth ∧
          _root_.StrengthenedPartialConsistencyPayloadTruth ∧
            Nonempty _root_.StrengthenedToPartialConsistencyConstantProjection ∧
              Nonempty _root_.StrengthenedToPartialConsistencyLowerBoundTransfer ∧
                Nonempty
                  _root_.StrengthenedToPartialConsistencyLowerBoundTransfer ∧
                  h.accepted_projection_transfer =
                    h.accepted_projection_package.toTransfer ∧
                    h.constant_projection_transfer =
                      h.lower_inputs.strengthened_to_partial_transfer :=
  ⟨h.lowerInputs_nonempty,
    h.acceptedProjectionPackage_nonempty,
    h.strengthenedAcceptedTruth,
    h.strengthenedPayloadTruth,
    h.constantProjection_nonempty,
    h.acceptedProjectionTransfer_nonempty,
    h.constantProjectionTransfer_nonempty,
    h.accepted_projection_transfer_eq_package_transfer,
    h.constant_projection_transfer_eq_lower_inputs_transfer⟩

/-- Calibrated checker endpoint whose Sondow upper side is generated from the
structured payload-spec verifier route.  This is the narrow Month 9-10 handoff
shape before replacing the remaining strengthened-payload and proof-length
frontiers by concrete PA/Hilbert checker data. -/
structure Month9Month10PayloadSpecCalibratedEndpointInputs :
    Type (q + 1) where
  scale_data : InternalPudlakTheorem5ScaleData
  checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data
  enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker
  extractor :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      checker enumeration
  length_calibration :
    InternalPudlakTheorem5CheckerFamilyLengthCalibration checker
  strengthened_to_partial_projection :
    _root_.StrengthenedToPartialConsistencyConstantProjection
  partial_to_graft_projection :
    _root_.PAConjunctionEliminationConstantCost
  computable_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox
  upper_inputs : Month9Month10PayloadSpecUpperInputs

namespace Month9Month10PayloadSpecCalibratedEndpointInputs

def project_upper
    (h : Month9Month10PayloadSpecCalibratedEndpointInputs.{q}) :
    SondowProjectLocalS21CollapseConclusion :=
  h.upper_inputs.toProjectUpper

def toCalibratedFamilyEndpointInputs
    (h : Month9Month10PayloadSpecCalibratedEndpointInputs.{q}) :
    Month9Month10CheckerExtractorCalibratedFamilyEndpointInputs.{q} where
  scale_data := h.scale_data
  checker := h.checker
  enumeration := h.enumeration
  extractor := h.extractor
  length_calibration := h.length_calibration
  strengthened_to_partial_projection :=
    h.strengthened_to_partial_projection
  partial_to_graft_projection := h.partial_to_graft_projection
  computable_gap := h.computable_gap
  project_upper := h.project_upper

def toProjectEndpointInputs
    (h : Month9Month10PayloadSpecCalibratedEndpointInputs.{q}) :
    Month9Month10CheckerExtractorProjectEndpointInputs.{q} :=
  h.toCalibratedFamilyEndpointInputs.toProjectEndpointInputs

theorem endpoint_frontier
    (h : Month9Month10PayloadSpecCalibratedEndpointInputs.{q}) :
    h.toProjectEndpointInputs.EndpointFrontier :=
  h.toCalibratedFamilyEndpointInputs.endpoint_frontier

theorem not_rational
    (h : Month9Month10PayloadSpecCalibratedEndpointInputs.{q}) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toCalibratedFamilyEndpointInputs.not_rational

noncomputable def computedCollisionNOfRationality
    (h : Month9Month10PayloadSpecCalibratedEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  h.toCalibratedFamilyEndpointInputs.computedCollisionNOfRationality hrat

theorem computedCollisionN_eq_searchGapWitness
    (h : Month9Month10PayloadSpecCalibratedEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    h.computedCollisionNOfRationality hrat =
      ((h.toProjectEndpointInputs.toProjectGapTransferChecklist
          |>.toComputableSearchGapCertificate
          |>.gap_for_polynomial_upper
            (h.toProjectEndpointInputs.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).U
            (h.toProjectEndpointInputs.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).polynomial)
        |>.witness
          (h.toProjectEndpointInputs.toProjectGapTransferChecklist
            |>.upperTailOfRationality h.project_upper hrat).upperN) :=
  h.toCalibratedFamilyEndpointInputs.computedCollisionN_eq_searchGapWitness
    hrat

theorem computedCollisionN_ge_upperN
    (h : Month9Month10PayloadSpecCalibratedEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.toProjectEndpointInputs.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).upperN ≤
      h.computedCollisionNOfRationality hrat :=
  h.toCalibratedFamilyEndpointInputs.computedCollisionN_ge_upperN hrat

theorem endpoint_lower_at_computedCollisionN
    (h : Month9Month10PayloadSpecCalibratedEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.toProjectEndpointInputs.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).U
        (h.computedCollisionNOfRationality hrat) <
      sondowProjectLocalPudlakCollisionBox
        (h.computedCollisionNOfRationality hrat) :=
  h.toCalibratedFamilyEndpointInputs.endpoint_lower_at_computedCollisionN
    hrat

theorem endpoint_upper_at_computedCollisionN
    (h : Month9Month10PayloadSpecCalibratedEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    sondowProjectLocalPudlakCollisionBox
        (h.computedCollisionNOfRationality hrat) ≤
      (h.toProjectEndpointInputs.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).U
        (h.computedCollisionNOfRationality hrat) :=
  h.toCalibratedFamilyEndpointInputs.endpoint_upper_at_computedCollisionN
    hrat

theorem endpoint_contradiction
    (h : Month9Month10PayloadSpecCalibratedEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.toCalibratedFamilyEndpointInputs.endpoint_contradiction hrat

structure Audit
    (h : Month9Month10PayloadSpecCalibratedEndpointInputs.{q}) :
    Prop where
  upperAudit :
    h.upper_inputs.Audit
  calibratedAudit :
    h.toCalibratedFamilyEndpointInputs.Audit
  endpointFrontier :
    h.toProjectEndpointInputs.EndpointFrontier
  computed_n_eq_searchGapWitness :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      h.computedCollisionNOfRationality hrat =
        ((h.toProjectEndpointInputs.toProjectGapTransferChecklist
            |>.toComputableSearchGapCertificate
            |>.gap_for_polynomial_upper
              (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                |>.upperTailOfRationality h.project_upper hrat).U
              (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                |>.upperTailOfRationality h.project_upper hrat).polynomial)
          |>.witness
            (h.toProjectEndpointInputs.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).upperN)
  contradiction_at_computed_n :
    ∀ _ : _root_.is_rational _root_.euler_mascheroni,
      False
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem audit
    (h : Month9Month10PayloadSpecCalibratedEndpointInputs.{q}) :
    Audit h where
  upperAudit := h.upper_inputs.audit
  calibratedAudit := h.toCalibratedFamilyEndpointInputs.audit
  endpointFrontier := h.endpoint_frontier
  computed_n_eq_searchGapWitness := h.computedCollisionN_eq_searchGapWitness
  contradiction_at_computed_n := fun hrat => h.endpoint_contradiction hrat
  endpointNotRational := h.not_rational

end Month9Month10PayloadSpecCalibratedEndpointInputs

theorem month9_month10_payload_spec_calibrated_endpoint_closure
    (h : Month9Month10PayloadSpecCalibratedEndpointInputs.{q}) :
    Nonempty SondowProjectLocalReflectionGraftVerifier ∧
      Nonempty PartialConsistencyPayloadSpecCertificate ∧
        Nonempty _root_.PartialConsistencyAcceptedTruth ∧
          Nonempty _root_.PartialConsistencyPayloadTruth ∧
            Nonempty
              (InternalPudlakTheorem5CheckerFamilyLengthCalibration
                h.checker) ∧
              h.toProjectEndpointInputs.EndpointFrontier ∧
                (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                  h.computedCollisionNOfRationality hrat =
                    ((h.toProjectEndpointInputs.toProjectGapTransferChecklist
                        |>.toComputableSearchGapCertificate
                        |>.gap_for_polynomial_upper
                          (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                            |>.upperTailOfRationality h.project_upper hrat).U
                          (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                            |>.upperTailOfRationality h.project_upper hrat).polynomial)
                      |>.witness
                        (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                          |>.upperTailOfRationality h.project_upper hrat).upperN)) ∧
                  (∀ _ : _root_.is_rational _root_.euler_mascheroni,
                    False) ∧
                    ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact
    ⟨h.upper_inputs.verifier_nonempty,
      h.upper_inputs.payloadSpec_nonempty,
      h.upper_inputs.acceptedTruth_nonempty,
      h.upper_inputs.payloadTruth_nonempty,
      ⟨h.length_calibration⟩,
      h.endpoint_frontier,
      h.computedCollisionN_eq_searchGapWitness,
      (fun hrat => h.endpoint_contradiction hrat),
      h.not_rational⟩

/-- Fully payload-spec-facing Month 9-10 endpoint.  The ordinary Sondow upper
payload and the strengthened Pudlak lower payload are both represented by
structured certificates; the remaining lower-route projection is exposed as the
separate constant-projection field inside `lower_inputs`. -/
structure Month9Month10DualPayloadSpecCalibratedEndpointInputs :
    Type (q + 1) where
  scale_data : InternalPudlakTheorem5ScaleData
  checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data
  enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker
  extractor :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      checker enumeration
  length_calibration :
    InternalPudlakTheorem5CheckerFamilyLengthCalibration checker
  lower_inputs : Month9Month10StrengthenedPayloadLowerInputs
  partial_to_graft_projection :
    _root_.PAConjunctionEliminationConstantCost
  computable_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox
  upper_inputs : Month9Month10PayloadSpecUpperInputs

namespace Month9Month10DualPayloadSpecCalibratedEndpointInputs

def toPayloadSpecCalibratedEndpointInputs
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{q}) :
    Month9Month10PayloadSpecCalibratedEndpointInputs.{q} where
  scale_data := h.scale_data
  checker := h.checker
  enumeration := h.enumeration
  extractor := h.extractor
  length_calibration := h.length_calibration
  strengthened_to_partial_projection :=
    h.lower_inputs.strengthened_to_partial_projection
  partial_to_graft_projection := h.partial_to_graft_projection
  computable_gap := h.computable_gap
  upper_inputs := h.upper_inputs

def project_upper
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{q}) :
    SondowProjectLocalS21CollapseConclusion :=
  h.upper_inputs.toProjectUpper

def toProjectEndpointInputs
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{q}) :
    Month9Month10CheckerExtractorProjectEndpointInputs.{q} :=
  h.toPayloadSpecCalibratedEndpointInputs.toProjectEndpointInputs

theorem endpoint_frontier
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{q}) :
    h.toProjectEndpointInputs.EndpointFrontier :=
  h.toPayloadSpecCalibratedEndpointInputs.endpoint_frontier

theorem not_rational
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{q}) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPayloadSpecCalibratedEndpointInputs.not_rational

noncomputable def computedCollisionNOfRationality
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  h.toPayloadSpecCalibratedEndpointInputs.computedCollisionNOfRationality
    hrat

theorem computedCollisionN_eq_searchGapWitness
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    h.computedCollisionNOfRationality hrat =
      ((h.toProjectEndpointInputs.toProjectGapTransferChecklist
          |>.toComputableSearchGapCertificate
          |>.gap_for_polynomial_upper
            (h.toProjectEndpointInputs.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).U
            (h.toProjectEndpointInputs.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).polynomial)
        |>.witness
          (h.toProjectEndpointInputs.toProjectGapTransferChecklist
            |>.upperTailOfRationality h.project_upper hrat).upperN) :=
  h.toPayloadSpecCalibratedEndpointInputs
    |>.computedCollisionN_eq_searchGapWitness hrat

theorem endpoint_contradiction
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.toPayloadSpecCalibratedEndpointInputs.endpoint_contradiction hrat

structure Audit
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{q}) :
    Prop where
  upperAudit :
    h.upper_inputs.Audit
  strengthenedLowerAudit :
    h.lower_inputs.Audit
  endpointAudit :
    h.toPayloadSpecCalibratedEndpointInputs.Audit
  ordinaryPayloadSpec :
    Nonempty PartialConsistencyPayloadSpecCertificate
  strengthenedPayloadSpec :
    Nonempty Month9Month10StrengthenedPayloadSpecCertificate
  strengthenedConstantProjection :
    Nonempty _root_.StrengthenedToPartialConsistencyConstantProjection
  partialToGraftProjection :
    Nonempty _root_.PAConjunctionEliminationConstantCost
  computableGap :
    Nonempty (ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
  lengthCalibration :
    Nonempty
      (InternalPudlakTheorem5CheckerFamilyLengthCalibration h.checker)
  endpointFrontier :
    h.toProjectEndpointInputs.EndpointFrontier
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem audit
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{q}) :
    Audit h where
  upperAudit := h.upper_inputs.audit
  strengthenedLowerAudit := h.lower_inputs.audit
  endpointAudit := h.toPayloadSpecCalibratedEndpointInputs.audit
  ordinaryPayloadSpec := h.upper_inputs.payloadSpec_nonempty
  strengthenedPayloadSpec := h.lower_inputs.strengthenedSpec_nonempty
  strengthenedConstantProjection := h.lower_inputs.constantProjection_nonempty
  partialToGraftProjection := ⟨h.partial_to_graft_projection⟩
  computableGap := ⟨h.computable_gap⟩
  lengthCalibration := ⟨h.length_calibration⟩
  endpointFrontier := h.endpoint_frontier
  endpointNotRational := h.not_rational

end Month9Month10DualPayloadSpecCalibratedEndpointInputs

theorem month9_month10_dual_payload_spec_calibrated_endpoint_closure
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{q}) :
    Nonempty PartialConsistencyPayloadSpecCertificate ∧
      Nonempty Month9Month10StrengthenedPayloadSpecCertificate ∧
        _root_.StrengthenedPartialConsistencyAcceptedTruth ∧
          _root_.StrengthenedPartialConsistencyPayloadTruth ∧
            Nonempty _root_.StrengthenedToPartialConsistencyConstantProjection ∧
              Nonempty _root_.PAConjunctionEliminationConstantCost ∧
                Nonempty
                  (ComputableGapCertificate
                    sondowProjectLocalPudlakCollisionBox) ∧
                  Nonempty
                    (InternalPudlakTheorem5CheckerFamilyLengthCalibration
                      h.checker) ∧
                    h.toProjectEndpointInputs.EndpointFrontier ∧
                      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                        h.computedCollisionNOfRationality hrat =
                          ((h.toProjectEndpointInputs.toProjectGapTransferChecklist
                              |>.toComputableSearchGapCertificate
                              |>.gap_for_polynomial_upper
                                (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                                  |>.upperTailOfRationality h.project_upper hrat).U
                                (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                                  |>.upperTailOfRationality h.project_upper hrat).polynomial)
                            |>.witness
                              (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                                |>.upperTailOfRationality h.project_upper hrat).upperN)) ∧
                        (∀ _ : _root_.is_rational _root_.euler_mascheroni,
                          False) ∧
                          ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact
    ⟨h.upper_inputs.payloadSpec_nonempty,
      h.lower_inputs.strengthenedSpec_nonempty,
      h.lower_inputs.strengthenedAcceptedTruth,
      h.lower_inputs.strengthenedPayloadTruth,
      h.lower_inputs.constantProjection_nonempty,
      ⟨h.partial_to_graft_projection⟩,
      ⟨h.computable_gap⟩,
      ⟨h.length_calibration⟩,
      h.endpoint_frontier,
      h.computedCollisionN_eq_searchGapWitness,
      (fun hrat => h.endpoint_contradiction hrat),
      h.not_rational⟩

/-- Payload-spec endpoint with the strengthened lower route split into the
accepted-projection calibration and the constant-overhead projection.  This is
an audit-oriented entry point: it delegates the collision proof to the existing
dual endpoint while making the weaker lower-transfer source visible. -/
structure Month9Month10SplitPayloadSpecCalibratedEndpointInputs :
    Type (q + 1) where
  scale_data : InternalPudlakTheorem5ScaleData
  checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data
  enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker
  extractor :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      checker enumeration
  length_calibration :
    InternalPudlakTheorem5CheckerFamilyLengthCalibration checker
  lower_split : Month9Month10StrengthenedPayloadProjectionSplitInputs
  partial_to_graft_projection :
    _root_.PAConjunctionEliminationConstantCost
  computable_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox
  upper_inputs : Month9Month10PayloadSpecUpperInputs

namespace Month9Month10SplitPayloadSpecCalibratedEndpointInputs

def toDualPayloadSpecCalibratedEndpointInputs
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{q}) :
    Month9Month10DualPayloadSpecCalibratedEndpointInputs.{q} where
  scale_data := h.scale_data
  checker := h.checker
  enumeration := h.enumeration
  extractor := h.extractor
  length_calibration := h.length_calibration
  lower_inputs := h.lower_split.lower_inputs
  partial_to_graft_projection := h.partial_to_graft_projection
  computable_gap := h.computable_gap
  upper_inputs := h.upper_inputs

def project_upper
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{q}) :
    SondowProjectLocalS21CollapseConclusion :=
  h.upper_inputs.toProjectUpper

def toProjectEndpointInputs
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{q}) :
    Month9Month10CheckerExtractorProjectEndpointInputs.{q} :=
  h.toDualPayloadSpecCalibratedEndpointInputs.toProjectEndpointInputs

theorem endpoint_frontier
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{q}) :
    h.toProjectEndpointInputs.EndpointFrontier :=
  h.toDualPayloadSpecCalibratedEndpointInputs.endpoint_frontier

theorem not_rational
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{q}) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toDualPayloadSpecCalibratedEndpointInputs.not_rational

noncomputable def computedCollisionNOfRationality
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  h.toDualPayloadSpecCalibratedEndpointInputs
    |>.computedCollisionNOfRationality hrat

noncomputable def computedSearchCollisionWitnessOfRationality
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ComputedSearchCollisionWitness
      ((h.toProjectEndpointInputs.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).U)
      sondowProjectLocalPudlakCollisionBox :=
  h.toProjectEndpointInputs.projectSearchCollisionWitnessOfRationality hrat

theorem computedSearchCollisionWitness_n_eq_computedCollisionN
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.computedSearchCollisionWitnessOfRationality hrat).n =
      h.computedCollisionNOfRationality hrat :=
  rfl

theorem computedCollisionN_eq_searchGapWitness
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    h.computedCollisionNOfRationality hrat =
      ((h.toProjectEndpointInputs.toProjectGapTransferChecklist
          |>.toComputableSearchGapCertificate
          |>.gap_for_polynomial_upper
            (h.toProjectEndpointInputs.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).U
            (h.toProjectEndpointInputs.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).polynomial)
        |>.witness
          (h.toProjectEndpointInputs.toProjectGapTransferChecklist
            |>.upperTailOfRationality h.project_upper hrat).upperN) :=
  h.toDualPayloadSpecCalibratedEndpointInputs
    |>.computedCollisionN_eq_searchGapWitness hrat

theorem computedCollisionN_ge_upperN
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.toProjectEndpointInputs.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).upperN ≤
      h.computedCollisionNOfRationality hrat :=
  h.toProjectEndpointInputs.computedCollisionN_ge_upperN hrat

theorem endpoint_lower_at_computedCollisionN
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.toProjectEndpointInputs.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).U
        (h.computedCollisionNOfRationality hrat) <
      sondowProjectLocalPudlakCollisionBox
        (h.computedCollisionNOfRationality hrat) :=
  h.toProjectEndpointInputs.endpoint_lower_at_computedCollisionN hrat

theorem endpoint_upper_at_computedCollisionN
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    sondowProjectLocalPudlakCollisionBox
        (h.computedCollisionNOfRationality hrat) ≤
      (h.toProjectEndpointInputs.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).U
        (h.computedCollisionNOfRationality hrat) :=
  h.toProjectEndpointInputs.endpoint_upper_at_computedCollisionN hrat

theorem endpoint_contradiction
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.toDualPayloadSpecCalibratedEndpointInputs.endpoint_contradiction hrat

/-- One-rationality-assumption witness trace for the split endpoint.  It keeps
the computed search witness, the formula for its index, the upper/lower
inequalities at that exact index, and the resulting contradiction together. -/
structure ComputedEndpointWitnessTrace
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Prop where
  computedWitness :
    Nonempty
      (ComputedSearchCollisionWitness
        ((h.toProjectEndpointInputs.toProjectGapTransferChecklist
          |>.upperTailOfRationality h.project_upper hrat).U)
        sondowProjectLocalPudlakCollisionBox)
  witness_n_eq_computed_n :
    (h.computedSearchCollisionWitnessOfRationality hrat).n =
      h.computedCollisionNOfRationality hrat
  computed_n_eq_searchGapWitness :
    h.computedCollisionNOfRationality hrat =
      ((h.toProjectEndpointInputs.toProjectGapTransferChecklist
          |>.toComputableSearchGapCertificate
          |>.gap_for_polynomial_upper
            (h.toProjectEndpointInputs.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).U
            (h.toProjectEndpointInputs.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).polynomial)
        |>.witness
          (h.toProjectEndpointInputs.toProjectGapTransferChecklist
            |>.upperTailOfRationality h.project_upper hrat).upperN)
  computed_n_ge_upperN :
    (h.toProjectEndpointInputs.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).upperN ≤
      h.computedCollisionNOfRationality hrat
  lower_at_computed_n :
    (h.toProjectEndpointInputs.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).U
        (h.computedCollisionNOfRationality hrat) <
      sondowProjectLocalPudlakCollisionBox
        (h.computedCollisionNOfRationality hrat)
  upper_at_computed_n :
    sondowProjectLocalPudlakCollisionBox
        (h.computedCollisionNOfRationality hrat) ≤
      (h.toProjectEndpointInputs.toProjectGapTransferChecklist
        |>.upperTailOfRationality h.project_upper hrat).U
        (h.computedCollisionNOfRationality hrat)
  contradiction_at_computed_n :
    False

theorem computedEndpointWitnessTrace
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{q})
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ComputedEndpointWitnessTrace h hrat where
  computedWitness :=
    ⟨h.computedSearchCollisionWitnessOfRationality hrat⟩
  witness_n_eq_computed_n :=
    h.computedSearchCollisionWitness_n_eq_computedCollisionN hrat
  computed_n_eq_searchGapWitness :=
    h.computedCollisionN_eq_searchGapWitness hrat
  computed_n_ge_upperN :=
    h.computedCollisionN_ge_upperN hrat
  lower_at_computed_n :=
    h.endpoint_lower_at_computedCollisionN hrat
  upper_at_computed_n :=
    h.endpoint_upper_at_computedCollisionN hrat
  contradiction_at_computed_n :=
    h.endpoint_contradiction hrat

structure Audit
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{q}) :
    Prop where
  upperAudit :
    h.upper_inputs.Audit
  splitLowerAudit :
    h.lower_split.Audit
  dualEndpointAudit :
    h.toDualPayloadSpecCalibratedEndpointInputs.Audit
  acceptedProjectionPackage :
    Nonempty _root_.StrengthenedToPartialAcceptedProjectionPackage
  acceptedTransfer :
    Nonempty _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  constantTransfer :
    Nonempty _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  endpointFrontier :
    h.toProjectEndpointInputs.EndpointFrontier
  computedEndpointWitnessTrace :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      h.ComputedEndpointWitnessTrace hrat
  computed_n_eq_searchGapWitness :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      h.computedCollisionNOfRationality hrat =
        ((h.toProjectEndpointInputs.toProjectGapTransferChecklist
            |>.toComputableSearchGapCertificate
            |>.gap_for_polynomial_upper
              (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                |>.upperTailOfRationality h.project_upper hrat).U
              (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                |>.upperTailOfRationality h.project_upper hrat).polynomial)
          |>.witness
            (h.toProjectEndpointInputs.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).upperN)
  computed_n_ge_upperN :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (h.toProjectEndpointInputs.toProjectGapTransferChecklist
          |>.upperTailOfRationality h.project_upper hrat).upperN ≤
        h.computedCollisionNOfRationality hrat
  lower_at_computed_n :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (h.toProjectEndpointInputs.toProjectGapTransferChecklist
          |>.upperTailOfRationality h.project_upper hrat).U
          (h.computedCollisionNOfRationality hrat) <
        sondowProjectLocalPudlakCollisionBox
          (h.computedCollisionNOfRationality hrat)
  upper_at_computed_n :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      sondowProjectLocalPudlakCollisionBox
          (h.computedCollisionNOfRationality hrat) ≤
        (h.toProjectEndpointInputs.toProjectGapTransferChecklist
          |>.upperTailOfRationality h.project_upper hrat).U
          (h.computedCollisionNOfRationality hrat)
  contradiction_at_computed_n :
    ∀ _ : _root_.is_rational _root_.euler_mascheroni,
      False
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem audit
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{q}) :
    Audit h where
  upperAudit := h.upper_inputs.audit
  splitLowerAudit := h.lower_split.audit
  dualEndpointAudit := h.toDualPayloadSpecCalibratedEndpointInputs.audit
  acceptedProjectionPackage :=
    h.lower_split.acceptedProjectionPackage_nonempty
  acceptedTransfer :=
    h.lower_split.acceptedProjectionTransfer_nonempty
  constantTransfer :=
    h.lower_split.constantProjectionTransfer_nonempty
  endpointFrontier := h.endpoint_frontier
  computedEndpointWitnessTrace := h.computedEndpointWitnessTrace
  computed_n_eq_searchGapWitness := h.computedCollisionN_eq_searchGapWitness
  computed_n_ge_upperN := h.computedCollisionN_ge_upperN
  lower_at_computed_n := h.endpoint_lower_at_computedCollisionN
  upper_at_computed_n := h.endpoint_upper_at_computedCollisionN
  contradiction_at_computed_n := fun hrat => h.endpoint_contradiction hrat
  endpointNotRational := h.not_rational

end Month9Month10SplitPayloadSpecCalibratedEndpointInputs

theorem month9_month10_split_payload_spec_calibrated_endpoint_closure
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{q}) :
    Nonempty PartialConsistencyPayloadSpecCertificate ∧
      Nonempty Month9Month10StrengthenedPayloadSpecCertificate ∧
        Nonempty _root_.StrengthenedToPartialAcceptedProjectionPackage ∧
          _root_.StrengthenedPartialConsistencyAcceptedTruth ∧
            _root_.StrengthenedPartialConsistencyPayloadTruth ∧
              Nonempty _root_.StrengthenedToPartialConsistencyConstantProjection ∧
                Nonempty _root_.StrengthenedToPartialConsistencyLowerBoundTransfer ∧
                  Nonempty _root_.PAConjunctionEliminationConstantCost ∧
                    Nonempty
                      (ComputableGapCertificate
                        sondowProjectLocalPudlakCollisionBox) ∧
                      Nonempty
                        (InternalPudlakTheorem5CheckerFamilyLengthCalibration
                          h.checker) ∧
                        h.toProjectEndpointInputs.EndpointFrontier ∧
                          (∀ hrat :
                            _root_.is_rational _root_.euler_mascheroni,
                            h.computedCollisionNOfRationality hrat =
                              ((h.toProjectEndpointInputs
                                  |>.toProjectGapTransferChecklist
                                  |>.toComputableSearchGapCertificate
                                  |>.gap_for_polynomial_upper
                                    (h.toProjectEndpointInputs
                                      |>.toProjectGapTransferChecklist
                                      |>.upperTailOfRationality
                                        h.project_upper hrat).U
                                    (h.toProjectEndpointInputs
                                      |>.toProjectGapTransferChecklist
                                      |>.upperTailOfRationality
                                        h.project_upper hrat).polynomial)
                                |>.witness
                                  (h.toProjectEndpointInputs
                                    |>.toProjectGapTransferChecklist
                                    |>.upperTailOfRationality
                                      h.project_upper hrat).upperN)) ∧
                            (∀ _ :
                              _root_.is_rational _root_.euler_mascheroni,
                              False) ∧
                              ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨h.upper_inputs.payloadSpec_nonempty,
    h.lower_split.lower_inputs.strengthenedSpec_nonempty,
    h.lower_split.acceptedProjectionPackage_nonempty,
    h.lower_split.strengthenedAcceptedTruth,
    h.lower_split.strengthenedPayloadTruth,
    h.lower_split.constantProjection_nonempty,
    h.lower_split.acceptedProjectionTransfer_nonempty,
    ⟨h.partial_to_graft_projection⟩,
    ⟨h.computable_gap⟩,
    ⟨h.length_calibration⟩,
    h.endpoint_frontier,
    h.computedCollisionN_eq_searchGapWitness,
    (fun hrat => h.endpoint_contradiction hrat),
    h.not_rational⟩

theorem month9_month10_split_payload_spec_computed_inequality_closure
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{q}) :
    h.toProjectEndpointInputs.EndpointFrontier ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (h.toProjectEndpointInputs.toProjectGapTransferChecklist
            |>.upperTailOfRationality h.project_upper hrat).upperN ≤
          h.computedCollisionNOfRationality hrat) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (h.toProjectEndpointInputs.toProjectGapTransferChecklist
              |>.upperTailOfRationality h.project_upper hrat).U
              (h.computedCollisionNOfRationality hrat) <
            sondowProjectLocalPudlakCollisionBox
              (h.computedCollisionNOfRationality hrat)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            sondowProjectLocalPudlakCollisionBox
                (h.computedCollisionNOfRationality hrat) ≤
              (h.toProjectEndpointInputs.toProjectGapTransferChecklist
                |>.upperTailOfRationality h.project_upper hrat).U
                (h.computedCollisionNOfRationality hrat)) ∧
            (∀ _ : _root_.is_rational _root_.euler_mascheroni,
              False) :=
  ⟨h.endpoint_frontier,
    h.computedCollisionN_ge_upperN,
    h.endpoint_lower_at_computedCollisionN,
    h.endpoint_upper_at_computedCollisionN,
    fun hrat => h.endpoint_contradiction hrat⟩

namespace Month9Month10ProjectBoxAlignedComputableSearchChecklist

def toProjectGapTransferChecklist
    (h : Month9Month10ProjectBoxAlignedComputableSearchChecklist.{q}) :
    Month9Month10ProjectGapTransferComputableSearchChecklist.{q} where
  computable_search_checklist := h.computable_search_checklist
  project_gap_transfer := h.project_box_alignment.toComputableProjectGapTransfer

end Month9Month10ProjectBoxAlignedComputableSearchChecklist

theorem month9_month10_intrinsic_theorem5_closure
    (h : Month9Month10IntrinsicTheorem5Checklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty IntrinsicPudlakTheorem5PowerBoundMachine ∧
      Nonempty InternalPudlakTheorem5PowerBoundMachine ∧
        Nonempty InternalPudlakTheorem5Machine ∧
          Nonempty _root_.PudlakFiniteConsistencyLowerBoundPackage ∧
            (∀ n : Nat,
              h.theorem5_machine.toRescaledMachine.toNormalForm.code n =
                _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
                  h.theorem5_machine.scale_data.scale n) ∧
              (h.toProjectChecklist project_upper).not_rational =
                GenericRationalCollisionInputs.not_rational
                  (h.toProjectChecklist project_upper).toGenericCollisionInputs :=
  ⟨⟨h.theorem5_machine⟩,
    ⟨h.theorem5_machine.toPowerBoundMachine⟩,
    ⟨h.theorem5_machine.toRescaledMachine⟩,
    ⟨h.toRefinedChecklist.lowerPackage⟩,
    h.intrinsic_normalForm_code_eq_rescaledPudlak,
    h.project_not_rational_eq_generic_core project_upper⟩

theorem month9_month10_lower_bound_core_closure
    (h : Month9Month10LowerBoundCoreChecklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty InternalPudlakTheorem5LowerBoundCore ∧
      Nonempty IntrinsicPudlakTheorem5PowerBoundMachine ∧
        Nonempty InternalPudlakTheorem5PowerBoundMachine ∧
          Nonempty InternalPudlakTheorem5Machine ∧
            Nonempty _root_.PudlakFiniteConsistencyLowerBoundPackage ∧
              (∀ n : Nat,
                h.toIntrinsicChecklist.theorem5_machine.toRescaledMachine.toNormalForm.code n =
                  _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
                    h.theorem5_core.scale_data.scale n) ∧
                (h.toProjectChecklist project_upper).not_rational =
                  GenericRationalCollisionInputs.not_rational
                    (h.toProjectChecklist project_upper).toGenericCollisionInputs :=
  ⟨⟨h.theorem5_core⟩,
    ⟨h.toIntrinsicChecklist.theorem5_machine⟩,
    ⟨h.toIntrinsicChecklist.theorem5_machine.toPowerBoundMachine⟩,
    ⟨h.toIntrinsicChecklist.theorem5_machine.toRescaledMachine⟩,
    ⟨h.toIntrinsicChecklist.toRefinedChecklist.lowerPackage⟩,
    h.core_normalForm_code_eq_rescaledPudlak,
    h.project_not_rational_eq_generic_core project_upper⟩

theorem month9_month10_no_small_code_semantics_core_closure
    (h : Month9Month10NoSmallCodeSemanticsCoreChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty InternalPudlakTheorem5NoSmallCodeSemanticsCore.{q} ∧
      Nonempty InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q} ∧
        Nonempty InternalPudlakTheorem5ProofCodeSemanticsCore.{q} ∧
          Nonempty InternalPudlakTheorem5CheckedLowerBoundCore ∧
            Nonempty InternalPudlakTheorem5LowerBoundCore ∧
              Nonempty IntrinsicPudlakTheorem5PowerBoundMachine ∧
                Nonempty InternalPudlakTheorem5PowerBoundMachine ∧
                  Nonempty InternalPudlakTheorem5Machine ∧
                    Nonempty _root_.PudlakFiniteConsistencyLowerBoundPackage ∧
                      (∀ f : Nat → Real, _root_.is_polynomial_bound f →
                        ∃ᶠ n in atTop,
                          (h.theorem5_no_small_code_core.proof_code_semantics
                            |>.minProofCodeSize
                              (h.theorem5_no_small_code_core.scale_data.powerBoundRawCode n)
                              ⟨n, rfl⟩ : Real) > f n) ∧
                        (∀ code : _root_.FormulaCode,
                          ∀ hcode :
                            InternalPudlakTheorem5PowerBoundRelevantCode
                              h.theorem5_no_small_code_core.scale_data code,
                            _root_.proof_length _root_.ProofSystem.PA
                              _root_.ProofLengthMeasure.symbolSize code =
                              (h.theorem5_no_small_code_core.proof_code_semantics
                                |>.minProofCodeSize code hcode : Real)) ∧
                          (h.toProjectChecklist project_upper).not_rational =
                            GenericRationalCollisionInputs.not_rational
                              (h.toProjectChecklist project_upper).toGenericCollisionInputs :=
  ⟨⟨h.theorem5_no_small_code_core⟩,
    ⟨h.theorem5_no_small_code_core.toProofLengthCodeSemanticsCore⟩,
    ⟨h.theorem5_no_small_code_core.toProofCodeSemanticsCore⟩,
    ⟨h.theorem5_no_small_code_core
      |>.toProofLengthCodeSemanticsCore
      |>.toCheckedLowerBoundCore⟩,
    ⟨h.theorem5_no_small_code_core.toLowerBoundCore⟩,
    ⟨h.toProofLengthCodeSemanticsCoreChecklist
      |>.toProofCodeSemanticsCoreChecklist
      |>.toCheckedLowerBoundCoreChecklist
      |>.toLowerBoundCoreChecklist
      |>.toIntrinsicChecklist
      |>.theorem5_machine⟩,
    ⟨h.toProofLengthCodeSemanticsCoreChecklist
      |>.toProofCodeSemanticsCoreChecklist
      |>.toCheckedLowerBoundCoreChecklist
      |>.toLowerBoundCoreChecklist
      |>.toIntrinsicChecklist
      |>.theorem5_machine
      |>.toPowerBoundMachine⟩,
    ⟨h.toProofLengthCodeSemanticsCoreChecklist
      |>.toProofCodeSemanticsCoreChecklist
      |>.toCheckedLowerBoundCoreChecklist
      |>.toLowerBoundCoreChecklist
      |>.toIntrinsicChecklist
      |>.theorem5_machine
      |>.toRescaledMachine⟩,
    ⟨h.toProofLengthCodeSemanticsCoreChecklist
      |>.toProofCodeSemanticsCoreChecklist
      |>.toCheckedLowerBoundCoreChecklist
      |>.toLowerBoundCoreChecklist
      |>.toIntrinsicChecklist
      |>.toRefinedChecklist
      |>.lowerPackage⟩,
    h.no_small_codes_to_minProofCodeSize_lower_bound,
    h.calibration_proof_length_eq_minProofCodeSize,
    h.project_not_rational_eq_generic_core project_upper⟩

theorem month9_month10_finite_search_no_small_code_closure
    (h : Month9Month10FiniteSearchNoSmallCodeChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty InternalPudlakTheorem5FiniteSearchNoSmallCore.{q} ∧
      Nonempty InternalPudlakTheorem5NoSmallCodeSemanticsCore.{q} ∧
        Nonempty InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q} ∧
          Nonempty InternalPudlakTheorem5ProofCodeSemanticsCore.{q} ∧
            Nonempty InternalPudlakTheorem5CheckedLowerBoundCore ∧
              Nonempty InternalPudlakTheorem5LowerBoundCore ∧
                Nonempty IntrinsicPudlakTheorem5PowerBoundMachine ∧
                  Nonempty InternalPudlakTheorem5PowerBoundMachine ∧
                    Nonempty InternalPudlakTheorem5Machine ∧
                      Nonempty _root_.PudlakFiniteConsistencyLowerBoundPackage ∧
                        InternalPudlakTheorem5FiniteSearchExclusion
                          h.theorem5_finite_search_core.scale_data
                          h.theorem5_finite_search_core.proof_code_semantics
                          h.theorem5_finite_search_core.small_code_search ∧
                        (∀ f : Nat → Real, _root_.is_polynomial_bound f →
                          ∃ᶠ n in atTop,
                            (h.theorem5_finite_search_core.proof_code_semantics
                              |>.minProofCodeSize
                                (h.theorem5_finite_search_core.scale_data.powerBoundRawCode n)
                                ⟨n, rfl⟩ : Real) > f n) ∧
                          (h.toProjectChecklist project_upper).not_rational =
                            GenericRationalCollisionInputs.not_rational
                              (h.toProjectChecklist project_upper).toGenericCollisionInputs := by
  rcases month9_month10_no_small_code_semantics_core_closure
      h.toNoSmallCodeSemanticsCoreChecklist project_upper with
    ⟨h_no_small, h_proof_length, h_proof_code, h_checked, h_lower,
      h_intrinsic, h_power, h_machine, h_package, h_min, _h_calibration,
      h_generic⟩
  exact
    ⟨⟨h.theorem5_finite_search_core⟩,
      h_no_small,
      h_proof_length,
      h_proof_code,
      h_checked,
      h_lower,
      h_intrinsic,
      h_power,
      h_machine,
      h_package,
      h.finite_search_exclusion_statement,
      h_min,
      h_generic⟩

theorem month9_month10_computable_finite_search_no_small_code_closure
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} ∧
      Nonempty InternalPudlakTheorem5FiniteSearchNoSmallCore.{q} ∧
        Nonempty InternalPudlakTheorem5NoSmallCodeSemanticsCore.{q} ∧
          Nonempty InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q} ∧
            Nonempty InternalPudlakTheorem5ProofCodeSemanticsCore.{q} ∧
              Nonempty InternalPudlakTheorem5CheckedLowerBoundCore ∧
                Nonempty InternalPudlakTheorem5LowerBoundCore ∧
                  Nonempty IntrinsicPudlakTheorem5PowerBoundMachine ∧
                    Nonempty InternalPudlakTheorem5PowerBoundMachine ∧
                      Nonempty InternalPudlakTheorem5Machine ∧
                        Nonempty _root_.PudlakFiniteConsistencyLowerBoundPackage ∧
                          InternalPudlakTheorem5FiniteSearchExclusion
                            h.theorem5_computable_search_core.scale_data
                            h.theorem5_computable_search_core.proof_code_semantics
                            h.theorem5_computable_search_core.small_code_search ∧
                          (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f,
                            ∀ N : Nat,
                              Nonempty
                                (InternalPudlakTheorem5ComputedLowerSearchWitness
                                  h.theorem5_computable_search_core.scale_data
                                  h.theorem5_computable_search_core.proof_code_semantics
                                  h.theorem5_computable_search_core.small_code_search f hf N)) ∧
                          (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f,
                            ∀ N : Nat,
                              N ≤
                                (h.theorem5_computable_search_core
                                  |>.computable_search_exclusion
                                  |>.witness f hf N)) ∧
                            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                              ((h.toProjectChecklist project_upper)
                                |>.upperTailOfRationality hrat).upperN ≤
                                (h.projectLowerSearchWitnessOfRationality
                                  project_upper hrat).n) ∧
                            (∀ f : Nat → Real, _root_.is_polynomial_bound f →
                              ∃ᶠ n in atTop,
                                (h.theorem5_computable_search_core.proof_code_semantics
                                  |>.minProofCodeSize
                                    (h.theorem5_computable_search_core.scale_data.powerBoundRawCode n)
                                    ⟨n, rfl⟩ : Real) > f n) ∧
                              (h.toProjectChecklist project_upper).not_rational =
                                GenericRationalCollisionInputs.not_rational
                                  (h.toProjectChecklist project_upper).toGenericCollisionInputs := by
  rcases month9_month10_finite_search_no_small_code_closure
      h.toFiniteSearchNoSmallCodeChecklist project_upper with
    ⟨h_finite_core, h_no_small, h_proof_length, h_proof_code, h_checked,
      h_lower, h_intrinsic, h_power, h_machine, h_package, h_exclusion,
      h_min, h_generic⟩
  exact
    ⟨⟨h.theorem5_computable_search_core⟩,
      h_finite_core,
      h_no_small,
      h_proof_length,
      h_proof_code,
      h_checked,
      h_lower,
      h_intrinsic,
      h_power,
      h_machine,
        h_package,
        h_exclusion,
        h.computed_lower_search_nonempty,
        h.computable_search_witness_ge,
        h.project_lower_search_witness_ge_upperN project_upper,
        h_min,
        h_generic⟩

theorem month9_month10_project_box_aligned_computable_search_closure
    (h : Month9Month10ProjectBoxAlignedComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty
        (InternalPudlakTheorem5ProjectBoxAlignment
          h.theorem5_computable_search_core.scale_data
          h.theorem5_computable_search_core.proof_code_semantics) ∧
      Nonempty (ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox) ∧
        (∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
          (h.toComputableSearchGapCertificate.gap_for_polynomial_upper
              U hU).witness N =
            (h.computable_search_checklist.computedLowerSearchWitness U hU N).n) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n =
              (h.computable_search_checklist.projectLowerSearchWitnessOfRationality
                project_upper hrat).n) ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              (h.upperTailOfRationality project_upper hrat).upperN ≤
                (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n) ∧
              (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                (h.upperTailOfRationality project_upper hrat).U
                    (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n <
                  sondowProjectLocalPudlakCollisionBox
                    (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n) ∧
                h.search_not_rational project_upper =
                  GenericRationalCollisionInputs.not_rational
                    (h.toSearchGenericCollisionInputs project_upper) :=
  ⟨⟨h.project_box_alignment⟩,
    ⟨h.toComputableSearchGapCertificate⟩,
    h.project_box_alignment.toComputableSearchGapCertificate_witness_eq
      h.theorem5_search_exclusion,
    h.project_search_witness_eq_lower_search project_upper,
    h.project_search_witness_ge_upperN project_upper,
    h.project_search_gap_at_witness project_upper,
    h.search_not_rational_eq_generic_core project_upper⟩

theorem month9_month10_project_gap_transfer_computable_search_closure
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty
        (InternalPudlakTheorem5ComputableProjectGapTransfer
          h.theorem5_computable_search_core.scale_data
          h.theorem5_computable_search_core.proof_code_semantics
          h.theorem5_computable_search_core.small_code_search) ∧
      Nonempty (ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox) ∧
        (∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
          N ≤ (h.toComputableSearchGapCertificate
            |>.gap_for_polynomial_upper U hU).witness N) ∧
          (∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
            U ((h.toComputableSearchGapCertificate
                |>.gap_for_polynomial_upper U hU).witness N) <
              sondowProjectLocalPudlakCollisionBox
                ((h.toComputableSearchGapCertificate
                  |>.gap_for_polynomial_upper U hU).witness N)) ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              (h.upperTailOfRationality project_upper hrat).upperN ≤
                (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n) ∧
              (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                (h.upperTailOfRationality project_upper hrat).U
                    (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n <
                  sondowProjectLocalPudlakCollisionBox
                    (h.projectSearchCollisionWitnessOfRationality project_upper hrat).n) ∧
                h.search_not_rational project_upper =
                  GenericRationalCollisionInputs.not_rational
                    (h.toSearchGenericCollisionInputs project_upper) :=
  ⟨⟨h.project_gap_transfer⟩,
    ⟨h.toComputableSearchGapCertificate⟩,
    fun U hU N =>
      (h.toComputableSearchGapCertificate
        |>.gap_for_polynomial_upper U hU).witness_ge N,
    fun U hU N =>
      (h.toComputableSearchGapCertificate
        |>.gap_for_polynomial_upper U hU).strict_at_witness N,
    h.project_search_witness_ge_upperN project_upper,
    h.project_search_gap_at_witness project_upper,
    h.search_not_rational_eq_generic_core project_upper⟩

theorem month9_month10_constant_projection_computable_search_closure
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        h.theorem5_computable_search_core.scale_data.powerBoundRawCode
        _root_.sondowReflectionGraftCode)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty
        (_root_.ConstantProofLengthProjection
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          h.theorem5_computable_search_core.scale_data.powerBoundRawCode
          _root_.sondowReflectionGraftCode) ∧
      Nonempty
        (InternalPudlakTheorem5ProofLengthProjectBoxProjection
          h.theorem5_computable_search_core.scale_data
          h.theorem5_computable_search_core.proof_code_semantics) ∧
        Nonempty
          (InternalPudlakTheorem5AdditiveProjectBoxProjection
            h.theorem5_computable_search_core.scale_data
            h.theorem5_computable_search_core.proof_code_semantics) ∧
          Nonempty
            (InternalPudlakTheorem5ComputableProjectGapTransfer
              h.theorem5_computable_search_core.scale_data
              h.theorem5_computable_search_core.proof_code_semantics
              h.theorem5_computable_search_core.small_code_search) ∧
            Nonempty
              (ComputableSearchGapCertificate
                sondowProjectLocalPudlakCollisionBox) :=
  have hclosure :=
    month9_month10_project_gap_transfer_computable_search_closure
      (h.toProjectGapTransferChecklistOfConstantProjection projection)
      project_upper
  ⟨⟨projection⟩,
    ⟨h.theorem5_computable_search_core
      |>.toProofLengthProjectBoxProjection projection⟩,
    ⟨h.theorem5_computable_search_core
      |>.toAdditiveProjectBoxProjectionOfConstantProjection projection⟩,
    hclosure.1,
    hclosure.2.1⟩

theorem month9_month10_scaled_constant_projection_computable_search_closure
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (projectIndex : Nat → Nat)
    (projectIndex_ge_source : ∀ n : Nat, n ≤ projectIndex n)
    (projectIndex_polynomial :
      _root_.is_polynomial_bound (fun n : Nat => (projectIndex n : Real)))
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        h.theorem5_computable_search_core.scale_data.powerBoundRawCode
        (fun n : Nat => _root_.sondowReflectionGraftCode (projectIndex n)))
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty
        (_root_.ConstantProofLengthProjection
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          h.theorem5_computable_search_core.scale_data.powerBoundRawCode
          (fun n : Nat => _root_.sondowReflectionGraftCode (projectIndex n))) ∧
      Nonempty
        (InternalPudlakTheorem5ScaledProofLengthProjectBoxProjection
          h.theorem5_computable_search_core.scale_data
          h.theorem5_computable_search_core.proof_code_semantics) ∧
        Nonempty
          (InternalPudlakTheorem5ScaledAdditiveProjectBoxProjection
            h.theorem5_computable_search_core.scale_data
            h.theorem5_computable_search_core.proof_code_semantics) ∧
          Nonempty
            (InternalPudlakTheorem5ComputableProjectGapTransfer
              h.theorem5_computable_search_core.scale_data
              h.theorem5_computable_search_core.proof_code_semantics
              h.theorem5_computable_search_core.small_code_search) ∧
            Nonempty
              (ComputableSearchGapCertificate
                sondowProjectLocalPudlakCollisionBox) :=
  have hclosure :=
    month9_month10_project_gap_transfer_computable_search_closure
      (h.toProjectGapTransferChecklistOfScaledConstantProjection
        projectIndex projectIndex_ge_source projectIndex_polynomial projection)
      project_upper
  ⟨⟨projection⟩,
    ⟨h.theorem5_computable_search_core
      |>.toScaledProofLengthProjectBoxProjection
        projectIndex projectIndex_ge_source projectIndex_polynomial projection⟩,
    ⟨h.theorem5_computable_search_core
      |>.toScaledAdditiveProjectBoxProjectionOfConstantProjection
        projectIndex projectIndex_ge_source projectIndex_polynomial projection⟩,
    hclosure.1,
    hclosure.2.1⟩

theorem month9_month10_scale_constant_projection_computable_search_closure
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        h.theorem5_computable_search_core.scale_data.powerBoundRawCode
        (fun n : Nat =>
          _root_.sondowReflectionGraftCode
            (h.theorem5_computable_search_core.scale_data.scale n)))
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty
        (_root_.ConstantProofLengthProjection
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          h.theorem5_computable_search_core.scale_data.powerBoundRawCode
          (fun n : Nat =>
            _root_.sondowReflectionGraftCode
              (h.theorem5_computable_search_core.scale_data.scale n))) ∧
      Nonempty
        (InternalPudlakTheorem5ScaledProofLengthProjectBoxProjection
          h.theorem5_computable_search_core.scale_data
          h.theorem5_computable_search_core.proof_code_semantics) ∧
        Nonempty
          (InternalPudlakTheorem5ScaledAdditiveProjectBoxProjection
            h.theorem5_computable_search_core.scale_data
            h.theorem5_computable_search_core.proof_code_semantics) ∧
          Nonempty
            (InternalPudlakTheorem5ComputableProjectGapTransfer
              h.theorem5_computable_search_core.scale_data
              h.theorem5_computable_search_core.proof_code_semantics
              h.theorem5_computable_search_core.small_code_search) ∧
            Nonempty
              (ComputableSearchGapCertificate
                sondowProjectLocalPudlakCollisionBox) :=
  month9_month10_scaled_constant_projection_computable_search_closure
    h
    h.theorem5_computable_search_core.scale_data.scale
    h.theorem5_computable_search_core.scale_data.scale_id_le
    h.theorem5_computable_search_core.scale_data.scale_polynomial_bound
    projection
    project_upper

theorem month9_month10_scale_projection_pieces_computable_search_closure
    (h : Month9Month10ComputableFiniteSearchNoSmallCodeChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty _root_.StrengthenedToPartialConsistencyConstantProjection ∧
      Nonempty _root_.PAConjunctionEliminationConstantCost ∧
        Nonempty
          (_root_.ConstantProofLengthProjection
            _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
            h.theorem5_computable_search_core.scale_data.powerBoundRawCode
            (fun n : Nat =>
              _root_.sondowReflectionGraftCode
                (h.theorem5_computable_search_core.scale_data.scale n))) ∧
          Nonempty
            (InternalPudlakTheorem5ScaledProofLengthProjectBoxProjection
              h.theorem5_computable_search_core.scale_data
              h.theorem5_computable_search_core.proof_code_semantics) ∧
            Nonempty
              (InternalPudlakTheorem5ScaledAdditiveProjectBoxProjection
                h.theorem5_computable_search_core.scale_data
                h.theorem5_computable_search_core.proof_code_semantics) ∧
              Nonempty
                (InternalPudlakTheorem5ComputableProjectGapTransfer
                  h.theorem5_computable_search_core.scale_data
                  h.theorem5_computable_search_core.proof_code_semantics
                  h.theorem5_computable_search_core.small_code_search) ∧
                Nonempty
                  (ComputableSearchGapCertificate
                    sondowProjectLocalPudlakCollisionBox) :=
  let projection :=
    h.theorem5_computable_search_core.scale_data
      |>.powerBoundToScaledReflectionGraftConstantProjection
        strengthened_to_partial partial_to_graft
  have hclosure :=
    month9_month10_scale_constant_projection_computable_search_closure
      h projection project_upper
  ⟨⟨strengthened_to_partial⟩,
    ⟨partial_to_graft⟩,
    hclosure.1,
    hclosure.2.1,
    hclosure.2.2.1,
    hclosure.2.2.2.1,
    hclosure.2.2.2.2⟩

theorem month9_month10_checker_extractor_computable_search_closure
    (h : Month9Month10CheckerExtractorComputableSearchChecklist.{q})
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty
        (InternalPudlakTheorem5CheckerFiniteEnumeration h.checker) ∧
      Nonempty
        (InternalPudlakTheorem5CheckerComputableRejectionExtractor
          h.checker h.enumeration) ∧
        Nonempty
          (InternalPudlakTheorem5CheckerProofLengthExactness h.checker) ∧
          Nonempty
            InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} ∧
            Nonempty
              (InternalPudlakTheorem5ComputableProjectGapTransfer
                h.scale_data h.proof_code_semantics h.small_code_search) ∧
              Nonempty
                (ComputableSearchGapCertificate
                  sondowProjectLocalPudlakCollisionBox) ∧
                (∀ f : Nat → Real,
                  ∀ hf : _root_.is_polynomial_bound f,
                    ∀ N : Nat,
                      (h.computedLowerSearchWitness f hf N).n =
                        h.extractor.witness f hf N) ∧
                  (∀ f : Nat → Real,
                    ∀ hf : _root_.is_polynomial_bound f,
                      ∀ N : Nat,
                        (h.computedLowerSearchWitness f hf N).K =
                          h.extractor.cutoff f hf N) ∧
                    ¬ _root_.is_rational _root_.euler_mascheroni :=
  let hscale :=
    month9_month10_scale_projection_pieces_computable_search_closure
      h.toComputableFiniteSearchNoSmallCodeChecklist
      strengthened_to_partial partial_to_graft project_upper
  ⟨⟨h.enumeration⟩,
    ⟨h.extractor⟩,
    ⟨h.exactness⟩,
    ⟨h.theorem5_computable_search_core⟩,
    hscale.2.2.2.2.2.1,
    hscale.2.2.2.2.2.2,
    h.computedLowerSearchWitness_n_eq_extractor,
    h.computedLowerSearchWitness_K_eq_extractor,
    h.search_not_rational_of_scale_projection_pieces
      strengthened_to_partial partial_to_graft project_upper⟩

theorem month9_month10_proof_length_code_semantics_core_closure
    (h : Month9Month10ProofLengthCodeSemanticsCoreChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q} ∧
      Nonempty InternalPudlakTheorem5ProofCodeSemanticsCore.{q} ∧
        Nonempty InternalPudlakTheorem5CheckedLowerBoundCore ∧
          Nonempty InternalPudlakTheorem5LowerBoundCore ∧
            Nonempty IntrinsicPudlakTheorem5PowerBoundMachine ∧
              Nonempty InternalPudlakTheorem5PowerBoundMachine ∧
                Nonempty InternalPudlakTheorem5Machine ∧
                  Nonempty _root_.PudlakFiniteConsistencyLowerBoundPackage ∧
                    (∀ n : Nat,
                      h.theorem5_proof_length_code_core.toProofCodeSemanticsCore.checkedLength n =
                        h.theorem5_proof_length_code_core.proof_code_semantics.minProofCodeSize
                          (h.theorem5_proof_length_code_core.scale_data.powerBoundRawCode n)
                          ⟨n, rfl⟩) ∧
                      (∀ n : Nat,
                        _root_.proof_length _root_.ProofSystem.PA
                          _root_.ProofLengthMeasure.symbolSize
                          (h.theorem5_proof_length_code_core.scale_data.powerBoundRawCode n) =
                          (h.theorem5_proof_length_code_core
                            |>.toProofCodeSemanticsCore
                            |>.checkedLength n : Real)) ∧
                        (h.toProjectChecklist project_upper).not_rational =
                          GenericRationalCollisionInputs.not_rational
                            (h.toProjectChecklist project_upper).toGenericCollisionInputs :=
  ⟨⟨h.theorem5_proof_length_code_core⟩,
    ⟨h.theorem5_proof_length_code_core.toProofCodeSemanticsCore⟩,
    ⟨h.theorem5_proof_length_code_core.toCheckedLowerBoundCore⟩,
    ⟨h.theorem5_proof_length_code_core.toLowerBoundCore⟩,
    ⟨h.toProofCodeSemanticsCoreChecklist
      |>.toCheckedLowerBoundCoreChecklist
      |>.toLowerBoundCoreChecklist
      |>.toIntrinsicChecklist
      |>.theorem5_machine⟩,
    ⟨h.toProofCodeSemanticsCoreChecklist
      |>.toCheckedLowerBoundCoreChecklist
      |>.toLowerBoundCoreChecklist
      |>.toIntrinsicChecklist
      |>.theorem5_machine
      |>.toPowerBoundMachine⟩,
    ⟨h.toProofCodeSemanticsCoreChecklist
      |>.toCheckedLowerBoundCoreChecklist
      |>.toLowerBoundCoreChecklist
      |>.toIntrinsicChecklist
      |>.theorem5_machine
      |>.toRescaledMachine⟩,
    ⟨h.toProofCodeSemanticsCoreChecklist
      |>.toCheckedLowerBoundCoreChecklist
      |>.toLowerBoundCoreChecklist
      |>.toIntrinsicChecklist
      |>.toRefinedChecklist
      |>.lowerPackage⟩,
    h.theorem5_proof_length_code_core.toProofCodeSemanticsCore_checkedLength_eq_minProofCodeSize,
    h.proof_length_exact_at_powerBoundRawCode,
    h.project_not_rational_eq_generic_core project_upper⟩

theorem month9_month10_proof_code_semantics_core_closure
    (h : Month9Month10ProofCodeSemanticsCoreChecklist.{q})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty InternalPudlakTheorem5ProofCodeSemanticsCore.{q} ∧
      Nonempty InternalPudlakTheorem5CheckedLowerBoundCore ∧
        Nonempty InternalPudlakTheorem5LowerBoundCore ∧
          Nonempty IntrinsicPudlakTheorem5PowerBoundMachine ∧
            Nonempty InternalPudlakTheorem5PowerBoundMachine ∧
              Nonempty InternalPudlakTheorem5Machine ∧
                Nonempty _root_.PudlakFiniteConsistencyLowerBoundPackage ∧
                  (∀ n : Nat,
                    h.toCheckedLowerBoundCoreChecklist.theorem5_checked_core.checkedLength n =
                      h.theorem5_proof_code_core.proof_code_semantics.minProofCodeSize
                        (h.theorem5_proof_code_core.scale_data.powerBoundRawCode n)
                        ⟨n, rfl⟩) ∧
                    (∀ n : Nat,
                      _root_.proof_length _root_.ProofSystem.PA
                        _root_.ProofLengthMeasure.symbolSize
                        (h.theorem5_proof_code_core.scale_data.powerBoundRawCode n) =
                        (h.theorem5_proof_code_core.checkedLength n : Real)) ∧
                      (h.toProjectChecklist project_upper).not_rational =
                        GenericRationalCollisionInputs.not_rational
                          (h.toProjectChecklist project_upper).toGenericCollisionInputs :=
  ⟨⟨h.theorem5_proof_code_core⟩,
    ⟨h.theorem5_proof_code_core.toCheckedLowerBoundCore⟩,
    ⟨h.theorem5_proof_code_core.toLowerBoundCore⟩,
    ⟨h.toCheckedLowerBoundCoreChecklist.toLowerBoundCoreChecklist
      |>.toIntrinsicChecklist
      |>.theorem5_machine⟩,
    ⟨h.toCheckedLowerBoundCoreChecklist.toLowerBoundCoreChecklist
      |>.toIntrinsicChecklist
      |>.theorem5_machine
      |>.toPowerBoundMachine⟩,
    ⟨h.toCheckedLowerBoundCoreChecklist.toLowerBoundCoreChecklist
      |>.toIntrinsicChecklist
      |>.theorem5_machine
      |>.toRescaledMachine⟩,
    ⟨h.toCheckedLowerBoundCoreChecklist.toLowerBoundCoreChecklist
      |>.toIntrinsicChecklist
      |>.toRefinedChecklist
      |>.lowerPackage⟩,
    h.checkedLength_eq_minProofCodeSize,
    h.proof_length_exact_at_powerBoundRawCode,
    h.project_not_rational_eq_generic_core project_upper⟩

theorem month9_month10_checked_lower_bound_core_closure
    (h : Month9Month10CheckedLowerBoundCoreChecklist)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty InternalPudlakTheorem5CheckedLowerBoundCore ∧
      Nonempty InternalPudlakTheorem5LowerBoundCore ∧
        Nonempty IntrinsicPudlakTheorem5PowerBoundMachine ∧
          Nonempty InternalPudlakTheorem5PowerBoundMachine ∧
            Nonempty InternalPudlakTheorem5Machine ∧
              Nonempty _root_.PudlakFiniteConsistencyLowerBoundPackage ∧
                (∀ n : Nat,
                  _root_.proof_length _root_.ProofSystem.PA
                    _root_.ProofLengthMeasure.symbolSize
                    (h.theorem5_checked_core.scale_data.powerBoundRawCode n) =
                    (h.theorem5_checked_core.checkedLength n : Real)) ∧
                  (∀ n : Nat,
                    (h.toLowerBoundCoreChecklist.toIntrinsicChecklist
                        |>.theorem5_machine
                        |>.toRescaledMachine
                        |>.toNormalForm).code n =
                      _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
                        h.theorem5_checked_core.scale_data.scale n) ∧
                    (h.toProjectChecklist project_upper).not_rational =
                      GenericRationalCollisionInputs.not_rational
                        (h.toProjectChecklist project_upper).toGenericCollisionInputs :=
  ⟨⟨h.theorem5_checked_core⟩,
    ⟨h.theorem5_checked_core.toLowerBoundCore⟩,
    ⟨h.toLowerBoundCoreChecklist.toIntrinsicChecklist.theorem5_machine⟩,
    ⟨h.toLowerBoundCoreChecklist.toIntrinsicChecklist.theorem5_machine.toPowerBoundMachine⟩,
    ⟨h.toLowerBoundCoreChecklist.toIntrinsicChecklist.theorem5_machine.toRescaledMachine⟩,
    ⟨h.toLowerBoundCoreChecklist.toIntrinsicChecklist.toRefinedChecklist.lowerPackage⟩,
    h.checked_exactness,
    h.core_normalForm_code_eq_rescaledPudlak,
    h.project_not_rational_eq_generic_core project_upper⟩

end SondowProjectMonth9Month10InternalPudlakWitnessSurface
end SondowMainCheckedCodeBridge

end
