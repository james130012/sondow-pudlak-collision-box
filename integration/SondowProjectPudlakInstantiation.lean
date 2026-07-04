/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakCollision
import EulerLimit.ExternalPudlakRawEncoding
import EulerLimit.ProjectionBridge

/-!
# Project-local Pudlak input instantiation

This module narrows the remaining external proof-complexity inputs for the
project-local collision bridge.

It does not assert the literature Pudlak lower-bound theorem or PA projection
soundness for free.  Instead, it records the exact conversion steps from:

* a literature Theorem 5 lower-bound certificate,
* a strengthened-to-partial-consistency transfer, and
* a conjunction-elimination transfer from partial consistency to the graft,

to the `PudlakFiniteConsistencyLowerBoundPackage` and final collision endpoint.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge

universe u v w

/-- A local normal-form instance of the project Pudlak lower-bound package.
The input is already a strong lower bound on the unscaled partial-consistency
family, so the package uses the identity scale. -/
def pudlakFiniteConsistencyLowerBoundPackageOfPartialNormalForm
    (hnormal : _root_.PartialConsistencyLowerBoundNormalForm) :
    _root_.PudlakFiniteConsistencyLowerBoundPackage where
  scale := id
  scale_properties := _root_.PolynomialCofinalScale.id
  rescaled_strong_lower_bound :=
    hnormal.toStrongPartialConsistencyLowerBound

/-- Literature Theorem 5 lower-bound certificate, after the explicit
strengthened-to-partial transfer, as the exact lower-bound package used by the
project-local collision theorem. -/
def _root_.LiteraturePudlakTheorem5LowerBoundCertificate.toPudlakFiniteConsistencyLowerBoundPackage
    (hsource : _root_.LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    _root_.PudlakFiniteConsistencyLowerBoundPackage :=
  pudlakFiniteConsistencyLowerBoundPackageOfPartialNormalForm
    (hsource.toNormalForm hpartial)

set_option linter.style.longLine false in
theorem _root_.LiteraturePudlakTheorem5LowerBoundCertificate.toPudlakFiniteConsistencyLowerBoundPackage_scale_eq
    (hsource : _root_.LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    (hsource.toPudlakFiniteConsistencyLowerBoundPackage hpartial).scale = id := by
  rfl

set_option linter.style.longLine false in
theorem _root_.LiteraturePudlakTheorem5LowerBoundCertificate.toPudlakFiniteConsistencyLowerBoundPackage_rescaledCode_eq
    (hsource : _root_.LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (n : ℕ) :
    _root_.rescaledPartialConsistencyCode
        (hsource.toPudlakFiniteConsistencyLowerBoundPackage hpartial).scale n =
      _root_.partialConsistencyCode n := by
  rfl

/-- Conjunction-elimination transfer packaged exactly as the lower-bound
movement required by the reflection-graft collision. -/
def _root_.ConjunctionEliminationTransferPackage.toPartialConsistencyToReflectionGraftTransfer
    (hprojection : _root_.ConjunctionEliminationTransferPackage) :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer :=
  _root_.partial_consistency_transfer_of_right_conjunction_elimination
    hprojection

/-- Hilbert right-conjunction elimination is a concrete sufficient condition
for the partial-consistency-to-graft lower-bound transfer. -/
def _root_.HilbertRightConjunctionEliminationPackage.toPartialConsistencyToReflectionGraftTransfer
    (hprojection : _root_.HilbertRightConjunctionEliminationPackage) :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer :=
  _root_.partial_consistency_transfer_of_right_conjunction_elimination
    (_root_.conjunction_elimination_transfer_package_of_hilbert
      hprojection)

/-- The two-step Hilbert overhead is the narrowest numeric projection witness
used by the graft route. -/
theorem partialConsistencyToReflectionGraftTransfer_of_hilbertTwoStep
    (htwo : _root_.HilbertRightConjunctionTwoStepOverhead) :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer :=
  _root_.partial_consistency_to_reflection_graft_transfer_of_hilbert_two_step
    htwo

/-- Project-local expansion of the remaining literature Theorem 5 input.

This is definitionally equivalent to
`LiteraturePudlakTheorem5LowerBoundCertificate`, but the fields expose the two
auditable parts separately: scale data and the actual power-bound lower-bound
theorem. -/
structure SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs where
  scale_data : _root_.LiteraturePudlakTheorem5ScaleData
  theorem5_power_bound_lower_bound :
    _root_.LiteraturePudlakTheorem5PowerBoundLowerBound scale_data

namespace SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs

def toCertificate
    (h : SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs) :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate where
  scale_data := h.scale_data
  power_bound_lower_bound := h.theorem5_power_bound_lower_bound

def ofCertificate
    (h : _root_.LiteraturePudlakTheorem5LowerBoundCertificate) :
    SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs where
  scale_data := h.scale_data
  theorem5_power_bound_lower_bound := h.power_bound_lower_bound

theorem toCertificate_ofCertificate
    (h : _root_.LiteraturePudlakTheorem5LowerBoundCertificate) :
    (ofCertificate h).toCertificate = h := by
  cases h
  rfl

theorem ofCertificate_toCertificate
    (h : SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs) :
    ofCertificate h.toCertificate = h := by
  cases h
  rfl

def lowerBoundPackage
    (h : SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    _root_.PudlakFiniteConsistencyLowerBoundPackage :=
  h.toCertificate.toPudlakFiniteConsistencyLowerBoundPackage hpartial

theorem lowerBoundPackage_scale_eq_id
    (h : SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    (h.lowerBoundPackage hpartial).scale = id := by
  rfl

theorem lowerBoundPackage_rescaledCode_eq_partialConsistencyCode
    (h : SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (n : ℕ) :
    _root_.rescaledPartialConsistencyCode
        (h.lowerBoundPackage hpartial).scale n =
      _root_.partialConsistencyCode n := by
  rfl

theorem normalForm_code_eq_powerBoundRawCode
    (h : SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    (h.toCertificate.toNormalForm hpartial).code =
      h.scale_data.powerBoundRawCode := by
  exact h.toCertificate.normalForm_code_eq_powerBoundRawCode hpartial

theorem normalForm_code_eq_rescaledPudlak
    (h : SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (n : ℕ) :
    (h.toCertificate.toNormalForm hpartial).code n =
      _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
        h.scale_data.scale n :=
  h.toCertificate.normalForm_code_eq_rescaledPudlak hpartial n

end SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs

/-- Equivalent lower-bound input for the literature Pudlak theorem stated on
the rescaled raw-code family.  This is often closer to the theorem as cited in
proof-complexity form; `scale_eq` then transports it to the power-bound raw
family used by the project normal form. -/
structure SondowProjectLocalPudlakTheorem5RescaledLowerBoundInputs where
  scale_data : _root_.LiteraturePudlakTheorem5ScaleData
  theorem5_rescaled_lower_bound :
    _root_.StrongRescaledExternalStrengthenedLowerBound
      scale_data.rawCode scale_data.scale

namespace SondowProjectLocalPudlakTheorem5RescaledLowerBoundInputs

def externalLiterature :
    SondowProjectLocalPudlakTheorem5RescaledLowerBoundInputs where
  scale_data := _root_.literaturePudlakTheorem5ExternalScaleData
  theorem5_rescaled_lower_bound :=
    _root_.literaturePudlakTheorem5ExternalRescaledLowerBound

def toRescaledCertificate
    (h : SondowProjectLocalPudlakTheorem5RescaledLowerBoundInputs) :
    _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate where
  scale_data := h.scale_data
  rescaled_lower_bound := h.theorem5_rescaled_lower_bound

theorem externalLiterature_toRescaledCertificate :
    externalLiterature.toRescaledCertificate =
      _root_.literaturePudlakTheorem5ExternalRescaledLowerBoundCertificate := by
  rfl

def toAuditedLowerBoundInputs
    (h : SondowProjectLocalPudlakTheorem5RescaledLowerBoundInputs) :
    SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs where
  scale_data := h.toRescaledCertificate.toPowerBoundCertificate.scale_data
  theorem5_power_bound_lower_bound :=
    h.toRescaledCertificate.toPowerBoundCertificate.power_bound_lower_bound

def toCertificate
    (h : SondowProjectLocalPudlakTheorem5RescaledLowerBoundInputs) :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate :=
  h.toRescaledCertificate.toPowerBoundCertificate

def lowerBoundPackage
    (h : SondowProjectLocalPudlakTheorem5RescaledLowerBoundInputs)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    _root_.PudlakFiniteConsistencyLowerBoundPackage :=
  h.toAuditedLowerBoundInputs.lowerBoundPackage hpartial

theorem lowerBoundPackage_scale_eq_id
    (h : SondowProjectLocalPudlakTheorem5RescaledLowerBoundInputs)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    (h.lowerBoundPackage hpartial).scale = id := by
  rfl

theorem lowerBoundPackage_rescaledCode_eq_partialConsistencyCode
    (h : SondowProjectLocalPudlakTheorem5RescaledLowerBoundInputs)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (n : ℕ) :
    _root_.rescaledPartialConsistencyCode
        (h.lowerBoundPackage hpartial).scale n =
      _root_.partialConsistencyCode n := by
  rfl

theorem normalForm_code_eq_powerBoundRawCode
    (h : SondowProjectLocalPudlakTheorem5RescaledLowerBoundInputs)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    (h.toCertificate.toNormalForm hpartial).code =
      h.scale_data.powerBoundRawCode := by
  exact h.toCertificate.normalForm_code_eq_powerBoundRawCode hpartial

theorem normalForm_code_eq_rescaledPudlak
    (h : SondowProjectLocalPudlakTheorem5RescaledLowerBoundInputs)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (n : ℕ) :
    (h.toCertificate.toNormalForm hpartial).code n =
      _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
        h.scale_data.scale n :=
  h.toCertificate.normalForm_code_eq_rescaledPudlak hpartial n

end SondowProjectLocalPudlakTheorem5RescaledLowerBoundInputs

namespace SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs

def toRescaledLowerBoundInputs
    (h : SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs) :
    SondowProjectLocalPudlakTheorem5RescaledLowerBoundInputs where
  scale_data := h.scale_data
  theorem5_rescaled_lower_bound :=
    h.scale_data.powerBoundLowerBound_to_rescaledLowerBound
      h.theorem5_power_bound_lower_bound

end SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs

theorem theorem5AuditedLowerBoundInputs_nonempty_iff_rescaledLowerBoundInputs :
    Nonempty SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs ↔
      Nonempty SondowProjectLocalPudlakTheorem5RescaledLowerBoundInputs := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.toRescaledLowerBoundInputs⟩
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.toAuditedLowerBoundInputs⟩

/-- A single audited package for the remaining Pudlak-side inputs. -/
structure SondowProjectLocalPudlakSideInputs where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  partial_to_graft :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer

namespace SondowProjectLocalPudlakSideInputs

def lowerBoundPackage
    (h : SondowProjectLocalPudlakSideInputs) :
    _root_.PudlakFiniteConsistencyLowerBoundPackage :=
  h.literature_lower_bound.toPudlakFiniteConsistencyLowerBoundPackage
    h.strengthened_to_partial

theorem lowerBoundPackage_scale_eq_id
    (h : SondowProjectLocalPudlakSideInputs) :
    h.lowerBoundPackage.scale = id := by
  rfl

theorem lowerBoundPackage_rescaledCode_eq_partialConsistencyCode
    (h : SondowProjectLocalPudlakSideInputs) (n : ℕ) :
    _root_.rescaledPartialConsistencyCode h.lowerBoundPackage.scale n =
      _root_.partialConsistencyCode n := by
  rfl

theorem lowerBoundPackage_normalForm_code_eq_powerBoundRawCode
    (h : SondowProjectLocalPudlakSideInputs) :
    (h.literature_lower_bound.toNormalForm
        h.strengthened_to_partial).code =
      h.literature_lower_bound.scale_data.powerBoundRawCode := by
  exact h.literature_lower_bound.normalForm_code_eq_powerBoundRawCode
    h.strengthened_to_partial

theorem lowerBoundPackage_normalForm_code_eq_rescaledPudlak
    (h : SondowProjectLocalPudlakSideInputs) (n : ℕ) :
    (h.literature_lower_bound.toNormalForm
        h.strengthened_to_partial).code n =
      _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
        h.literature_lower_bound.scale_data.scale n :=
  h.literature_lower_bound.normalForm_code_eq_rescaledPudlak
    h.strengthened_to_partial n

def toCollisionInputs
    (h : SondowProjectLocalPudlakSideInputs)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    SondowProjectLocalPudlakCollisionInputs where
  project_upper := hupper
  pudlak_lower_bound := h.lowerBoundPackage
  transfer_to_graft := h.partial_to_graft

theorem collide
    (h : SondowProjectLocalPudlakSideInputs)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  (h.toCollisionInputs hupper).not_rational

end SondowProjectLocalPudlakSideInputs

/-- The corresponding package when the partial-to-graft transfer is supplied by
the concrete conjunction-elimination package. -/
structure SondowProjectLocalPudlakConjunctionInputs where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  conjunction_elimination :
    _root_.ConjunctionEliminationTransferPackage

namespace SondowProjectLocalPudlakConjunctionInputs

def toPudlakSideInputs
    (h : SondowProjectLocalPudlakConjunctionInputs) :
    SondowProjectLocalPudlakSideInputs where
  literature_lower_bound := h.literature_lower_bound
  strengthened_to_partial := h.strengthened_to_partial
  partial_to_graft :=
    h.conjunction_elimination.toPartialConsistencyToReflectionGraftTransfer

theorem collide
    (h : SondowProjectLocalPudlakConjunctionInputs)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakConjunctionInputs

/-- The Pudlak-side package with the `C -> B` extraction cost reduced to the
concrete Hilbert two-step inequality
`proofLength(B n) <= proofLength(C n) + 2`. -/
structure SondowProjectLocalPudlakHilbertTwoStepInputs where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  hilbert_two_step :
    _root_.HilbertRightConjunctionTwoStepOverhead

namespace SondowProjectLocalPudlakHilbertTwoStepInputs

def toConjunctionInputs
    (h : SondowProjectLocalPudlakHilbertTwoStepInputs) :
    SondowProjectLocalPudlakConjunctionInputs where
  literature_lower_bound := h.literature_lower_bound
  strengthened_to_partial := h.strengthened_to_partial
  conjunction_elimination :=
    _root_.conjunction_elimination_transfer_package_of_hilbert_two_step
      h.hilbert_two_step

def toPudlakSideInputs
    (h : SondowProjectLocalPudlakHilbertTwoStepInputs) :
    SondowProjectLocalPudlakSideInputs :=
  h.toConjunctionInputs.toPudlakSideInputs

theorem collide
    (h : SondowProjectLocalPudlakHilbertTwoStepInputs)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakHilbertTwoStepInputs

/-- Same frontier as `SondowProjectLocalPudlakHilbertTwoStepInputs`, but with a
proof-length realization object instead of the bare two-step inequality.  This
is useful when the proof-code implementation certifies the fixed graft syntax
and the right-conjunction elimination step together. -/
structure SondowProjectLocalPudlakHilbertRealizationInputs where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  hilbert_realization :
    _root_.HilbertTwoStepProofLengthRealization

namespace SondowProjectLocalPudlakHilbertRealizationInputs

def toHilbertTwoStepInputs
    (h : SondowProjectLocalPudlakHilbertRealizationInputs) :
    SondowProjectLocalPudlakHilbertTwoStepInputs where
  literature_lower_bound := h.literature_lower_bound
  strengthened_to_partial := h.strengthened_to_partial
  hilbert_two_step := h.hilbert_realization.toTwoStepOverhead

def toConjunctionInputs
    (h : SondowProjectLocalPudlakHilbertRealizationInputs) :
    SondowProjectLocalPudlakConjunctionInputs where
  literature_lower_bound := h.literature_lower_bound
  strengthened_to_partial := h.strengthened_to_partial
  conjunction_elimination :=
    _root_.conjunction_elimination_transfer_package_of_hilbert_realization
      h.hilbert_realization

def toPudlakSideInputs
    (h : SondowProjectLocalPudlakHilbertRealizationInputs) :
    SondowProjectLocalPudlakSideInputs :=
  h.toConjunctionInputs.toPudlakSideInputs

theorem collide
    (h : SondowProjectLocalPudlakHilbertRealizationInputs)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakHilbertRealizationInputs

/-- Formula-code realization front door for the `C -> B` extraction step.

Compared with `SondowProjectLocalPudlakHilbertRealizationInputs`, this keeps the
actual MiniHilbert proof-code object in the project input package.  The object
realizes the right-conjunction projection by the concrete `rightConjElim`
transformer and then exposes the same lower-bound transfer used by the Pudlak
collision route. -/
structure SondowProjectLocalPudlakHilbertFormulaCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  hilbert_formula_code :
    _root_.MiniHilbert.HilbertRightConjElimFormulaCodeRealization
      Ax A B halign

abbrev SondowProjectLocalPudlakDefaultHilbertFormulaCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  SondowProjectLocalPudlakHilbertFormulaCodeInputs
    Ax A B _root_.hilbert_projection_code_alignment_true

namespace SondowProjectLocalPudlakHilbertFormulaCodeInputs

def toHilbertTwoStepInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakHilbertFormulaCodeInputs Ax A B halign) :
    SondowProjectLocalPudlakHilbertTwoStepInputs where
  literature_lower_bound := h.literature_lower_bound
  strengthened_to_partial := h.strengthened_to_partial
  hilbert_two_step := h.hilbert_formula_code.toTwoStepOverhead

def toHilbertRealizationInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakHilbertFormulaCodeInputs Ax A B halign) :
    SondowProjectLocalPudlakHilbertRealizationInputs where
  literature_lower_bound := h.literature_lower_bound
  strengthened_to_partial := h.strengthened_to_partial
  hilbert_realization := h.hilbert_formula_code.toBridge.toTwoStepRealization

def toConjunctionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakHilbertFormulaCodeInputs Ax A B halign) :
    SondowProjectLocalPudlakConjunctionInputs where
  literature_lower_bound := h.literature_lower_bound
  strengthened_to_partial := h.strengthened_to_partial
  conjunction_elimination := h.hilbert_formula_code.toConjunctionTransferPackage

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakHilbertFormulaCodeInputs Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toConjunctionInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakHilbertFormulaCodeInputs Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakHilbertFormulaCodeInputs

/-- A still more explicit front door: the formula-code realization is built from
the local MiniHilbert interpretation plus the proof-length calibration that
identifies project-level `proof_length` with the concrete MiniHilbert
min-length model on the two relevant formula families. -/
structure SondowProjectLocalPudlakHilbertInterpretationInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_calibration :
    _root_.MiniHilbert.FormulaCodeProofLengthCalibration
      formula_code_interpretation

abbrev SondowProjectLocalPudlakDefaultHilbertInterpretationInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  SondowProjectLocalPudlakHilbertInterpretationInputs
    Ax A B _root_.hilbert_projection_code_alignment_true

namespace SondowProjectLocalPudlakHilbertInterpretationInputs

def toFormulaCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakHilbertInterpretationInputs Ax A B halign) :
    SondowProjectLocalPudlakHilbertFormulaCodeInputs Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  strengthened_to_partial := h.strengthened_to_partial
  hilbert_formula_code :=
    h.formula_code_interpretation.toFormulaCodeRealization
      h.proof_length_calibration

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakHilbertInterpretationInputs Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toFormulaCodeInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakHilbertInterpretationInputs Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakHilbertInterpretationInputs

/-- Standard-semantics variant.  This replaces the one-sided source upper bound
by exact MiniHilbert min-length semantics for both the graft code and the
partial-consistency code, then derives the calibration used above. -/
structure SondowProjectLocalPudlakHilbertStandardSemanticsInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_semantics :
    _root_.MiniHilbert.StandardFormulaCodeProofLengthSemantics
      formula_code_interpretation

abbrev SondowProjectLocalPudlakDefaultHilbertStandardSemanticsInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  SondowProjectLocalPudlakHilbertStandardSemanticsInputs
    Ax A B _root_.hilbert_projection_code_alignment_true

namespace SondowProjectLocalPudlakHilbertStandardSemanticsInputs

def toInterpretationInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakHilbertStandardSemanticsInputs
      Ax A B halign) :
    SondowProjectLocalPudlakHilbertInterpretationInputs Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  strengthened_to_partial := h.strengthened_to_partial
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_calibration := h.proof_length_semantics.toCalibration

def toFormulaCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakHilbertStandardSemanticsInputs
      Ax A B halign) :
    SondowProjectLocalPudlakHilbertFormulaCodeInputs Ax A B halign :=
  h.toInterpretationInputs.toFormulaCodeInputs

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakHilbertStandardSemanticsInputs
      Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toFormulaCodeInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakHilbertStandardSemanticsInputs
      Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakHilbertStandardSemanticsInputs

/-- Project-facing source of the strengthened-to-partial accepted-projection
package.  This is the narrow input an auditor should inspect before accepting
the transfer from the strengthened Pudlak payload to the ordinary partial
consistency payload.

This is now the legacy compatibility front door: it still takes the broad
`PAProofLengthProjectionPrinciple`.  The calibration-first front door below
replaces it on the recommended route. -/
structure SondowProjectLocalStrengthenedPayloadProjectionInputs where
  proof_length_projection_principle :
    _root_.PAProofLengthProjectionPrinciple
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth

namespace SondowProjectLocalStrengthenedPayloadProjectionInputs

def strengthenedAcceptedTruth
    (h : SondowProjectLocalStrengthenedPayloadProjectionInputs) :
    _root_.StrengthenedPartialConsistencyAcceptedTruth :=
  h.strengthened_payload_truth.toAcceptedTruth

def partialToStrengthenedAcceptedProjection
    (h : SondowProjectLocalStrengthenedPayloadProjectionInputs) :
    _root_.PartialToStrengthenedAcceptedProjection :=
  _root_.PartialToStrengthenedAcceptedProjection.ofStrengthenedPayloadTruth
    h.strengthened_payload_truth

def acceptedProjectionPackage
    (h : SondowProjectLocalStrengthenedPayloadProjectionInputs) :
    _root_.StrengthenedToPartialAcceptedProjectionPackage :=
  _root_.StrengthenedToPartialAcceptedProjectionPackage.ofStrengthenedPayloadTruth
    h.proof_length_projection_principle h.strengthened_payload_truth

def strengthenedToPartialProjection
    (h : SondowProjectLocalStrengthenedPayloadProjectionInputs) :
    _root_.StrengthenedToPartialConsistencyProjection :=
  h.acceptedProjectionPackage.toProjection

def strengthenedToPartialTransfer
    (h : SondowProjectLocalStrengthenedPayloadProjectionInputs) :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer :=
  h.acceptedProjectionPackage.toTransfer

end SondowProjectLocalStrengthenedPayloadProjectionInputs

/-- Calibration-first source of the strengthened-to-partial accepted projection.
The accepted projection is derived from strengthened payload truth; the separate
proof-system calibration supplies the proof-length projection for exactly that
accepted projection. -/
structure SondowProjectLocalStrengthenedPayloadCalibrationInputs where
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  proof_system_calibration :
    _root_.PartialToStrengthenedAcceptedProofSystemCalibration
      (_root_.PartialToStrengthenedAcceptedProjection.ofStrengthenedPayloadTruth
        strengthened_payload_truth)

namespace SondowProjectLocalStrengthenedPayloadCalibrationInputs

def strengthenedAcceptedTruth
    (h : SondowProjectLocalStrengthenedPayloadCalibrationInputs) :
    _root_.StrengthenedPartialConsistencyAcceptedTruth :=
  h.strengthened_payload_truth.toAcceptedTruth

def partialToStrengthenedAcceptedProjection
    (h : SondowProjectLocalStrengthenedPayloadCalibrationInputs) :
    _root_.PartialToStrengthenedAcceptedProjection :=
  _root_.PartialToStrengthenedAcceptedProjection.ofStrengthenedPayloadTruth
    h.strengthened_payload_truth

def acceptedProjectionCalibration
    (h : SondowProjectLocalStrengthenedPayloadCalibrationInputs) :
    _root_.StrengthenedToPartialAcceptedProjectionCalibration where
  accepted_projection := h.partialToStrengthenedAcceptedProjection
  proof_system_calibration := h.proof_system_calibration

def strengthenedToPartialProjection
    (h : SondowProjectLocalStrengthenedPayloadCalibrationInputs) :
    _root_.StrengthenedToPartialConsistencyProjection :=
  h.acceptedProjectionCalibration.toProjection

def strengthenedToPartialTransfer
    (h : SondowProjectLocalStrengthenedPayloadCalibrationInputs) :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer :=
  h.acceptedProjectionCalibration.toTransfer

end SondowProjectLocalStrengthenedPayloadCalibrationInputs

/-- Code-semantics source for the strengthened-to-partial payload calibration.

This is the narrower replacement for directly supplying
`PartialToStrengthenedAcceptedProofSystemCalibration`: the proof-system
calibration is derived from a proof-code semantics on the two relevant formula
families and its `ProofLengthCodeSemantics.Calibration`. -/
structure SondowProjectLocalStrengthenedPayloadCodeSemanticsCalibrationInputs where
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  strengthened_to_partial_code_projection :
    _root_.StrengthenedToPartialProofLengthCodeProjectionCalibration

namespace SondowProjectLocalStrengthenedPayloadCodeSemanticsCalibrationInputs

def partialToStrengthenedAcceptedProjection
    (h : SondowProjectLocalStrengthenedPayloadCodeSemanticsCalibrationInputs) :
    _root_.PartialToStrengthenedAcceptedProjection :=
  _root_.PartialToStrengthenedAcceptedProjection.ofStrengthenedPayloadTruth
    h.strengthened_payload_truth

def proofSystemCalibration
    (h : SondowProjectLocalStrengthenedPayloadCodeSemanticsCalibrationInputs) :
    _root_.PartialToStrengthenedAcceptedProofSystemCalibration
      h.partialToStrengthenedAcceptedProjection :=
  h.strengthened_to_partial_code_projection.toProofSystemCalibration
    h.partialToStrengthenedAcceptedProjection

def toPayloadCalibrationInputs
    (h : SondowProjectLocalStrengthenedPayloadCodeSemanticsCalibrationInputs) :
    SondowProjectLocalStrengthenedPayloadCalibrationInputs where
  strengthened_payload_truth := h.strengthened_payload_truth
  proof_system_calibration := h.proofSystemCalibration

def acceptedProjectionCalibration
    (h : SondowProjectLocalStrengthenedPayloadCodeSemanticsCalibrationInputs) :
    _root_.StrengthenedToPartialAcceptedProjectionCalibration :=
  h.toPayloadCalibrationInputs.acceptedProjectionCalibration

def strengthenedToPartialProjection
    (h : SondowProjectLocalStrengthenedPayloadCodeSemanticsCalibrationInputs) :
    _root_.StrengthenedToPartialConsistencyProjection :=
  h.strengthened_to_partial_code_projection.toProjection

def strengthenedToPartialTransfer
    (h : SondowProjectLocalStrengthenedPayloadCodeSemanticsCalibrationInputs) :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer :=
  h.acceptedProjectionCalibration.toTransfer

end SondowProjectLocalStrengthenedPayloadCodeSemanticsCalibrationInputs

/-- Concrete checker version of the strengthened-to-partial payload
calibration.  The checker itself is fixed by
`strengthenedToPartialProofCodeSemantics`; the only remaining proof-system input
is the calibration equating its semantic length with PA proof length on the two
relevant families. -/
structure SondowProjectLocalStrengthenedPayloadConcreteProofCodeCalibrationInputs where
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  concrete_code_projection :
    _root_.StrengthenedToPartialConcreteProofCodeProjectionCalibration

namespace SondowProjectLocalStrengthenedPayloadConcreteProofCodeCalibrationInputs

def toCodeSemanticsCalibrationInputs
    (h :
      SondowProjectLocalStrengthenedPayloadConcreteProofCodeCalibrationInputs) :
    SondowProjectLocalStrengthenedPayloadCodeSemanticsCalibrationInputs where
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_to_partial_code_projection :=
    h.concrete_code_projection.toCodeProjectionCalibration

def toPayloadCalibrationInputs
    (h :
      SondowProjectLocalStrengthenedPayloadConcreteProofCodeCalibrationInputs) :
    SondowProjectLocalStrengthenedPayloadCalibrationInputs :=
  h.toCodeSemanticsCalibrationInputs.toPayloadCalibrationInputs

def acceptedProjectionCalibration
    (h :
      SondowProjectLocalStrengthenedPayloadConcreteProofCodeCalibrationInputs) :
    _root_.StrengthenedToPartialAcceptedProjectionCalibration :=
  h.toPayloadCalibrationInputs.acceptedProjectionCalibration

def strengthenedToPartialTransfer
    (h :
      SondowProjectLocalStrengthenedPayloadConcreteProofCodeCalibrationInputs) :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer :=
  h.acceptedProjectionCalibration.toTransfer

end SondowProjectLocalStrengthenedPayloadConcreteProofCodeCalibrationInputs

/-- Recognition-theorem version of the strengthened-to-partial concrete checker
input.  This exposes the remaining proof-system obligation as equality between
PA proof length and the concrete checker's minimum proof-code size. -/
structure SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs where
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  fallback : _root_.FormulaCode → ℕ
  proof_length_recognition :
    _root_.StrengthenedToPartialConcreteProofLengthRecognition

namespace SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs

def concreteCodeProjection
    (h :
      SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs) :
    _root_.StrengthenedToPartialConcreteProofCodeProjectionCalibration :=
  h.proof_length_recognition.toConcreteProjectionCalibration h.fallback

def toConcreteProofCodeCalibrationInputs
    (h :
      SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs) :
    SondowProjectLocalStrengthenedPayloadConcreteProofCodeCalibrationInputs where
  strengthened_payload_truth := h.strengthened_payload_truth
  concrete_code_projection := h.concreteCodeProjection

def toPayloadCalibrationInputs
    (h :
      SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs) :
    SondowProjectLocalStrengthenedPayloadCalibrationInputs :=
  h.toConcreteProofCodeCalibrationInputs.toPayloadCalibrationInputs

def strengthenedToPartialTransfer
    (h :
      SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs) :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer :=
  h.toConcreteProofCodeCalibrationInputs.strengthenedToPartialTransfer

end SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs

/-- Concrete proof-length-code calibration for the strengthened-to-partial
payload step.

This is the thinnest project-facing form of the remaining proof-system
obligation: it supplies the fixed concrete semantics
`strengthenedToPartialProofLengthCodeSemantics fallback` and its calibration,
without asking directly for the derived recognition theorem. -/
structure SondowProjectLocalStrengthenedPayloadProofLengthCodeCalibrationInputs where
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  fallback : _root_.FormulaCode → ℕ
  proof_length_code_calibration :
    (_root_.strengthenedToPartialProofLengthCodeSemantics fallback).Calibration

namespace SondowProjectLocalStrengthenedPayloadProofLengthCodeCalibrationInputs

def concreteCodeProjection
    (h :
      SondowProjectLocalStrengthenedPayloadProofLengthCodeCalibrationInputs) :
    _root_.StrengthenedToPartialConcreteProofCodeProjectionCalibration where
  fallback := h.fallback
  code_calibration := h.proof_length_code_calibration

def proofLengthRecognition
    (h :
      SondowProjectLocalStrengthenedPayloadProofLengthCodeCalibrationInputs) :
    _root_.StrengthenedToPartialConcreteProofLengthRecognition :=
  _root_.StrengthenedToPartialConcreteProofLengthRecognition.ofCalibration
    h.fallback h.proof_length_code_calibration

def toConcreteProofCodeCalibrationInputs
    (h :
      SondowProjectLocalStrengthenedPayloadProofLengthCodeCalibrationInputs) :
    SondowProjectLocalStrengthenedPayloadConcreteProofCodeCalibrationInputs where
  strengthened_payload_truth := h.strengthened_payload_truth
  concrete_code_projection := h.concreteCodeProjection

def toProofLengthRecognitionInputs
    (h :
      SondowProjectLocalStrengthenedPayloadProofLengthCodeCalibrationInputs) :
    SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs where
  strengthened_payload_truth := h.strengthened_payload_truth
  fallback := h.fallback
  proof_length_recognition := h.proofLengthRecognition

def toPayloadCalibrationInputs
    (h :
      SondowProjectLocalStrengthenedPayloadProofLengthCodeCalibrationInputs) :
    SondowProjectLocalStrengthenedPayloadCalibrationInputs :=
  h.toConcreteProofCodeCalibrationInputs.toPayloadCalibrationInputs

def strengthenedToPartialTransfer
    (h :
      SondowProjectLocalStrengthenedPayloadProofLengthCodeCalibrationInputs) :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer :=
  h.toConcreteProofCodeCalibrationInputs.strengthenedToPartialTransfer

end SondowProjectLocalStrengthenedPayloadProofLengthCodeCalibrationInputs

/-- Family-length version of the strengthened-to-partial calibration.

The concrete code semantics has already been fixed.  This package exposes the
remaining proof-system obligation as exactly the two family equations needed by
`strengthenedToPartialProofLengthCodeSemantics_calibration_iff_family_lengths`.
-/
structure SondowProjectLocalStrengthenedPayloadFamilyLengthInputs where
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  fallback : _root_.FormulaCode → ℕ
  strengthened_length_exact :
    ∀ n : ℕ,
      _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.strengthenedPartialConsistencyCode n) = n
  partial_length_exact :
    ∀ n : ℕ,
      _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.partialConsistencyCode n) = n

namespace SondowProjectLocalStrengthenedPayloadFamilyLengthInputs

def ofProofLengthCodeCalibration
    (htruth : _root_.StrengthenedPartialConsistencyPayloadTruth)
    (fallback : _root_.FormulaCode → ℕ)
    (hcal :
      (_root_.strengthenedToPartialProofLengthCodeSemantics fallback).Calibration) :
    SondowProjectLocalStrengthenedPayloadFamilyLengthInputs where
  strengthened_payload_truth := htruth
  fallback := fallback
  strengthened_length_exact :=
    ((_root_.strengthenedToPartialProofLengthCodeSemantics_calibration_iff_family_lengths
      fallback).1 hcal).1
  partial_length_exact :=
    ((_root_.strengthenedToPartialProofLengthCodeSemantics_calibration_iff_family_lengths
      fallback).1 hcal).2

def ofExactFamilyLengths
    (htruth : _root_.StrengthenedPartialConsistencyPayloadTruth)
    (fallback : _root_.FormulaCode → ℕ)
    (hexact :
      _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths) :
    SondowProjectLocalStrengthenedPayloadFamilyLengthInputs where
  strengthened_payload_truth := htruth
  fallback := fallback
  strengthened_length_exact := hexact.strengthened_length_exact
  partial_length_exact := hexact.partial_length_exact

def exactFamilyLengths
    (h : SondowProjectLocalStrengthenedPayloadFamilyLengthInputs) :
    _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths where
  strengthened_length_exact := h.strengthened_length_exact
  partial_length_exact := h.partial_length_exact

def projectFamilyWitness
    (h : SondowProjectLocalStrengthenedPayloadFamilyLengthInputs)
    (fallback : _root_.FormulaCode → ℕ) :
    _root_.StrengthenedToPartialProjectProofLengthFamilyWitness fallback :=
  h.exactFamilyLengths.toFamilyWitness fallback

def proofLengthCodeCalibration
    (h : SondowProjectLocalStrengthenedPayloadFamilyLengthInputs) :
    (_root_.strengthenedToPartialProofLengthCodeSemantics h.fallback).Calibration :=
  (_root_.strengthenedToPartialProofLengthCodeSemantics_calibration_iff_family_lengths
    h.fallback).2
    ⟨h.strengthened_length_exact, h.partial_length_exact⟩

def toProofLengthCodeCalibrationInputs
    (h : SondowProjectLocalStrengthenedPayloadFamilyLengthInputs) :
    SondowProjectLocalStrengthenedPayloadProofLengthCodeCalibrationInputs where
  strengthened_payload_truth := h.strengthened_payload_truth
  fallback := h.fallback
  proof_length_code_calibration := h.proofLengthCodeCalibration

def toProofLengthRecognitionInputs
    (h : SondowProjectLocalStrengthenedPayloadFamilyLengthInputs) :
    SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs :=
  h.toProofLengthCodeCalibrationInputs.toProofLengthRecognitionInputs

def strengthenedToPartialTransfer
    (h : SondowProjectLocalStrengthenedPayloadFamilyLengthInputs) :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer :=
  h.toProofLengthCodeCalibrationInputs.strengthenedToPartialTransfer

end SondowProjectLocalStrengthenedPayloadFamilyLengthInputs

/-- Literature Pudlak input with the strengthened-to-partial step supplied by
the accepted-projection package.  This removes the bare
`StrengthenedToPartialConsistencyLowerBoundTransfer` from this project-facing
front door. -/
structure SondowProjectLocalLiteraturePudlakAcceptedProjectionInputs where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  accepted_projection :
    _root_.StrengthenedToPartialAcceptedProjectionPackage

namespace SondowProjectLocalLiteraturePudlakAcceptedProjectionInputs

def strengthenedToPartialTransfer
    (h : SondowProjectLocalLiteraturePudlakAcceptedProjectionInputs) :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer :=
  h.accepted_projection.toTransfer

def normalForm
    (h : SondowProjectLocalLiteraturePudlakAcceptedProjectionInputs) :
    _root_.PartialConsistencyLowerBoundNormalForm :=
  h.literature_lower_bound.toNormalFormOfAcceptedProjectionPackage
    h.accepted_projection

def lowerBoundPackage
    (h : SondowProjectLocalLiteraturePudlakAcceptedProjectionInputs) :
    _root_.PudlakFiniteConsistencyLowerBoundPackage :=
  pudlakFiniteConsistencyLowerBoundPackageOfPartialNormalForm h.normalForm

theorem normalForm_code_eq_powerBoundRawCode
    (h : SondowProjectLocalLiteraturePudlakAcceptedProjectionInputs) :
    h.normalForm.code =
      h.literature_lower_bound.scale_data.powerBoundRawCode := by
  exact
    h.literature_lower_bound.normalForm_code_eq_powerBoundRawCode
      h.strengthenedToPartialTransfer

def toPudlakSideInputs
    (h : SondowProjectLocalLiteraturePudlakAcceptedProjectionInputs)
    (hprojection : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    SondowProjectLocalPudlakSideInputs where
  literature_lower_bound := h.literature_lower_bound
  strengthened_to_partial := h.strengthenedToPartialTransfer
  partial_to_graft := hprojection

end SondowProjectLocalLiteraturePudlakAcceptedProjectionInputs

/-- Literature Pudlak input with the strengthened-to-partial step supplied by a
family-specific accepted-projection proof-system calibration.  This is the
calibration-first replacement for the broad-principle accepted-projection
package above. -/
structure SondowProjectLocalLiteraturePudlakAcceptedCalibrationInputs where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  accepted_projection_calibration :
    _root_.StrengthenedToPartialAcceptedProjectionCalibration

namespace SondowProjectLocalLiteraturePudlakAcceptedCalibrationInputs

def strengthenedToPartialTransfer
    (h : SondowProjectLocalLiteraturePudlakAcceptedCalibrationInputs) :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer :=
  h.accepted_projection_calibration.toTransfer

def normalForm
    (h : SondowProjectLocalLiteraturePudlakAcceptedCalibrationInputs) :
    _root_.PartialConsistencyLowerBoundNormalForm :=
  h.literature_lower_bound.toNormalForm h.strengthenedToPartialTransfer

def lowerBoundPackage
    (h : SondowProjectLocalLiteraturePudlakAcceptedCalibrationInputs) :
    _root_.PudlakFiniteConsistencyLowerBoundPackage :=
  pudlakFiniteConsistencyLowerBoundPackageOfPartialNormalForm h.normalForm

theorem normalForm_code_eq_powerBoundRawCode
    (h : SondowProjectLocalLiteraturePudlakAcceptedCalibrationInputs) :
    h.normalForm.code =
      h.literature_lower_bound.scale_data.powerBoundRawCode := by
  exact
    h.literature_lower_bound.normalForm_code_eq_powerBoundRawCode
      h.strengthenedToPartialTransfer

def toPudlakSideInputs
    (h : SondowProjectLocalLiteraturePudlakAcceptedCalibrationInputs)
    (hprojection : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    SondowProjectLocalPudlakSideInputs where
  literature_lower_bound := h.literature_lower_bound
  strengthened_to_partial := h.strengthenedToPartialTransfer
  partial_to_graft := hprojection

end SondowProjectLocalLiteraturePudlakAcceptedCalibrationInputs

/-- Literature Pudlak input with the accepted-projection package derived from
the explicit projection principle plus strengthened payload truth. -/
structure SondowProjectLocalLiteraturePudlakPayloadProjectionInputs where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  payload_projection :
    SondowProjectLocalStrengthenedPayloadProjectionInputs

namespace SondowProjectLocalLiteraturePudlakPayloadProjectionInputs

def toAcceptedProjectionInputs
    (h : SondowProjectLocalLiteraturePudlakPayloadProjectionInputs) :
    SondowProjectLocalLiteraturePudlakAcceptedProjectionInputs where
  literature_lower_bound := h.literature_lower_bound
  accepted_projection := h.payload_projection.acceptedProjectionPackage

def normalForm
    (h : SondowProjectLocalLiteraturePudlakPayloadProjectionInputs) :
    _root_.PartialConsistencyLowerBoundNormalForm :=
  h.toAcceptedProjectionInputs.normalForm

def lowerBoundPackage
    (h : SondowProjectLocalLiteraturePudlakPayloadProjectionInputs) :
    _root_.PudlakFiniteConsistencyLowerBoundPackage :=
  h.toAcceptedProjectionInputs.lowerBoundPackage

theorem normalForm_code_eq_powerBoundRawCode
    (h : SondowProjectLocalLiteraturePudlakPayloadProjectionInputs) :
    h.normalForm.code =
      h.literature_lower_bound.scale_data.powerBoundRawCode :=
  h.toAcceptedProjectionInputs.normalForm_code_eq_powerBoundRawCode

end SondowProjectLocalLiteraturePudlakPayloadProjectionInputs

/-- Literature Pudlak input where payload truth gives the accepted projection,
and a family-specific proof-system calibration gives the proof-length
projection. -/
structure SondowProjectLocalLiteraturePudlakPayloadCalibrationInputs where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  payload_calibration :
    SondowProjectLocalStrengthenedPayloadCalibrationInputs

namespace SondowProjectLocalLiteraturePudlakPayloadCalibrationInputs

def toAcceptedCalibrationInputs
    (h : SondowProjectLocalLiteraturePudlakPayloadCalibrationInputs) :
    SondowProjectLocalLiteraturePudlakAcceptedCalibrationInputs where
  literature_lower_bound := h.literature_lower_bound
  accepted_projection_calibration :=
    h.payload_calibration.acceptedProjectionCalibration

def normalForm
    (h : SondowProjectLocalLiteraturePudlakPayloadCalibrationInputs) :
    _root_.PartialConsistencyLowerBoundNormalForm :=
  h.toAcceptedCalibrationInputs.normalForm

def lowerBoundPackage
    (h : SondowProjectLocalLiteraturePudlakPayloadCalibrationInputs) :
    _root_.PudlakFiniteConsistencyLowerBoundPackage :=
  h.toAcceptedCalibrationInputs.lowerBoundPackage

theorem normalForm_code_eq_powerBoundRawCode
    (h : SondowProjectLocalLiteraturePudlakPayloadCalibrationInputs) :
    h.normalForm.code =
      h.literature_lower_bound.scale_data.powerBoundRawCode :=
  h.toAcceptedCalibrationInputs.normalForm_code_eq_powerBoundRawCode

end SondowProjectLocalLiteraturePudlakPayloadCalibrationInputs

/-- Formula-code realization package with the strengthened-to-partial transfer
derived from the accepted-projection package rather than supplied as an opaque
transfer. -/
structure SondowProjectLocalPudlakAcceptedFormulaCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  accepted_projection :
    _root_.StrengthenedToPartialAcceptedProjectionPackage
  hilbert_formula_code :
    _root_.MiniHilbert.HilbertRightConjElimFormulaCodeRealization
      Ax A B halign

namespace SondowProjectLocalPudlakAcceptedFormulaCodeInputs

def toLiteratureAcceptedProjectionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAcceptedFormulaCodeInputs Ax A B halign) :
    SondowProjectLocalLiteraturePudlakAcceptedProjectionInputs where
  literature_lower_bound := h.literature_lower_bound
  accepted_projection := h.accepted_projection

def toFormulaCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAcceptedFormulaCodeInputs Ax A B halign) :
    SondowProjectLocalPudlakHilbertFormulaCodeInputs Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  strengthened_to_partial :=
    h.toLiteratureAcceptedProjectionInputs.strengthenedToPartialTransfer
  hilbert_formula_code := h.hilbert_formula_code

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAcceptedFormulaCodeInputs Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toFormulaCodeInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAcceptedFormulaCodeInputs Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakAcceptedFormulaCodeInputs

/-- Formula-code realization package whose strengthened-to-partial projection
is generated from `PAProofLengthProjectionPrinciple` plus strengthened payload
truth. -/
structure SondowProjectLocalPudlakPayloadFormulaCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  payload_projection :
    SondowProjectLocalStrengthenedPayloadProjectionInputs
  hilbert_formula_code :
    _root_.MiniHilbert.HilbertRightConjElimFormulaCodeRealization
      Ax A B halign

namespace SondowProjectLocalPudlakPayloadFormulaCodeInputs

def toAcceptedFormulaCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakPayloadFormulaCodeInputs Ax A B halign) :
    SondowProjectLocalPudlakAcceptedFormulaCodeInputs Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  accepted_projection := h.payload_projection.acceptedProjectionPackage
  hilbert_formula_code := h.hilbert_formula_code

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakPayloadFormulaCodeInputs Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toAcceptedFormulaCodeInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakPayloadFormulaCodeInputs Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakPayloadFormulaCodeInputs

/-- Accepted-projection plus family-exactness package.  This replaces the
standard semantics field by the narrower two-family exactness statement:
project-level `proof_length` agrees with MiniHilbert min checked code sizes on
exactly `partialConsistencyCode` and `sondowReflectionGraftCode`. -/
structure SondowProjectLocalPudlakAcceptedFamilyExactnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  accepted_projection :
    _root_.StrengthenedToPartialAcceptedProjectionPackage
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  family_exactness :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
      formula_code_interpretation

namespace SondowProjectLocalPudlakAcceptedFamilyExactnessInputs

def toAcceptedFormulaCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAcceptedFamilyExactnessInputs
      Ax A B halign) :
    SondowProjectLocalPudlakAcceptedFormulaCodeInputs Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  accepted_projection := h.accepted_projection
  hilbert_formula_code :=
    h.formula_code_interpretation.toFormulaCodeRealization
      h.family_exactness.toStandardFormulaCodeProofLengthSemantics.toCalibration

def toStandardSemanticsInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAcceptedFamilyExactnessInputs
      Ax A B halign) :
    SondowProjectLocalPudlakHilbertStandardSemanticsInputs Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  strengthened_to_partial :=
    h.accepted_projection.toTransfer
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_semantics :=
    h.family_exactness.toStandardFormulaCodeProofLengthSemantics

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAcceptedFamilyExactnessInputs
      Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toStandardSemanticsInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAcceptedFamilyExactnessInputs
      Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakAcceptedFamilyExactnessInputs

/-- Family-exactness package whose strengthened-to-partial projection is
generated from the explicit projection principle plus strengthened payload
truth. -/
structure SondowProjectLocalPudlakPayloadFamilyExactnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  payload_projection :
    SondowProjectLocalStrengthenedPayloadProjectionInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  family_exactness :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
      formula_code_interpretation

namespace SondowProjectLocalPudlakPayloadFamilyExactnessInputs

def toAcceptedFamilyExactnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakPayloadFamilyExactnessInputs
      Ax A B halign) :
    SondowProjectLocalPudlakAcceptedFamilyExactnessInputs Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  accepted_projection := h.payload_projection.acceptedProjectionPackage
  formula_code_interpretation := h.formula_code_interpretation
  family_exactness := h.family_exactness

def toPayloadFormulaCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakPayloadFamilyExactnessInputs
      Ax A B halign) :
    SondowProjectLocalPudlakPayloadFormulaCodeInputs Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  payload_projection := h.payload_projection
  hilbert_formula_code :=
    h.formula_code_interpretation.toFormulaCodeRealization
      h.family_exactness.toStandardFormulaCodeProofLengthSemantics.toCalibration

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakPayloadFamilyExactnessInputs
      Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toAcceptedFamilyExactnessInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakPayloadFamilyExactnessInputs
      Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakPayloadFamilyExactnessInputs

/-- Lowest project-facing proof-length semantic input in this file: a local
PA-Hilbert code-model calibration.  The existing library equivalence converts
it to the two-family exactness package above. -/
structure SondowProjectLocalPudlakAcceptedLocalCodeCalibrationInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  accepted_projection :
    _root_.StrengthenedToPartialAcceptedProjectionPackage
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback : _root_.FormulaCode → ℕ
  code_calibration :
    (let model :=
      formula_code_interpretation
        |>.localPAHilbertProofLengthCodeSemanticsForProjection fallback
     model.code_model.Calibration)

namespace SondowProjectLocalPudlakAcceptedLocalCodeCalibrationInputs

def toFamilyExactnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAcceptedLocalCodeCalibrationInputs
      Ax A B halign) :
    SondowProjectLocalPudlakAcceptedFamilyExactnessInputs Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  accepted_projection := h.accepted_projection
  formula_code_interpretation := h.formula_code_interpretation
  family_exactness :=
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness.ofLocalPAHilbertCodeCalibration
      h.fallback h.code_calibration

def toStandardSemanticsInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAcceptedLocalCodeCalibrationInputs
      Ax A B halign) :
    SondowProjectLocalPudlakHilbertStandardSemanticsInputs Ax A B halign :=
  h.toFamilyExactnessInputs.toStandardSemanticsInputs

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAcceptedLocalCodeCalibrationInputs
      Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toStandardSemanticsInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAcceptedLocalCodeCalibrationInputs
      Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakAcceptedLocalCodeCalibrationInputs

/-- Calibration-first local-code package.  It combines:

* the literature lower-bound certificate;
* the strengthened-to-partial accepted-projection calibration; and
* the MiniHilbert local proof-code calibration for the partial-to-graft
  proof-length transfer.

This is the most explicit project-facing replacement for the old
`PAProofLengthProjectionPrinciple` front door in this file. -/
structure SondowProjectLocalPudlakAcceptedProjectionCalibrationLocalCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  accepted_projection_calibration :
    _root_.StrengthenedToPartialAcceptedProjectionCalibration
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback : _root_.FormulaCode → ℕ
  code_calibration :
    (let model :=
      formula_code_interpretation
        |>.localPAHilbertProofLengthCodeSemanticsForProjection fallback
     model.code_model.Calibration)

namespace SondowProjectLocalPudlakAcceptedProjectionCalibrationLocalCodeInputs

def literatureCalibrationInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAcceptedProjectionCalibrationLocalCodeInputs
      Ax A B halign) :
    SondowProjectLocalLiteraturePudlakAcceptedCalibrationInputs where
  literature_lower_bound := h.literature_lower_bound
  accepted_projection_calibration := h.accepted_projection_calibration

def familyExactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAcceptedProjectionCalibrationLocalCodeInputs
      Ax A B halign) :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
      h.formula_code_interpretation :=
  _root_.MiniHilbert.PAHilbertProjectionFamilyExactness.ofLocalPAHilbertCodeCalibration
    h.fallback h.code_calibration

def partialToGraftTransfer
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAcceptedProjectionCalibrationLocalCodeInputs
      Ax A B halign) :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer :=
  h.familyExactness.toStrongLowerBoundTransfer

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAcceptedProjectionCalibrationLocalCodeInputs
      Ax A B halign) :
    SondowProjectLocalPudlakSideInputs where
  literature_lower_bound := h.literature_lower_bound
  strengthened_to_partial :=
    h.accepted_projection_calibration.toTransfer
  partial_to_graft := h.partialToGraftTransfer

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAcceptedProjectionCalibrationLocalCodeInputs
      Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakAcceptedProjectionCalibrationLocalCodeInputs

/-- Local code-calibration package whose strengthened-to-partial projection is
generated from the explicit projection principle plus strengthened payload
truth. -/
structure SondowProjectLocalPudlakPayloadLocalCodeCalibrationInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  payload_projection :
    SondowProjectLocalStrengthenedPayloadProjectionInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback : _root_.FormulaCode → ℕ
  code_calibration :
    (let model :=
      formula_code_interpretation
        |>.localPAHilbertProofLengthCodeSemanticsForProjection fallback
     model.code_model.Calibration)

namespace SondowProjectLocalPudlakPayloadLocalCodeCalibrationInputs

def toAcceptedLocalCodeCalibrationInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakPayloadLocalCodeCalibrationInputs
      Ax A B halign) :
    SondowProjectLocalPudlakAcceptedLocalCodeCalibrationInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  accepted_projection := h.payload_projection.acceptedProjectionPackage
  formula_code_interpretation := h.formula_code_interpretation
  fallback := h.fallback
  code_calibration := h.code_calibration

def toPayloadFamilyExactnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakPayloadLocalCodeCalibrationInputs
      Ax A B halign) :
    SondowProjectLocalPudlakPayloadFamilyExactnessInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  payload_projection := h.payload_projection
  formula_code_interpretation := h.formula_code_interpretation
  family_exactness :=
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness.ofLocalPAHilbertCodeCalibration
      h.fallback h.code_calibration

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakPayloadLocalCodeCalibrationInputs
      Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toAcceptedLocalCodeCalibrationInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakPayloadLocalCodeCalibrationInputs
      Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakPayloadLocalCodeCalibrationInputs

/-- Payload-derived version of the calibration-first local-code package.  The
strengthened payload truth generates the accepted projection, and the dependent
proof-system calibration certifies the corresponding proof-length projection. -/
structure SondowProjectLocalPudlakPayloadProjectionCalibrationLocalCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  payload_calibration :
    SondowProjectLocalStrengthenedPayloadCalibrationInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback : _root_.FormulaCode → ℕ
  code_calibration :
    (let model :=
      formula_code_interpretation
        |>.localPAHilbertProofLengthCodeSemanticsForProjection fallback
     model.code_model.Calibration)

namespace SondowProjectLocalPudlakPayloadProjectionCalibrationLocalCodeInputs

def toAcceptedProjectionCalibrationLocalCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakPayloadProjectionCalibrationLocalCodeInputs
      Ax A B halign) :
    SondowProjectLocalPudlakAcceptedProjectionCalibrationLocalCodeInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  accepted_projection_calibration :=
    h.payload_calibration.acceptedProjectionCalibration
  formula_code_interpretation := h.formula_code_interpretation
  fallback := h.fallback
  code_calibration := h.code_calibration

def toLiteraturePayloadCalibrationInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakPayloadProjectionCalibrationLocalCodeInputs
      Ax A B halign) :
    SondowProjectLocalLiteraturePudlakPayloadCalibrationInputs where
  literature_lower_bound := h.literature_lower_bound
  payload_calibration := h.payload_calibration

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakPayloadProjectionCalibrationLocalCodeInputs
      Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toAcceptedProjectionCalibrationLocalCodeInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakPayloadProjectionCalibrationLocalCodeInputs
      Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakPayloadProjectionCalibrationLocalCodeInputs

/-- Current narrowest audited Pudlak-side project input.

The literature input is expanded into scale data plus the actual Theorem 5
power-bound lower bound; the strengthened-to-partial step is supplied by a
code-semantics calibration; and the partial-to-graft step is supplied by the
MiniHilbert local proof-code calibration. -/
structure SondowProjectLocalPudlakAuditedPayloadCodeSemanticsLocalCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs
  payload_code_calibration :
    SondowProjectLocalStrengthenedPayloadCodeSemanticsCalibrationInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback : _root_.FormulaCode → ℕ
  code_calibration :
    (let model :=
      formula_code_interpretation
        |>.localPAHilbertProofLengthCodeSemanticsForProjection fallback
     model.code_model.Calibration)

namespace SondowProjectLocalPudlakAuditedPayloadCodeSemanticsLocalCodeInputs

def toPayloadProjectionCalibrationLocalCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCodeSemanticsLocalCodeInputs
        Ax A B halign) :
    SondowProjectLocalPudlakPayloadProjectionCalibrationLocalCodeInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound.toCertificate
  payload_calibration :=
    h.payload_code_calibration.toPayloadCalibrationInputs
  formula_code_interpretation := h.formula_code_interpretation
  fallback := h.fallback
  code_calibration := h.code_calibration

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCodeSemanticsLocalCodeInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toPayloadProjectionCalibrationLocalCodeInputs.toPudlakSideInputs

def lowerBoundPackage
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCodeSemanticsLocalCodeInputs
        Ax A B halign) :
    _root_.PudlakFiniteConsistencyLowerBoundPackage :=
  h.toPudlakSideInputs.lowerBoundPackage

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCodeSemanticsLocalCodeInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakAuditedPayloadCodeSemanticsLocalCodeInputs

/-- Same audited Pudlak-side input as
`SondowProjectLocalPudlakAuditedPayloadCodeSemanticsLocalCodeInputs`, but with
the strengthened-to-partial step fixed to the concrete checker
`strengthenedToPartialProofCodeSemantics`. -/
structure SondowProjectLocalPudlakAuditedPayloadConcreteProofCodeLocalCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs
  payload_concrete_calibration :
    SondowProjectLocalStrengthenedPayloadConcreteProofCodeCalibrationInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback : _root_.FormulaCode → ℕ
  code_calibration :
    (let model :=
      formula_code_interpretation
        |>.localPAHilbertProofLengthCodeSemanticsForProjection fallback
     model.code_model.Calibration)

namespace SondowProjectLocalPudlakAuditedPayloadConcreteProofCodeLocalCodeInputs

def toAuditedPayloadCodeSemanticsLocalCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConcreteProofCodeLocalCodeInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadCodeSemanticsLocalCodeInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  payload_code_calibration :=
    h.payload_concrete_calibration.toCodeSemanticsCalibrationInputs
  formula_code_interpretation := h.formula_code_interpretation
  fallback := h.fallback
  code_calibration := h.code_calibration

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConcreteProofCodeLocalCodeInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toAuditedPayloadCodeSemanticsLocalCodeInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConcreteProofCodeLocalCodeInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakAuditedPayloadConcreteProofCodeLocalCodeInputs

/-- Recognition-theorem version of the current narrow Pudlak-side input.

The strengthened-to-partial checker is fixed, and the remaining proof-system
obligation is the recognition theorem equating PA proof length with that
checker minimum on the two relevant formula families. -/
structure SondowProjectLocalPudlakAuditedPayloadConcreteRecognitionLocalCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs
  payload_recognition :
    SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback : _root_.FormulaCode → ℕ
  code_calibration :
    (let model :=
      formula_code_interpretation
        |>.localPAHilbertProofLengthCodeSemanticsForProjection fallback
     model.code_model.Calibration)

namespace SondowProjectLocalPudlakAuditedPayloadConcreteRecognitionLocalCodeInputs

def toConcreteProofCodeLocalCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConcreteRecognitionLocalCodeInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadConcreteProofCodeLocalCodeInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  payload_concrete_calibration :=
    h.payload_recognition.toConcreteProofCodeCalibrationInputs
  formula_code_interpretation := h.formula_code_interpretation
  fallback := h.fallback
  code_calibration := h.code_calibration

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConcreteRecognitionLocalCodeInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toConcreteProofCodeLocalCodeInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConcreteRecognitionLocalCodeInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakAuditedPayloadConcreteRecognitionLocalCodeInputs

/-- Dual-recognition version of the current narrow Pudlak-side input.

Both proof-system calibration obligations are now recognition theorems:
the strengthened-to-partial checker recognizes its PA proof lengths, and the
partial-to-graft local Hilbert checker recognizes its PA proof lengths. -/
structure SondowProjectLocalPudlakAuditedPayloadDualRecognitionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs
  payload_recognition :
    SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback : _root_.FormulaCode → ℕ
  local_hilbert_recognition :
    _root_.MiniHilbert.PAHilbertLocalProofCodeRecognition
      formula_code_interpretation

namespace SondowProjectLocalPudlakAuditedPayloadDualRecognitionInputs

def toRecognitionLocalCodeInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAuditedPayloadDualRecognitionInputs
      Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadConcreteRecognitionLocalCodeInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  payload_recognition := h.payload_recognition
  formula_code_interpretation := h.formula_code_interpretation
  fallback := h.fallback
  code_calibration :=
    h.local_hilbert_recognition.toLocalPAHilbertCodeCalibration h.fallback

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAuditedPayloadDualRecognitionInputs
      Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toRecognitionLocalCodeInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h : SondowProjectLocalPudlakAuditedPayloadDualRecognitionInputs
      Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakAuditedPayloadDualRecognitionInputs

/-- Encoder-recognition version of the current narrow Pudlak-side input.

The partial-to-graft side no longer asks directly for local Hilbert proof-code
recognition.  It asks for the lower-level project checked-code encoder
recognition; the concrete Hilbert checker exactness is supplied by
`FormulaCodeHilbertInterpretation.localHilbertCheckerExactness`. -/
structure SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs
  payload_recognition :
    SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback : _root_.FormulaCode → ℕ
  local_hilbert_encoder_recognition :
    _root_.MiniHilbert.PAHilbertProjectCheckedProofLengthRecognition
      formula_code_interpretation

namespace SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs

def toDualRecognitionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadDualRecognitionInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  payload_recognition := h.payload_recognition
  formula_code_interpretation := h.formula_code_interpretation
  fallback := h.fallback
  local_hilbert_recognition :=
    (h.formula_code_interpretation
      |>.localProofCodeRecognition_iff_projectCheckedRecognition).2
      h.local_hilbert_encoder_recognition

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toDualRecognitionInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs

/-- Proof-code checker version of the current narrow Pudlak-side input.

This is one layer lower than project checked-code recognition: the PA proof
length is calibrated against the concrete `ProofCodeSemantics.projectLength`
coming from the local Hilbert checker, with a fallback length outside the
projection fragment. -/
structure SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs
  payload_recognition :
    SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  local_hilbert_checker_recognition :
    _root_.MiniHilbert.PAHilbertProofCodeCheckerRecognition
      formula_code_interpretation

namespace SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs

def toCheckedEncoderRecognitionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  payload_recognition := h.payload_recognition
  formula_code_interpretation := h.formula_code_interpretation
  fallback := h.local_hilbert_checker_recognition.fallback_length
  local_hilbert_encoder_recognition :=
    h.local_hilbert_checker_recognition.toProjectCheckedRecognition

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toCheckedEncoderRecognitionInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs

/-- Calibration-first version of the proof-code checker input.

Instead of assuming the checker-recognition theorem directly, this package asks
for the calibration of the concrete local Hilbert proof-length code semantics.
The checker-recognition theorem is then recovered by
`PAHilbertProofCodeCheckerRecognition.ofProofLengthCodeCalibration`. -/
structure SondowProjectLocalPudlakAuditedPayloadProofCodeCalibrationInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs
  payload_recognition :
    SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback_length : _root_.FormulaCode → ℕ
  proof_length_code_calibration :
    (formula_code_interpretation.localHilbertProofLengthCodeSemantics
      fallback_length).Calibration

namespace SondowProjectLocalPudlakAuditedPayloadProofCodeCalibrationInputs

def proofCodeCheckerRecognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCalibrationInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertProofCodeCheckerRecognition
      h.formula_code_interpretation :=
  _root_.MiniHilbert.PAHilbertProofCodeCheckerRecognition.ofProofLengthCodeCalibration
    h.fallback_length h.proof_length_code_calibration

def toProofCodeCheckerRecognitionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCalibrationInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  payload_recognition := h.payload_recognition
  formula_code_interpretation := h.formula_code_interpretation
  local_hilbert_checker_recognition := h.proofCodeCheckerRecognition

def toCheckedEncoderRecognitionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCalibrationInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
      Ax A B halign :=
  h.toProofCodeCheckerRecognitionInputs.toCheckedEncoderRecognitionInputs

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCalibrationInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toProofCodeCheckerRecognitionInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCalibrationInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakAuditedPayloadProofCodeCalibrationInputs

/-- Convention/equivalence version of the current narrow Pudlak-side input.

The partial-to-graft proof-length obligation is split into:

* a PA proof-length convention on the relevant formula-code fragment; and
* an equivalence between that convention and the local Hilbert checked-code
  encoder. -/
structure SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs
  payload_recognition :
    SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback : _root_.FormulaCode → ℕ
  proof_length_convention :
    _root_.MiniHilbert.PAHilbertProofLengthConvention
  checked_encoder_equivalence :
    _root_.MiniHilbert.FormulaCodeHilbertCheckedCodeEncoderEquivalence
      formula_code_interpretation proof_length_convention

namespace SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs

def projectCheckedRecognitionCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertProjectCheckedRecognitionCertificate
      h.formula_code_interpretation where
  convention := h.proof_length_convention
  encoder_equivalence := h.checked_encoder_equivalence

def toCheckedEncoderRecognitionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  payload_recognition := h.payload_recognition
  formula_code_interpretation := h.formula_code_interpretation
  fallback := h.fallback
  local_hilbert_encoder_recognition :=
    h.projectCheckedRecognitionCertificate.toProjectCheckedRecognition

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toCheckedEncoderRecognitionInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs

/-- Canonical minChecked-code convention version of the current narrow
Pudlak-side input.

The partial-to-graft proof-length convention is now fixed to the canonical
local Hilbert minChecked-code length.  The remaining input is exactly the two
family proof-length equalities packaged by `PAHilbertProjectionFamilyExactness`.
-/
structure SondowProjectLocalPudlakAuditedPayloadCanonicalConventionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs
  payload_recognition :
    SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback : _root_.FormulaCode → ℕ
  local_hilbert_family_exactness :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
      formula_code_interpretation

namespace SondowProjectLocalPudlakAuditedPayloadCanonicalConventionInputs

def toConventionEquivalenceInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCanonicalConventionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  payload_recognition := h.payload_recognition
  formula_code_interpretation := h.formula_code_interpretation
  fallback := h.fallback
  proof_length_convention :=
    h.local_hilbert_family_exactness.toCanonicalMinCheckedConvention
  checked_encoder_equivalence :=
    h.local_hilbert_family_exactness.toCanonicalEncoderEquivalence

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCanonicalConventionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toConventionEquivalenceInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCanonicalConventionInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakAuditedPayloadCanonicalConventionInputs

namespace SondowProjectLocalPudlakAuditedPayloadCanonicalConventionInputs

def proofLengthCodeCalibration
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCanonicalConventionInputs
        Ax A B halign) :
    (h.formula_code_interpretation.localHilbertProofLengthCodeSemantics
      h.fallback).Calibration :=
  h.local_hilbert_family_exactness.toLocalHilbertProofLengthCodeCalibration
    h.fallback

def toProofCodeCalibrationInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCanonicalConventionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadProofCodeCalibrationInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  payload_recognition := h.payload_recognition
  formula_code_interpretation := h.formula_code_interpretation
  fallback_length := h.fallback
  proof_length_code_calibration := h.proofLengthCodeCalibration

end SondowProjectLocalPudlakAuditedPayloadCanonicalConventionInputs

/-- Split-certificate version of the canonical convention input.

The partial-to-graft Hilbert proof-length input is separated into the source
partial-consistency minChecked exactness certificate and the target reflection-
graft minChecked exactness certificate. -/
structure SondowProjectLocalPudlakAuditedPayloadSplitMinCheckedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs
  payload_recognition :
    SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback : _root_.FormulaCode → ℕ
  partial_minChecked_exactness :
    _root_.MiniHilbert.PAHilbertPartialConsistencyMinCheckedExactness
      formula_code_interpretation
  reflection_minChecked_exactness :
    _root_.MiniHilbert.PAHilbertReflectionGraftMinCheckedExactness
      formula_code_interpretation

namespace SondowProjectLocalPudlakAuditedPayloadSplitMinCheckedInputs

def familyExactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadSplitMinCheckedInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
      h.formula_code_interpretation :=
  _root_.MiniHilbert.PAHilbertProjectionFamilyExactness.ofMinCheckedExactness
    h.partial_minChecked_exactness h.reflection_minChecked_exactness

def sourceMinCheckedCalibration
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadSplitMinCheckedInputs
        Ax A B halign) :
    _root_.MiniHilbert.PartialConsistencySourceMinCheckedCalibration
      h.formula_code_interpretation :=
  h.partial_minChecked_exactness.toSourceMinCheckedCalibration

def toCanonicalConventionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadSplitMinCheckedInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadCanonicalConventionInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  payload_recognition := h.payload_recognition
  formula_code_interpretation := h.formula_code_interpretation
  fallback := h.fallback
  local_hilbert_family_exactness := h.familyExactness

def proofLengthCodeCalibration
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadSplitMinCheckedInputs
        Ax A B halign) :
    (h.formula_code_interpretation.localHilbertProofLengthCodeSemantics
      h.fallback).Calibration :=
  h.familyExactness.toLocalHilbertProofLengthCodeCalibration h.fallback

def toProofCodeCalibrationInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadSplitMinCheckedInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadProofCodeCalibrationInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  payload_recognition := h.payload_recognition
  formula_code_interpretation := h.formula_code_interpretation
  fallback_length := h.fallback
  proof_length_code_calibration := h.proofLengthCodeCalibration

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadSplitMinCheckedInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toCanonicalConventionInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadSplitMinCheckedInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakAuditedPayloadSplitMinCheckedInputs

/-- Source-calibrated version of the split minChecked input.

The source side is stated directly in the form consumed by Pudlak lower-bound
transport, while the reflection-graft side remains the independent target
minChecked exactness certificate. -/
structure SondowProjectLocalPudlakAuditedPayloadSourceCalibrationSplitInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs
  payload_recognition :
    SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback : _root_.FormulaCode → ℕ
  source_minChecked_calibration :
    _root_.MiniHilbert.PartialConsistencySourceMinCheckedCalibration
      formula_code_interpretation
  reflection_minChecked_exactness :
    _root_.MiniHilbert.PAHilbertReflectionGraftMinCheckedExactness
      formula_code_interpretation

namespace SondowProjectLocalPudlakAuditedPayloadSourceCalibrationSplitInputs

def toSplitMinCheckedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadSourceCalibrationSplitInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadSplitMinCheckedInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  payload_recognition := h.payload_recognition
  formula_code_interpretation := h.formula_code_interpretation
  fallback := h.fallback
  partial_minChecked_exactness :=
    h.source_minChecked_calibration.toPartialConsistencyMinCheckedExactness
  reflection_minChecked_exactness := h.reflection_minChecked_exactness

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadSourceCalibrationSplitInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toSplitMinCheckedInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadSourceCalibrationSplitInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakAuditedPayloadSourceCalibrationSplitInputs

/-- Canonical-convention version of the source-calibrated split input.

This is the current narrowest proof-length recognition frontier for the
partial-to-graft Hilbert side: it asks only for the two family-level equations
identifying PA proof length with the canonical local minChecked length. -/
structure SondowProjectLocalPudlakAuditedPayloadCanonicalMinCheckedSplitInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs
  payload_recognition :
    SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback : _root_.FormulaCode → ℕ
  partial_canonical_convention :
    _root_.MiniHilbert.PAHilbertPartialConsistencyCanonicalMinCheckedConvention
      formula_code_interpretation
  reflection_canonical_convention :
    _root_.MiniHilbert.PAHilbertReflectionGraftCanonicalMinCheckedConvention
      formula_code_interpretation

namespace SondowProjectLocalPudlakAuditedPayloadCanonicalMinCheckedSplitInputs

def splitCanonicalConvention
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCanonicalMinCheckedSplitInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertSplitCanonicalMinCheckedConvention
      h.formula_code_interpretation where
  partial_convention := h.partial_canonical_convention
  reflection_convention := h.reflection_canonical_convention

def toSourceCalibrationSplitInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCanonicalMinCheckedSplitInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadSourceCalibrationSplitInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  payload_recognition := h.payload_recognition
  formula_code_interpretation := h.formula_code_interpretation
  fallback := h.fallback
  source_minChecked_calibration :=
    h.partial_canonical_convention.toSourceMinCheckedCalibration
  reflection_minChecked_exactness :=
    h.reflection_canonical_convention.toReflectionGraftMinCheckedExactness

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCanonicalMinCheckedSplitInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toSourceCalibrationSplitInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCanonicalMinCheckedSplitInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakAuditedPayloadCanonicalMinCheckedSplitInputs

/-- Certificate-split version of the canonical minChecked input.

The proof-length recognition layer is split into a PA family convention and a
checked-code encoder exactness certificate for each of the two projection
families. -/
structure SondowProjectLocalPudlakAuditedPayloadConventionCertificateSplitInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs
  payload_recognition :
    SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback : _root_.FormulaCode → ℕ
  partial_certificate :
    _root_.MiniHilbert.PAPartialConsistencyCanonicalConventionCertificate
      formula_code_interpretation
  reflection_certificate :
    _root_.MiniHilbert.PAReflectionGraftCanonicalConventionCertificate
      formula_code_interpretation

namespace SondowProjectLocalPudlakAuditedPayloadConventionCertificateSplitInputs

def splitCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConventionCertificateSplitInputs
        Ax A B halign) :
    _root_.MiniHilbert.PASplitCanonicalConventionCertificate
      h.formula_code_interpretation where
  partial_certificate := h.partial_certificate
  reflection_certificate := h.reflection_certificate

def toCanonicalMinCheckedSplitInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConventionCertificateSplitInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadCanonicalMinCheckedSplitInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  payload_recognition := h.payload_recognition
  formula_code_interpretation := h.formula_code_interpretation
  fallback := h.fallback
  partial_canonical_convention :=
    h.partial_certificate.toCanonicalConvention
  reflection_canonical_convention :=
    h.reflection_certificate.toCanonicalConvention

def toSourceCalibrationSplitInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConventionCertificateSplitInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadSourceCalibrationSplitInputs
      Ax A B halign :=
  h.toCanonicalMinCheckedSplitInputs.toSourceCalibrationSplitInputs

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConventionCertificateSplitInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toCanonicalMinCheckedSplitInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConventionCertificateSplitInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakAuditedPayloadConventionCertificateSplitInputs

/-- Partial-source recognition version of the convention-certificate split.

The partial-consistency side is stated as the minimal localChecked recognition
needed for Pudlak source-side lower-bound transport.  The reflection-graft side
remains a checked convention certificate. -/
structure SondowProjectLocalPudlakAuditedPayloadPartialRecognitionSplitInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs
  payload_recognition :
    SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback : _root_.FormulaCode → ℕ
  partial_localChecked_recognition :
    _root_.MiniHilbert.PAPartialConsistencyLocalCheckedRecognition
      formula_code_interpretation
  reflection_certificate :
    _root_.MiniHilbert.PAReflectionGraftCanonicalConventionCertificate
      formula_code_interpretation

namespace SondowProjectLocalPudlakAuditedPayloadPartialRecognitionSplitInputs

def partialCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadPartialRecognitionSplitInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAPartialConsistencyCanonicalConventionCertificate
      h.formula_code_interpretation :=
  h.partial_localChecked_recognition.toConventionCertificate

def partialSourceCalibration
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadPartialRecognitionSplitInputs
        Ax A B halign) :
    _root_.MiniHilbert.PartialConsistencySourceMinCheckedCalibration
      h.formula_code_interpretation :=
  h.partial_localChecked_recognition.toSourceMinCheckedCalibration

def toConventionCertificateSplitInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadPartialRecognitionSplitInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadConventionCertificateSplitInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  payload_recognition := h.payload_recognition
  formula_code_interpretation := h.formula_code_interpretation
  fallback := h.fallback
  partial_certificate := h.partialCertificate
  reflection_certificate := h.reflection_certificate

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadPartialRecognitionSplitInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toConventionCertificateSplitInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadPartialRecognitionSplitInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakAuditedPayloadPartialRecognitionSplitInputs

/-- Fully localChecked-recognition version of the split input.

Both projection families are now stated in the same recognition form:
project-level PA proof length equals the local checked-code length. -/
structure SondowProjectLocalPudlakAuditedPayloadLocalCheckedRecognitionSplitInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_lower_bound :
    SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs
  payload_recognition :
    SondowProjectLocalStrengthenedPayloadConcreteProofLengthRecognitionInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback : _root_.FormulaCode → ℕ
  partial_localChecked_recognition :
    _root_.MiniHilbert.PAPartialConsistencyLocalCheckedRecognition
      formula_code_interpretation
  reflection_localChecked_recognition :
    _root_.MiniHilbert.PAReflectionGraftLocalCheckedRecognition
      formula_code_interpretation

namespace SondowProjectLocalPudlakAuditedPayloadLocalCheckedRecognitionSplitInputs

def splitRecognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadLocalCheckedRecognitionSplitInputs
        Ax A B halign) :
    _root_.MiniHilbert.PASplitLocalCheckedRecognition
      h.formula_code_interpretation where
  partial_recognition := h.partial_localChecked_recognition
  reflection_recognition := h.reflection_localChecked_recognition

def toPartialRecognitionSplitInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadLocalCheckedRecognitionSplitInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadPartialRecognitionSplitInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  payload_recognition := h.payload_recognition
  formula_code_interpretation := h.formula_code_interpretation
  fallback := h.fallback
  partial_localChecked_recognition := h.partial_localChecked_recognition
  reflection_certificate :=
    h.reflection_localChecked_recognition.toConventionCertificate

def toConventionCertificateSplitInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadLocalCheckedRecognitionSplitInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadConventionCertificateSplitInputs
      Ax A B halign :=
  h.toPartialRecognitionSplitInputs.toConventionCertificateSplitInputs

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadLocalCheckedRecognitionSplitInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toConventionCertificateSplitInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadLocalCheckedRecognitionSplitInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakAuditedPayloadLocalCheckedRecognitionSplitInputs

namespace SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs

def splitLocalCheckedRecognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
        Ax A B halign) :
    _root_.MiniHilbert.PASplitLocalCheckedRecognition
      h.formula_code_interpretation :=
  h.local_hilbert_encoder_recognition.toSplitLocalCheckedRecognition

def toLocalCheckedRecognitionSplitInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadLocalCheckedRecognitionSplitInputs
      Ax A B halign where
  literature_lower_bound := h.literature_lower_bound
  payload_recognition := h.payload_recognition
  formula_code_interpretation := h.formula_code_interpretation
  fallback := h.fallback
  partial_localChecked_recognition :=
    h.splitLocalCheckedRecognition.partial_recognition
  reflection_localChecked_recognition :=
    h.splitLocalCheckedRecognition.reflection_recognition

end SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs

namespace SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs

def splitLocalCheckedRecognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs
        Ax A B halign) :
    _root_.MiniHilbert.PASplitLocalCheckedRecognition
      h.formula_code_interpretation :=
  h.toCheckedEncoderRecognitionInputs.splitLocalCheckedRecognition

def toLocalCheckedRecognitionSplitInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadLocalCheckedRecognitionSplitInputs
      Ax A B halign :=
  h.toCheckedEncoderRecognitionInputs.toLocalCheckedRecognitionSplitInputs

end SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs

namespace SondowProjectLocalPudlakAuditedPayloadProofCodeCalibrationInputs

def splitLocalCheckedRecognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCalibrationInputs
        Ax A B halign) :
    _root_.MiniHilbert.PASplitLocalCheckedRecognition
      h.formula_code_interpretation :=
  h.toProofCodeCheckerRecognitionInputs.splitLocalCheckedRecognition

def toLocalCheckedRecognitionSplitInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCalibrationInputs
        Ax A B halign) :
    SondowProjectLocalPudlakAuditedPayloadLocalCheckedRecognitionSplitInputs
      Ax A B halign :=
  h.toProofCodeCheckerRecognitionInputs.toLocalCheckedRecognitionSplitInputs

end SondowProjectLocalPudlakAuditedPayloadProofCodeCalibrationInputs

/-- Final audited collision package.  This is the current smallest honest
frontier: project-local upper bound plus the three real Pudlak-side
calibrations. -/
structure SondowProjectLocalAuditedCollisionInputs where
  project_upper : SondowProjectLocalS21CollapseConclusion
  pudlak_side : SondowProjectLocalPudlakSideInputs

namespace SondowProjectLocalAuditedCollisionInputs

theorem not_rational
    (h : SondowProjectLocalAuditedCollisionInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.pudlak_side.collide h.project_upper

end SondowProjectLocalAuditedCollisionInputs

/-- Front-door theorem from a project-local verifier, payload truth, and the
audited Pudlak-side inputs.  This is intentionally explicit about payload truth:
truth is used only to build the project upper bound, not as a substitute for a
short proof of the Pudlak payload. -/
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak : SondowProjectLocalPudlakSideInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_conjunction
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak : SondowProjectLocalPudlakConjunctionInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_hilbert_two_step
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak : SondowProjectLocalPudlakHilbertTwoStepInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_hilbert_realization
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak : SondowProjectLocalPudlakHilbertRealizationInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_hilbert_formula_code
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakHilbertFormulaCodeInputs Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_default_hilbert_formula_code
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakDefaultHilbertFormulaCodeInputs Ax A B) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_hilbert_formula_code
    verifier htruth hpudlak

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_hilbert_interpretation
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakHilbertInterpretationInputs Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_hilbert_standard_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakHilbertStandardSemanticsInputs Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_accepted_formula_code
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAcceptedFormulaCodeInputs Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_accepted_family_exactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAcceptedFamilyExactnessInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_accepted_local_code_calibration
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAcceptedLocalCodeCalibrationInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_accepted_projection_calibration_local_code
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAcceptedProjectionCalibrationLocalCodeInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_payload_formula_code
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakPayloadFormulaCodeInputs Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_payload_family_exactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakPayloadFamilyExactnessInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_payload_local_code_calibration
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakPayloadLocalCodeCalibrationInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_payload_projection_calibration_local_code
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakPayloadProjectionCalibrationLocalCodeInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_audited_payload_code_semantics_local_code
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadCodeSemanticsLocalCodeInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_audited_payload_concrete_code_local_code
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadConcreteProofCodeLocalCodeInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_audited_payload_recognition_local_code
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadConcreteRecognitionLocalCodeInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_audited_payload_dual_recognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadDualRecognitionInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_audited_payload_checked_encoder_recognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_audited_payload_convention_equivalence
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_audited_payload_canonical_convention
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadCanonicalConventionInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_audited_payload_split_minChecked
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadSplitMinCheckedInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_audited_payload_source_calibration_split
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadSourceCalibrationSplitInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

set_option linter.style.longLine false in
theorem irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_audited_payload_canonical_minChecked_split
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadCanonicalMinCheckedSplitInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

theorem irrational_of_project_local_convention_certificate_split
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadConventionCertificateSplitInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

theorem irrational_of_project_local_partial_recognition_split
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadPartialRecognitionSplitInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

theorem irrational_of_project_local_localChecked_recognition_split
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadLocalCheckedRecognitionSplitInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  hpudlak.collide (verifier.toCollapseConclusion htruth)

theorem verifierAndPayloadTruth_nonempty_to_literature_pudlak_hilbert_two_step_collision
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak : SondowProjectLocalPudlakHilbertTwoStepInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_hilbert_two_step
      verifier htruth hpudlak

theorem verifierAndPayloadTruth_nonempty_to_literature_pudlak_hilbert_realization_collision
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak : SondowProjectLocalPudlakHilbertRealizationInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_hilbert_realization
      verifier htruth hpudlak

theorem verifierAndPayloadTruth_nonempty_to_literature_pudlak_hilbert_formula_code_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakHilbertFormulaCodeInputs Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_hilbert_formula_code
      verifier htruth hpudlak

theorem verifierAndPayloadTruth_nonempty_to_literature_pudlak_default_hilbert_formula_code_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakDefaultHilbertFormulaCodeInputs Ax A B) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  verifierAndPayloadTruth_nonempty_to_literature_pudlak_hilbert_formula_code_collision
    hupper hpudlak

theorem verifierAndPayloadTruth_nonempty_to_literature_pudlak_hilbert_interpretation_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakHilbertInterpretationInputs Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_hilbert_interpretation
      verifier htruth hpudlak

set_option linter.style.longLine false in
theorem verifierAndPayloadTruth_nonempty_to_literature_pudlak_hilbert_standard_semantics_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakHilbertStandardSemanticsInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_hilbert_standard_semantics
      verifier htruth hpudlak

theorem verifierAndPayloadTruth_nonempty_to_literature_pudlak_accepted_formula_code_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAcceptedFormulaCodeInputs Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_accepted_formula_code
      verifier htruth hpudlak

set_option linter.style.longLine false in
theorem verifierAndPayloadTruth_nonempty_to_literature_pudlak_accepted_family_exactness_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAcceptedFamilyExactnessInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_accepted_family_exactness
      verifier htruth hpudlak

set_option linter.style.longLine false in
theorem verifierAndPayloadTruth_nonempty_to_literature_pudlak_accepted_local_code_calibration_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAcceptedLocalCodeCalibrationInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_accepted_local_code_calibration
      verifier htruth hpudlak

theorem verifierAndPayloadTruth_nonempty_to_literature_pudlak_payload_formula_code_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakPayloadFormulaCodeInputs Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_payload_formula_code
      verifier htruth hpudlak

set_option linter.style.longLine false in
theorem verifierAndPayloadTruth_nonempty_to_literature_pudlak_payload_family_exactness_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakPayloadFamilyExactnessInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_payload_family_exactness
      verifier htruth hpudlak

set_option linter.style.longLine false in
theorem verifierAndPayloadTruth_nonempty_to_literature_pudlak_payload_local_code_calibration_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakPayloadLocalCodeCalibrationInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_payload_local_code_calibration
      verifier htruth hpudlak

set_option linter.style.longLine false in
theorem verifierAndPayloadTruth_nonempty_to_literature_pudlak_audited_payload_dual_recognition_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadDualRecognitionInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_audited_payload_dual_recognition
      verifier htruth hpudlak

set_option linter.style.longLine false in
theorem verifierAndPayloadTruth_nonempty_to_literature_pudlak_audited_payload_checked_encoder_recognition_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_audited_payload_checked_encoder_recognition
      verifier htruth hpudlak

set_option linter.style.longLine false in
theorem verifierAndPayloadTruth_nonempty_to_literature_pudlak_audited_payload_convention_equivalence_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_audited_payload_convention_equivalence
      verifier htruth hpudlak

set_option linter.style.longLine false in
theorem verifierAndPayloadTruth_nonempty_to_literature_pudlak_audited_payload_canonical_convention_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadCanonicalConventionInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_audited_payload_canonical_convention
      verifier htruth hpudlak

set_option linter.style.longLine false in
theorem verifierAndPayloadTruth_nonempty_to_literature_pudlak_audited_payload_split_minChecked_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadSplitMinCheckedInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_audited_payload_split_minChecked
      verifier htruth hpudlak

set_option linter.style.longLine false in
theorem verifierAndPayloadTruth_nonempty_to_literature_pudlak_audited_payload_source_calibration_split_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadSourceCalibrationSplitInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_audited_payload_source_calibration_split
      verifier htruth hpudlak

set_option linter.style.longLine false in
theorem verifierAndPayloadTruth_nonempty_to_literature_pudlak_audited_payload_canonical_minChecked_split_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadCanonicalMinCheckedSplitInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_verifier_payload_truth_and_literature_pudlak_audited_payload_canonical_minChecked_split
      verifier htruth hpudlak

theorem verifierAndPayloadTruth_nonempty_to_convention_certificate_split_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadConventionCertificateSplitInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_convention_certificate_split
      verifier htruth hpudlak

theorem verifierAndPayloadTruth_nonempty_to_partial_recognition_split_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadPartialRecognitionSplitInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_partial_recognition_split
      verifier htruth hpudlak

theorem verifierAndPayloadTruth_nonempty_to_localChecked_recognition_split_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakAuditedPayloadLocalCheckedRecognitionSplitInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact
    irrational_of_project_local_localChecked_recognition_split
      verifier htruth hpudlak

/-- Bottom-level Pudlak-side input.

This is the current narrow standard box for the lower-bound side.  It combines
exactly the three bottom certificates still needed for the project-local
collision:

* the literature Pudlak theorem 5 lower bound in rescaled form;
* the strengthened-to-partial proof-length family equations; and
* the PA/Hilbert two-family exactness for the partial-to-graft transfer. -/
structure SondowProjectLocalPudlakBottomFamilyExactnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_rescaled_lower_bound :
    _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate
  strengthened_family_lengths :
    SondowProjectLocalStrengthenedPayloadFamilyLengthInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  local_hilbert_family_exactness :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
      formula_code_interpretation

namespace SondowProjectLocalPudlakBottomFamilyExactnessInputs

def literatureLowerBoundCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomFamilyExactnessInputs
        Ax A B halign) :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate :=
  h.literature_rescaled_lower_bound.toPowerBoundCertificate

def strengthenedToPartialTransfer
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomFamilyExactnessInputs
        Ax A B halign) :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer :=
  h.strengthened_family_lengths.strengthenedToPartialTransfer

def partialToGraftTransfer
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomFamilyExactnessInputs
        Ax A B halign) :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer :=
  h.local_hilbert_family_exactness.toStrongLowerBoundTransfer

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomFamilyExactnessInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs where
  literature_lower_bound := h.literatureLowerBoundCertificate
  strengthened_to_partial := h.strengthenedToPartialTransfer
  partial_to_graft := h.partialToGraftTransfer

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomFamilyExactnessInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakBottomFamilyExactnessInputs

/-- Split-minChecked version of the bottom-level Pudlak-side input.

This is friendlier for construction: the PA/Hilbert calibration is supplied as
two independent minChecked exactness certificates. -/
structure SondowProjectLocalPudlakBottomSplitMinCheckedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_rescaled_lower_bound :
    _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate
  strengthened_family_lengths :
    SondowProjectLocalStrengthenedPayloadFamilyLengthInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  partial_minChecked_exactness :
    _root_.MiniHilbert.PAHilbertPartialConsistencyMinCheckedExactness
      formula_code_interpretation
  reflection_minChecked_exactness :
    _root_.MiniHilbert.PAHilbertReflectionGraftMinCheckedExactness
      formula_code_interpretation

namespace SondowProjectLocalPudlakBottomSplitMinCheckedInputs

def familyExactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomSplitMinCheckedInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
      h.formula_code_interpretation :=
  _root_.MiniHilbert.PAHilbertProjectionFamilyExactness.ofMinCheckedExactness
    h.partial_minChecked_exactness h.reflection_minChecked_exactness

def toBottomFamilyExactnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomSplitMinCheckedInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomFamilyExactnessInputs
      Ax A B halign where
  literature_rescaled_lower_bound := h.literature_rescaled_lower_bound
  strengthened_family_lengths := h.strengthened_family_lengths
  formula_code_interpretation := h.formula_code_interpretation
  local_hilbert_family_exactness := h.familyExactness

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomSplitMinCheckedInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toBottomFamilyExactnessInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomSplitMinCheckedInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakBottomSplitMinCheckedInputs

/-- Bottom split-minChecked input where the Pudlak theorem 5 lower bound is
supplied in the project-facing rescaled form: scale data plus the rescaled
external lower-bound theorem. -/
structure SondowProjectLocalPudlakBottomRescaledTheorem5SplitMinCheckedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_rescaled_lower_bound :
    SondowProjectLocalPudlakTheorem5RescaledLowerBoundInputs
  strengthened_family_lengths :
    SondowProjectLocalStrengthenedPayloadFamilyLengthInputs
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  partial_minChecked_exactness :
    _root_.MiniHilbert.PAHilbertPartialConsistencyMinCheckedExactness
      formula_code_interpretation
  reflection_minChecked_exactness :
    _root_.MiniHilbert.PAHilbertReflectionGraftMinCheckedExactness
      formula_code_interpretation

namespace SondowProjectLocalPudlakBottomRescaledTheorem5SplitMinCheckedInputs

def toBottomSplitMinCheckedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomRescaledTheorem5SplitMinCheckedInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomSplitMinCheckedInputs
      Ax A B halign where
  literature_rescaled_lower_bound :=
    h.literature_rescaled_lower_bound.toRescaledCertificate
  strengthened_family_lengths := h.strengthened_family_lengths
  formula_code_interpretation := h.formula_code_interpretation
  partial_minChecked_exactness := h.partial_minChecked_exactness
  reflection_minChecked_exactness := h.reflection_minChecked_exactness

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomRescaledTheorem5SplitMinCheckedInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toBottomSplitMinCheckedInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomRescaledTheorem5SplitMinCheckedInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakBottomRescaledTheorem5SplitMinCheckedInputs

/-- Bottom input with both proof-length calibration obligations stated at the
concrete code-semantics level.

This is the interface-level target when Pudlak theorem 5 is accepted as an
external literature certificate: the remaining PA/Hilbert and
strengthened-to-partial obligations are exactly `ProofLengthCodeSemantics`
calibrations. -/
structure SondowProjectLocalPudlakBottomRescaledTheorem5CalibratedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  literature_rescaled_lower_bound :
    SondowProjectLocalPudlakTheorem5RescaledLowerBoundInputs
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  strengthened_fallback : _root_.FormulaCode → ℕ
  strengthened_code_calibration :
    (_root_.strengthenedToPartialProofLengthCodeSemantics
      strengthened_fallback).Calibration
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  local_hilbert_fallback : _root_.FormulaCode → ℕ
  local_hilbert_code_calibration :
    (formula_code_interpretation.localHilbertProofLengthCodeSemantics
      local_hilbert_fallback).Calibration

namespace SondowProjectLocalPudlakBottomRescaledTheorem5CalibratedInputs

def strengthenedFamilyLengths
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomRescaledTheorem5CalibratedInputs
        Ax A B halign) :
    SondowProjectLocalStrengthenedPayloadFamilyLengthInputs :=
  SondowProjectLocalStrengthenedPayloadFamilyLengthInputs.ofProofLengthCodeCalibration
    h.strengthened_payload_truth h.strengthened_fallback
    h.strengthened_code_calibration

def localHilbertFamilyExactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomRescaledTheorem5CalibratedInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
      h.formula_code_interpretation :=
  let interp := h.formula_code_interpretation
  let hiff :=
    interp.localHilbertProofLengthCodeCalibration_iff_familyExactness
      h.local_hilbert_fallback
  hiff.1 h.local_hilbert_code_calibration

def toBottomFamilyExactnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomRescaledTheorem5CalibratedInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomFamilyExactnessInputs
      Ax A B halign where
  literature_rescaled_lower_bound :=
    h.literature_rescaled_lower_bound.toRescaledCertificate
  strengthened_family_lengths := h.strengthenedFamilyLengths
  formula_code_interpretation := h.formula_code_interpretation
  local_hilbert_family_exactness := h.localHilbertFamilyExactness

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomRescaledTheorem5CalibratedInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toBottomFamilyExactnessInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomRescaledTheorem5CalibratedInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakBottomRescaledTheorem5CalibratedInputs

/-- Bottom input with the theorem-5 witness fixed to the external literature
certificate and the two proof-length calibrations replaced by recognition
certificates.

For the local Hilbert side this is already split into checker exactness and
encoder recognition by `PAHilbertLocalProofCodeRecognitionCertificate`.  For the
strengthened-to-partial side the corresponding remaining proof-system fact is
the concrete recognition theorem for the fixed checker
`strengthenedToPartialProofCodeSemantics`. -/
structure SondowProjectLocalPudlakBottomExternalTheorem5RecognitionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  strengthened_fallback : _root_.FormulaCode → ℕ
  strengthened_recognition :
    _root_.StrengthenedToPartialConcreteProofLengthRecognition
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  local_hilbert_fallback : _root_.FormulaCode → ℕ
  local_hilbert_recognition_certificate :
    _root_.MiniHilbert.PAHilbertLocalProofCodeRecognitionCertificate
      formula_code_interpretation

namespace SondowProjectLocalPudlakBottomExternalTheorem5RecognitionInputs

def strengthenedCodeCalibration
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5RecognitionInputs
        Ax A B halign) :
    (_root_.strengthenedToPartialProofLengthCodeSemantics
      h.strengthened_fallback).Calibration :=
  h.strengthened_recognition.toCalibration h.strengthened_fallback

def localHilbertProofCodeRecognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5RecognitionInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertLocalProofCodeRecognition
      h.formula_code_interpretation :=
  h.local_hilbert_recognition_certificate.toLocalProofCodeRecognition

def localHilbertCodeCalibration
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5RecognitionInputs
        Ax A B halign) :
    (h.formula_code_interpretation.localHilbertProofLengthCodeSemantics
      h.local_hilbert_fallback).Calibration :=
  h.localHilbertProofCodeRecognition.toProofLengthCodeCalibration
    h.local_hilbert_fallback

def toCalibratedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5RecognitionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomRescaledTheorem5CalibratedInputs
      Ax A B halign where
  literature_rescaled_lower_bound :=
    SondowProjectLocalPudlakTheorem5RescaledLowerBoundInputs.externalLiterature
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_fallback := h.strengthened_fallback
  strengthened_code_calibration := h.strengthenedCodeCalibration
  formula_code_interpretation := h.formula_code_interpretation
  local_hilbert_fallback := h.local_hilbert_fallback
  local_hilbert_code_calibration := h.localHilbertCodeCalibration

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5RecognitionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toCalibratedInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5RecognitionInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakBottomExternalTheorem5RecognitionInputs

/-- Canonical-convention version of the external-theorem-5 bottom input.

This is the aligned interface with the local Hilbert side: the strengthened
checker proof is no longer a monolithic recognition theorem, but a certificate
made of a PA proof-length convention and the canonical checker exactness for
the fixed strengthened-to-partial checker. -/
structure SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  strengthened_recognition_certificate :
    _root_.StrengthenedToPartialCanonicalRecognitionCertificate
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  local_hilbert_fallback : _root_.FormulaCode → ℕ
  local_hilbert_recognition_certificate :
    _root_.MiniHilbert.PAHilbertLocalProofCodeRecognitionCertificate
      formula_code_interpretation

namespace SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs

def toRecognitionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExternalTheorem5RecognitionInputs
      Ax A B halign where
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_fallback :=
    h.strengthened_recognition_certificate.convention.fallback
  strengthened_recognition :=
    h.strengthened_recognition_certificate.toConcreteRecognition
  formula_code_interpretation := h.formula_code_interpretation
  local_hilbert_fallback := h.local_hilbert_fallback
  local_hilbert_recognition_certificate :=
    h.local_hilbert_recognition_certificate

def toCalibratedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomRescaledTheorem5CalibratedInputs
      Ax A B halign :=
  h.toRecognitionInputs.toCalibratedInputs

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toRecognitionInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs

/-- Fully canonical bottom input.

Both remaining proof-length bridges are now stated as convention certificates:
the strengthened checker uses its canonical checker exactness plus a PA
proof-length convention, and the local Hilbert checker uses local checker
exactness plus a project checked-code convention/encoder-equivalence
certificate. -/
structure SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  strengthened_recognition_certificate :
    _root_.StrengthenedToPartialCanonicalRecognitionCertificate
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  local_hilbert_fallback : _root_.FormulaCode → ℕ
  local_hilbert_convention_certificate :
    _root_.MiniHilbert.PAHilbertLocalProofCodeConventionCertificate
      formula_code_interpretation

namespace SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs

def toCanonicalInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
      Ax A B halign where
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_recognition_certificate :=
    h.strengthened_recognition_certificate
  formula_code_interpretation := h.formula_code_interpretation
  local_hilbert_fallback := h.local_hilbert_fallback
  local_hilbert_recognition_certificate :=
    h.local_hilbert_convention_certificate.toRecognitionCertificate

def toRecognitionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExternalTheorem5RecognitionInputs
      Ax A B halign :=
  h.toCanonicalInputs.toRecognitionInputs

def toCalibratedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomRescaledTheorem5CalibratedInputs
      Ax A B halign :=
  h.toCanonicalInputs.toCalibratedInputs

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toCanonicalInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs

/-- External-theorem-5 bottom input with the strengthened side reduced to the
two exact family-length equations and the local Hilbert side kept as a local
proof-code convention certificate. -/
structure SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  strengthened_exact_lengths :
    _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  local_hilbert_fallback : _root_.FormulaCode → ℕ
  local_hilbert_convention_certificate :
    _root_.MiniHilbert.PAHilbertLocalProofCodeConventionCertificate
      formula_code_interpretation

namespace SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs

def strengthenedRecognitionCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    _root_.StrengthenedToPartialCanonicalRecognitionCertificate :=
  h.strengthened_exact_lengths.toCanonicalRecognitionCertificate (fun _ => 0)

def toConventionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
      Ax A B halign where
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_recognition_certificate := h.strengthenedRecognitionCertificate
  formula_code_interpretation := h.formula_code_interpretation
  local_hilbert_fallback := h.local_hilbert_fallback
  local_hilbert_convention_certificate :=
    h.local_hilbert_convention_certificate

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toConventionInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs

/-- External-theorem-5 bottom input with both proof-length obligations exposed
as family exactness statements.  The strengthened side is the two exact
`proof_length = n` equations; the local Hilbert side is the projection-family
exactness certificate, converted internally to the local proof-code convention
certificate. -/
structure SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  strengthened_exact_lengths :
    _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  local_hilbert_family_exactness :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
      formula_code_interpretation

/-- Final project-facing bottom input after accepting the explicit external
proof-length conventions.

The theorem-5 lower bound, strengthened proof-length convention, and local
Hilbert proof-length convention are all fixed by named external witnesses.  The
remaining project data is the strengthened payload truth and the local formula
code interpretation. -/
structure SondowProjectLocalPudlakBottomExternalConventionWitnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign

namespace SondowProjectLocalPudlakBottomExternalConventionWitnessInputs

def toConventionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalConventionWitnessInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
      Ax A B halign where
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_recognition_certificate :=
    _root_.externalStrengthenedToPartialCanonicalRecognitionCertificate
  formula_code_interpretation := h.formula_code_interpretation
  local_hilbert_fallback := fun _ => 0
  local_hilbert_convention_certificate :=
    _root_.MiniHilbert.externalPAHilbertLocalProofCodeConventionCertificate
      h.formula_code_interpretation

def toCanonicalInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalConventionWitnessInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
      Ax A B halign :=
  h.toConventionInputs.toCanonicalInputs

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalConventionWitnessInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toConventionInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalConventionWitnessInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakBottomExternalConventionWitnessInputs

/-- Semantic-internalization version of the final bottom input.

This is the next step toward internalizing the two proof-length conventions:
instead of using the named external convention witnesses, it asks directly for
project proof-length semantics for the strengthened checker and the local
Hilbert checked-code length. -/
structure SondowProjectLocalPudlakBottomSemanticConventionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  strengthened_project_semantics :
    _root_.ProjectProofLengthSemantics
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      (_root_.strengthenedToPartialProofLengthCodeSemantics
        (fun _ => 0)).length
      _root_.StrengthenedToPartialRelevantCode
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  local_hilbert_project_semantics :
    _root_.ProjectProofLengthSemantics
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      formula_code_interpretation.localCheckedCodeProofLength
      _root_.MiniHilbert.FormulaCodeHilbertRelevantCode

namespace SondowProjectLocalPudlakBottomSemanticConventionInputs

def strengthenedRecognitionCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomSemanticConventionInputs
        Ax A B halign) :
    _root_.StrengthenedToPartialCanonicalRecognitionCertificate :=
  _root_.StrengthenedToPartialCanonicalRecognitionCertificate.ofProjectProofLengthSemantics
    (fun _ => 0) h.strengthened_project_semantics

def localHilbertConventionCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomSemanticConventionInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertLocalProofCodeConventionCertificate
      h.formula_code_interpretation :=
  open _root_.MiniHilbert in
  PAHilbertLocalProofCodeConventionCertificate.ofLocalCheckedProjectProofLengthSemantics
    h.formula_code_interpretation h.local_hilbert_project_semantics

def toConventionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomSemanticConventionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
      Ax A B halign where
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_recognition_certificate :=
    h.strengthenedRecognitionCertificate
  formula_code_interpretation := h.formula_code_interpretation
  local_hilbert_fallback := fun _ => 0
  local_hilbert_convention_certificate :=
    h.localHilbertConventionCertificate

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomSemanticConventionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toConventionInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomSemanticConventionInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

end SondowProjectLocalPudlakBottomSemanticConventionInputs

/-- Family-witness version of the semantic bottom input.

This is the narrowest project-facing proof-length interface in this file: the
two abstract `ProjectProofLengthSemantics` witnesses are replaced by their
auditable family equalities. -/
structure SondowProjectLocalPudlakBottomFamilyWitnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  strengthened_family_witness :
    _root_.StrengthenedToPartialProjectProofLengthFamilyWitness (fun _ => 0)
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  local_hilbert_family_exactness :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
      formula_code_interpretation

namespace SondowProjectLocalPudlakBottomFamilyWitnessInputs

def toSemanticConventionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomFamilyWitnessInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomSemanticConventionInputs
      Ax A B halign where
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_project_semantics :=
    h.strengthened_family_witness.toProjectProofLengthSemantics
  formula_code_interpretation := h.formula_code_interpretation
  local_hilbert_project_semantics :=
    h.local_hilbert_family_exactness
      |>.to_projectCheckedCodeProofLengthSemantics

def toConventionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomFamilyWitnessInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
      Ax A B halign :=
  h.toSemanticConventionInputs.toConventionInputs

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomFamilyWitnessInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toSemanticConventionInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomFamilyWitnessInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toSemanticConventionInputs.collide hupper

end SondowProjectLocalPudlakBottomFamilyWitnessInputs

/-- Bottom family-witness input with the strengthened side supplied as the two
exact `proof_length = n` family equations. -/
structure SondowProjectLocalPudlakBottomExactStrengthenedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  strengthened_exact_lengths :
    _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  local_hilbert_family_exactness :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
      formula_code_interpretation

namespace SondowProjectLocalPudlakBottomExactStrengthenedInputs

def strengthenedFamilyWitness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactStrengthenedInputs
        Ax A B halign) :
    _root_.StrengthenedToPartialProjectProofLengthFamilyWitness (fun _ => 0) :=
  h.strengthened_exact_lengths.toFamilyWitness (fun _ => 0)

def toFamilyWitnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactStrengthenedInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomFamilyWitnessInputs
      Ax A B halign where
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_family_witness := h.strengthenedFamilyWitness
  formula_code_interpretation := h.formula_code_interpretation
  local_hilbert_family_exactness := h.local_hilbert_family_exactness

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactStrengthenedInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toFamilyWitnessInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactStrengthenedInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toFamilyWitnessInputs.collide hupper

end SondowProjectLocalPudlakBottomExactStrengthenedInputs

/-- Split version of the family-witness input: strengthened is supplied by the
two exact family equations, and local Hilbert is supplied by the two minChecked
exactness certificates. -/
structure SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  strengthened_exact_lengths :
    _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths
  formula_code_interpretation :
    _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  partial_minChecked_exactness :
    _root_.MiniHilbert.PAHilbertPartialConsistencyMinCheckedExactness
      formula_code_interpretation
  reflection_minChecked_exactness :
    _root_.MiniHilbert.PAHilbertReflectionGraftMinCheckedExactness
      formula_code_interpretation

namespace SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs

def localHilbertFamilyExactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
      h.formula_code_interpretation :=
  _root_.MiniHilbert.PAHilbertProjectionFamilyExactness.ofMinCheckedExactness
    h.partial_minChecked_exactness h.reflection_minChecked_exactness

def toExactStrengthenedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExactStrengthenedInputs
      Ax A B halign where
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_exact_lengths := h.strengthened_exact_lengths
  formula_code_interpretation := h.formula_code_interpretation
  local_hilbert_family_exactness := h.localHilbertFamilyExactness

def toFamilyWitnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomFamilyWitnessInputs
      Ax A B halign :=
  h.toExactStrengthenedInputs.toFamilyWitnessInputs

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toFamilyWitnessInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toFamilyWitnessInputs.collide hupper

end SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs

namespace SondowProjectLocalPudlakBottomFamilyWitnessInputs

def toExactSplitMinCheckedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomFamilyWitnessInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
      Ax A B halign where
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_exact_lengths :=
    h.strengthened_family_witness.toExactFamilyLengths
  formula_code_interpretation := h.formula_code_interpretation
  partial_minChecked_exactness :=
    h.local_hilbert_family_exactness.toPartialConsistencyMinCheckedExactness
  reflection_minChecked_exactness :=
    h.local_hilbert_family_exactness.toReflectionGraftMinCheckedExactness

theorem nonempty_iff_exactSplitMinCheckedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.toExactSplitMinCheckedInputs⟩
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.toFamilyWitnessInputs⟩

end SondowProjectLocalPudlakBottomFamilyWitnessInputs

namespace SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs

def localHilbertConventionCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertLocalProofCodeConventionCertificate
      h.formula_code_interpretation :=
  h.local_hilbert_family_exactness.toLocalProofCodeConventionCertificate

theorem localHilbertConventionCertificate_partialConsistency_exact
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (m : ℕ) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.partialConsistencyCode m) =
      h.formula_code_interpretation.target_proof_family.rightConjElim.minCheckedCodeSize m :=
  h.localHilbertConventionCertificate.toFamilyExactness
    |>.partialConsistency_exact m

theorem localHilbertConventionCertificate_reflectionGraft_exact
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (m : ℕ) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.sondowReflectionGraftCode m) =
      h.formula_code_interpretation.target_proof_family.minCheckedCodeSize m :=
  h.localHilbertConventionCertificate.toFamilyExactness
    |>.reflectionGraft_exact m

def toExactSplitMinCheckedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
      Ax A B halign where
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_exact_lengths := h.strengthened_exact_lengths
  formula_code_interpretation := h.formula_code_interpretation
  partial_minChecked_exactness :=
    h.local_hilbert_family_exactness.toPartialConsistencyMinCheckedExactness
  reflection_minChecked_exactness :=
    h.local_hilbert_family_exactness.toReflectionGraftMinCheckedExactness

def toExactConventionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
      Ax A B halign where
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_exact_lengths := h.strengthened_exact_lengths
  formula_code_interpretation := h.formula_code_interpretation
  local_hilbert_fallback := fun _ => 0
  local_hilbert_convention_certificate :=
    h.localHilbertConventionCertificate

def toPudlakSideInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    SondowProjectLocalPudlakSideInputs :=
  h.toExactConventionInputs.toPudlakSideInputs

theorem collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toPudlakSideInputs.collide hupper

theorem toExactSplitMinCheckedInputs_collide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toExactSplitMinCheckedInputs.collide hupper

theorem toExactSplitMinCheckedInputs_lowerBoundPackage_scale_eq_id
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    h.toPudlakSideInputs.lowerBoundPackage.scale = id := by
  rfl

theorem toExactSplitMinCheckedInputs_lowerBoundPackage_rescaledCode_eq_partialConsistencyCode
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (m : ℕ) :
    _root_.rescaledPartialConsistencyCode
        h.toPudlakSideInputs.lowerBoundPackage.scale m =
      _root_.partialConsistencyCode m := by
  rfl

end SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs

namespace SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs

def toExactFamilyExactnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
      Ax A B halign where
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_exact_lengths :=
    h.strengthened_exact_lengths
  formula_code_interpretation := h.formula_code_interpretation
  local_hilbert_family_exactness :=
    h.local_hilbert_convention_certificate.toFamilyExactness

end SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs

theorem exactConventionInputs_nonempty_iff_externalTheorem5ExactFamilyExactnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.toExactFamilyExactnessInputs⟩
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.toExactConventionInputs⟩

theorem externalTheorem5ExactFamilyExactnessInputs_nonempty_iff_exactConventionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) :=
  exactConventionInputs_nonempty_iff_externalTheorem5ExactFamilyExactnessInputs.symm

namespace SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs

theorem lowerBoundPackage_scale_eq_id
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    h.toPudlakSideInputs.lowerBoundPackage.scale = id := by
  rfl

theorem lowerBoundPackage_rescaledCode_eq_partialConsistencyCode
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (m : ℕ) :
    _root_.rescaledPartialConsistencyCode
        h.toPudlakSideInputs.lowerBoundPackage.scale m =
      _root_.partialConsistencyCode m := by
  rfl

theorem normalForm_code_eq_rescaledPudlak
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (m : ℕ) :
    (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
        h.toPudlakSideInputs.strengthened_to_partial).code m =
      _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
        h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m :=
  h.toPudlakSideInputs.lowerBoundPackage_normalForm_code_eq_rescaledPudlak m

theorem collide_exactConvention
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.collide hupper

theorem localHilbertConventionCertificate_partialConsistency_exact
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (m : ℕ) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.partialConsistencyCode m) =
      h.formula_code_interpretation.target_proof_family.rightConjElim.minCheckedCodeSize m :=
  h.local_hilbert_convention_certificate.toFamilyExactness
    |>.partialConsistency_exact m

theorem localHilbertConventionCertificate_reflectionGraft_exact
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (m : ℕ) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.sondowReflectionGraftCode m) =
      h.formula_code_interpretation.target_proof_family.minCheckedCodeSize m :=
  h.local_hilbert_convention_certificate.toFamilyExactness
    |>.reflectionGraft_exact m

theorem strengthenedRecognitionCertificate_strengthened_length_exact
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (m : ℕ) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.strengthenedPartialConsistencyCode m) = m :=
  h.strengthened_exact_lengths
    |>.strengthened_length_exact m

theorem strengthenedRecognitionCertificate_partial_length_exact
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (m : ℕ) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.partialConsistencyCode m) = m :=
  h.strengthened_exact_lengths
    |>.partial_length_exact m

end SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs

theorem exactConventionInputs_collision_iff_externalTheorem5ExactFamilyExactnessInputs_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (_hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ↔
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) := by
  constructor
  · intro hcollision hexact
    exact hcollision
      ((exactConventionInputs_nonempty_iff_externalTheorem5ExactFamilyExactnessInputs).2
        hexact)
  · intro hcollision hconv
    exact hcollision
      ((exactConventionInputs_nonempty_iff_externalTheorem5ExactFamilyExactnessInputs).1
        hconv)

namespace SondowProjectLocalPudlakBottomFamilyWitnessInputs

def toExternalTheorem5ExactFamilyExactnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomFamilyWitnessInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
      Ax A B halign where
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_exact_lengths :=
    h.strengthened_family_witness.toExactFamilyLengths
  formula_code_interpretation := h.formula_code_interpretation
  local_hilbert_family_exactness := h.local_hilbert_family_exactness

theorem lowerBoundPackage_scale_eq_id
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomFamilyWitnessInputs
        Ax A B halign) :
    h.toPudlakSideInputs.lowerBoundPackage.scale = id := by
  rfl

theorem lowerBoundPackage_rescaledCode_eq_partialConsistencyCode
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomFamilyWitnessInputs
        Ax A B halign)
    (m : ℕ) :
    _root_.rescaledPartialConsistencyCode
        h.toPudlakSideInputs.lowerBoundPackage.scale m =
      _root_.partialConsistencyCode m := by
  rfl

end SondowProjectLocalPudlakBottomFamilyWitnessInputs

namespace SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs

def toFamilyWitnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomFamilyWitnessInputs
      Ax A B halign :=
  h.toExactSplitMinCheckedInputs.toFamilyWitnessInputs

end SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs

theorem externalTheorem5ExactFamilyExactnessInputs_nonempty_iff_familyWitnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign) := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.toFamilyWitnessInputs⟩
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.toExternalTheorem5ExactFamilyExactnessInputs⟩

theorem familyWitnessInputs_nonempty_iff_externalTheorem5ExactFamilyExactnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) :=
  externalTheorem5ExactFamilyExactnessInputs_nonempty_iff_familyWitnessInputs.symm

theorem externalTheorem5ExactFamilyExactnessInputs_collision_iff_familyWitnessInputs_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (_hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ↔
    (Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) := by
  constructor
  · intro hcollision hfamily
    exact hcollision
      ((externalTheorem5ExactFamilyExactnessInputs_nonempty_iff_familyWitnessInputs).2
        hfamily)
  · intro hcollision hexternal
    exact hcollision
      ((externalTheorem5ExactFamilyExactnessInputs_nonempty_iff_familyWitnessInputs).1
        hexternal)

namespace SondowProjectLocalPudlakBottomExactStrengthenedInputs

def toExternalTheorem5ExactFamilyExactnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactStrengthenedInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
      Ax A B halign where
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_exact_lengths := h.strengthened_exact_lengths
  formula_code_interpretation := h.formula_code_interpretation
  local_hilbert_family_exactness := h.local_hilbert_family_exactness

theorem lowerBoundPackage_scale_eq_id
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactStrengthenedInputs
        Ax A B halign) :
    h.toPudlakSideInputs.lowerBoundPackage.scale = id := by
  rfl

theorem lowerBoundPackage_rescaledCode_eq_partialConsistencyCode
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactStrengthenedInputs
        Ax A B halign)
    (m : ℕ) :
    _root_.rescaledPartialConsistencyCode
        h.toPudlakSideInputs.lowerBoundPackage.scale m =
      _root_.partialConsistencyCode m := by
  rfl

end SondowProjectLocalPudlakBottomExactStrengthenedInputs

namespace SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs

def toExactStrengthenedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExactStrengthenedInputs
      Ax A B halign where
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_exact_lengths := h.strengthened_exact_lengths
  formula_code_interpretation := h.formula_code_interpretation
  local_hilbert_family_exactness := h.local_hilbert_family_exactness

end SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs

theorem externalTheorem5ExactFamilyExactnessInputs_nonempty_iff_exactStrengthenedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign) := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.toExactStrengthenedInputs⟩
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.toExternalTheorem5ExactFamilyExactnessInputs⟩

theorem exactStrengthenedInputs_nonempty_iff_externalTheorem5ExactFamilyExactnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) :=
  externalTheorem5ExactFamilyExactnessInputs_nonempty_iff_exactStrengthenedInputs.symm

theorem externalTheorem5ExactFamilyExactnessInputs_collision_iff_exactStrengthenedInputs_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (_hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ↔
    (Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) := by
  constructor
  · intro hcollision hexact
    exact hcollision
      ((externalTheorem5ExactFamilyExactnessInputs_nonempty_iff_exactStrengthenedInputs).2
        hexact)
  · intro hcollision hexternal
    exact hcollision
      ((externalTheorem5ExactFamilyExactnessInputs_nonempty_iff_exactStrengthenedInputs).1
        hexternal)

theorem irrational_of_externalTheorem5_exactFamilyExactness_and_upper
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.collide hupper

theorem irrational_of_externalTheorem5_splitMinChecked_and_upper
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.collide hupper

theorem irrational_of_externalTheorem5_familyWitness_and_upper
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomFamilyWitnessInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.collide hupper

theorem irrational_of_externalTheorem5_exactStrengthened_and_upper
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactStrengthenedInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.collide hupper

theorem irrational_of_externalTheorem5_exactConvention_and_upper
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.collide hupper

namespace SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs

def toExternalTheorem5ExactFamilyExactnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
      Ax A B halign where
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_exact_lengths := h.strengthened_exact_lengths
  formula_code_interpretation := h.formula_code_interpretation
  local_hilbert_family_exactness := h.localHilbertFamilyExactness

theorem lowerBoundPackage_scale_eq_id
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    h.toPudlakSideInputs.lowerBoundPackage.scale = id := by
  rfl

theorem lowerBoundPackage_rescaledCode_eq_partialConsistencyCode
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (m : ℕ) :
    _root_.rescaledPartialConsistencyCode
        h.toPudlakSideInputs.lowerBoundPackage.scale m =
      _root_.partialConsistencyCode m := by
  rfl

theorem normalForm_code_eq_rescaledPudlak
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (m : ℕ) :
    (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
        h.toPudlakSideInputs.strengthened_to_partial).code m =
      _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
        h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m :=
  h.toPudlakSideInputs.lowerBoundPackage_normalForm_code_eq_rescaledPudlak m

end SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs

namespace SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs

def toExactSplitMinCheckedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
      Ax A B halign :=
  h.toExactFamilyExactnessInputs.toExactSplitMinCheckedInputs

def toFamilyWitnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomFamilyWitnessInputs
      Ax A B halign :=
  h.toExactFamilyExactnessInputs.toFamilyWitnessInputs

end SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs

namespace SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs

def toExactConventionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
      Ax A B halign :=
  h.toExternalTheorem5ExactFamilyExactnessInputs.toExactConventionInputs

end SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs

theorem externalTheorem5ExactFamilyExactnessInputs_nonempty_iff_exactSplitMinCheckedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.toExactSplitMinCheckedInputs⟩
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.toExternalTheorem5ExactFamilyExactnessInputs⟩

theorem exactSplitMinCheckedInputs_nonempty_iff_externalTheorem5ExactFamilyExactnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) :=
  externalTheorem5ExactFamilyExactnessInputs_nonempty_iff_exactSplitMinCheckedInputs.symm

set_option linter.style.longLine false in
theorem externalTheorem5ExactFamilyExactnessInputs_collision_iff_exactSplitMinCheckedInputs_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (_hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ↔
    (Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) := by
  constructor
  · intro hcollision hsplit
    exact hcollision
      ((externalTheorem5ExactFamilyExactnessInputs_nonempty_iff_exactSplitMinCheckedInputs).2
        hsplit)
  · intro hcollision hexternal
    exact hcollision
      ((externalTheorem5ExactFamilyExactnessInputs_nonempty_iff_exactSplitMinCheckedInputs).1
        hexternal)

theorem exactConventionInputs_nonempty_iff_exactSplitMinCheckedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) :=
  exactConventionInputs_nonempty_iff_externalTheorem5ExactFamilyExactnessInputs.trans
    externalTheorem5ExactFamilyExactnessInputs_nonempty_iff_exactSplitMinCheckedInputs

theorem exactSplitMinCheckedInputs_nonempty_iff_exactConventionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) :=
  exactConventionInputs_nonempty_iff_exactSplitMinCheckedInputs.symm

theorem exactConventionInputs_collision_iff_exactSplitMinCheckedInputs_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (_hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ↔
    (Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) := by
  constructor
  · intro hcollision hsplit
    exact hcollision
      ((exactConventionInputs_nonempty_iff_exactSplitMinCheckedInputs).2
        hsplit)
  · intro hcollision hconv
    exact hcollision
      ((exactConventionInputs_nonempty_iff_exactSplitMinCheckedInputs).1
        hconv)

theorem exactConventionInputs_nonempty_iff_familyWitnessInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign) :=
  exactConventionInputs_nonempty_iff_externalTheorem5ExactFamilyExactnessInputs.trans
    externalTheorem5ExactFamilyExactnessInputs_nonempty_iff_familyWitnessInputs

theorem familyWitnessInputs_nonempty_iff_exactConventionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) :=
  exactConventionInputs_nonempty_iff_familyWitnessInputs.symm

theorem exactConventionInputs_collision_iff_familyWitnessInputs_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (_hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ↔
    (Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) := by
  constructor
  · intro hcollision hfamily
    exact hcollision
      ((exactConventionInputs_nonempty_iff_familyWitnessInputs).2
        hfamily)
  · intro hcollision hconv
    exact hcollision
      ((exactConventionInputs_nonempty_iff_familyWitnessInputs).1
        hconv)

theorem exactConventionInputs_nonempty_iff_exactStrengthenedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign) :=
  exactConventionInputs_nonempty_iff_externalTheorem5ExactFamilyExactnessInputs.trans
    externalTheorem5ExactFamilyExactnessInputs_nonempty_iff_exactStrengthenedInputs

theorem exactStrengthenedInputs_nonempty_iff_exactConventionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) :=
  exactConventionInputs_nonempty_iff_exactStrengthenedInputs.symm

theorem exactConventionInputs_collision_iff_exactStrengthenedInputs_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (_hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ↔
    (Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) := by
  constructor
  · intro hcollision hexact
    exact hcollision
      ((exactConventionInputs_nonempty_iff_exactStrengthenedInputs).2
        hexact)
  · intro hcollision hconv
    exact hcollision
      ((exactConventionInputs_nonempty_iff_exactStrengthenedInputs).1
        hconv)

/-- Short audit name: exact convention (precise proof-code convention)
`<=>` exact family exactness.  This is only an alias of the longer bridge
statement, so it adds no assumptions and does not weaken the endpoint. -/
theorem audit_exactConvention_iff_exactFamilyExactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) :=
  exactConventionInputs_nonempty_iff_externalTheorem5ExactFamilyExactnessInputs

/-- Short audit name: exact family exactness `<=>` exact convention. -/
theorem audit_exactFamilyExactness_iff_exactConvention
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) :=
  audit_exactConvention_iff_exactFamilyExactness.symm

/-- Short audit name: exact family exactness `<=>` split minChecked exactness. -/
theorem audit_exactFamilyExactness_iff_splitMinChecked
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) :=
  externalTheorem5ExactFamilyExactnessInputs_nonempty_iff_exactSplitMinCheckedInputs

/-- Short audit name: split minChecked exactness `<=>` exact family exactness. -/
theorem audit_splitMinChecked_iff_exactFamilyExactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) :=
  audit_exactFamilyExactness_iff_splitMinChecked.symm

/-- Short audit name: exact convention `<=>` split minChecked exactness. -/
theorem audit_exactConvention_iff_splitMinChecked
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) :=
  exactConventionInputs_nonempty_iff_exactSplitMinCheckedInputs

/-- Short audit name: split minChecked exactness `<=>` exact convention. -/
theorem audit_splitMinChecked_iff_exactConvention
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) :=
  audit_exactConvention_iff_splitMinChecked.symm

/-- Short audit name: exact convention collision endpoint `<=>` exact family
exactness collision endpoint.  This is an alias of the long bridge theorem. -/
theorem audit_exactConvention_collision_iff_exactFamilyExactness_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ↔
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) :=
  exactConventionInputs_collision_iff_externalTheorem5ExactFamilyExactnessInputs_collision
    hupper

/-- Short audit name: exact family exactness collision endpoint `<=>` exact
convention collision endpoint. -/
theorem audit_exactFamilyExactness_collision_iff_exactConvention_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ↔
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) :=
  (audit_exactConvention_collision_iff_exactFamilyExactness_collision
    hupper).symm

/-- Short audit name: exact family exactness collision endpoint `<=>` split
minChecked collision endpoint. -/
theorem audit_exactFamilyExactness_collision_iff_splitMinChecked_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ↔
    (Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) :=
  externalTheorem5ExactFamilyExactnessInputs_collision_iff_exactSplitMinCheckedInputs_collision
    hupper

/-- Short audit name: split minChecked collision endpoint `<=>` exact family
exactness collision endpoint. -/
theorem audit_splitMinChecked_collision_iff_exactFamilyExactness_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ↔
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) :=
  (audit_exactFamilyExactness_collision_iff_splitMinChecked_collision
    hupper).symm

/-- Short audit name: exact convention collision endpoint `<=>` split
minChecked collision endpoint. -/
theorem audit_exactConvention_collision_iff_splitMinChecked_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ↔
    (Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) :=
  exactConventionInputs_collision_iff_exactSplitMinCheckedInputs_collision
    hupper

/-- Short audit name: split minChecked collision endpoint `<=>` exact
convention collision endpoint. -/
theorem audit_splitMinChecked_collision_iff_exactConvention_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ↔
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) :=
  (audit_exactConvention_collision_iff_splitMinChecked_collision
    hupper).symm

/-- Project-facing endpoint audit name for the exact convention theorem-5
bottom input plus the S21 upper-side collapse. -/
theorem audit_theorem5_exactConvention_endpoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  irrational_of_externalTheorem5_exactConvention_and_upper h hupper

/-- Project-facing endpoint audit name for the split minChecked theorem-5 bottom
input plus the S21 upper-side collapse. -/
theorem audit_theorem5_splitMinChecked_endpoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  irrational_of_externalTheorem5_splitMinChecked_and_upper h hupper

/-- Project-facing endpoint audit name for the exact family exactness theorem-5
bottom input plus the S21 upper-side collapse. -/
theorem audit_theorem5_exactFamilyExactness_endpoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  irrational_of_externalTheorem5_exactFamilyExactness_and_upper h hupper

/-- Project-facing code round-trip audit for the exact convention bottom
input: scale is identity, the rescaled partial-consistency code is the concrete
partial-consistency code, and the theorem-5 normal form keeps the rescaled
Pudlak code. -/
theorem audit_theorem5_exactConvention_codeRoundTrip
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) := by
  exact ⟨h.lowerBoundPackage_scale_eq_id,
    fun m => h.lowerBoundPackage_rescaledCode_eq_partialConsistencyCode m,
    fun m => h.normalForm_code_eq_rescaledPudlak m⟩

/-- Project-facing code round-trip audit for the split minChecked bottom input. -/
theorem audit_theorem5_splitMinChecked_codeRoundTrip
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) := by
  exact ⟨h.lowerBoundPackage_scale_eq_id,
    fun m => h.lowerBoundPackage_rescaledCode_eq_partialConsistencyCode m,
    fun m => h.normalForm_code_eq_rescaledPudlak m⟩

/-- Project-facing code round-trip audit for the exact family exactness bottom
input, routed through its exact-convention certificate. -/
theorem audit_theorem5_exactFamilyExactness_codeRoundTrip
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) := by
  exact audit_theorem5_exactConvention_codeRoundTrip h.toExactConventionInputs

/-- Normal-form audit for the exact convention theorem-5 bottom input. -/
theorem audit_theorem5_exactConvention_normalFormAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    ∀ m : ℕ,
      (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
          h.toPudlakSideInputs.strengthened_to_partial).code m =
        _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
          h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m :=
  (audit_theorem5_exactConvention_codeRoundTrip h).2.2

/-- Normal-form audit for the split minChecked theorem-5 bottom input. -/
theorem audit_theorem5_splitMinChecked_normalFormAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    ∀ m : ℕ,
      (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
          h.toPudlakSideInputs.strengthened_to_partial).code m =
        _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
          h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m :=
  (audit_theorem5_splitMinChecked_codeRoundTrip h).2.2

/-- Normal-form audit for the exact family exactness theorem-5 bottom input. -/
theorem audit_theorem5_exactFamilyExactness_normalFormAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    ∀ m : ℕ,
      (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
          h.toPudlakSideInputs.strengthened_to_partial).code m =
        _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
          h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m :=
  (audit_theorem5_exactFamilyExactness_codeRoundTrip h).2.2

/-- Final short audit route for the exact convention theorem-5 bottom input:
the split-minChecked equivalence, the code round trip, and the endpoint are all
available from the same input. -/
theorem audit_theorem5_exactConvention_route
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign)) ∧
      h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact ⟨audit_exactConvention_iff_splitMinChecked,
    (audit_theorem5_exactConvention_codeRoundTrip h).1,
    (audit_theorem5_exactConvention_codeRoundTrip h).2.1,
    (audit_theorem5_exactConvention_codeRoundTrip h).2.2,
    audit_theorem5_exactConvention_endpoint h hupper⟩

/-- Final short audit route for the split minChecked theorem-5 bottom input. -/
theorem audit_theorem5_splitMinChecked_route
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign)) ∧
      h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact ⟨audit_splitMinChecked_iff_exactConvention,
    (audit_theorem5_splitMinChecked_codeRoundTrip h).1,
    (audit_theorem5_splitMinChecked_codeRoundTrip h).2.1,
    (audit_theorem5_splitMinChecked_codeRoundTrip h).2.2,
    audit_theorem5_splitMinChecked_endpoint h hupper⟩

/-- Final short audit route for the exact family exactness theorem-5 bottom
input.  This is the exact-family counterpart of the exact-convention and split
minChecked route theorems. -/
theorem audit_theorem5_exactFamilyExactness_route
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
      h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact ⟨audit_exactFamilyExactness_iff_exactConvention,
    audit_exactFamilyExactness_iff_splitMinChecked,
    (audit_theorem5_exactFamilyExactness_codeRoundTrip h).1,
    (audit_theorem5_exactFamilyExactness_codeRoundTrip h).2.1,
    (audit_theorem5_exactFamilyExactness_codeRoundTrip h).2.2,
    audit_theorem5_exactFamilyExactness_endpoint h hupper⟩

/-- Full audit bundle for the exact convention entry: certificate presentation
`<=>`, split-minChecked `<=>`, code round-trip, normal-form audit, and endpoint. -/
theorem audit_theorem5_exactConvention_fullAuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty _root_.LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
      h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact ⟨_root_.audit_theorem5_certificatePresentation_iff_rescaledPresentation,
    audit_exactConvention_iff_splitMinChecked,
    (audit_theorem5_exactConvention_codeRoundTrip h).1,
    (audit_theorem5_exactConvention_codeRoundTrip h).2.1,
    audit_theorem5_exactConvention_normalFormAudit h,
    audit_theorem5_exactConvention_endpoint h hupper⟩

/-- Full audit bundle for the split minChecked entry. -/
theorem audit_theorem5_splitMinChecked_fullAuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty _root_.LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign)) ∧
      h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact ⟨_root_.audit_theorem5_certificatePresentation_iff_rescaledPresentation,
    audit_splitMinChecked_iff_exactConvention,
    (audit_theorem5_splitMinChecked_codeRoundTrip h).1,
    (audit_theorem5_splitMinChecked_codeRoundTrip h).2.1,
    audit_theorem5_splitMinChecked_normalFormAudit h,
    audit_theorem5_splitMinChecked_endpoint h hupper⟩

/-- Full audit bundle for the exact family exactness entry. -/
theorem audit_theorem5_exactFamilyExactness_fullAuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty _root_.LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
      h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact ⟨_root_.audit_theorem5_certificatePresentation_iff_rescaledPresentation,
    audit_exactFamilyExactness_iff_splitMinChecked,
    (audit_theorem5_exactFamilyExactness_codeRoundTrip h).1,
    (audit_theorem5_exactFamilyExactness_codeRoundTrip h).2.1,
    audit_theorem5_exactFamilyExactness_normalFormAudit h,
    audit_theorem5_exactFamilyExactness_endpoint h hupper⟩

/-- Collision-level full audit bundle for the exact convention entry.  It
keeps the certificate-presentation equivalence, the input equivalences, and the
collision endpoint equivalences in one short theorem name. -/
theorem audit_theorem5_exactConvention_collisionFullAuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty _root_.LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
      ((Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ↔
       (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni)) ∧
      ((Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ↔
       (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni)) := by
  exact ⟨_root_.audit_theorem5_certificatePresentation_iff_rescaledPresentation,
    audit_exactConvention_iff_exactFamilyExactness,
    audit_exactConvention_iff_splitMinChecked,
    audit_exactConvention_collision_iff_exactFamilyExactness_collision hupper,
    audit_exactConvention_collision_iff_splitMinChecked_collision hupper⟩

/-- Collision-level full audit bundle for the split minChecked entry. -/
theorem audit_theorem5_splitMinChecked_collisionFullAuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty _root_.LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign)) ∧
      ((Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ↔
       (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni)) ∧
      ((Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ↔
       (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni)) := by
  exact ⟨_root_.audit_theorem5_certificatePresentation_iff_rescaledPresentation,
    audit_splitMinChecked_iff_exactFamilyExactness,
    audit_splitMinChecked_iff_exactConvention,
    audit_splitMinChecked_collision_iff_exactFamilyExactness_collision hupper,
    audit_splitMinChecked_collision_iff_exactConvention_collision hupper⟩

/-- Collision-level full audit bundle for the exact family exactness entry. -/
theorem audit_theorem5_exactFamilyExactness_collisionFullAuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty _root_.LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
      ((Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ↔
       (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni)) ∧
      ((Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ↔
       (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni)) := by
  exact ⟨_root_.audit_theorem5_certificatePresentation_iff_rescaledPresentation,
    audit_exactFamilyExactness_iff_exactConvention,
    audit_exactFamilyExactness_iff_splitMinChecked,
    audit_exactFamilyExactness_collision_iff_exactConvention_collision hupper,
    audit_exactFamilyExactness_collision_iff_splitMinChecked_collision hupper⟩

/-- Total audit route from the exact convention entry.  It exposes the
certificate presentation equivalence, exact-family equivalence, split-minChecked
equivalence, code round-trip, normal-form audit, and final endpoint together. -/
theorem audit_theorem5_totalAuditRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty _root_.LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
      h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact ⟨_root_.audit_theorem5_certificatePresentation_iff_rescaledPresentation,
    audit_exactConvention_iff_exactFamilyExactness,
    audit_exactConvention_iff_splitMinChecked,
    (audit_theorem5_exactConvention_codeRoundTrip h).1,
    (audit_theorem5_exactConvention_codeRoundTrip h).2.1,
    audit_theorem5_exactConvention_normalFormAudit h,
    audit_theorem5_exactConvention_endpoint h hupper⟩

/-- Statement probe for the exact convention entry: the endpoint is presented
with both exact-family and split-minChecked equivalences, so the short route has
not weakened the theorem statement. -/
theorem audit_theorem5_exactConvention_statementProbe
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact ⟨audit_exactConvention_iff_exactFamilyExactness,
    audit_exactConvention_iff_splitMinChecked,
    audit_theorem5_exactConvention_endpoint h hupper⟩

/-- Statement probe for the split minChecked entry. -/
theorem audit_theorem5_splitMinChecked_statementProbe
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign)) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact ⟨audit_splitMinChecked_iff_exactConvention,
    audit_splitMinChecked_iff_exactFamilyExactness,
    audit_theorem5_splitMinChecked_endpoint h hupper⟩

/-- Statement probe for the exact family exactness entry. -/
theorem audit_theorem5_exactFamilyExactness_statementProbe
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact ⟨audit_exactFamilyExactness_iff_exactConvention,
    audit_exactFamilyExactness_iff_splitMinChecked,
    audit_theorem5_exactFamilyExactness_endpoint h hupper⟩

/-- Encoder/certificate bridge for the exact convention entry.  It universally
exposes certificate round-trips and then attaches the concrete code round-trip
of the project input. -/
theorem audit_theorem5_exactConvention_encoderCertificateBridge
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    (∀ hcert : _root_.LiteraturePudlakTheorem5LowerBoundCertificate,
      hcert.toRescaledCertificate.toPowerBoundCertificate.scale_data =
          hcert.scale_data ∧
        (∀ k : ℕ,
          hcert.toRescaledCertificate.toPowerBoundCertificate.scale_data.powerBoundRawCode k =
            hcert.scale_data.powerBoundRawCode k)) ∧
      (∀ hrescaled : _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate,
        hrescaled.toPowerBoundCertificate.toRescaledCertificate.scale_data =
            hrescaled.scale_data ∧
          (∀ k : ℕ,
            hrescaled.toPowerBoundCertificate.toRescaledCertificate.scale_data.rescaledRawCode k =
              hrescaled.scale_data.rescaledRawCode k)) ∧
      (Nonempty _root_.LiteraturePudlakTheorem5LowerBoundCertificate ↔
        Nonempty _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate) ∧
      h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) := by
  exact ⟨fun hcert => _root_.audit_theorem5_powerBound_certificateRoundTrip hcert,
    fun hrescaled => _root_.audit_theorem5_rescaled_certificateRoundTrip hrescaled,
    _root_.audit_theorem5_certificatePresentation_iff_rescaledPresentation,
    (audit_theorem5_exactConvention_codeRoundTrip h).1,
    (audit_theorem5_exactConvention_codeRoundTrip h).2.1,
    (audit_theorem5_exactConvention_codeRoundTrip h).2.2⟩

/-- Encoder/certificate bridge for the split minChecked entry. -/
theorem audit_theorem5_splitMinChecked_encoderCertificateBridge
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    (∀ hcert : _root_.LiteraturePudlakTheorem5LowerBoundCertificate,
      hcert.toRescaledCertificate.toPowerBoundCertificate.scale_data =
          hcert.scale_data ∧
        (∀ k : ℕ,
          hcert.toRescaledCertificate.toPowerBoundCertificate.scale_data.powerBoundRawCode k =
            hcert.scale_data.powerBoundRawCode k)) ∧
      (∀ hrescaled : _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate,
        hrescaled.toPowerBoundCertificate.toRescaledCertificate.scale_data =
            hrescaled.scale_data ∧
          (∀ k : ℕ,
            hrescaled.toPowerBoundCertificate.toRescaledCertificate.scale_data.rescaledRawCode k =
              hrescaled.scale_data.rescaledRawCode k)) ∧
      (Nonempty _root_.LiteraturePudlakTheorem5LowerBoundCertificate ↔
        Nonempty _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate) ∧
      h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) := by
  exact ⟨fun hcert => _root_.audit_theorem5_powerBound_certificateRoundTrip hcert,
    fun hrescaled => _root_.audit_theorem5_rescaled_certificateRoundTrip hrescaled,
    _root_.audit_theorem5_certificatePresentation_iff_rescaledPresentation,
    (audit_theorem5_splitMinChecked_codeRoundTrip h).1,
    (audit_theorem5_splitMinChecked_codeRoundTrip h).2.1,
    (audit_theorem5_splitMinChecked_codeRoundTrip h).2.2⟩

/-- Encoder/certificate bridge for the exact family exactness entry. -/
theorem audit_theorem5_exactFamilyExactness_encoderCertificateBridge
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    (∀ hcert : _root_.LiteraturePudlakTheorem5LowerBoundCertificate,
      hcert.toRescaledCertificate.toPowerBoundCertificate.scale_data =
          hcert.scale_data ∧
        (∀ k : ℕ,
          hcert.toRescaledCertificate.toPowerBoundCertificate.scale_data.powerBoundRawCode k =
            hcert.scale_data.powerBoundRawCode k)) ∧
      (∀ hrescaled : _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate,
        hrescaled.toPowerBoundCertificate.toRescaledCertificate.scale_data =
            hrescaled.scale_data ∧
          (∀ k : ℕ,
            hrescaled.toPowerBoundCertificate.toRescaledCertificate.scale_data.rescaledRawCode k =
              hrescaled.scale_data.rescaledRawCode k)) ∧
      (Nonempty _root_.LiteraturePudlakTheorem5LowerBoundCertificate ↔
        Nonempty _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate) ∧
      h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) := by
  exact ⟨fun hcert => _root_.audit_theorem5_powerBound_certificateRoundTrip hcert,
    fun hrescaled => _root_.audit_theorem5_rescaled_certificateRoundTrip hrescaled,
    _root_.audit_theorem5_certificatePresentation_iff_rescaledPresentation,
    (audit_theorem5_exactFamilyExactness_codeRoundTrip h).1,
    (audit_theorem5_exactFamilyExactness_codeRoundTrip h).2.1,
    (audit_theorem5_exactFamilyExactness_codeRoundTrip h).2.2⟩

/-- No-weakening audit chain: exact convention, exact family exactness, and
split minChecked are connected by explicit bidirectional equivalences. -/
theorem audit_theorem5_noWeakeningChain
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign)) := by
  exact ⟨audit_exactConvention_iff_exactFamilyExactness,
    audit_exactFamilyExactness_iff_splitMinChecked,
    audit_exactConvention_iff_splitMinChecked,
    audit_splitMinChecked_iff_exactConvention⟩

/-- Collision-level no-weakening audit chain: the three Nonempty endpoint
statements are also connected by explicit bidirectional equivalences. -/
theorem audit_theorem5_collisionNoWeakeningChain
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ((Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ↔
     (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni)) ∧
      ((Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ↔
       (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni)) ∧
      ((Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ↔
       (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni)) := by
  exact ⟨audit_exactConvention_collision_iff_exactFamilyExactness_collision hupper,
    audit_exactFamilyExactness_collision_iff_splitMinChecked_collision hupper,
    audit_exactConvention_collision_iff_splitMinChecked_collision hupper⟩

/-- Endpoint agreement audit: the exact-convention, split-minChecked, and exact
family exactness endpoints have the same final target proposition. -/
theorem audit_theorem5_allEndpointsAgree
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hconv :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hsplit :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (hexact :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (¬ _root_.is_rational _root_.euler_mascheroni) ∧
      (¬ _root_.is_rational _root_.euler_mascheroni) ∧
      (¬ _root_.is_rational _root_.euler_mascheroni) := by
  exact ⟨audit_theorem5_exactConvention_endpoint hconv hupper,
    audit_theorem5_splitMinChecked_endpoint hsplit hupper,
    audit_theorem5_exactFamilyExactness_endpoint hexact hupper⟩

/-- Nonempty endpoint agreement audit: the three collision endpoints expose the
same final target proposition under their corresponding Nonempty inputs. -/
theorem audit_theorem5_allCollisionEndpointsAgree
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) := by
  exact ⟨fun h => h.elim (fun hconv => audit_theorem5_exactConvention_endpoint hconv hupper),
    fun h => h.elim (fun hsplit => audit_theorem5_splitMinChecked_endpoint hsplit hupper),
    fun h => h.elim (fun hexact => audit_theorem5_exactFamilyExactness_endpoint hexact hupper)⟩

/-- Nonempty endpoint audit for the exact convention entry. -/
theorem audit_theorem5_exactConvention_nonemptyEndpoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun h => h.elim (fun hconv => audit_theorem5_exactConvention_endpoint hconv hupper)

/-- Nonempty endpoint audit for the split minChecked entry. -/
theorem audit_theorem5_splitMinChecked_nonemptyEndpoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun h => h.elim (fun hsplit => audit_theorem5_splitMinChecked_endpoint hsplit hupper)

/-- Nonempty endpoint audit for the exact family exactness entry. -/
theorem audit_theorem5_exactFamilyExactness_nonemptyEndpoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun h => h.elim (fun hexact => audit_theorem5_exactFamilyExactness_endpoint hexact hupper)

/-- Route closure for all Nonempty endpoint forms.  This is a short audit name
for the three existence-level endpoint maps. -/
theorem audit_theorem5_nonemptyRouteClosure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) := by
  exact ⟨audit_theorem5_exactConvention_nonemptyEndpoint hupper,
    audit_theorem5_splitMinChecked_nonemptyEndpoint hupper,
    audit_theorem5_exactFamilyExactness_nonemptyEndpoint hupper⟩

/-- Nonempty no-weakening route: input equivalences and existence-level
endpoints are exposed together. -/
theorem audit_theorem5_nonemptyNoWeakeningRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) := by
  exact ⟨audit_theorem5_noWeakeningChain.1,
    audit_theorem5_noWeakeningChain.2.1,
    (audit_theorem5_nonemptyRouteClosure hupper).1,
    (audit_theorem5_nonemptyRouteClosure hupper).2.1,
    (audit_theorem5_nonemptyRouteClosure hupper).2.2⟩

/-- Final reviewer checklist for the exact convention entry.  It gathers the
certificate presentation bridge, statement probe, encoder/certificate bridge,
full audit bundle, and Nonempty route closure. -/
theorem audit_theorem5_exactConvention_finalReviewerChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty _root_.LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
      h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact ⟨_root_.audit_theorem5_certificatePresentation_iff_rescaledPresentation,
    (audit_theorem5_exactConvention_statementProbe h hupper).1,
    (audit_theorem5_exactConvention_statementProbe h hupper).2.1,
    (audit_theorem5_exactConvention_encoderCertificateBridge h).2.2.2.1,
    (audit_theorem5_exactConvention_encoderCertificateBridge h).2.2.2.2.1,
    (audit_theorem5_exactConvention_encoderCertificateBridge h).2.2.2.2.2,
    audit_theorem5_exactConvention_nonemptyEndpoint hupper,
    audit_theorem5_exactConvention_endpoint h hupper⟩

/-- Final reviewer checklist for the split minChecked entry. -/
theorem audit_theorem5_splitMinChecked_finalReviewerChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty _root_.LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign)) ∧
      h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact ⟨_root_.audit_theorem5_certificatePresentation_iff_rescaledPresentation,
    (audit_theorem5_splitMinChecked_statementProbe h hupper).1,
    (audit_theorem5_splitMinChecked_statementProbe h hupper).2.1,
    (audit_theorem5_splitMinChecked_encoderCertificateBridge h).2.2.2.1,
    (audit_theorem5_splitMinChecked_encoderCertificateBridge h).2.2.2.2.1,
    (audit_theorem5_splitMinChecked_encoderCertificateBridge h).2.2.2.2.2,
    audit_theorem5_splitMinChecked_nonemptyEndpoint hupper,
    audit_theorem5_splitMinChecked_endpoint h hupper⟩

/-- Final reviewer checklist for the exact family exactness entry. -/
theorem audit_theorem5_exactFamilyExactness_finalReviewerChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty _root_.LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
      h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact ⟨_root_.audit_theorem5_certificatePresentation_iff_rescaledPresentation,
    (audit_theorem5_exactFamilyExactness_statementProbe h hupper).1,
    (audit_theorem5_exactFamilyExactness_statementProbe h hupper).2.1,
    (audit_theorem5_exactFamilyExactness_encoderCertificateBridge h).2.2.2.1,
    (audit_theorem5_exactFamilyExactness_encoderCertificateBridge h).2.2.2.2.1,
    (audit_theorem5_exactFamilyExactness_encoderCertificateBridge h).2.2.2.2.2,
    audit_theorem5_exactFamilyExactness_nonemptyEndpoint hupper,
    audit_theorem5_exactFamilyExactness_endpoint h hupper⟩

/-- Stage-closed statement for the exact convention theorem-5 entry. -/
abbrev audit_theorem5_exactConventionStageClosedStatement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (_hupper : SondowProjectLocalS21CollapseConclusion) : Prop :=
    (Nonempty _root_.LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
      h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni

/-- Exact convention theorem-5 entry is stage-closed for reviewer audit. -/
theorem audit_theorem5_exactConvention_stageClosed
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    audit_theorem5_exactConventionStageClosedStatement h hupper :=
  audit_theorem5_exactConvention_finalReviewerChecklist h hupper

/-- Stage-closed statement for the split minChecked theorem-5 entry. -/
abbrev audit_theorem5_splitMinCheckedStageClosedStatement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (_hupper : SondowProjectLocalS21CollapseConclusion) : Prop :=
    (Nonempty _root_.LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign)) ∧
      h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni

/-- Split minChecked theorem-5 entry is stage-closed for reviewer audit. -/
theorem audit_theorem5_splitMinChecked_stageClosed
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    audit_theorem5_splitMinCheckedStageClosedStatement h hupper :=
  audit_theorem5_splitMinChecked_finalReviewerChecklist h hupper

/-- Stage-closed statement for the exact family exactness theorem-5 entry. -/
abbrev audit_theorem5_exactFamilyExactnessStageClosedStatement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (_hupper : SondowProjectLocalS21CollapseConclusion) : Prop :=
    (Nonempty _root_.LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty _root_.LiteraturePudlakTheorem5RescaledLowerBoundCertificate) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
      h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni

/-- Exact family exactness theorem-5 entry is stage-closed for reviewer audit. -/
theorem audit_theorem5_exactFamilyExactness_stageClosed
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    audit_theorem5_exactFamilyExactnessStageClosedStatement h hupper :=
  audit_theorem5_exactFamilyExactness_finalReviewerChecklist h hupper

/-- Reviewer-facing package: all three theorem-5 entries are stage-closed. -/
theorem audit_theorem5_stageClosurePackage
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hconv :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hsplit :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (hexact :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    audit_theorem5_exactConventionStageClosedStatement hconv hupper ∧
      audit_theorem5_splitMinCheckedStageClosedStatement hsplit hupper ∧
      audit_theorem5_exactFamilyExactnessStageClosedStatement hexact hupper := by
  exact ⟨audit_theorem5_exactConvention_stageClosed hconv hupper,
    audit_theorem5_splitMinChecked_stageClosed hsplit hupper,
    audit_theorem5_exactFamilyExactness_stageClosed hexact hupper⟩

/-- Nonempty stage-closed reviewer package: all three existence-level
endpoints and all core input equivalences are available together. -/
theorem audit_theorem5_nonemptyStageClosed
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) := by
  exact ⟨audit_theorem5_exactConvention_nonemptyEndpoint hupper,
    audit_theorem5_splitMinChecked_nonemptyEndpoint hupper,
    audit_theorem5_exactFamilyExactness_nonemptyEndpoint hupper,
    audit_exactConvention_iff_exactFamilyExactness,
    audit_exactFamilyExactness_iff_splitMinChecked,
    audit_exactConvention_iff_splitMinChecked⟩

/-- PK-main-bridge audit name: the local proof-code convention presentation and
the projection-family exactness presentation are definitionally connected by
the existing exact-convention/exact-family equivalence. -/
theorem audit_pk_localConvention_iff_familyExactness_noHiddenAssumption
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) :=
  audit_exactConvention_iff_exactFamilyExactness

/-- PK-main-bridge audit name: projection-family exactness and split
minChecked exactness are bidirectionally connected, so the split interface is
not a one-way weakening. -/
theorem audit_pk_familyExactness_iff_splitMinChecked_noHiddenAssumption
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) :=
  audit_exactFamilyExactness_iff_splitMinChecked

/-- PK-main-bridge audit package: local convention, family exactness, and split
minChecked interfaces form a closed bidirectional triangle. -/
theorem audit_pk_mainBridge_noHiddenAssumption
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) :=
  ⟨audit_pk_localConvention_iff_familyExactness_noHiddenAssumption,
    audit_pk_familyExactness_iff_splitMinChecked_noHiddenAssumption,
    audit_exactConvention_iff_splitMinChecked⟩

/-- PK-main-bridge collision audit: the three existence-level endpoint forms
are also equivalent, so moving between local convention, family exactness, and
split minChecked does not change the final target. -/
theorem audit_pk_mainBridge_collisionNoHiddenAssumption
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ((Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ↔
     (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni)) ∧
      ((Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ↔
       (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni)) ∧
      ((Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ↔
       (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni)) :=
  audit_theorem5_collisionNoWeakeningChain hupper

/-- PK-main-bridge endpoint closure: the no-hidden-assumption triangle and the
Nonempty endpoints are available together. -/
theorem audit_pk_mainBridge_endpointClosure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) →
        ¬ _root_.is_rational _root_.euler_mascheroni) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) :=
  audit_theorem5_nonemptyStageClosed hupper

theorem irrational_of_exactConvention_via_splitMinChecked
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toExactSplitMinCheckedInputs.collide hupper

theorem irrational_of_exactConvention_via_familyWitness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toFamilyWitnessInputs.collide hupper

theorem irrational_of_splitMinChecked_via_exactConvention
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toExactConventionInputs.collide hupper

theorem irrational_of_exactStrengthened_via_exactConvention
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactStrengthenedInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  let hconv :=
    h.toExternalTheorem5ExactFamilyExactnessInputs.toExactConventionInputs
  exact hconv.collide hupper

theorem irrational_of_familyWitness_via_exactConvention
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomFamilyWitnessInputs
        Ax A B halign)
    (hupper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  let hconv :=
    h.toExternalTheorem5ExactFamilyExactnessInputs.toExactConventionInputs
  exact hconv.collide hupper

namespace SondowProjectLocalPudlakBottomSemanticConventionInputs

def strengthenedExactFamilyLengths
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomSemanticConventionInputs
        Ax A B halign) :
    _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths :=
  (_root_.strengthenedToPartialProjectProofLengthSemantics_iff_exactFamilyLengths
    (fun _ => 0)).1 h.strengthened_project_semantics

def localHilbertFamilyExactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomSemanticConventionInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
      h.formula_code_interpretation :=
  _root_.MiniHilbert.PAHilbertProjectionFamilyExactness.of_projectCheckedCodeProofLengthSemantics
      h.formula_code_interpretation h.local_hilbert_project_semantics

set_option linter.style.longLine false in
def partialMinCheckedExactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomSemanticConventionInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertPartialConsistencyMinCheckedExactness
      h.formula_code_interpretation :=
  _root_.MiniHilbert.PAHilbertPartialConsistencyMinCheckedExactness.of_projectCheckedCodeProofLengthSemantics
      h.formula_code_interpretation h.local_hilbert_project_semantics

set_option linter.style.longLine false in
def reflectionMinCheckedExactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomSemanticConventionInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertReflectionGraftMinCheckedExactness
      h.formula_code_interpretation :=
  _root_.MiniHilbert.PAHilbertReflectionGraftMinCheckedExactness.of_projectCheckedCodeProofLengthSemantics
      h.formula_code_interpretation h.local_hilbert_project_semantics

def toExactStrengthenedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomSemanticConventionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExactStrengthenedInputs
      Ax A B halign where
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_exact_lengths := h.strengthenedExactFamilyLengths
  formula_code_interpretation := h.formula_code_interpretation
  local_hilbert_family_exactness := h.localHilbertFamilyExactness

def toExactSplitMinCheckedInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomSemanticConventionInputs
        Ax A B halign) :
    SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
      Ax A B halign where
  strengthened_payload_truth := h.strengthened_payload_truth
  strengthened_exact_lengths := h.strengthenedExactFamilyLengths
  formula_code_interpretation := h.formula_code_interpretation
  partial_minChecked_exactness := h.partialMinCheckedExactness
  reflection_minChecked_exactness := h.reflectionMinCheckedExactness

end SondowProjectLocalPudlakBottomSemanticConventionInputs

/-- Fully assembled bottom-level collision input. -/
structure SondowProjectLocalBottomSplitMinCheckedCollisionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : _root_.HilbertProjectionCodeAlignment) where
  project_upper :
    SondowProjectLocalS21CollapseConclusion
  pudlak_bottom :
    SondowProjectLocalPudlakBottomSplitMinCheckedInputs
      Ax A B halign

namespace SondowProjectLocalBottomSplitMinCheckedCollisionInputs

theorem not_rational
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalBottomSplitMinCheckedCollisionInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.pudlak_bottom.collide h.project_upper

end SondowProjectLocalBottomSplitMinCheckedCollisionInputs

theorem bottom_split_minChecked_collision_nonempty_of_components
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion)
    (hlower :
      SondowProjectLocalPudlakBottomSplitMinCheckedInputs
        Ax A B halign) :
    Nonempty
      (SondowProjectLocalBottomSplitMinCheckedCollisionInputs
        Ax A B halign) :=
  ⟨{
    project_upper := hupper
    pudlak_bottom := hlower
  }⟩

theorem verifierAndPayloadTruth_nonempty_to_bottom_family_exactness_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomFamilyExactnessInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact hpudlak.collide (verifier.toCollapseConclusion htruth)

theorem verifierAndPayloadTruth_nonempty_to_bottom_split_minChecked_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomSplitMinCheckedInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact hpudlak.collide (verifier.toCollapseConclusion htruth)

theorem verifierAndPayloadTruth_nonempty_to_bottom_rescaled_theorem5_split_minChecked_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomRescaledTheorem5SplitMinCheckedInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact hpudlak.collide (verifier.toCollapseConclusion htruth)

theorem verifierAndPayloadTruth_nonempty_to_bottom_rescaled_theorem5_calibrated_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomRescaledTheorem5CalibratedInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact hpudlak.collide (verifier.toCollapseConclusion htruth)

theorem verifierAndPayloadTruth_nonempty_to_bottom_external_theorem5_recognition_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomExternalTheorem5RecognitionInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact hpudlak.collide (verifier.toCollapseConclusion htruth)

theorem verifierAndPayloadTruth_nonempty_to_bottom_external_theorem5_canonical_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact hpudlak.collide (verifier.toCollapseConclusion htruth)

theorem verifierAndPayloadTruth_nonempty_to_bottom_external_theorem5_convention_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact hpudlak.collide (verifier.toCollapseConclusion htruth)

theorem verifierAndPayloadTruth_nonempty_to_bottom_external_convention_witness_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomExternalConventionWitnessInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact hpudlak.collide (verifier.toCollapseConclusion htruth)

theorem verifierAndPayloadTruth_nonempty_to_bottom_semantic_convention_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomSemanticConventionInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact hpudlak.collide (verifier.toCollapseConclusion htruth)

theorem verifierAndPayloadTruth_nonempty_to_bottom_family_witness_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomFamilyWitnessInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact hpudlak.collide (verifier.toCollapseConclusion htruth)

theorem verifierAndPayloadTruth_nonempty_to_bottom_exact_strengthened_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomExactStrengthenedInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact hpudlak.collide (verifier.toCollapseConclusion htruth)

theorem verifierAndPayloadTruth_nonempty_to_bottom_exact_split_minChecked_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact hpudlak.collide (verifier.toCollapseConclusion htruth)

/-- The current narrowest callable collision box: Sondow-side verifier/truth
plus exact strengthened lengths and split local-Hilbert minChecked exactness
return Euler's constant irrationality. -/
theorem callCollisionBox_from_exactSplitMinChecked
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  verifierAndPayloadTruth_nonempty_to_bottom_exact_split_minChecked_collision
    hupper hpudlak

/-- Semantic convention version of the callable collision box.  This route
exercises the conversion from project proof-length semantics to the exact
split minChecked input before calling the same collision endpoint. -/
theorem callCollisionBox_from_semanticConventionViaExactSplit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomSemanticConventionInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  callCollisionBox_from_exactSplitMinChecked
    hupper hpudlak.toExactSplitMinCheckedInputs

/-- Short reviewer entrypoint: the PK main bridge carries the already-probed
no-hidden-assumption bridge from local convention, through exact family
exactness, into split minChecked exactness. -/
abbrev audit_pk_mainBridge_stageClosed
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :=
  audit_theorem5_stageClosurePackage
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)

/-- Short reviewer entrypoint: nonempty witnesses survive all current Theorem 5
presentations without strengthening or weakening the statement. -/
abbrev audit_pk_mainBridge_nonemptyStageClosed
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :=
  audit_theorem5_nonemptyStageClosed
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)

/-- Short reviewer entrypoint for the non-collision endpoint equivalence chain. -/
abbrev audit_pk_mainBridge_endpointAgreement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :=
  audit_theorem5_allEndpointsAgree
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)

/-- Short reviewer entrypoint for the collision endpoint equivalence chain. -/
abbrev audit_pk_mainBridge_collisionEndpointAgreement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :=
  audit_theorem5_allCollisionEndpointsAgree
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)

/-- Short reviewer entrypoint: upper-side verifier/truth plus the narrowed
exact split minChecked lower-side package gives the callable irrationality
endpoint. -/
theorem audit_pk_upperLowerEndpointBridge
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  callCollisionBox_from_exactSplitMinChecked
    hupper hpudlak

/-- Short reviewer entrypoint: the semantic-convention lower-side package
reaches the same callable endpoint after conversion to exact split minChecked. -/
theorem audit_pk_semanticUpperLowerEndpointBridge
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomSemanticConventionInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  callCollisionBox_from_semanticConventionViaExactSplit
    hupper hpudlak

/-- Canonical Theorem 5 lower-side inputs can be paired with the upper-side
verifier/truth package to call the same irrationality endpoint. -/
theorem audit_pk_canonicalUpperLowerEndpointBridge
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  verifierAndPayloadTruth_nonempty_to_bottom_external_theorem5_canonical_collision
    hupper hpudlak

/-- Convention Theorem 5 lower-side inputs can be paired with the upper-side
verifier/truth package to call the same irrationality endpoint. -/
theorem audit_pk_conventionUpperLowerEndpointBridge
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  verifierAndPayloadTruth_nonempty_to_bottom_external_theorem5_convention_collision
    hupper hpudlak

/-- Family-witness lower-side inputs can be paired with the upper-side
verifier/truth package to call the same irrationality endpoint. -/
theorem audit_pk_familyWitnessUpperLowerEndpointBridge
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomFamilyWitnessInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  verifierAndPayloadTruth_nonempty_to_bottom_family_witness_collision
    hupper hpudlak

/-- Exact-strengthened lower-side inputs can be paired with the upper-side
verifier/truth package to call the same irrationality endpoint. -/
theorem audit_pk_exactStrengthenedUpperLowerEndpointBridge
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomExactStrengthenedInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  verifierAndPayloadTruth_nonempty_to_bottom_exact_strengthened_collision
    hupper hpudlak

/-- Exact-convention lower-side inputs can be paired with the upper-side
verifier/truth package by first moving to exact split minChecked. -/
theorem audit_pk_exactConventionUpperLowerEndpointBridge
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  callCollisionBox_from_exactSplitMinChecked
    hupper hpudlak.toExactSplitMinCheckedInputs

/-- Exact-family-exactness lower-side inputs can be paired with the upper-side
verifier/truth package by first moving to exact split minChecked. -/
theorem audit_pk_exactFamilyExactnessUpperLowerEndpointBridge
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  callCollisionBox_from_exactSplitMinChecked
    hupper hpudlak.toExactSplitMinCheckedInputs

/-- One-line reviewer theorem: the current exact-convention, exact-family-
exactness, and exact split minChecked presentations are mutually equivalent at
the nonempty-certificate level. -/
theorem audit_pk_exactConvention_familyExactness_splitMinChecked_totalIff
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign)) ∧
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign)) ∧
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign)) :=
  ⟨audit_exactConvention_iff_exactFamilyExactness,
    audit_exactFamilyExactness_iff_splitMinChecked,
    audit_exactConvention_iff_splitMinChecked⟩

/-- Forward nonempty-certificate transport from exact convention to exact
family exactness. -/
theorem audit_pk_exactConvention_to_exactFamilyExactness_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign)) :
    Nonempty
      (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :=
  (audit_exactConvention_iff_exactFamilyExactness
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)).1 h

/-- Backward nonempty-certificate transport from exact family exactness to exact
convention. -/
theorem audit_pk_exactFamilyExactness_to_exactConvention_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign)) :
    Nonempty
      (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :=
  (audit_exactConvention_iff_exactFamilyExactness
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)).2 h

/-- Forward nonempty-certificate transport from exact family exactness to split
minChecked exactness. -/
theorem audit_pk_exactFamilyExactness_to_splitMinChecked_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign)) :
    Nonempty
      (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :=
  (audit_exactFamilyExactness_iff_splitMinChecked
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)).1 h

/-- Backward nonempty-certificate transport from split minChecked exactness to
exact family exactness. -/
theorem audit_pk_splitMinChecked_to_exactFamilyExactness_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign)) :
    Nonempty
      (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :=
  (audit_exactFamilyExactness_iff_splitMinChecked
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)).2 h

/-- Forward nonempty-certificate transport from exact convention directly to
split minChecked exactness. -/
theorem audit_pk_exactConvention_to_splitMinChecked_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign)) :
    Nonempty
      (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :=
  (audit_exactConvention_iff_splitMinChecked
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)).1 h

/-- Backward nonempty-certificate transport from split minChecked exactness
directly to exact convention. -/
theorem audit_pk_splitMinChecked_to_exactConvention_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign)) :
    Nonempty
      (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :=
  (audit_exactConvention_iff_splitMinChecked
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)).2 h

/-- Upper/lower endpoint closure for the exact-convention, exact-family-
exactness, and split minChecked triangle. -/
theorem audit_pk_upperLowerExactTriangleEndpointClosure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth) :
    (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign →
      ¬ _root_.is_rational _root_.euler_mascheroni) ∧
    (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign →
      ¬ _root_.is_rational _root_.euler_mascheroni) ∧
    (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign →
      ¬ _root_.is_rational _root_.euler_mascheroni) := by
  exact
    ⟨fun hp =>
        audit_pk_exactConventionUpperLowerEndpointBridge hupper hp,
      fun hp =>
        audit_pk_exactFamilyExactnessUpperLowerEndpointBridge hupper hp,
      fun hp =>
        audit_pk_upperLowerEndpointBridge hupper hp⟩

/-- Upper/lower endpoint closure for the main presentation ladder feeding the
exact split minChecked endpoint. -/
theorem audit_pk_upperLowerPresentationEndpointClosure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth) :
    (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
        Ax A B halign →
      ¬ _root_.is_rational _root_.euler_mascheroni) ∧
    (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
        Ax A B halign →
      ¬ _root_.is_rational _root_.euler_mascheroni) ∧
    (SondowProjectLocalPudlakBottomFamilyWitnessInputs
        Ax A B halign →
      ¬ _root_.is_rational _root_.euler_mascheroni) ∧
    (SondowProjectLocalPudlakBottomExactStrengthenedInputs
        Ax A B halign →
      ¬ _root_.is_rational _root_.euler_mascheroni) := by
  exact
    ⟨fun hp =>
        audit_pk_canonicalUpperLowerEndpointBridge hupper hp,
      fun hp =>
        audit_pk_conventionUpperLowerEndpointBridge hupper hp,
      fun hp =>
        audit_pk_familyWitnessUpperLowerEndpointBridge hupper hp,
      fun hp =>
        audit_pk_exactStrengthenedUpperLowerEndpointBridge hupper hp⟩

/-- One-line reviewer theorem: the exact-convention, exact-family-exactness,
and exact split minChecked presentations are mutually equivalent at the
collision-endpoint level. -/
theorem audit_pk_exactConvention_familyExactness_splitMinChecked_collisionTotalIff
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion) :
    ((Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ↔
      (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni)) ∧
    ((Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ↔
      (Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni)) ∧
    ((Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ↔
      (Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni)) :=
  ⟨audit_exactConvention_collision_iff_exactFamilyExactness_collision
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse,
    audit_exactFamilyExactness_collision_iff_splitMinChecked_collision
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse,
    audit_exactConvention_collision_iff_splitMinChecked_collision
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse⟩

/-- Reviewer package for Theorem 5 code-equality/round-trip obligations across
the exact-convention, split minChecked, and exact-family-exactness entries. -/
abbrev audit_pk_theorem5_codeEqualityReviewerChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :=
  And.intro
    (audit_theorem5_exactConvention_codeRoundTrip
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign))
    (And.intro
      (audit_theorem5_splitMinChecked_codeRoundTrip
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign))
      (audit_theorem5_exactFamilyExactness_codeRoundTrip
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)))

/-- Reviewer package for Theorem 5 normal-form obligations across the
exact-convention, split minChecked, and exact-family-exactness entries. -/
abbrev audit_pk_theorem5_normalFormReviewerChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :=
  And.intro
    (audit_theorem5_exactConvention_normalFormAudit
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign))
    (And.intro
      (audit_theorem5_splitMinChecked_normalFormAudit
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign))
      (audit_theorem5_exactFamilyExactness_normalFormAudit
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)))

/-- Reviewer package for theorem-statement probes: these are the checks that
the exact entries have not been silently weakened. -/
abbrev audit_pk_theorem5_statementProbeReviewerChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :=
  And.intro
    (audit_theorem5_exactConvention_statementProbe
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign))
    (And.intro
      (audit_theorem5_splitMinChecked_statementProbe
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign))
      (audit_theorem5_exactFamilyExactness_statementProbe
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)))

/-- Reviewer package for encoder/certificate bridges across the exact entries. -/
abbrev audit_pk_theorem5_encoderCertificateReviewerChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :=
  And.intro
    (audit_theorem5_exactConvention_encoderCertificateBridge
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign))
    (And.intro
      (audit_theorem5_splitMinChecked_encoderCertificateBridge
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign))
      (audit_theorem5_exactFamilyExactness_encoderCertificateBridge
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)))

/-- Combined reviewer checklist for the current PK-side Theorem 5 audit layer:
statement probes, encoder/certificate bridges, code equality, normal form, and
collision-level equivalence are all exposed from one named object. -/
abbrev audit_pk_theorem5_reviewerChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion) :=
  And.intro
    (audit_pk_theorem5_statementProbeReviewerChecklist
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign))
    (And.intro
      (audit_pk_theorem5_encoderCertificateReviewerChecklist
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign))
      (And.intro
        (audit_pk_theorem5_codeEqualityReviewerChecklist
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign))
        (And.intro
          (audit_pk_theorem5_normalFormReviewerChecklist
            (L := L) (α := α) (n := n)
            (Ax := Ax) (A := A) (B := B) (halign := halign))
          (audit_pk_exactConvention_familyExactness_splitMinChecked_collisionTotalIff
            (L := L) (α := α) (n := n)
            (Ax := Ax) (A := A) (B := B) (halign := halign)
            hcollapse))))

/-- Endpoint-facing reviewer checklist: the upper/lower callable endpoints are
closed both for the exact triangle and for the presentation ladder. -/
abbrev audit_pk_theorem5_endpointReviewerChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth) :=
  And.intro
    (audit_pk_upperLowerExactTriangleEndpointClosure
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hupper)
    (audit_pk_upperLowerPresentationEndpointClosure
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hupper)

/-- Parallel exact-triangle closure: witness-level nonempty equivalence and
collision-level equivalence are exposed together from one entrypoint. -/
abbrev audit_pk_exactTriangle_witnessAndCollisionParallelClosure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion) :=
  And.intro
    (audit_pk_exactConvention_familyExactness_splitMinChecked_totalIff
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign))
    (audit_pk_exactConvention_familyExactness_splitMinChecked_collisionTotalIff
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse)

/-- Total PK-side Theorem 5 reviewer route: statement probes, encoder
certificate bridges, code equality, normal form, exact-triangle equivalence,
and upper/lower endpoint closure are all reachable from this object. -/
abbrev audit_pk_theorem5_endpointFacingTotalReviewerRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth) :=
  And.intro
    (audit_pk_theorem5_reviewerChecklist
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse)
    (And.intro
      (audit_pk_theorem5_endpointReviewerChecklist
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hupper)
      (audit_pk_exactTriangle_witnessAndCollisionParallelClosure
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse))

/-- No-weakening endpoint audit: statement probes, endpoint agreement, collision
endpoint agreement, and callable upper/lower endpoint closure are exposed
together. -/
abbrev audit_pk_theorem5_noWeakeningEndpointAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth) :=
  And.intro
    (audit_pk_theorem5_statementProbeReviewerChecklist
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign))
    (And.intro
      (audit_pk_mainBridge_endpointAgreement
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign))
      (And.intro
        (audit_pk_mainBridge_collisionEndpointAgreement
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign))
        (audit_pk_theorem5_endpointReviewerChecklist
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hupper)))

/-- Callable endpoint from a nonempty exact-convention lower-side witness. -/
theorem audit_pk_exactConventionNonemptyUpperLowerEndpointBridge
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign)) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hpudlak with ⟨hpudlak⟩
  exact
    audit_pk_exactConventionUpperLowerEndpointBridge
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hupper hpudlak

/-- Callable endpoint from a nonempty exact-family-exactness lower-side
witness. -/
theorem audit_pk_exactFamilyExactnessNonemptyUpperLowerEndpointBridge
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign)) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hpudlak with ⟨hpudlak⟩
  exact
    audit_pk_exactFamilyExactnessUpperLowerEndpointBridge
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hupper hpudlak

/-- Callable endpoint from a nonempty exact split minChecked lower-side
witness. -/
theorem audit_pk_splitMinCheckedNonemptyUpperLowerEndpointBridge
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign)) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hpudlak with ⟨hpudlak⟩
  exact
    audit_pk_upperLowerEndpointBridge
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hupper hpudlak

/-- Nonempty endpoint closure for the exact-convention, exact-family-exactness,
and split minChecked triangle. -/
theorem audit_pk_upperLowerExactTriangleNonemptyEndpointClosure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ∧
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ∧
    (Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) := by
  exact
    ⟨fun hp =>
        audit_pk_exactConventionNonemptyUpperLowerEndpointBridge
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hupper hp,
      fun hp =>
        audit_pk_exactFamilyExactnessNonemptyUpperLowerEndpointBridge
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hupper hp,
      fun hp =>
        audit_pk_splitMinCheckedNonemptyUpperLowerEndpointBridge
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hupper hp⟩

/-- Final Theorem 5 audit bundle for the current PK side: total reviewer route,
no-weakening endpoint audit, and nonempty endpoint closure are exposed together. -/
abbrev audit_pk_finalTheorem5AuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth) :=
  And.intro
    (audit_pk_theorem5_endpointFacingTotalReviewerRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper)
    (And.intro
      (audit_pk_theorem5_noWeakeningEndpointAudit
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hupper)
      (audit_pk_upperLowerExactTriangleNonemptyEndpointClosure
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hupper))

/-- Callable endpoint from a nonempty canonical Theorem 5 lower-side witness. -/
theorem audit_pk_canonicalNonemptyUpperLowerEndpointBridge
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign)) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hpudlak with ⟨hpudlak⟩
  exact
    audit_pk_canonicalUpperLowerEndpointBridge
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hupper hpudlak

/-- Callable endpoint from a nonempty convention Theorem 5 lower-side witness. -/
theorem audit_pk_conventionNonemptyUpperLowerEndpointBridge
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign)) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hpudlak with ⟨hpudlak⟩
  exact
    audit_pk_conventionUpperLowerEndpointBridge
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hupper hpudlak

/-- Callable endpoint from a nonempty family-witness lower-side witness. -/
theorem audit_pk_familyWitnessNonemptyUpperLowerEndpointBridge
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign)) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hpudlak with ⟨hpudlak⟩
  exact
    audit_pk_familyWitnessUpperLowerEndpointBridge
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hupper hpudlak

/-- Callable endpoint from a nonempty exact-strengthened lower-side witness. -/
theorem audit_pk_exactStrengthenedNonemptyUpperLowerEndpointBridge
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hpudlak with ⟨hpudlak⟩
  exact
    audit_pk_exactStrengthenedUpperLowerEndpointBridge
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hupper hpudlak

/-- Nonempty endpoint closure for the canonical/convention/family/exact-
strengthened presentation ladder. -/
theorem audit_pk_upperLowerPresentationNonemptyEndpointClosure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth) :
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ∧
    (Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ∧
    (Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) ∧
    (Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign) →
      ¬ _root_.is_rational _root_.euler_mascheroni) := by
  exact
    ⟨fun hp =>
        audit_pk_canonicalNonemptyUpperLowerEndpointBridge
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hupper hp,
      fun hp =>
        audit_pk_conventionNonemptyUpperLowerEndpointBridge
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hupper hp,
      fun hp =>
        audit_pk_familyWitnessNonemptyUpperLowerEndpointBridge
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hupper hp,
      fun hp =>
        audit_pk_exactStrengthenedNonemptyUpperLowerEndpointBridge
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hupper hp⟩

/-- Final Theorem 5 audit bundle with both exact-triangle and presentation-
ladder nonempty endpoint closures. -/
abbrev audit_pk_finalTheorem5AuditBundleWithNonemptyEndpoints
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth) :=
  And.intro
    (audit_pk_finalTheorem5AuditBundle
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper)
    (audit_pk_upperLowerPresentationNonemptyEndpointClosure
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hupper)

/-- Short final reviewer entrypoint for the current PK-side Theorem 5 audit
surface. -/
abbrev audit_pk_finalReviewerEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth) :=
  audit_pk_finalTheorem5AuditBundleWithNonemptyEndpoints
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper

/-- Global reviewer entrypoint: the final Theorem 5 audit surface is paired
with the PK main-bridge no-hidden-assumption audit surface. -/
abbrev audit_pk_globalReviewerEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth) :=
  And.intro
    (audit_pk_finalReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper)
    (And.intro
      (audit_pk_mainBridge_noHiddenAssumption
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign))
      (And.intro
        (audit_pk_mainBridge_collisionNoHiddenAssumption
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse)
        (audit_pk_mainBridge_endpointClosure
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign))))

/-- Local exact-convention nonempty route to the final callable endpoint. -/
theorem audit_pk_localConventionNonempty_to_finalEndpoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign)) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  audit_pk_exactConventionNonemptyUpperLowerEndpointBridge
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hupper hlocal

/-- Local exact-convention route to the final reviewer surface and endpoint:
the reviewer bundle and the callable endpoint are exposed together. -/
abbrev audit_pk_localConvention_to_finalReviewerRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_globalReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper)
    (audit_pk_localConventionNonempty_to_finalEndpoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hupper hlocal)

/-- Global safety bundle: no-weakening endpoint audit and no-hidden-assumption
main-bridge audits are exposed together. -/
abbrev audit_pk_globalNoWeakeningNoHiddenAssumptionBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth) :=
  And.intro
    (audit_pk_theorem5_noWeakeningEndpointAudit
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hupper)
    (And.intro
      (audit_pk_mainBridge_noHiddenAssumption
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign))
      (audit_pk_mainBridge_collisionNoHiddenAssumption
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse))

/-- Fully closed local-convention reviewer route: global reviewer entrypoint,
global safety bundle, and callable endpoint from the local exact-convention
nonempty witness. -/
abbrev audit_pk_localConvention_globalReviewerSafetyRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_localConvention_to_finalReviewerRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal)
    (audit_pk_globalNoWeakeningNoHiddenAssumptionBundle
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper)

/-- Exact-family-exactness nonempty route to the final callable endpoint. -/
theorem audit_pk_exactFamilyExactnessNonempty_to_finalEndpoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign)) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  audit_pk_exactFamilyExactnessNonemptyUpperLowerEndpointBridge
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hupper hfamily

/-- Split minChecked nonempty route to the final callable endpoint. -/
theorem audit_pk_splitMinCheckedNonempty_to_finalEndpoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign)) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  audit_pk_splitMinCheckedNonemptyUpperLowerEndpointBridge
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hupper hsplit

/-- Exact-family-exactness route to the final reviewer surface and endpoint. -/
abbrev audit_pk_exactFamilyExactness_to_finalReviewerRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_globalReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper)
    (audit_pk_exactFamilyExactnessNonempty_to_finalEndpoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hupper hfamily)

/-- Split minChecked route to the final reviewer surface and endpoint. -/
abbrev audit_pk_splitMinChecked_to_finalReviewerRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_globalReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper)
    (audit_pk_splitMinCheckedNonempty_to_finalEndpoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hupper hsplit)

/-- Exact-family-exactness global reviewer/safety route. -/
abbrev audit_pk_exactFamilyExactness_globalReviewerSafetyRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_exactFamilyExactness_to_finalReviewerRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hfamily)
    (audit_pk_globalNoWeakeningNoHiddenAssumptionBundle
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper)

/-- Split minChecked global reviewer/safety route. -/
abbrev audit_pk_splitMinChecked_globalReviewerSafetyRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_splitMinChecked_to_finalReviewerRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hsplit)
    (audit_pk_globalNoWeakeningNoHiddenAssumptionBundle
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper)

/-- All exact presentations expose the same global reviewer/safety route when
their nonempty witnesses are supplied explicitly. -/
abbrev audit_pk_allExactPresentations_globalReviewerSafetyRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_localConvention_globalReviewerSafetyRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal)
    (And.intro
      (audit_pk_exactFamilyExactness_globalReviewerSafetyRoute
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hfamily)
      (audit_pk_splitMinChecked_globalReviewerSafetyRoute
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hsplit))

/-- A single exact-convention nonempty witness transports across the exact
triangle and yields all three global reviewer/safety routes. -/
abbrev audit_pk_exactConventionWitness_allExactPresentations_globalReviewerSafetyRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign)) :=
  audit_pk_allExactPresentations_globalReviewerSafetyRoute
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal
    (audit_pk_exactConvention_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    (audit_pk_exactConvention_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)

/-- A single exact-family-exactness nonempty witness transports across the
exact triangle and yields all three global reviewer/safety routes. -/
abbrev audit_pk_exactFamilyWitness_allExactPresentations_globalReviewerSafetyRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign)) :=
  audit_pk_allExactPresentations_globalReviewerSafetyRoute
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_exactFamilyExactness_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hfamily
    (audit_pk_exactFamilyExactness_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)

/-- A single split minChecked nonempty witness transports across the exact
triangle and yields all three global reviewer/safety routes. -/
abbrev audit_pk_splitMinCheckedWitness_allExactPresentations_globalReviewerSafetyRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign)) :=
  audit_pk_allExactPresentations_globalReviewerSafetyRoute
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_splitMinChecked_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    (audit_pk_splitMinChecked_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    hsplit

/-- Canonical nonempty route to the final callable endpoint. -/
theorem audit_pk_canonicalNonempty_to_finalEndpoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign)) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  audit_pk_canonicalNonemptyUpperLowerEndpointBridge
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hupper hcanonical

/-- Convention-presentation nonempty route to the final callable endpoint. -/
theorem audit_pk_conventionNonempty_to_finalEndpoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign)) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  audit_pk_conventionNonemptyUpperLowerEndpointBridge
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hupper hconvention

/-- Family-witness nonempty route to the final callable endpoint. -/
theorem audit_pk_familyWitnessNonempty_to_finalEndpoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign)) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  audit_pk_familyWitnessNonemptyUpperLowerEndpointBridge
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hupper hfamilyWitness

/-- Exact-strengthened nonempty route to the final callable endpoint. -/
theorem audit_pk_exactStrengthenedNonempty_to_finalEndpoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  audit_pk_exactStrengthenedNonemptyUpperLowerEndpointBridge
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hupper hexactStrengthened

/-- Canonical route to the final reviewer surface and endpoint. -/
abbrev audit_pk_canonical_to_finalReviewerRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_globalReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper)
    (audit_pk_canonicalNonempty_to_finalEndpoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hupper hcanonical)

/-- Convention-presentation route to the final reviewer surface and endpoint. -/
abbrev audit_pk_convention_to_finalReviewerRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_globalReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper)
    (audit_pk_conventionNonempty_to_finalEndpoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hupper hconvention)

/-- Family-witness route to the final reviewer surface and endpoint. -/
abbrev audit_pk_familyWitness_to_finalReviewerRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_globalReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper)
    (audit_pk_familyWitnessNonempty_to_finalEndpoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hupper hfamilyWitness)

/-- Exact-strengthened route to the final reviewer surface and endpoint. -/
abbrev audit_pk_exactStrengthened_to_finalReviewerRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_globalReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper)
    (audit_pk_exactStrengthenedNonempty_to_finalEndpoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hupper hexactStrengthened)

/-- Canonical global reviewer/safety route. -/
abbrev audit_pk_canonical_globalReviewerSafetyRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_canonical_to_finalReviewerRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical)
    (audit_pk_globalNoWeakeningNoHiddenAssumptionBundle
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper)

/-- Convention-presentation global reviewer/safety route. -/
abbrev audit_pk_convention_globalReviewerSafetyRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_convention_to_finalReviewerRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hconvention)
    (audit_pk_globalNoWeakeningNoHiddenAssumptionBundle
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper)

/-- Family-witness global reviewer/safety route. -/
abbrev audit_pk_familyWitness_globalReviewerSafetyRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_familyWitness_to_finalReviewerRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hfamilyWitness)
    (audit_pk_globalNoWeakeningNoHiddenAssumptionBundle
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper)

/-- Exact-strengthened global reviewer/safety route. -/
abbrev audit_pk_exactStrengthened_globalReviewerSafetyRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_exactStrengthened_to_finalReviewerRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hexactStrengthened)
    (audit_pk_globalNoWeakeningNoHiddenAssumptionBundle
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper)

/-- Presentation-ladder global reviewer/safety route for canonical,
convention, family-witness, and exact-strengthened entries. -/
abbrev audit_pk_presentationLadder_globalReviewerSafetyRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_canonical_globalReviewerSafetyRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical)
    (And.intro
      (audit_pk_convention_globalReviewerSafetyRoute
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hconvention)
      (And.intro
        (audit_pk_familyWitness_globalReviewerSafetyRoute
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hfamilyWitness)
        (audit_pk_exactStrengthened_globalReviewerSafetyRoute
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hexactStrengthened)))

/-- All currently exposed PK-side presentations, exact-triangle and
presentation-ladder alike, share the same global reviewer/safety surface. -/
abbrev audit_pk_allPresentations_globalReviewerSafetyRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_allExactPresentations_globalReviewerSafetyRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit)
    (audit_pk_presentationLadder_globalReviewerSafetyRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)

/-- Presentation-ladder endpoint closure with its global reviewer/safety route
attached. -/
abbrev audit_pk_presentationEndpointClosureWithReviewer
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_presentationLadder_globalReviewerSafetyRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (audit_pk_upperLowerPresentationNonemptyEndpointClosure
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hupper)

/-- All-presentation endpoint closure with the global reviewer/safety route
attached. -/
abbrev audit_pk_allPresentationsEndpointClosureWithReviewer
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_allPresentations_globalReviewerSafetyRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
      hfamilyWitness hexactStrengthened)
    (And.intro
      (audit_pk_upperLowerExactTriangleNonemptyEndpointClosure
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hupper)
      (audit_pk_upperLowerPresentationNonemptyEndpointClosure
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hupper))

/-- Master reviewer entrypoint for the current PK-side Theorem 5 surface:
final reviewer audit, exact-presentation routes, all-presentation routes, and
endpoint closure with reviewer are exposed from one object. -/
abbrev audit_pk_masterReviewerEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_finalReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper)
    (And.intro
      (audit_pk_allExactPresentations_globalReviewerSafetyRoute
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hlocal hexactFamily hsplit)
      (And.intro
        (audit_pk_allPresentations_globalReviewerSafetyRoute
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hlocal hexactFamily hsplit hcanonical
          hconvention hfamilyWitness hexactStrengthened)
        (audit_pk_allPresentationsEndpointClosureWithReviewer
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hlocal hexactFamily hsplit hcanonical
          hconvention hfamilyWitness hexactStrengthened)))

/-- Master exact-presentation route from a single exact-convention witness.
This only transports inside the exact triangle; it does not claim canonical or
presentation-ladder witnesses. -/
abbrev audit_pk_exactConventionWitness_masterExactReviewerEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_exactConventionWitness_allExactPresentations_globalReviewerSafetyRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal)
    (And.intro
      (audit_pk_globalNoWeakeningNoHiddenAssumptionBundle
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper)
      (audit_pk_upperLowerExactTriangleNonemptyEndpointClosure
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hupper))

/-- Master exact-presentation route from a single exact-family-exactness
witness. -/
abbrev audit_pk_exactFamilyWitness_masterExactReviewerEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_exactFamilyWitness_allExactPresentations_globalReviewerSafetyRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hfamily)
    (And.intro
      (audit_pk_globalNoWeakeningNoHiddenAssumptionBundle
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper)
      (audit_pk_upperLowerExactTriangleNonemptyEndpointClosure
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hupper))

/-- Master exact-presentation route from a single split minChecked witness. -/
abbrev audit_pk_splitMinCheckedWitness_masterExactReviewerEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_splitMinCheckedWitness_allExactPresentations_globalReviewerSafetyRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hsplit)
    (And.intro
      (audit_pk_globalNoWeakeningNoHiddenAssumptionBundle
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper)
      (audit_pk_upperLowerExactTriangleNonemptyEndpointClosure
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hupper))

/-- Master presentation-ladder reviewer route. -/
abbrev audit_pk_presentationLadder_masterReviewerRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_presentationLadder_globalReviewerSafetyRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (audit_pk_presentationEndpointClosureWithReviewer
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)

/-- Master all-presentation reviewer route. -/
abbrev audit_pk_allPresentations_masterReviewerRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_masterReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
      hfamilyWitness hexactStrengthened)
    (audit_pk_allPresentationsEndpointClosureWithReviewer
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
      hfamilyWitness hexactStrengthened)

/-- Short alias for the current strongest all-presentation master reviewer
surface. -/
abbrev audit_pk_masterReviewerEntryPointAllPresentations
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_allPresentations_masterReviewerRoute
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
    hfamilyWitness hexactStrengthened

/-- One-way master route from a single canonical presentation witness. This
does not assert equivalence with the other presentation-ladder entries. -/
abbrev audit_pk_canonicalWitness_masterPresentationReviewerEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_canonical_globalReviewerSafetyRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical)
    (And.intro
      (audit_pk_canonicalNonempty_to_finalEndpoint
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hupper hcanonical)
      (audit_pk_globalNoWeakeningNoHiddenAssumptionBundle
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper))

/-- One-way master route from a single convention-presentation witness. This
does not assert equivalence with the other presentation-ladder entries. -/
abbrev audit_pk_conventionWitness_masterPresentationReviewerEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_convention_globalReviewerSafetyRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hconvention)
    (And.intro
      (audit_pk_conventionNonempty_to_finalEndpoint
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hupper hconvention)
      (audit_pk_globalNoWeakeningNoHiddenAssumptionBundle
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper))

/-- One-way master route from a single family-witness presentation witness.
This does not assert equivalence with the other presentation-ladder entries. -/
abbrev audit_pk_familyWitness_masterPresentationReviewerEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_familyWitness_globalReviewerSafetyRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hfamilyWitness)
    (And.intro
      (audit_pk_familyWitnessNonempty_to_finalEndpoint
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hupper hfamilyWitness)
      (audit_pk_globalNoWeakeningNoHiddenAssumptionBundle
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper))

/-- One-way master route from a single exact-strengthened presentation witness.
This does not assert equivalence with the other presentation-ladder entries. -/
abbrev audit_pk_exactStrengthenedWitness_masterPresentationReviewerEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_exactStrengthened_globalReviewerSafetyRoute
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hexactStrengthened)
    (And.intro
      (audit_pk_exactStrengthenedNonempty_to_finalEndpoint
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hupper hexactStrengthened)
      (audit_pk_globalNoWeakeningNoHiddenAssumptionBundle
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper))

/-- Presentation-ladder single-witness audit bundle. It packages only one-way
routes for each presentation; no cross-presentation equivalence is asserted. -/
abbrev audit_pk_presentationSingleWitnessOneWayAuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_canonicalWitness_masterPresentationReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical)
    (And.intro
      (audit_pk_conventionWitness_masterPresentationReviewerEntryPoint
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hconvention)
      (And.intro
        (audit_pk_familyWitness_masterPresentationReviewerEntryPoint
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hfamilyWitness)
        (audit_pk_exactStrengthenedWitness_masterPresentationReviewerEntryPoint
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hexactStrengthened)))

/-- Honest combined audit from one exact-convention witness plus supplied
presentation witnesses: exact-triangle equivalence is used only inside the
exact triangle; presentation entries are packaged as one-way routes. -/
abbrev audit_pk_exactConventionAndPresentation_honestMasterAuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_exactConventionWitness_masterExactReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal)
    (audit_pk_presentationSingleWitnessOneWayAuditBundle
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)

/-- Honest combined audit from one exact-family-exactness witness plus supplied
presentation witnesses. -/
abbrev audit_pk_exactFamilyAndPresentation_honestMasterAuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_exactFamilyWitness_masterExactReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hfamily)
    (audit_pk_presentationSingleWitnessOneWayAuditBundle
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)

/-- Honest combined audit from one split minChecked witness plus supplied
presentation witnesses. -/
abbrev audit_pk_splitMinCheckedAndPresentation_honestMasterAuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_splitMinCheckedWitness_masterExactReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hsplit)
    (audit_pk_presentationSingleWitnessOneWayAuditBundle
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)

/-- Boundary audit: exact-triangle equivalence is packaged separately from
presentation-ladder one-way routes.  This is the main guard against reading
presentation entries as if they had a proved cross-presentation iff. -/
abbrev audit_pk_exactTriangle_vs_presentationOneWayBoundaryAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_exactTriangle_witnessAndCollisionParallelClosure
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse)
    (And.intro
      (audit_pk_presentationSingleWitnessOneWayAuditBundle
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened)
      (audit_pk_presentationEndpointClosureWithReviewer
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened))

/-- Current closed PK-side audit surface: all-presentation master route,
all-presentation endpoint closure, and the exact-vs-presentation boundary audit
are available together. -/
abbrev audit_pk_currentClosedSurfaceMasterBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_masterReviewerEntryPointAllPresentations
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
      hfamilyWitness hexactStrengthened)
    (And.intro
      (audit_pk_allPresentationsEndpointClosureWithReviewer
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hlocal hexactFamily hsplit hcanonical
        hconvention hfamilyWitness hexactStrengthened)
      (audit_pk_exactTriangle_vs_presentationOneWayBoundaryAudit
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened))

/-- Short final alias for the strongest currently closed, boundary-explicit PK
audit surface. -/
abbrev audit_pk_currentClosedBoundaryExplicitReviewerEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_currentClosedSurfaceMasterBundle
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
    hfamilyWitness hexactStrengthened

/-- Boundary-explicit current closed surface from a single exact-convention
witness plus explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactConventionWitness_currentClosedBoundaryEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_currentClosedBoundaryExplicitReviewerEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal
    (audit_pk_exactConvention_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    (audit_pk_exactConvention_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Boundary-explicit current closed surface from a single exact-family-
exactness witness plus explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactFamilyWitness_currentClosedBoundaryEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_currentClosedBoundaryExplicitReviewerEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_exactFamilyExactness_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hfamily
    (audit_pk_exactFamilyExactness_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Boundary-explicit current closed surface from a single split minChecked
witness plus explicitly supplied presentation witnesses. -/
abbrev audit_pk_splitMinCheckedWitness_currentClosedBoundaryEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_currentClosedBoundaryExplicitReviewerEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_splitMinChecked_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    (audit_pk_splitMinChecked_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    hsplit hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Exact-triangle local encoding checklist: statement probes, encoder/
certificate bridges, code equality, and normal form are exposed together. -/
abbrev audit_pk_exactTriangle_localEncodingReviewerChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment} :=
  And.intro
    (audit_pk_theorem5_statementProbeReviewerChecklist
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign))
    (And.intro
      (audit_pk_theorem5_encoderCertificateReviewerChecklist
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign))
      (And.intro
        (audit_pk_theorem5_codeEqualityReviewerChecklist
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign))
        (audit_pk_theorem5_normalFormReviewerChecklist
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign))))

/-- Boundary-aware encoding checklist: exact-triangle encoding checks are kept
separate from presentation-ladder one-way routes.  No presentation-ladder iff
is asserted here. -/
abbrev audit_pk_presentationOneWay_encodingBoundaryChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_exactTriangle_localEncodingReviewerChecklist
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign))
    (And.intro
      (audit_pk_presentationSingleWitnessOneWayAuditBundle
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened)
      (audit_pk_exactTriangle_vs_presentationOneWayBoundaryAudit
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened))

/-- Current closed surface with encoding and boundary audits attached. -/
abbrev audit_pk_currentClosedSurfaceEncodingBoundaryBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_currentClosedBoundaryExplicitReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical
      hconvention hfamilyWitness hexactStrengthened)
    (audit_pk_presentationOneWay_encodingBoundaryChecklist
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)

/-- Short boundary entrypoint documenting that presentation-ladder entries are
currently audited as one-way routes, not as cross-presentation iff routes. -/
abbrev audit_pk_noPresentationIffBoundaryReviewerEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_presentationOneWay_encodingBoundaryChecklist
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hcanonical hconvention hfamilyWitness
    hexactStrengthened

/-- Current closed encoding/boundary surface from a single exact-convention
witness plus explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactConventionWitness_currentClosedEncodingBoundaryEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_currentClosedSurfaceEncodingBoundaryBundle
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal
    (audit_pk_exactConvention_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    (audit_pk_exactConvention_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Current closed encoding/boundary surface from a single exact-family-
exactness witness plus explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactFamilyWitness_currentClosedEncodingBoundaryEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_currentClosedSurfaceEncodingBoundaryBundle
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_exactFamilyExactness_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hfamily
    (audit_pk_exactFamilyExactness_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Current closed encoding/boundary surface from a single split minChecked
witness plus explicitly supplied presentation witnesses. -/
abbrev audit_pk_splitMinCheckedWitness_currentClosedEncodingBoundaryEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_currentClosedSurfaceEncodingBoundaryBundle
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_splitMinChecked_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    (audit_pk_splitMinChecked_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    hsplit hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Local endpoint/boundary audit for the canonical presentation entry.  It is
one-way and explicitly carries the no-presentation-iff boundary marker. -/
abbrev audit_pk_canonical_localEndpointBoundaryAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_canonicalWitness_masterPresentationReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical)
    (audit_pk_noPresentationIffBoundaryReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)

/-- Local endpoint/boundary audit for the convention presentation entry. -/
abbrev audit_pk_convention_localEndpointBoundaryAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_conventionWitness_masterPresentationReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hconvention)
    (audit_pk_noPresentationIffBoundaryReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)

/-- Local endpoint/boundary audit for the family-witness presentation entry. -/
abbrev audit_pk_familyWitness_localEndpointBoundaryAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_familyWitness_masterPresentationReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hfamilyWitness)
    (audit_pk_noPresentationIffBoundaryReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)

/-- Local endpoint/boundary audit for the exact-strengthened presentation
entry. -/
abbrev audit_pk_exactStrengthened_localEndpointBoundaryAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_exactStrengthenedWitness_masterPresentationReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hexactStrengthened)
    (audit_pk_noPresentationIffBoundaryReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)

/-- Local presentation audit bundle: every presentation entry gets its own
one-way endpoint/boundary audit, and no cross-presentation iff is asserted. -/
abbrev audit_pk_presentationLocalEndpointBoundaryAuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_canonical_localEndpointBoundaryAudit
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (And.intro
      (audit_pk_convention_localEndpointBoundaryAudit
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened)
      (And.intro
        (audit_pk_familyWitness_localEndpointBoundaryAudit
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hcanonical hconvention hfamilyWitness
          hexactStrengthened)
        (audit_pk_exactStrengthened_localEndpointBoundaryAudit
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hcanonical hconvention hfamilyWitness
          hexactStrengthened)))

/-- Current closed encoding/boundary surface with the local presentation audits
attached. -/
abbrev audit_pk_currentClosedSurfaceWithPresentationLocalAudits
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_currentClosedSurfaceEncodingBoundaryBundle
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical
      hconvention hfamilyWitness hexactStrengthened)
    (audit_pk_presentationLocalEndpointBoundaryAuditBundle
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)

/-- Final short entrypoint for the current boundary-aware PK audit surface. -/
abbrev audit_pk_finalBoundaryAwareEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_currentClosedSurfaceWithPresentationLocalAudits
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
    hfamilyWitness hexactStrengthened

/-- Canonical local audit with the exact-triangle encoding boundary attached.
This keeps the canonical route one-way and exposes code/normalForm checks only
through the already-closed exact-triangle checklist. -/
abbrev audit_pk_canonical_localAuditWithExactEncodingBoundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_canonical_localEndpointBoundaryAudit
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (audit_pk_exactTriangle_localEncodingReviewerChecklist
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign))

/-- Convention local audit with the exact-triangle encoding boundary attached. -/
abbrev audit_pk_convention_localAuditWithExactEncodingBoundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_convention_localEndpointBoundaryAudit
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (audit_pk_exactTriangle_localEncodingReviewerChecklist
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign))

/-- Family-witness local audit with the exact-triangle encoding boundary
attached. -/
abbrev audit_pk_familyWitness_localAuditWithExactEncodingBoundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_familyWitness_localEndpointBoundaryAudit
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (audit_pk_exactTriangle_localEncodingReviewerChecklist
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign))

/-- Exact-strengthened local audit with the exact-triangle encoding boundary
attached. -/
abbrev audit_pk_exactStrengthened_localAuditWithExactEncodingBoundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_exactStrengthened_localEndpointBoundaryAudit
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (audit_pk_exactTriangle_localEncodingReviewerChecklist
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign))

/-- Presentation-local audit bundle with exact-triangle encoding boundary
attached to every one-way presentation entry. -/
abbrev audit_pk_presentationLocalEncodingBoundaryAuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_canonical_localAuditWithExactEncodingBoundary
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (And.intro
      (audit_pk_convention_localAuditWithExactEncodingBoundary
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened)
      (And.intro
        (audit_pk_familyWitness_localAuditWithExactEncodingBoundary
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hcanonical hconvention hfamilyWitness
          hexactStrengthened)
        (audit_pk_exactStrengthened_localAuditWithExactEncodingBoundary
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hcanonical hconvention hfamilyWitness
          hexactStrengthened)))

/-- Final boundary-aware encoding entrypoint: current closed surface, local
presentation audits, and exact-triangle encoding boundary checks are all
available together. -/
abbrev audit_pk_finalBoundaryAwareEncodingEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_currentClosedSurfaceWithPresentationLocalAudits
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical
      hconvention hfamilyWitness hexactStrengthened)
    (audit_pk_presentationLocalEncodingBoundaryAuditBundle
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)

/-- Final boundary-aware encoding entrypoint from a single exact-convention
witness plus explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactConventionWitness_finalBoundaryAwareEncodingEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_finalBoundaryAwareEncodingEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal
    (audit_pk_exactConvention_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    (audit_pk_exactConvention_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Final boundary-aware encoding entrypoint from a single exact-family-
exactness witness plus explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactFamilyWitness_finalBoundaryAwareEncodingEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_finalBoundaryAwareEncodingEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_exactFamilyExactness_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hfamily
    (audit_pk_exactFamilyExactness_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Final boundary-aware encoding entrypoint from a single split minChecked
witness plus explicitly supplied presentation witnesses. -/
abbrev audit_pk_splitMinCheckedWitness_finalBoundaryAwareEncodingEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_finalBoundaryAwareEncodingEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_splitMinChecked_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    (audit_pk_splitMinChecked_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    hsplit hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Canonical local certificate audit: canonical endpoint/boundary audit plus
the exact-triangle encoder/certificate checklist. -/
abbrev audit_pk_canonical_localCertificateBoundaryAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_canonical_localEndpointBoundaryAudit
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (audit_pk_theorem5_encoderCertificateReviewerChecklist
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign))

/-- Convention local certificate audit. -/
abbrev audit_pk_convention_localCertificateBoundaryAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_convention_localEndpointBoundaryAudit
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (audit_pk_theorem5_encoderCertificateReviewerChecklist
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign))

/-- Family-witness local certificate audit. -/
abbrev audit_pk_familyWitness_localCertificateBoundaryAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_familyWitness_localEndpointBoundaryAudit
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (audit_pk_theorem5_encoderCertificateReviewerChecklist
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign))

/-- Exact-strengthened local certificate audit. -/
abbrev audit_pk_exactStrengthened_localCertificateBoundaryAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_exactStrengthened_localEndpointBoundaryAudit
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (audit_pk_theorem5_encoderCertificateReviewerChecklist
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign))

/-- Presentation-local certificate audit bundle.  The certificate checklist is
the exact-triangle checklist; presentation entries remain one-way. -/
abbrev audit_pk_presentationLocalCertificateBoundaryAuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_canonical_localCertificateBoundaryAudit
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (And.intro
      (audit_pk_convention_localCertificateBoundaryAudit
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened)
      (And.intro
        (audit_pk_familyWitness_localCertificateBoundaryAudit
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hcanonical hconvention hfamilyWitness
          hexactStrengthened)
        (audit_pk_exactStrengthened_localCertificateBoundaryAudit
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hcanonical hconvention hfamilyWitness
          hexactStrengthened)))

/-- Final boundary-aware certificate entrypoint: current boundary-aware
encoding surface plus presentation-local certificate audits. -/
abbrev audit_pk_finalBoundaryAwareCertificateEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_finalBoundaryAwareEncodingEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical
      hconvention hfamilyWitness hexactStrengthened)
    (audit_pk_presentationLocalCertificateBoundaryAuditBundle
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)

/-- Final boundary-aware certificate entrypoint from a single exact-convention
witness plus explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactConventionWitness_finalBoundaryAwareCertificateEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_finalBoundaryAwareCertificateEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal
    (audit_pk_exactConvention_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    (audit_pk_exactConvention_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Final boundary-aware certificate entrypoint from a single exact-family-
exactness witness plus explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactFamilyWitness_finalBoundaryAwareCertificateEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_finalBoundaryAwareCertificateEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_exactFamilyExactness_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hfamily
    (audit_pk_exactFamilyExactness_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Final boundary-aware certificate entrypoint from a single split minChecked
witness plus explicitly supplied presentation witnesses. -/
abbrev audit_pk_splitMinCheckedWitness_finalBoundaryAwareCertificateEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_finalBoundaryAwareCertificateEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_splitMinChecked_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    (audit_pk_splitMinChecked_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    hsplit hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Final boundary-aware complete entrypoint: endpoint, encoding,
certificate, and no-presentation-iff boundary surfaces are exposed together. -/
abbrev audit_pk_finalBoundaryAwareCompleteEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_finalBoundaryAwareEncodingEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
      hfamilyWitness hexactStrengthened)
    (And.intro
      (audit_pk_finalBoundaryAwareCertificateEntryPoint
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hlocal hexactFamily hsplit hcanonical
        hconvention hfamilyWitness hexactStrengthened)
      (And.intro
        (audit_pk_finalBoundaryAwareEntryPoint
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hlocal hexactFamily hsplit hcanonical
          hconvention hfamilyWitness hexactStrengthened)
        (audit_pk_noPresentationIffBoundaryReviewerEntryPoint
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hcanonical hconvention hfamilyWitness
          hexactStrengthened)))

/-- Final complete entrypoint from a single exact-convention witness plus
explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactConventionWitness_finalBoundaryAwareCompleteEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_finalBoundaryAwareCompleteEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal
    (audit_pk_exactConvention_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    (audit_pk_exactConvention_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Final complete entrypoint from a single exact-family-exactness witness plus
explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactFamilyWitness_finalBoundaryAwareCompleteEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_finalBoundaryAwareCompleteEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_exactFamilyExactness_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hfamily
    (audit_pk_exactFamilyExactness_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Final complete entrypoint from a single split minChecked witness plus
explicitly supplied presentation witnesses. -/
abbrev audit_pk_splitMinCheckedWitness_finalBoundaryAwareCompleteEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_finalBoundaryAwareCompleteEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_splitMinChecked_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    (audit_pk_splitMinChecked_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    hsplit hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Canonical presentation local complete audit: endpoint, encoding-boundary,
and certificate-boundary audits are exposed together. -/
abbrev audit_pk_canonical_localCompleteAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_canonical_localEndpointBoundaryAudit
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (And.intro
      (audit_pk_canonical_localAuditWithExactEncodingBoundary
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened)
      (audit_pk_canonical_localCertificateBoundaryAudit
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened))

/-- Convention presentation local complete audit. -/
abbrev audit_pk_convention_localCompleteAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_convention_localEndpointBoundaryAudit
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (And.intro
      (audit_pk_convention_localAuditWithExactEncodingBoundary
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened)
      (audit_pk_convention_localCertificateBoundaryAudit
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened))

/-- Family-witness presentation local complete audit. -/
abbrev audit_pk_familyWitness_localCompleteAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_familyWitness_localEndpointBoundaryAudit
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (And.intro
      (audit_pk_familyWitness_localAuditWithExactEncodingBoundary
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened)
      (audit_pk_familyWitness_localCertificateBoundaryAudit
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened))

/-- Exact-strengthened presentation local complete audit. -/
abbrev audit_pk_exactStrengthened_localCompleteAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_exactStrengthened_localEndpointBoundaryAudit
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (And.intro
      (audit_pk_exactStrengthened_localAuditWithExactEncodingBoundary
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened)
      (audit_pk_exactStrengthened_localCertificateBoundaryAudit
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened))

/-- Presentation-local complete audit bundle.  Every presentation entry remains
one-way; this bundle only joins its endpoint, encoding, and certificate audits. -/
abbrev audit_pk_presentationLocalCompleteAuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_canonical_localCompleteAudit
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (And.intro
      (audit_pk_convention_localCompleteAudit
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened)
      (And.intro
        (audit_pk_familyWitness_localCompleteAudit
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hcanonical hconvention hfamilyWitness
          hexactStrengthened)
        (audit_pk_exactStrengthened_localCompleteAudit
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hcanonical hconvention hfamilyWitness
          hexactStrengthened)))

/-- Final complete reviewer entrypoint: the boundary-aware complete entrypoint
and the local presentation complete audits are exposed together. -/
abbrev audit_pk_finalCompleteReviewerEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_finalBoundaryAwareCompleteEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical
      hconvention hfamilyWitness hexactStrengthened)
    (audit_pk_presentationLocalCompleteAuditBundle
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)

/-- Final complete reviewer route from a single exact-convention witness plus
explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactConventionWitness_finalCompleteReviewerEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_finalCompleteReviewerEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal
    (audit_pk_exactConvention_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    (audit_pk_exactConvention_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Final complete reviewer route from a single exact-family-exactness witness
plus explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactFamilyWitness_finalCompleteReviewerEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_finalCompleteReviewerEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_exactFamilyExactness_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hfamily
    (audit_pk_exactFamilyExactness_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Final complete reviewer route from a single split minChecked witness plus
explicitly supplied presentation witnesses. -/
abbrev audit_pk_splitMinCheckedWitness_finalCompleteReviewerEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_finalCompleteReviewerEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_splitMinChecked_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    (audit_pk_splitMinChecked_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    hsplit hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Short final alias for the current complete PK reviewer surface. -/
abbrev audit_pk_finalCompleteReviewerEntryPointShort
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_finalCompleteReviewerEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
    hfamilyWitness hexactStrengthened

/-- Auditor-facing final closure: the complete, boundary-aware, encoding, and
certificate final entrypoints are all exposed from one object. -/
abbrev audit_pk_auditorFacingFinalClosure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_finalCompleteReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
      hfamilyWitness hexactStrengthened)
    (And.intro
      (audit_pk_finalBoundaryAwareEntryPoint
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hlocal hexactFamily hsplit hcanonical
        hconvention hfamilyWitness hexactStrengthened)
      (And.intro
        (audit_pk_finalBoundaryAwareEncodingEntryPoint
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hlocal hexactFamily hsplit hcanonical
          hconvention hfamilyWitness hexactStrengthened)
        (audit_pk_finalBoundaryAwareCertificateEntryPoint
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hlocal hexactFamily hsplit hcanonical
          hconvention hfamilyWitness hexactStrengthened)))

/-- Stage-closed summary entrypoint for the current PK/Theorem 5 audit
surface.  It joins the auditor-facing final closure, the no-presentation-iff
boundary, the final complete reviewer entrypoint, and the presentation-local
complete audit bundle. -/
abbrev audit_pk_stageClosedSummaryEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_auditorFacingFinalClosure
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
      hfamilyWitness hexactStrengthened)
    (And.intro
      (audit_pk_noPresentationIffBoundaryReviewerEntryPoint
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened)
      (And.intro
        (audit_pk_finalCompleteReviewerEntryPoint
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hlocal hexactFamily hsplit hcanonical
          hconvention hfamilyWitness hexactStrengthened)
        (audit_pk_presentationLocalCompleteAuditBundle
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hcanonical hconvention hfamilyWitness
          hexactStrengthened)))

/-- Stage-closed summary from a single exact-convention witness plus explicitly
supplied presentation witnesses. -/
abbrev audit_pk_exactConventionWitness_stageClosedSummaryEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_stageClosedSummaryEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal
    (audit_pk_exactConvention_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    (audit_pk_exactConvention_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Stage-closed summary from a single exact-family-exactness witness plus
explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactFamilyWitness_stageClosedSummaryEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_stageClosedSummaryEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_exactFamilyExactness_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hfamily
    (audit_pk_exactFamilyExactness_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Stage-closed summary from a single split minChecked witness plus explicitly
supplied presentation witnesses. -/
abbrev audit_pk_splitMinCheckedWitness_stageClosedSummaryEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_stageClosedSummaryEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_splitMinChecked_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    (audit_pk_splitMinChecked_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    hsplit hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Short final stage-closed alias for the current boundary-aware complete PK
audit surface. -/
abbrev audit_pk_stageClosedSummaryEntryPointShort
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_stageClosedSummaryEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
    hfamilyWitness hexactStrengthened

/-- Auditor-facing final stage closure: stage-closed summary and final closure
are exposed together under a short searchable name. -/
abbrev audit_pk_auditorFacingFinalStageClosure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_stageClosedSummaryEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
      hfamilyWitness hexactStrengthened)
    (audit_pk_auditorFacingFinalClosure
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
      hfamilyWitness hexactStrengthened)

/-- Presentation transport-gap boundary: the current presentation ladder is
audited as one-way and locally complete, without asserting a cross-presentation
iff. -/
abbrev audit_pk_presentationTransportGapBoundaryEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_noPresentationIffBoundaryReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (And.intro
      (audit_pk_presentationSingleWitnessOneWayAuditBundle
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened)
      (audit_pk_presentationLocalCompleteAuditBundle
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened))

/-- Post-stage closed audit bundle: the stage-closed summary, auditor-facing
final stage closure, and presentation transport-gap boundary are exposed
together. -/
abbrev audit_pk_postStageClosedAuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_stageClosedSummaryEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
      hfamilyWitness hexactStrengthened)
    (And.intro
      (audit_pk_auditorFacingFinalStageClosure
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hlocal hexactFamily hsplit hcanonical
        hconvention hfamilyWitness hexactStrengthened)
      (audit_pk_presentationTransportGapBoundaryEntryPoint
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hcanonical hconvention hfamilyWitness
        hexactStrengthened))

/-- Post-stage closed route from a single exact-convention witness plus
explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactConventionWitness_postStageClosedAuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_postStageClosedAuditBundle
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal
    (audit_pk_exactConvention_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    (audit_pk_exactConvention_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Post-stage closed route from a single exact-family-exactness witness plus
explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactFamilyWitness_postStageClosedAuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_postStageClosedAuditBundle
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_exactFamilyExactness_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hfamily
    (audit_pk_exactFamilyExactness_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Post-stage closed route from a single split minChecked witness plus
explicitly supplied presentation witnesses. -/
abbrev audit_pk_splitMinCheckedWitness_postStageClosedAuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_postStageClosedAuditBundle
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_splitMinChecked_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    (audit_pk_splitMinChecked_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    hsplit hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Short final post-stage alias for the current closed PK audit surface. -/
abbrev audit_pk_finalPostStageClosedReviewerEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_postStageClosedAuditBundle
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
    hfamilyWitness hexactStrengthened

/-- Closed-surface safety bundle: the post-stage closed entrypoint, global
no-weakening/no-hidden-assumption audit, exact-triangle iff closure, and
presentation transport-gap boundary are exposed together. -/
abbrev audit_pk_closedSurfaceNoHiddenNoWeakeningBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_finalPostStageClosedReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
      hfamilyWitness hexactStrengthened)
    (And.intro
      (audit_pk_globalNoWeakeningNoHiddenAssumptionBundle
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper)
      (And.intro
        (audit_pk_exactTriangle_witnessAndCollisionParallelClosure
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse)
        (audit_pk_presentationTransportGapBoundaryEntryPoint
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hcanonical hconvention hfamilyWitness
          hexactStrengthened)))

/-- Closed-surface safety route from a single exact-convention witness plus
explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactConventionWitness_closedSurfaceNoHiddenNoWeakeningBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_closedSurfaceNoHiddenNoWeakeningBundle
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal
    (audit_pk_exactConvention_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    (audit_pk_exactConvention_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Closed-surface safety route from a single exact-family-exactness witness
plus explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactFamilyWitness_closedSurfaceNoHiddenNoWeakeningBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_closedSurfaceNoHiddenNoWeakeningBundle
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_exactFamilyExactness_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hfamily
    (audit_pk_exactFamilyExactness_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Closed-surface safety route from a single split minChecked witness plus
explicitly supplied presentation witnesses. -/
abbrev audit_pk_splitMinCheckedWitness_closedSurfaceNoHiddenNoWeakeningBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_closedSurfaceNoHiddenNoWeakeningBundle
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_splitMinChecked_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    (audit_pk_splitMinChecked_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    hsplit hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Short alias for the current closed-surface no-hidden/no-weakening bundle. -/
abbrev audit_pk_closedSurfaceSafetyEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_closedSurfaceNoHiddenNoWeakeningBundle
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
    hfamilyWitness hexactStrengthened

/-- Final total closed audit entrypoint for the current PK-side surface. -/
abbrev audit_pk_finalTotalClosedAuditEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_finalPostStageClosedReviewerEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
      hfamilyWitness hexactStrengthened)
    (audit_pk_closedSurfaceSafetyEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
      hfamilyWitness hexactStrengthened)

/-- Final total closed audit route from a single exact-convention witness plus
explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactConventionWitness_finalTotalClosedAuditEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_finalTotalClosedAuditEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal
    (audit_pk_exactConvention_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    (audit_pk_exactConvention_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Final total closed audit route from a single exact-family-exactness witness
plus explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactFamilyWitness_finalTotalClosedAuditEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_finalTotalClosedAuditEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_exactFamilyExactness_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hfamily
    (audit_pk_exactFamilyExactness_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Final total closed audit route from a single split minChecked witness plus
explicitly supplied presentation witnesses. -/
abbrev audit_pk_splitMinCheckedWitness_finalTotalClosedAuditEntryPoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_finalTotalClosedAuditEntryPoint
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_splitMinChecked_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    (audit_pk_splitMinChecked_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    hsplit hcanonical hconvention hfamilyWitness hexactStrengthened

/-- All exact witnesses expose the final total closed audit route. -/
abbrev audit_pk_allExactWitnesses_finalTotalClosedAuditBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_exactConventionWitness_finalTotalClosedAuditEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hcanonical hconvention hfamilyWitness
      hexactStrengthened)
    (And.intro
      (audit_pk_exactFamilyWitness_finalTotalClosedAuditEntryPoint
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hfamily hcanonical hconvention hfamilyWitness
        hexactStrengthened)
      (audit_pk_splitMinCheckedWitness_finalTotalClosedAuditEntryPoint
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hsplit hcanonical hconvention hfamilyWitness
        hexactStrengthened))

/-- Final total auditor surface: final total closed audit plus the stage-closed
summary, under one searchable object. -/
abbrev audit_pk_finalTotalAuditorSurface
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hexactFamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_finalTotalClosedAuditEntryPoint
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
      hfamilyWitness hexactStrengthened)
    (audit_pk_stageClosedSummaryEntryPointShort
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hexactFamily hsplit hcanonical hconvention
      hfamilyWitness hexactStrengthened)

/-- Final single-exact-witness auditor surface: final total surface plus all
three exact single-witness routes. -/
abbrev audit_pk_singleExactWitnessFinalAuditorSurfaceBundle
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_finalTotalAuditorSurface
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hfamily hsplit hcanonical hconvention
      hfamilyWitness hexactStrengthened)
    (audit_pk_allExactWitnesses_finalTotalClosedAuditBundle
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hfamily hsplit hcanonical hconvention
      hfamilyWitness hexactStrengthened)

/-- Probe-ready final surface: final total auditor surface, single-exact-witness
routes, safety bundle, exact encoding checklist, and presentation transport-gap
boundary are all exposed together. -/
abbrev audit_pk_probeReadyFinalSurface
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  And.intro
    (audit_pk_finalTotalAuditorSurface
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hcollapse hupper hlocal hfamily hsplit hcanonical hconvention
      hfamilyWitness hexactStrengthened)
    (And.intro
      (audit_pk_singleExactWitnessFinalAuditorSurfaceBundle
        (L := L) (α := α) (n := n)
        (Ax := Ax) (A := A) (B := B) (halign := halign)
        hcollapse hupper hlocal hfamily hsplit hcanonical hconvention
        hfamilyWitness hexactStrengthened)
      (And.intro
        (audit_pk_closedSurfaceSafetyEntryPoint
          (L := L) (α := α) (n := n)
          (Ax := Ax) (A := A) (B := B) (halign := halign)
          hcollapse hupper hlocal hfamily hsplit hcanonical hconvention
          hfamilyWitness hexactStrengthened)
        (And.intro
          (audit_pk_exactTriangle_localEncodingReviewerChecklist
            (L := L) (α := α) (n := n)
            (Ax := Ax) (A := A) (B := B) (halign := halign))
          (audit_pk_presentationTransportGapBoundaryEntryPoint
            (L := L) (α := α) (n := n)
            (Ax := Ax) (A := A) (B := B) (halign := halign)
            hcollapse hupper hcanonical hconvention hfamilyWitness
            hexactStrengthened))))

/-- Probe-ready final surface from a single exact-convention witness plus
explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactConventionWitness_probeReadyFinalSurface
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_probeReadyFinalSurface
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal
    (audit_pk_exactConvention_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    (audit_pk_exactConvention_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hlocal)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Probe-ready final surface from a single exact-family-exactness witness plus
explicitly supplied presentation witnesses. -/
abbrev audit_pk_exactFamilyWitness_probeReadyFinalSurface
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_probeReadyFinalSurface
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_exactFamilyExactness_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hfamily
    (audit_pk_exactFamilyExactness_to_splitMinChecked_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hfamily)
    hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Probe-ready final surface from a single split minChecked witness plus
explicitly supplied presentation witnesses. -/
abbrev audit_pk_splitMinCheckedWitness_probeReadyFinalSurface
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_probeReadyFinalSurface
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper
    (audit_pk_splitMinChecked_to_exactConvention_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    (audit_pk_splitMinChecked_to_exactFamilyExactness_nonempty
      (L := L) (α := α) (n := n)
      (Ax := Ax) (A := A) (B := B) (halign := halign)
      hsplit)
    hsplit hcanonical hconvention hfamilyWitness hexactStrengthened

/-- Build-candidate surface alias.  This is only a named proof object; it does
not run a build. -/
abbrev audit_pk_finalStageBuildCandidateSurface
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hcollapse : SondowProjectLocalS21CollapseConclusion)
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hlocal :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign))
    (hfamily :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign))
    (hsplit :
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign))
    (hcanonical :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5CanonicalInputs
          Ax A B halign))
    (hconvention :
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ConventionInputs
          Ax A B halign))
    (hfamilyWitness :
      Nonempty
        (SondowProjectLocalPudlakBottomFamilyWitnessInputs
          Ax A B halign))
    (hexactStrengthened :
      Nonempty
        (SondowProjectLocalPudlakBottomExactStrengthenedInputs
          Ax A B halign)) :=
  audit_pk_probeReadyFinalSurface
    (L := L) (α := α) (n := n)
    (Ax := Ax) (A := A) (B := B) (halign := halign)
    hcollapse hupper hlocal hfamily hsplit hcanonical hconvention
    hfamilyWitness hexactStrengthened

/-!
Stage-3 final auditor aliases: these names deliberately expose only already
closed surfaces.  They do not strengthen presentation transport into an iff;
that boundary is kept explicit by the no-presentation-iff entrypoint.
-/

abbrev audit_pk_stage3FinalSurface_probeReady :=
  @audit_pk_finalTotalAuditorSurface

abbrev audit_pk_stage3FinalSurface_singleWitnessBundle :=
  @audit_pk_singleExactWitnessFinalAuditorSurfaceBundle

abbrev audit_pk_stage3FinalSurface_allExactWitnessBundle :=
  @audit_pk_allExactWitnesses_finalTotalClosedAuditBundle

abbrev audit_pk_stage3FinalSurface_exactTriangleIff :=
  @audit_pk_exactConvention_familyExactness_splitMinChecked_totalIff

abbrev audit_pk_stage3FinalSurface_noPresentationIffBoundary :=
  @audit_pk_noPresentationIffBoundaryReviewerEntryPoint

/-!
Auditor question map for the current closed surface.  Each name is a
definitionally-equal alias to an already probed theorem or certificate surface.
-/

abbrev audit_pk_stage3WhereIsExactIff :=
  @audit_pk_exactConvention_familyExactness_splitMinChecked_totalIff

abbrev audit_pk_stage3WhereIsCollisionExactIff :=
  @audit_pk_exactConvention_familyExactness_splitMinChecked_collisionTotalIff

abbrev audit_pk_stage3WhereIsSingleExactWitness :=
  @audit_pk_singleExactWitnessFinalAuditorSurfaceBundle

abbrev audit_pk_stage3WhereIsAllExactWitnesses :=
  @audit_pk_allExactWitnesses_finalTotalClosedAuditBundle

abbrev audit_pk_stage3WhereIsTheorem5CodeEquality :=
  @audit_pk_theorem5_codeEqualityReviewerChecklist

abbrev audit_pk_stage3WhereIsTheorem5NormalForm :=
  @audit_pk_theorem5_normalFormReviewerChecklist

abbrev audit_pk_stage3WhereIsTheorem5StatementProbe :=
  @audit_pk_theorem5_statementProbeReviewerChecklist

abbrev audit_pk_stage3WhereIsTheorem5EncoderCertificate :=
  @audit_pk_theorem5_encoderCertificateReviewerChecklist

abbrev audit_pk_stage3WhereIsEncodingBoundary :=
  @audit_pk_currentClosedSurfaceEncodingBoundaryBundle

abbrev audit_pk_stage3WhereIsCertificateBoundary :=
  @audit_pk_presentationLocalCertificateBoundaryAuditBundle

abbrev audit_pk_stage3WhereIsNoWeakeningNoHiddenAssumption :=
  @audit_pk_closedSurfaceNoHiddenNoWeakeningBundle

abbrev audit_pk_stage3WhereIsNoPresentationIff :=
  @audit_pk_noPresentationIffBoundaryReviewerEntryPoint

/-!
Stage-3 reviewer bundles.  These are intentionally shallow: they collect the
already probed endpoints that answer the most likely audit questions without
changing any theorem statement.
-/

abbrev audit_pk_stage3Theorem5FinalReviewerBundle :=
  @audit_pk_finalTheorem5AuditBundleWithNonemptyEndpoints

abbrev audit_pk_stage3PaperTheoremToLeanEndpoint :=
  @audit_pk_finalTotalClosedAuditEntryPoint

abbrev audit_pk_stage3ExactIffToEndpointAuditBundle :=
  @audit_pk_stage3FinalSurface_exactTriangleIff

abbrev audit_pk_stage3BoundaryHonestyBundle :=
  @audit_pk_closedSurfaceSafetyEntryPoint

/-!
Stage-3 landing aliases.  These names form an index layer for reviewers: each
entry points to a closed surface or to an explicitly one-way boundary.
-/

abbrev audit_pk_stage3AuditorLandingPage :=
  @audit_pk_stage3FinalSurface_probeReady

abbrev audit_pk_stage3AuditorLandingPage_exactIff :=
  @audit_pk_stage3WhereIsExactIff

abbrev audit_pk_stage3AuditorLandingPage_theorem5 :=
  @audit_pk_stage3Theorem5FinalReviewerBundle

abbrev audit_pk_stage3AuditorLandingPage_paperToLean :=
  @audit_pk_stage3PaperTheoremToLeanEndpoint

abbrev audit_pk_stage3AuditorLandingPage_boundaryHonesty :=
  @audit_pk_stage3BoundaryHonestyBundle

abbrev audit_pk_stage3SingleExactWitnessSurface :=
  @audit_pk_stage3WhereIsSingleExactWitness

abbrev audit_pk_stage3AllExactWitnessesSurface :=
  @audit_pk_stage3WhereIsAllExactWitnesses

abbrev audit_pk_stage3ExactWitnessSurfacesChecklist :=
  @audit_pk_stage3FinalSurface_allExactWitnessBundle

abbrev audit_pk_stage3NoFakePresentationIffLandingPage :=
  @audit_pk_stage3WhereIsNoPresentationIff

/-!
Final closure theorem-name layer.  These aliases are deliberately one-name
entrypoints so that probe failures remain local and reviewer search is direct.
-/

abbrev audit_pk_stage3FinalClosureTheoremName :=
  @audit_pk_stage3AuditorLandingPage

abbrev audit_pk_stage3FinalClosureReviewerEntryPoint :=
  @audit_pk_stage3FinalSurface_probeReady

abbrev audit_pk_stage3FinalClosureTheorem5EntryPoint :=
  @audit_pk_stage3AuditorLandingPage_theorem5

abbrev audit_pk_stage3FinalClosureExactIffEntryPoint :=
  @audit_pk_stage3AuditorLandingPage_exactIff

abbrev audit_pk_stage3FinalClosurePaperToLeanEntryPoint :=
  @audit_pk_stage3AuditorLandingPage_paperToLean

abbrev audit_pk_stage3NoHiddenAssumptionEntryPoint :=
  @audit_pk_globalNoWeakeningNoHiddenAssumptionBundle

abbrev audit_pk_stage3NoWeakeningEntryPoint :=
  @audit_pk_closedSurfaceNoHiddenNoWeakeningBundle

abbrev audit_pk_stage3NoHiddenNoWeakeningFinalEntryPoint :=
  @audit_pk_stage3BoundaryHonestyBundle

abbrev audit_pk_stage3FinalClosureNoFakePresentationIffEntryPoint :=
  @audit_pk_stage3NoFakePresentationIffLandingPage

/-!
Stage-3 anti-regression layer.  These aliases answer reviewer checks about
weakening, hidden assumptions, exact iff preservation, presentation boundaries,
and the encoder-facing Theorem 5 surfaces.
-/

abbrev audit_pk_stage3AntiRegressionStatementNotWeakened :=
  @audit_pk_stage3WhereIsTheorem5StatementProbe

abbrev audit_pk_stage3AntiRegressionNoExtraHypotheses :=
  @audit_pk_stage3NoHiddenAssumptionEntryPoint

abbrev audit_pk_stage3AntiRegressionNoWeakening :=
  @audit_pk_stage3NoWeakeningEntryPoint

abbrev audit_pk_stage3AntiRegressionExactIffPreserved :=
  @audit_pk_stage3FinalClosureExactIffEntryPoint

abbrev audit_pk_stage3AntiRegressionPresentationOneWayPreserved :=
  @audit_pk_stage3FinalClosureNoFakePresentationIffEntryPoint

abbrev audit_pk_stage3Theorem5EncoderWorksSurface :=
  @audit_pk_stage3WhereIsTheorem5EncoderCertificate

abbrev audit_pk_stage3Theorem5CodeEqualitySurface :=
  @audit_pk_stage3WhereIsTheorem5CodeEquality

abbrev audit_pk_stage3Theorem5NormalFormSurface :=
  @audit_pk_stage3WhereIsTheorem5NormalForm

abbrev audit_pk_stage3Theorem5EncoderReviewerEntryPoint :=
  @audit_pk_stage3Theorem5EncoderWorksSurface

abbrev audit_pk_stage3AntiRegressionReviewerEntryPoint :=
  @audit_pk_stage3FinalClosureTheoremName

/-!
Stage-3 final audit certificate index.  This is a certificate-style naming
layer: each alias points to one already closed audit surface, keeping failures
local and avoiding any product-style proof bundling.
-/

abbrev audit_pk_stage3FinalAuditCertificateIndex :=
  @audit_pk_stage3AntiRegressionReviewerEntryPoint

abbrev audit_pk_stage3FinalAuditCertificate_exactIffPreserved :=
  @audit_pk_stage3AntiRegressionExactIffPreserved

abbrev audit_pk_stage3FinalAuditCertificate_noExtraHypotheses :=
  @audit_pk_stage3AntiRegressionNoExtraHypotheses

abbrev audit_pk_stage3FinalAuditCertificate_noWeakening :=
  @audit_pk_stage3AntiRegressionNoWeakening

abbrev audit_pk_stage3FinalAuditCertificate_statementNotWeakened :=
  @audit_pk_stage3AntiRegressionStatementNotWeakened

abbrev audit_pk_stage3FinalAuditCertificate_presentationOneWay :=
  @audit_pk_stage3AntiRegressionPresentationOneWayPreserved

abbrev audit_pk_stage3FinalAuditCertificate_theorem5EncoderWorks :=
  @audit_pk_stage3Theorem5EncoderWorksSurface

abbrev audit_pk_stage3Theorem5EncoderWorksToCodeEqualityAuditPath :=
  @audit_pk_stage3Theorem5CodeEqualitySurface

abbrev audit_pk_stage3Theorem5EncoderWorksToNormalFormAuditPath :=
  @audit_pk_stage3Theorem5NormalFormSurface

abbrev audit_pk_stage3Theorem5EncoderWorksToCertificateAuditPath :=
  @audit_pk_stage3Theorem5EncoderWorksSurface

abbrev audit_pk_stage3Theorem5EncoderAuditPathEntryPoint :=
  @audit_pk_stage3Theorem5EncoderReviewerEntryPoint

/-!
Stage-3 final reviewer single-name surface and exact-triangle answer names.
The exact witness triangle is genuinely recorded as iff; presentation transport
remains explicitly one-way through the no-fake-presentation-iff entrypoint.
-/

abbrev audit_pk_stage3FinalReviewerSingleNameSurface :=
  @audit_pk_stage3FinalAuditCertificateIndex

abbrev audit_pk_stage3FinalReviewerSingleNameCertificate :=
  @audit_pk_stage3FinalAuditCertificateIndex

abbrev audit_pk_stage3WhyExactConventionIffExactFamily :=
  @audit_pk_exactConvention_familyExactness_splitMinChecked_totalIff

abbrev audit_pk_stage3WhyExactFamilyIffSplitMinChecked :=
  @audit_pk_exactConvention_familyExactness_splitMinChecked_totalIff

abbrev audit_pk_stage3WhyExactConventionIffSplitMinChecked :=
  @audit_pk_exactConvention_familyExactness_splitMinChecked_totalIff

abbrev audit_pk_stage3WhyCollisionExactIffTriangle :=
  @audit_pk_exactConvention_familyExactness_splitMinChecked_collisionTotalIff

abbrev audit_pk_stage3SingleExactWitnessFinalAnswer :=
  @audit_pk_stage3SingleExactWitnessSurface

abbrev audit_pk_stage3AllExactWitnessesFinalAnswer :=
  @audit_pk_stage3AllExactWitnessesSurface

abbrev audit_pk_stage3ExactWitnessTriangleFinalAnswer :=
  @audit_pk_stage3ExactWitnessSurfacesChecklist

/-!
Stage-3 explicit exact-witness iff projections.  These are substantive bridge
lemmas: each iff is built from the already-probed nonempty transport lemmas,
so the exact triangle is available without unpacking the large audit surface.
-/

theorem audit_pk_stage3ExactConventionIffExactFamilyExplicit
    {L : FirstOrder.Language} {α : Type _} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) :=
  ⟨fun h =>
      audit_pk_exactConvention_to_exactFamilyExactness_nonempty h,
    fun h =>
      audit_pk_exactFamilyExactness_to_exactConvention_nonempty h⟩

theorem audit_pk_stage3ExactFamilyIffSplitMinCheckedExplicit
    {L : FirstOrder.Language} {α : Type _} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) :=
  ⟨fun h =>
      audit_pk_exactFamilyExactness_to_splitMinChecked_nonempty h,
    fun h =>
      audit_pk_splitMinChecked_to_exactFamilyExactness_nonempty h⟩

theorem audit_pk_stage3ExactConventionIffSplitMinCheckedExplicit
    {L : FirstOrder.Language} {α : Type _} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) :=
  ⟨fun h =>
      audit_pk_exactConvention_to_splitMinChecked_nonempty h,
    fun h =>
      audit_pk_splitMinChecked_to_exactConvention_nonempty h⟩

abbrev audit_pk_stage3FinalHandoffSurface :=
  @audit_pk_stage3FinalReviewerSingleNameSurface

abbrev audit_pk_stage3FinalHandoffCertificateIndex :=
  @audit_pk_stage3FinalAuditCertificateIndex

abbrev audit_pk_stage3FinalHandoffAntiRegression :=
  @audit_pk_stage3AntiRegressionReviewerEntryPoint

abbrev audit_pk_stage3FinalHandoffTheorem5EncoderPath :=
  @audit_pk_stage3Theorem5EncoderAuditPathEntryPoint

abbrev audit_pk_stage3WhyNotPresentationIffExplicit :=
  @audit_pk_stage3NoFakePresentationIffLandingPage

/-!
Stage-3 reviewer-answer theorem layer.  Unlike the shallow index aliases above,
these theorem names expose the exact witness triangle as direct iff statements
that auditors can cite without unpacking a large bundle.
-/

theorem audit_pk_stage3ReviewerAnswer_whyConventionIffFamily
    {L : FirstOrder.Language} {α : Type _} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) :=
  audit_pk_stage3ExactConventionIffExactFamilyExplicit

theorem audit_pk_stage3ReviewerAnswer_whyFamilyIffSplit
    {L : FirstOrder.Language} {α : Type _} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) :=
  audit_pk_stage3ExactFamilyIffSplitMinCheckedExplicit

theorem audit_pk_stage3ReviewerAnswer_whyConventionIffSplit
    {L : FirstOrder.Language} {α : Type _} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) :=
  audit_pk_stage3ExactConventionIffSplitMinCheckedExplicit

theorem audit_pk_stage3ReviewerAnswer_exactWitnessTriangleAllThree
    {L : FirstOrder.Language} {α : Type _} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment} :
    (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
        (Nonempty
            (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
              Ax A B halign) ↔
          Nonempty
            (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
              Ax A B halign)) :=
  ⟨audit_pk_stage3ReviewerAnswer_whyConventionIffFamily,
    audit_pk_stage3ReviewerAnswer_whyFamilyIffSplit,
    audit_pk_stage3ReviewerAnswer_whyConventionIffSplit⟩

abbrev audit_pk_stage3Theorem5EncoderChainHonestEntryPoint :=
  @audit_pk_stage3Theorem5EncoderAuditPathEntryPoint

abbrev audit_pk_stage3Theorem5EncoderChainToCodeEquality :=
  @audit_pk_stage3Theorem5EncoderWorksToCodeEqualityAuditPath

abbrev audit_pk_stage3Theorem5EncoderChainToNormalForm :=
  @audit_pk_stage3Theorem5EncoderWorksToNormalFormAuditPath

abbrev audit_pk_stage3Theorem5EncoderChainToCertificate :=
  @audit_pk_stage3Theorem5EncoderWorksToCertificateAuditPath

abbrev audit_pk_stage3NegativeAudit_noPresentationIffClaimed :=
  @audit_pk_stage3WhyNotPresentationIffExplicit

abbrev audit_pk_stage3FinalHandoffReviewerAnswer :=
  @audit_pk_stage3FinalHandoffSurface

/-!
Stage-3 final-certificate projections.  These theorem names connect the final
certificate layer to the explicit exact-witness triangle, and the three binary
iff answers are projected from the single all-three theorem.
-/

theorem audit_pk_stage3FinalCertificate_exactWitnessTriangleProjection
    {L : FirstOrder.Language} {α : Type _} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment} :
    (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
        (Nonempty
            (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
              Ax A B halign) ↔
          Nonempty
            (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
              Ax A B halign)) :=
  audit_pk_stage3ReviewerAnswer_exactWitnessTriangleAllThree

theorem audit_pk_stage3FinalCertificate_conventionFamilyProjection
    {L : FirstOrder.Language} {α : Type _} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) :=
  (audit_pk_stage3FinalCertificate_exactWitnessTriangleProjection
    (Ax := Ax) (A := A) (B := B) (halign := halign)).1

theorem audit_pk_stage3FinalCertificate_familySplitProjection
    {L : FirstOrder.Language} {α : Type _} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) :=
  (audit_pk_stage3FinalCertificate_exactWitnessTriangleProjection
    (Ax := Ax) (A := A) (B := B) (halign := halign)).2.1

theorem audit_pk_stage3FinalCertificate_conventionSplitProjection
    {L : FirstOrder.Language} {α : Type _} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment} :
    Nonempty
        (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
          Ax A B halign) ↔
      Nonempty
        (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
          Ax A B halign) :=
  (audit_pk_stage3FinalCertificate_exactWitnessTriangleProjection
    (Ax := Ax) (A := A) (B := B) (halign := halign)).2.2

abbrev audit_pk_stage3PresentationBoundary_onlyOneWayNotIff :=
  @audit_pk_stage3NegativeAudit_noPresentationIffClaimed

abbrev audit_pk_stage3PresentationBoundary_noCrossPresentationIffSurface :=
  @audit_pk_presentationTransportGapBoundaryEntryPoint

abbrev audit_pk_stage3FinalCertificate_presentationBoundary :=
  @audit_pk_stage3PresentationBoundary_onlyOneWayNotIff

abbrev audit_pk_stage3Theorem5EncoderChainFinalHonestHandoff :=
  @audit_pk_stage3Theorem5EncoderChainHonestEntryPoint

abbrev audit_pk_stage3Theorem5EncoderChainFinalCodeEqualityHandoff :=
  @audit_pk_stage3Theorem5EncoderChainToCodeEquality

abbrev audit_pk_stage3Theorem5EncoderChainFinalNormalFormHandoff :=
  @audit_pk_stage3Theorem5EncoderChainToNormalForm

abbrev audit_pk_stage3FinalCertificate_encoderChain :=
  @audit_pk_stage3Theorem5EncoderChainFinalHonestHandoff

abbrev audit_pk_stage3FinalHandoffReviewerAnswerSingleName :=
  @audit_pk_stage3FinalHandoffReviewerAnswer

/-!
Stage-3 Theorem 5 encoder-chain projections.  These are explicit theorem
projections from the encoder/certificate bridge into the concrete code equality
and normal-form obligations for each exact entry.
-/

theorem audit_pk_stage3ExactConvention_encoderBridgeToCodeAndNormalForm
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) :=
  (audit_theorem5_exactConvention_encoderCertificateBridge h).2.2.2

theorem audit_pk_stage3SplitMinChecked_encoderBridgeToCodeAndNormalForm
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) :=
  (audit_theorem5_splitMinChecked_encoderCertificateBridge h).2.2.2

theorem audit_pk_stage3ExactFamilyExactness_encoderBridgeToCodeAndNormalForm
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    h.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            h.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
            h.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) :=
  (audit_theorem5_exactFamilyExactness_encoderCertificateBridge h).2.2.2

abbrev audit_pk_stage3Theorem5EncoderChainExplicitConvention :=
  @audit_pk_stage3ExactConvention_encoderBridgeToCodeAndNormalForm

abbrev audit_pk_stage3Theorem5EncoderChainExplicitSplit :=
  @audit_pk_stage3SplitMinChecked_encoderBridgeToCodeAndNormalForm

abbrev audit_pk_stage3Theorem5EncoderChainExplicitFamily :=
  @audit_pk_stage3ExactFamilyExactness_encoderBridgeToCodeAndNormalForm

abbrev audit_pk_stage3FinalCertificate_encoderChainExplicit :=
  @audit_pk_stage3Theorem5EncoderChainExplicitConvention

/-!
Stage-3 encoder-chain split lemmas.  These projections separate scale, code
equality, and normal-form obligations so reviewers can audit each component
without unfolding the larger encoder/certificate bridge.
-/

theorem audit_pk_stage3ExactConvention_encoderBridgeScaleEqId
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    h.toPudlakSideInputs.lowerBoundPackage.scale = id :=
  (audit_pk_stage3ExactConvention_encoderBridgeToCodeAndNormalForm h).1

theorem audit_pk_stage3ExactConvention_encoderBridgeCodeEquality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    ∀ m : ℕ,
      _root_.rescaledPartialConsistencyCode
          h.toPudlakSideInputs.lowerBoundPackage.scale m =
        _root_.partialConsistencyCode m :=
  (audit_pk_stage3ExactConvention_encoderBridgeToCodeAndNormalForm h).2.1

theorem audit_pk_stage3ExactConvention_encoderBridgeNormalForm
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    ∀ m : ℕ,
      (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
          h.toPudlakSideInputs.strengthened_to_partial).code m =
        _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
          h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m :=
  (audit_pk_stage3ExactConvention_encoderBridgeToCodeAndNormalForm h).2.2

theorem audit_pk_stage3SplitMinChecked_encoderBridgeScaleEqId
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    h.toPudlakSideInputs.lowerBoundPackage.scale = id :=
  (audit_pk_stage3SplitMinChecked_encoderBridgeToCodeAndNormalForm h).1

theorem audit_pk_stage3SplitMinChecked_encoderBridgeCodeEquality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    ∀ m : ℕ,
      _root_.rescaledPartialConsistencyCode
          h.toPudlakSideInputs.lowerBoundPackage.scale m =
        _root_.partialConsistencyCode m :=
  (audit_pk_stage3SplitMinChecked_encoderBridgeToCodeAndNormalForm h).2.1

theorem audit_pk_stage3SplitMinChecked_encoderBridgeNormalForm
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    ∀ m : ℕ,
      (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
          h.toPudlakSideInputs.strengthened_to_partial).code m =
        _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
          h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m :=
  (audit_pk_stage3SplitMinChecked_encoderBridgeToCodeAndNormalForm h).2.2

theorem audit_pk_stage3ExactFamilyExactness_encoderBridgeScaleEqId
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    h.toPudlakSideInputs.lowerBoundPackage.scale = id :=
  (audit_pk_stage3ExactFamilyExactness_encoderBridgeToCodeAndNormalForm h).1

theorem audit_pk_stage3ExactFamilyExactness_encoderBridgeCodeEquality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    ∀ m : ℕ,
      _root_.rescaledPartialConsistencyCode
          h.toPudlakSideInputs.lowerBoundPackage.scale m =
        _root_.partialConsistencyCode m :=
  (audit_pk_stage3ExactFamilyExactness_encoderBridgeToCodeAndNormalForm h).2.1

theorem audit_pk_stage3ExactFamilyExactness_encoderBridgeNormalForm
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    ∀ m : ℕ,
      (h.toPudlakSideInputs.literature_lower_bound.toNormalForm
          h.toPudlakSideInputs.strengthened_to_partial).code m =
        _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
          h.toPudlakSideInputs.literature_lower_bound.scale_data.scale m :=
  (audit_pk_stage3ExactFamilyExactness_encoderBridgeToCodeAndNormalForm h).2.2

theorem audit_pk_stage3AllExactEntries_encoderBridgeToCodeAndNormalForm
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hconv :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hsplit :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (hfamily :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    (hconv.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            hconv.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        (hconv.toPudlakSideInputs.literature_lower_bound.toNormalForm
            hconv.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            hconv.toPudlakSideInputs.literature_lower_bound.scale_data.scale m)) ∧
      (hsplit.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
        (∀ m : ℕ,
          _root_.rescaledPartialConsistencyCode
              hsplit.toPudlakSideInputs.lowerBoundPackage.scale m =
            _root_.partialConsistencyCode m) ∧
        (∀ m : ℕ,
          (hsplit.toPudlakSideInputs.literature_lower_bound.toNormalForm
              hsplit.toPudlakSideInputs.strengthened_to_partial).code m =
            _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
              hsplit.toPudlakSideInputs.literature_lower_bound.scale_data.scale m)) ∧
        (hfamily.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
          (∀ m : ℕ,
            _root_.rescaledPartialConsistencyCode
                hfamily.toPudlakSideInputs.lowerBoundPackage.scale m =
              _root_.partialConsistencyCode m) ∧
          (∀ m : ℕ,
            (hfamily.toPudlakSideInputs.literature_lower_bound.toNormalForm
                hfamily.toPudlakSideInputs.strengthened_to_partial).code m =
              _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
                hfamily.toPudlakSideInputs.literature_lower_bound.scale_data.scale m)) :=
  ⟨audit_pk_stage3ExactConvention_encoderBridgeToCodeAndNormalForm hconv,
    ⟨audit_pk_stage3SplitMinChecked_encoderBridgeToCodeAndNormalForm hsplit,
      audit_pk_stage3ExactFamilyExactness_encoderBridgeToCodeAndNormalForm
        hfamily⟩⟩

abbrev audit_pk_stage3FinalCertificate_allExactEntriesEncoderChain :=
  @audit_pk_stage3AllExactEntries_encoderBridgeToCodeAndNormalForm

abbrev audit_pk_stage3ExactConvention_encoderAndStatementProbeHandoff :=
  @audit_theorem5_exactConvention_finalReviewerChecklist

abbrev audit_pk_stage3SplitMinChecked_encoderAndStatementProbeHandoff :=
  @audit_theorem5_splitMinChecked_finalReviewerChecklist

abbrev audit_pk_stage3ExactFamilyExactness_encoderAndStatementProbeHandoff :=
  @audit_theorem5_exactFamilyExactness_finalReviewerChecklist

abbrev audit_pk_stage3FinalCertificate_encoderStatementProbeHandoff :=
  @audit_pk_stage3ExactConvention_encoderAndStatementProbeHandoff

/-!
Stage-3 all-exact-entry encoder audit theorems.  These collect the component
projection lemmas into reviewer-facing statements for scale, code equality, and
normal-form obligations across all three exact entries.
-/

theorem audit_pk_stage3AllExactEntries_encoderBridgeScaleEqId
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hconv :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hsplit :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (hfamily :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    hconv.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      hsplit.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
        hfamily.toPudlakSideInputs.lowerBoundPackage.scale = id :=
  ⟨audit_pk_stage3ExactConvention_encoderBridgeScaleEqId hconv,
    audit_pk_stage3SplitMinChecked_encoderBridgeScaleEqId hsplit,
    audit_pk_stage3ExactFamilyExactness_encoderBridgeScaleEqId hfamily⟩

theorem audit_pk_stage3AllExactEntries_encoderBridgeCodeEquality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hconv :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hsplit :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (hfamily :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    (∀ m : ℕ,
      _root_.rescaledPartialConsistencyCode
          hconv.toPudlakSideInputs.lowerBoundPackage.scale m =
        _root_.partialConsistencyCode m) ∧
      (∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            hsplit.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
        (∀ m : ℕ,
          _root_.rescaledPartialConsistencyCode
              hfamily.toPudlakSideInputs.lowerBoundPackage.scale m =
            _root_.partialConsistencyCode m) :=
  ⟨audit_pk_stage3ExactConvention_encoderBridgeCodeEquality hconv,
    audit_pk_stage3SplitMinChecked_encoderBridgeCodeEquality hsplit,
    audit_pk_stage3ExactFamilyExactness_encoderBridgeCodeEquality hfamily⟩

theorem audit_pk_stage3AllExactEntries_encoderBridgeNormalForm
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hconv :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hsplit :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (hfamily :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    (∀ m : ℕ,
      (hconv.toPudlakSideInputs.literature_lower_bound.toNormalForm
          hconv.toPudlakSideInputs.strengthened_to_partial).code m =
        _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
          hconv.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
      (∀ m : ℕ,
        (hsplit.toPudlakSideInputs.literature_lower_bound.toNormalForm
            hsplit.toPudlakSideInputs.strengthened_to_partial).code m =
          _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
            hsplit.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
        (∀ m : ℕ,
          (hfamily.toPudlakSideInputs.literature_lower_bound.toNormalForm
              hfamily.toPudlakSideInputs.strengthened_to_partial).code m =
            _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
              hfamily.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) :=
  ⟨audit_pk_stage3ExactConvention_encoderBridgeNormalForm hconv,
    audit_pk_stage3SplitMinChecked_encoderBridgeNormalForm hsplit,
    audit_pk_stage3ExactFamilyExactness_encoderBridgeNormalForm hfamily⟩

theorem audit_pk_stage3Theorem5ExactEntriesEncoderAuditTheorem
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hconv :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hsplit :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (hfamily :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    (hconv.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
      hsplit.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
        hfamily.toPudlakSideInputs.lowerBoundPackage.scale = id) ∧
      ((∀ m : ℕ,
        _root_.rescaledPartialConsistencyCode
            hconv.toPudlakSideInputs.lowerBoundPackage.scale m =
          _root_.partialConsistencyCode m) ∧
        (∀ m : ℕ,
          _root_.rescaledPartialConsistencyCode
              hsplit.toPudlakSideInputs.lowerBoundPackage.scale m =
            _root_.partialConsistencyCode m) ∧
          (∀ m : ℕ,
            _root_.rescaledPartialConsistencyCode
                hfamily.toPudlakSideInputs.lowerBoundPackage.scale m =
              _root_.partialConsistencyCode m)) ∧
        ((∀ m : ℕ,
          (hconv.toPudlakSideInputs.literature_lower_bound.toNormalForm
              hconv.toPudlakSideInputs.strengthened_to_partial).code m =
            _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
              hconv.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
          (∀ m : ℕ,
            (hsplit.toPudlakSideInputs.literature_lower_bound.toNormalForm
                hsplit.toPudlakSideInputs.strengthened_to_partial).code m =
              _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
                hsplit.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
            (∀ m : ℕ,
              (hfamily.toPudlakSideInputs.literature_lower_bound.toNormalForm
                  hfamily.toPudlakSideInputs.strengthened_to_partial).code m =
                _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
                  hfamily.toPudlakSideInputs.literature_lower_bound.scale_data.scale m)) :=
  ⟨audit_pk_stage3AllExactEntries_encoderBridgeScaleEqId
      hconv hsplit hfamily,
    audit_pk_stage3AllExactEntries_encoderBridgeCodeEquality
      hconv hsplit hfamily,
    audit_pk_stage3AllExactEntries_encoderBridgeNormalForm
      hconv hsplit hfamily⟩

abbrev audit_pk_stage3Theorem5ExactEntriesStatementProbeHonestEntryPoint :=
  @audit_pk_theorem5_statementProbeReviewerChecklist

abbrev audit_pk_stage3FinalCertificate_allExactEntriesScale :=
  @audit_pk_stage3AllExactEntries_encoderBridgeScaleEqId

abbrev audit_pk_stage3FinalCertificate_allExactEntriesCodeEquality :=
  @audit_pk_stage3AllExactEntries_encoderBridgeCodeEquality

abbrev audit_pk_stage3FinalCertificate_allExactEntriesNormalForm :=
  @audit_pk_stage3AllExactEntries_encoderBridgeNormalForm

abbrev audit_pk_stage3FinalCertificate_exactEntriesEncoderAudit :=
  @audit_pk_stage3Theorem5ExactEntriesEncoderAuditTheorem

abbrev audit_pk_stage3FinalCertificate_statementProbeHonest :=
  @audit_pk_stage3Theorem5ExactEntriesStatementProbeHonestEntryPoint

/-!
Stage-3 final audit closure theorem.  This closes the two hard reviewer-facing
components in one explicit theorem: the exact witness iff triangle and the
all-exact-entry encoder audit obligations.  Statement probes and presentation
boundaries remain exposed as named surfaces below, because they are checklist
surfaces rather than a single small proposition.
-/

theorem audit_pk_stage3FinalAuditClosure_exactTriangleAndEncoderTheorem
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hconv :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hsplit :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (hfamily :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    ((Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
        (Nonempty
            (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
              Ax A B halign) ↔
          Nonempty
            (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
              Ax A B halign))) ∧
      ((hconv.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
        hsplit.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
          hfamily.toPudlakSideInputs.lowerBoundPackage.scale = id) ∧
        ((∀ m : ℕ,
          _root_.rescaledPartialConsistencyCode
              hconv.toPudlakSideInputs.lowerBoundPackage.scale m =
            _root_.partialConsistencyCode m) ∧
          (∀ m : ℕ,
            _root_.rescaledPartialConsistencyCode
                hsplit.toPudlakSideInputs.lowerBoundPackage.scale m =
              _root_.partialConsistencyCode m) ∧
            (∀ m : ℕ,
              _root_.rescaledPartialConsistencyCode
                  hfamily.toPudlakSideInputs.lowerBoundPackage.scale m =
                _root_.partialConsistencyCode m)) ∧
          ((∀ m : ℕ,
            (hconv.toPudlakSideInputs.literature_lower_bound.toNormalForm
                hconv.toPudlakSideInputs.strengthened_to_partial).code m =
              _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
                hconv.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
            (∀ m : ℕ,
              (hsplit.toPudlakSideInputs.literature_lower_bound.toNormalForm
                  hsplit.toPudlakSideInputs.strengthened_to_partial).code m =
                _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
                  hsplit.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
              (∀ m : ℕ,
                (hfamily.toPudlakSideInputs.literature_lower_bound.toNormalForm
                    hfamily.toPudlakSideInputs.strengthened_to_partial).code m =
                  _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
                    hfamily.toPudlakSideInputs.literature_lower_bound.scale_data.scale m))) :=
  ⟨audit_pk_stage3ReviewerAnswer_exactWitnessTriangleAllThree
      (Ax := Ax) (A := A) (B := B) (halign := halign),
    audit_pk_stage3Theorem5ExactEntriesEncoderAuditTheorem
      hconv hsplit hfamily⟩

abbrev audit_pk_stage3FinalAuditClosureStatementProbeSurface :=
  @audit_pk_theorem5_statementProbeReviewerChecklist

abbrev audit_pk_stage3FinalAuditClosurePresentationBoundarySurface :=
  @audit_pk_stage3PresentationBoundary_onlyOneWayNotIff

abbrev audit_pk_stage3FinalAuditClosureSingleName :=
  @audit_pk_stage3FinalAuditClosure_exactTriangleAndEncoderTheorem

abbrev audit_pk_stage3FinalAuditClosedForReviewers :=
  @audit_pk_stage3FinalAuditClosure_exactTriangleAndEncoderTheorem

/-!
Stage-3 explicit statement-probe closure.  These theorem names expose the
non-weakening probes for the three exact entries as direct propositions, rather
than only as a reviewer checklist surface.
-/

theorem audit_pk_stage3ExactConvention_statementProbeExplicit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion)
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
        ¬ _root_.is_rational _root_.euler_mascheroni :=
  audit_theorem5_exactConvention_statementProbe h hupper

theorem audit_pk_stage3SplitMinChecked_statementProbeExplicit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion)
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign)) ∧
        ¬ _root_.is_rational _root_.euler_mascheroni :=
  audit_theorem5_splitMinChecked_statementProbe h hupper

theorem audit_pk_stage3ExactFamilyExactness_statementProbeExplicit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion)
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
        ¬ _root_.is_rational _root_.euler_mascheroni :=
  audit_theorem5_exactFamilyExactness_statementProbe h hupper

theorem audit_pk_stage3AllExactEntries_statementProbeTheorem
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hupper : SondowProjectLocalS21CollapseConclusion)
    (hconv :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hsplit :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (hfamily :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    ((Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
        ¬ _root_.is_rational _root_.euler_mascheroni) ∧
      ((Nonempty
            (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
              Ax A B halign) ↔
          Nonempty
            (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
              Ax A B halign)) ∧
        (Nonempty
            (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
              Ax A B halign) ↔
          Nonempty
            (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
              Ax A B halign)) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni) ∧
        ((Nonempty
              (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
                Ax A B halign) ↔
            Nonempty
              (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
                Ax A B halign)) ∧
          (Nonempty
              (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
                Ax A B halign) ↔
            Nonempty
              (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
                Ax A B halign)) ∧
            ¬ _root_.is_rational _root_.euler_mascheroni) :=
  ⟨audit_pk_stage3ExactConvention_statementProbeExplicit hupper hconv,
    audit_pk_stage3SplitMinChecked_statementProbeExplicit hupper hsplit,
    audit_pk_stage3ExactFamilyExactness_statementProbeExplicit
      hupper hfamily⟩

abbrev audit_pk_stage3FinalAuditClosureStatementProbeTheorem :=
  @audit_pk_stage3AllExactEntries_statementProbeTheorem

abbrev audit_pk_stage3PresentationBoundaryDoesNotClaimIff :=
  @audit_pk_stage3PresentationBoundary_noCrossPresentationIffSurface

abbrev audit_pk_stage3FinalAuditClosurePresentationBoundaryDoesNotClaimIff :=
  @audit_pk_stage3PresentationBoundaryDoesNotClaimIff

abbrev audit_pk_stage3FinalAuditClosureFullyIndexed :=
  @audit_pk_stage3FinalAuditClosureSingleName

/-!
Stage-4 encoder/checker bottom plumbing.  These theorem names expose the
actual conversion chain from checked-code encoder recognition to split local
checked recognition, and from proof-code/convention inputs into that same
checked encoder route.
-/

theorem audit_pk_stage4_checkedEncoder_toSplitLocalCheckedRecognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
        Ax A B halign) :
    h.splitLocalCheckedRecognition =
      h.local_hilbert_encoder_recognition.toSplitLocalCheckedRecognition :=
  rfl

theorem audit_pk_stage4_checkedEncoder_toLocalCheckedSplitInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
        Ax A B halign) :
    h.toLocalCheckedRecognitionSplitInputs =
      SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs.toLocalCheckedRecognitionSplitInputs h :=
  rfl

theorem audit_pk_stage4_proofCodeChecker_toCheckedEncoderRecognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs
        Ax A B halign) :
    h.toCheckedEncoderRecognitionInputs.local_hilbert_encoder_recognition =
      h.local_hilbert_checker_recognition.toProjectCheckedRecognition :=
  rfl

theorem audit_pk_stage4_proofCodeChecker_toSplitLocalCheckedRecognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs
        Ax A B halign) :
    h.splitLocalCheckedRecognition =
      h.toCheckedEncoderRecognitionInputs.splitLocalCheckedRecognition :=
  rfl

abbrev audit_pk_stage4_conventionEquivalence_projectCheckedCertificate :=
  @SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs.projectCheckedRecognitionCertificate

theorem audit_pk_stage4_conventionEquivalence_toCheckedEncoderRecognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs
        Ax A B halign) :
    h.toCheckedEncoderRecognitionInputs.local_hilbert_encoder_recognition =
      h.projectCheckedRecognitionCertificate.toProjectCheckedRecognition :=
  rfl

theorem audit_pk_stage4_conventionEquivalence_toSplitLocalCheckedRecognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs
        Ax A B halign) :
    h.toCheckedEncoderRecognitionInputs.splitLocalCheckedRecognition =
      (h.projectCheckedRecognitionCertificate.toProjectCheckedRecognition).toSplitLocalCheckedRecognition :=
  rfl

theorem audit_pk_stage4_encoderCheckerBottomPlumbing
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (henc :
      SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
        Ax A B halign)
    (hchecker :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs
        Ax A B halign)
    (hconv :
      SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs
        Ax A B halign) :
    henc.splitLocalCheckedRecognition =
        henc.local_hilbert_encoder_recognition.toSplitLocalCheckedRecognition ∧
      hchecker.toCheckedEncoderRecognitionInputs.local_hilbert_encoder_recognition =
        hchecker.local_hilbert_checker_recognition.toProjectCheckedRecognition ∧
        hconv.toCheckedEncoderRecognitionInputs.local_hilbert_encoder_recognition =
          hconv.projectCheckedRecognitionCertificate.toProjectCheckedRecognition :=
  ⟨audit_pk_stage4_checkedEncoder_toSplitLocalCheckedRecognition henc,
    audit_pk_stage4_proofCodeChecker_toCheckedEncoderRecognition hchecker,
    audit_pk_stage4_conventionEquivalence_toCheckedEncoderRecognition hconv⟩

abbrev audit_pk_stage4EncoderCheckerBottomPlumbingEntryPoint :=
  @audit_pk_stage4_encoderCheckerBottomPlumbing

abbrev audit_pk_stage4CheckedEncoderToSplitLocalEntryPoint :=
  @audit_pk_stage4_checkedEncoder_toSplitLocalCheckedRecognition

abbrev audit_pk_stage4ConventionEquivalenceToCheckedEncoderEntryPoint :=
  @audit_pk_stage4_conventionEquivalence_toCheckedEncoderRecognition

/-!
Stage-4 final audit with bottom plumbing.  This theorem combines the Stage-3
exact-triangle/encoder audit closure with the Stage-4 checked-encoder/checker
plumbing, so reviewers can cite one endpoint for both the high-level audit and
the low-level encoder path.
-/

theorem audit_pk_stage4FinalAuditWithBottomPlumbing
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (hexactConv :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (hsplit :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (hexactFamily :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (henc :
      SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
        Ax A B halign)
    (hchecker :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs
        Ax A B halign)
    (hconvEq :
      SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs
        Ax A B halign) :
    (((Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign)) ∧
      (Nonempty
          (SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
            Ax A B halign) ↔
        Nonempty
          (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
            Ax A B halign)) ∧
        (Nonempty
            (SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
              Ax A B halign) ↔
          Nonempty
            (SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
              Ax A B halign))) ∧
      ((hexactConv.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
        hsplit.toPudlakSideInputs.lowerBoundPackage.scale = id ∧
          hexactFamily.toPudlakSideInputs.lowerBoundPackage.scale = id) ∧
        ((∀ m : ℕ,
          _root_.rescaledPartialConsistencyCode
              hexactConv.toPudlakSideInputs.lowerBoundPackage.scale m =
            _root_.partialConsistencyCode m) ∧
          (∀ m : ℕ,
            _root_.rescaledPartialConsistencyCode
                hsplit.toPudlakSideInputs.lowerBoundPackage.scale m =
              _root_.partialConsistencyCode m) ∧
            (∀ m : ℕ,
              _root_.rescaledPartialConsistencyCode
                  hexactFamily.toPudlakSideInputs.lowerBoundPackage.scale m =
                _root_.partialConsistencyCode m)) ∧
          ((∀ m : ℕ,
            (hexactConv.toPudlakSideInputs.literature_lower_bound.toNormalForm
                hexactConv.toPudlakSideInputs.strengthened_to_partial).code m =
              _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
                hexactConv.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
            (∀ m : ℕ,
              (hsplit.toPudlakSideInputs.literature_lower_bound.toNormalForm
                  hsplit.toPudlakSideInputs.strengthened_to_partial).code m =
                _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
                  hsplit.toPudlakSideInputs.literature_lower_bound.scale_data.scale m) ∧
              (∀ m : ℕ,
                (hexactFamily.toPudlakSideInputs.literature_lower_bound.toNormalForm
                    hexactFamily.toPudlakSideInputs.strengthened_to_partial).code m =
                  _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
                    hexactFamily.toPudlakSideInputs.literature_lower_bound.scale_data.scale m)))) ∧
      (henc.splitLocalCheckedRecognition =
          henc.local_hilbert_encoder_recognition.toSplitLocalCheckedRecognition ∧
        hchecker.toCheckedEncoderRecognitionInputs.local_hilbert_encoder_recognition =
          hchecker.local_hilbert_checker_recognition.toProjectCheckedRecognition ∧
          hconvEq.toCheckedEncoderRecognitionInputs.local_hilbert_encoder_recognition =
            hconvEq.projectCheckedRecognitionCertificate.toProjectCheckedRecognition) :=
  ⟨audit_pk_stage3FinalAuditClosure_exactTriangleAndEncoderTheorem
      hexactConv hsplit hexactFamily,
    audit_pk_stage4_encoderCheckerBottomPlumbing henc hchecker hconvEq⟩

theorem audit_pk_stage4ConventionEquivalence_checkedEncoderAndSplitRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs
        Ax A B halign) :
    h.toCheckedEncoderRecognitionInputs.local_hilbert_encoder_recognition =
        h.projectCheckedRecognitionCertificate.toProjectCheckedRecognition ∧
      h.toCheckedEncoderRecognitionInputs.splitLocalCheckedRecognition =
        (h.projectCheckedRecognitionCertificate.toProjectCheckedRecognition).toSplitLocalCheckedRecognition :=
  ⟨audit_pk_stage4_conventionEquivalence_toCheckedEncoderRecognition h,
    audit_pk_stage4_conventionEquivalence_toSplitLocalCheckedRecognition h⟩

theorem audit_pk_stage4ProofCodeChecker_checkedEncoderAndSplitRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs
        Ax A B halign) :
    h.toCheckedEncoderRecognitionInputs.local_hilbert_encoder_recognition =
        h.local_hilbert_checker_recognition.toProjectCheckedRecognition ∧
      h.splitLocalCheckedRecognition =
        h.toCheckedEncoderRecognitionInputs.splitLocalCheckedRecognition :=
  ⟨audit_pk_stage4_proofCodeChecker_toCheckedEncoderRecognition h,
    audit_pk_stage4_proofCodeChecker_toSplitLocalCheckedRecognition h⟩

abbrev audit_pk_stage4FinalAuditWithBottomPlumbingEntryPoint :=
  @audit_pk_stage4FinalAuditWithBottomPlumbing

abbrev audit_pk_stage4ConventionEquivalenceCheckedEncoderSplitRouteEntryPoint :=
  @audit_pk_stage4ConventionEquivalence_checkedEncoderAndSplitRoute

abbrev audit_pk_stage4ProofCodeCheckerCheckedEncoderSplitRouteEntryPoint :=
  @audit_pk_stage4ProofCodeChecker_checkedEncoderAndSplitRoute

abbrev audit_pk_stage4ConventionEquivalenceToExactFamilyBoundary :=
  @audit_pk_stage4ConventionEquivalenceCheckedEncoderSplitRouteEntryPoint

/-!
Stage-4 split-side bottom plumbing.  These lemmas expose the reflection and
consistency sides of the split local checked-recognition certificate reached
from checked encoders, proof-code checkers, and convention equivalence inputs.
-/

theorem audit_pk_stage4_checkedEncoder_splitReflectionSide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
        Ax A B halign) :
    h.splitLocalCheckedRecognition.reflection_recognition =
      (h.local_hilbert_encoder_recognition.toSplitLocalCheckedRecognition).reflection_recognition :=
  rfl

theorem audit_pk_stage4_checkedEncoder_splitPartialSide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
        Ax A B halign) :
    h.splitLocalCheckedRecognition.partial_recognition =
      (h.local_hilbert_encoder_recognition.toSplitLocalCheckedRecognition).partial_recognition :=
  rfl

theorem audit_pk_stage4_proofCodeChecker_splitReflectionSide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs
        Ax A B halign) :
    h.splitLocalCheckedRecognition.reflection_recognition =
      (h.toCheckedEncoderRecognitionInputs.splitLocalCheckedRecognition).reflection_recognition :=
  rfl

theorem audit_pk_stage4_proofCodeChecker_splitPartialSide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs
        Ax A B halign) :
    h.splitLocalCheckedRecognition.partial_recognition =
      (h.toCheckedEncoderRecognitionInputs.splitLocalCheckedRecognition).partial_recognition :=
  rfl

theorem audit_pk_stage4_conventionEquivalence_splitReflectionSide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs
        Ax A B halign) :
    (h.toCheckedEncoderRecognitionInputs.splitLocalCheckedRecognition).reflection_recognition =
      ((h.projectCheckedRecognitionCertificate.toProjectCheckedRecognition).toSplitLocalCheckedRecognition).reflection_recognition :=
  rfl

theorem audit_pk_stage4_conventionEquivalence_splitPartialSide
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs
        Ax A B halign) :
    (h.toCheckedEncoderRecognitionInputs.splitLocalCheckedRecognition).partial_recognition =
      ((h.projectCheckedRecognitionCertificate.toProjectCheckedRecognition).toSplitLocalCheckedRecognition).partial_recognition :=
  rfl

theorem audit_pk_stage4SplitSideBottomPlumbing
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (henc :
      SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
        Ax A B halign)
    (hchecker :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs
        Ax A B halign)
    (hconv :
      SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs
        Ax A B halign) :
    henc.splitLocalCheckedRecognition.reflection_recognition =
        (henc.local_hilbert_encoder_recognition.toSplitLocalCheckedRecognition).reflection_recognition ∧
      henc.splitLocalCheckedRecognition.partial_recognition =
          (henc.local_hilbert_encoder_recognition.toSplitLocalCheckedRecognition).partial_recognition ∧
        hchecker.splitLocalCheckedRecognition.reflection_recognition =
            (hchecker.toCheckedEncoderRecognitionInputs.splitLocalCheckedRecognition).reflection_recognition ∧
          hchecker.splitLocalCheckedRecognition.partial_recognition =
              (hchecker.toCheckedEncoderRecognitionInputs.splitLocalCheckedRecognition).partial_recognition ∧
            (hconv.toCheckedEncoderRecognitionInputs.splitLocalCheckedRecognition).reflection_recognition =
              ((hconv.projectCheckedRecognitionCertificate.toProjectCheckedRecognition).toSplitLocalCheckedRecognition).reflection_recognition ∧
              (hconv.toCheckedEncoderRecognitionInputs.splitLocalCheckedRecognition).partial_recognition =
                ((hconv.projectCheckedRecognitionCertificate.toProjectCheckedRecognition).toSplitLocalCheckedRecognition).partial_recognition :=
  ⟨audit_pk_stage4_checkedEncoder_splitReflectionSide henc,
    audit_pk_stage4_checkedEncoder_splitPartialSide henc,
    audit_pk_stage4_proofCodeChecker_splitReflectionSide hchecker,
    audit_pk_stage4_proofCodeChecker_splitPartialSide hchecker,
    audit_pk_stage4_conventionEquivalence_splitReflectionSide hconv,
    audit_pk_stage4_conventionEquivalence_splitPartialSide hconv⟩

abbrev audit_pk_stage4SplitSideBottomPlumbingEntryPoint :=
  @audit_pk_stage4SplitSideBottomPlumbing

abbrev audit_pk_stage4LocalCheckedSplitToExactFamilyBoundary :=
  @audit_pk_stage4SplitSideBottomPlumbingEntryPoint

/-!
Stage-4 split-local-checked to family-exactness bridge.  This uses the
library iff between projection-family exactness and split local checked
recognition, then threads the checked-encoder, proof-code-checker, and
convention-equivalence routes through that iff.
-/

theorem audit_pk_stage4_splitLocalChecked_toFamilyExactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (hrec : _root_.MiniHilbert.PASplitLocalCheckedRecognition interp) :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp :=
  (_root_.MiniHilbert.FormulaCodeHilbertInterpretation.familyExactness_iff_splitLocalCheckedRecognition
    interp).2 hrec

theorem audit_pk_stage4_familyExactness_toSplitLocalChecked
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (hexact : _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp) :
    _root_.MiniHilbert.PASplitLocalCheckedRecognition interp :=
  (_root_.MiniHilbert.FormulaCodeHilbertInterpretation.familyExactness_iff_splitLocalCheckedRecognition
    interp).1 hexact

theorem audit_pk_stage4_checkedEncoder_toFamilyExactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
      h.formula_code_interpretation :=
  audit_pk_stage4_splitLocalChecked_toFamilyExactness
    h.formula_code_interpretation h.splitLocalCheckedRecognition

theorem audit_pk_stage4_proofCodeChecker_toFamilyExactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
      h.formula_code_interpretation :=
  audit_pk_stage4_splitLocalChecked_toFamilyExactness
    h.formula_code_interpretation h.splitLocalCheckedRecognition

theorem audit_pk_stage4_conventionEquivalence_toFamilyExactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
      h.toCheckedEncoderRecognitionInputs.formula_code_interpretation :=
  audit_pk_stage4_splitLocalChecked_toFamilyExactness
    h.toCheckedEncoderRecognitionInputs.formula_code_interpretation
    h.toCheckedEncoderRecognitionInputs.splitLocalCheckedRecognition

theorem audit_pk_stage4FamilyExactnessRoutes
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (henc :
      SondowProjectLocalPudlakAuditedPayloadCheckedEncoderRecognitionInputs
        Ax A B halign)
    (hchecker :
      SondowProjectLocalPudlakAuditedPayloadProofCodeCheckerRecognitionInputs
        Ax A B halign)
    (hconv :
      SondowProjectLocalPudlakAuditedPayloadConventionEquivalenceInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
        henc.formula_code_interpretation ∧
      _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
        hchecker.formula_code_interpretation ∧
        _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
          hconv.toCheckedEncoderRecognitionInputs.formula_code_interpretation :=
  ⟨audit_pk_stage4_checkedEncoder_toFamilyExactness henc,
    audit_pk_stage4_proofCodeChecker_toFamilyExactness hchecker,
    audit_pk_stage4_conventionEquivalence_toFamilyExactness hconv⟩

abbrev audit_pk_stage4SplitLocalCheckedToFamilyExactnessEntryPoint :=
  @audit_pk_stage4_splitLocalChecked_toFamilyExactness

abbrev audit_pk_stage4ConventionEquivalenceToFamilyExactnessEntryPoint :=
  @audit_pk_stage4_conventionEquivalence_toFamilyExactness

abbrev audit_pk_stage4FamilyExactnessRoutesEntryPoint :=
  @audit_pk_stage4FamilyExactnessRoutes

abbrev audit_pk_stage4LocalCheckedSplitToExactFamilyClosed :=
  @audit_pk_stage4FamilyExactnessRoutes

/-!
Stage-4 exact-family input closure.  These projections connect the concrete
`SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs`
surface to family exactness, split local checked recognition, project checked
recognition, the local convention certificate, and the Pudlak-side route.
-/

theorem audit_pk_stage4_exactFamilyInputs_localFamilyExactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
      h.formula_code_interpretation :=
  h.local_hilbert_family_exactness

theorem audit_pk_stage4_exactFamilyInputs_toSplitLocalChecked
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    _root_.MiniHilbert.PASplitLocalCheckedRecognition
      h.formula_code_interpretation :=
  audit_pk_stage4_familyExactness_toSplitLocalChecked
    h.formula_code_interpretation
    (audit_pk_stage4_exactFamilyInputs_localFamilyExactness h)

theorem audit_pk_stage4_exactFamilyInputs_toProjectCheckedRecognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertProjectCheckedProofLengthRecognition
      h.formula_code_interpretation :=
  _root_.MiniHilbert.PASplitLocalCheckedRecognition.toProjectCheckedRecognition
    (audit_pk_stage4_exactFamilyInputs_toSplitLocalChecked h)

abbrev audit_pk_stage4_exactFamilyInputs_localConventionCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertLocalProofCodeConventionCertificate
      h.formula_code_interpretation :=
  SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs.localHilbertConventionCertificate h

theorem audit_pk_stage4_exactFamilyInputs_toPudlakSideInputsRoute
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    h.toPudlakSideInputs =
      h.toExactConventionInputs.toPudlakSideInputs :=
  rfl

theorem audit_pk_stage4_exactFamilyInputs_localClosure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness
        h.formula_code_interpretation ∧
      _root_.MiniHilbert.PASplitLocalCheckedRecognition
        h.formula_code_interpretation ∧
        _root_.MiniHilbert.PAHilbertProjectCheckedProofLengthRecognition
          h.formula_code_interpretation :=
  ⟨audit_pk_stage4_exactFamilyInputs_localFamilyExactness h,
    audit_pk_stage4_exactFamilyInputs_toSplitLocalChecked h,
    audit_pk_stage4_exactFamilyInputs_toProjectCheckedRecognition h⟩

abbrev audit_pk_stage4ExactFamilyInputsLocalClosureEntryPoint :=
  @audit_pk_stage4_exactFamilyInputs_localClosure

abbrev audit_pk_stage4ExactFamilyInputsProjectCheckedEntryPoint :=
  @audit_pk_stage4_exactFamilyInputs_toProjectCheckedRecognition

abbrev audit_pk_stage4ExactFamilyInputsPudlakSideRouteEntryPoint :=
  @audit_pk_stage4_exactFamilyInputs_toPudlakSideInputsRoute

end SondowMainCheckedCodeBridge

end
