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

theorem normalForm_code_eq_powerBoundRawCode
    (h : SondowProjectLocalPudlakTheorem5AuditedLowerBoundInputs)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    (h.toCertificate.toNormalForm hpartial).code =
      h.scale_data.powerBoundRawCode := by
  exact h.toCertificate.normalForm_code_eq_powerBoundRawCode hpartial

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

theorem normalForm_code_eq_powerBoundRawCode
    (h : SondowProjectLocalPudlakTheorem5RescaledLowerBoundInputs)
    (hpartial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer) :
    (h.toCertificate.toNormalForm hpartial).code =
      h.scale_data.powerBoundRawCode := by
  exact h.toCertificate.normalForm_code_eq_powerBoundRawCode hpartial

end SondowProjectLocalPudlakTheorem5RescaledLowerBoundInputs

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

end SondowMainCheckedCodeBridge

end
