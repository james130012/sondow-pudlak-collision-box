/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.StrengthenedConsistency

/-!
# External Pudlak raw-encoding certificates

This module records the exact bridge required from a literature formula family
to the local Pudlak-strengthened finite-consistency code.  It deliberately
keeps the external lower-bound theorem separate from the encoding calibration:
an external source is admissible only after it supplies one of the explicit
certificates below.
-/

def adoptedPudlakRawEncoding (n : ℕ) : FormulaCode :=
  pudlakStrengthenedFiniteConsistencyCode n

theorem adoptedPudlakRawEncoding_eq
    (n : ℕ) :
    adoptedPudlakRawEncoding n =
      pudlakStrengthenedFiniteConsistencyCode n := by
  rfl

def rescaledAdoptedPudlakRawEncoding
    (ρ : ℕ → ℕ) (n : ℕ) : FormulaCode :=
  adoptedPudlakRawEncoding (ρ n)

theorem rescaledAdoptedPudlakRawEncoding_eq
    (ρ : ℕ → ℕ) (n : ℕ) :
    rescaledAdoptedPudlakRawEncoding ρ n =
      rescaledPudlakStrengthenedFiniteConsistencyCode ρ n := by
  rfl

inductive ExternalContradictionTarget
  | zeroEqOne

structure LiteratureFiniteConsistencyDescriptor where
  theory : ProofSystem
  measure : ProofLengthMeasure
  bound : ℕ
  contradiction : ExternalContradictionTarget

def LiteratureFiniteConsistencyDescriptor.isPudlakPA
    (d : LiteratureFiniteConsistencyDescriptor) : Prop :=
  d.theory = ProofSystem.PA ∧
    d.measure = ProofLengthMeasure.symbolSize ∧
    d.contradiction = ExternalContradictionTarget.zeroEqOne

def LiteratureFiniteConsistencyDescriptor.toFormulaCode
    (d : LiteratureFiniteConsistencyDescriptor) : FormulaCode :=
  match d.theory, d.measure, d.contradiction with
  | ProofSystem.PA, ProofLengthMeasure.symbolSize,
      ExternalContradictionTarget.zeroEqOne =>
      pudlakStrengthenedFiniteConsistencyCode d.bound
  | _, _, _ =>
      { family := FormulaFamily.strengthenedPartialConsistency, index := d.bound }

def bussPudlakPAFiniteConsistencyDescriptor
    (n : ℕ) : LiteratureFiniteConsistencyDescriptor where
  theory := ProofSystem.PA
  measure := ProofLengthMeasure.symbolSize
  bound := n
  contradiction := ExternalContradictionTarget.zeroEqOne

def bussPudlakPAFiniteConsistencyRawCode
    (n : ℕ) : FormulaCode :=
  (bussPudlakPAFiniteConsistencyDescriptor n).toFormulaCode

theorem bussPudlakPAFiniteConsistencyDescriptor_isPudlakPA
    (n : ℕ) :
    (bussPudlakPAFiniteConsistencyDescriptor n).isPudlakPA := by
  exact ⟨rfl, rfl, rfl⟩

theorem bussPudlakPAFiniteConsistencyRawCode_eq
    (n : ℕ) :
    bussPudlakPAFiniteConsistencyRawCode n =
      pudlakStrengthenedFiniteConsistencyCode n := by
  rfl

def rescaledBussPudlakPAFiniteConsistencyRawCode
    (ρ : ℕ → ℕ) (n : ℕ) : FormulaCode :=
  bussPudlakPAFiniteConsistencyRawCode (ρ n)

theorem rescaledBussPudlakPAFiniteConsistencyRawCode_eq
    (ρ : ℕ → ℕ) (n : ℕ) :
    rescaledBussPudlakPAFiniteConsistencyRawCode ρ n =
      rescaledPudlakStrengthenedFiniteConsistencyCode ρ n := by
  rfl

def bussPudlakPAFiniteConsistencyDescriptorAtScale
    (ρ : ℕ → ℕ) (n : ℕ) : LiteratureFiniteConsistencyDescriptor :=
  bussPudlakPAFiniteConsistencyDescriptor (ρ n)

theorem bussPudlakPAFiniteConsistencyDescriptorAtScale_isPudlakPA
    (ρ : ℕ → ℕ) (n : ℕ) :
    (bussPudlakPAFiniteConsistencyDescriptorAtScale ρ n).isPudlakPA := by
  exact bussPudlakPAFiniteConsistencyDescriptor_isPudlakPA (ρ n)

theorem bussPudlakPAFiniteConsistencyDescriptorAtScale_code_eq
    (ρ : ℕ → ℕ) (n : ℕ) :
    (bussPudlakPAFiniteConsistencyDescriptorAtScale ρ n).toFormulaCode =
      rescaledPudlakStrengthenedFiniteConsistencyCode ρ n := by
  rfl

theorem literature_finite_consistency_code_eq_pudlak_of_isPudlakPA
    {d : LiteratureFiniteConsistencyDescriptor}
    (hd : d.isPudlakPA) :
    d.toFormulaCode = pudlakStrengthenedFiniteConsistencyCode d.bound := by
  rcases d with ⟨theory, measure, bound, contradiction⟩
  rcases hd with ⟨htheory, hmeasure, hcontradiction⟩
  subst htheory
  subst hmeasure
  subst hcontradiction
  rfl

structure ExternalPudlakRawEncodingCertificate where
  raw : ℕ → FormulaCode
  transfer_to_pudlak : RawPudlakToPudlakStrengthenedTransfer raw

def ExternalPudlakRawEncodingCertificate.of_transfer
    {raw : ℕ → FormulaCode}
    (htransfer : RawPudlakToPudlakStrengthenedTransfer raw) :
    ExternalPudlakRawEncodingCertificate where
  raw := raw
  transfer_to_pudlak := htransfer

def ExternalPudlakRawEncodingCertificate.of_projection
    {raw : ℕ → FormulaCode}
    (hprojection : RawPudlakToPudlakStrengthenedProjection raw) :
    ExternalPudlakRawEncodingCertificate :=
  ExternalPudlakRawEncodingCertificate.of_transfer
    (raw_pudlak_to_pudlak_transfer_of_projection hprojection)

def ExternalPudlakRawEncodingCertificate.of_linear_projection
    {raw : ℕ → FormulaCode}
    (hprojection : RawPudlakToPudlakStrengthenedLinearProjection raw) :
    ExternalPudlakRawEncodingCertificate :=
  ExternalPudlakRawEncodingCertificate.of_transfer
    (raw_pudlak_to_pudlak_transfer_of_linear_projection hprojection)

def ExternalPudlakRawEncodingCertificate.of_constant_projection
    {raw : ℕ → FormulaCode}
    (hprojection : RawPudlakToPudlakStrengthenedConstantProjection raw) :
    ExternalPudlakRawEncodingCertificate :=
  ExternalPudlakRawEncodingCertificate.of_transfer
    (raw_pudlak_to_pudlak_transfer_of_constant_projection hprojection)

def ExternalPudlakRawEncodingCertificate.of_pointwise_eq
    {raw : ℕ → FormulaCode}
    (hcode : ∀ n : ℕ, raw n = pudlakStrengthenedFiniteConsistencyCode n) :
    ExternalPudlakRawEncodingCertificate :=
  ExternalPudlakRawEncodingCertificate.of_projection
    (raw_pudlak_to_pudlak_projection_of_pointwise_eq hcode)

def ExternalPudlakRawEncodingCertificate.adopted :
    ExternalPudlakRawEncodingCertificate :=
  ExternalPudlakRawEncodingCertificate.of_pointwise_eq
    adoptedPudlakRawEncoding_eq

def literaturePudlakPARawEncodingCertificate :
    ExternalPudlakRawEncodingCertificate :=
  ExternalPudlakRawEncodingCertificate.of_pointwise_eq
    bussPudlakPAFiniteConsistencyRawCode_eq

def ExternalPudlakRawEncodingCertificate.toCalibration
    (h : ExternalPudlakRawEncodingCertificate) :
    RawPudlakStrengthenedEncodingCalibration where
  raw := h.raw
  transfer_to_pudlak := h.transfer_to_pudlak

def ExternalPudlakRawEncodingCertificate.toLowerBoundSource
    (h : ExternalPudlakRawEncodingCertificate)
    (hlower :
      StrongProofLengthLowerBound
        ProofSystem.PA ProofLengthMeasure.symbolSize h.raw) :
    RawPudlakStrengthenedLowerBoundSource where
  raw := h.raw
  strong_lower_bound := hlower
  calibration := h.toCalibration
  calibration_raw_eq := rfl

theorem raw_pudlak_rescaled_projection_of_projection
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection : RawPudlakToPudlakStrengthenedProjection raw) :
    RescaledRawPudlakToRescaledPudlakStrengthenedProjection raw ρ where
  source_le_target := by
    intro n
    exact hprojection.source_le_target (ρ n)

def raw_pudlak_rescaled_linear_projection_of_linear_projection
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection : RawPudlakToPudlakStrengthenedLinearProjection raw) :
    RescaledRawPudlakToRescaledPudlakStrengthenedLinearProjection raw ρ where
  C := hprojection.C
  D := hprojection.D
  C_pos := hprojection.C_pos
  D_nonneg := hprojection.D_nonneg
  source_le_linear_target := by
    intro n
    exact hprojection.source_le_linear_target (ρ n)

def raw_pudlak_rescaled_constant_projection_of_constant_projection
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection : RawPudlakToPudlakStrengthenedConstantProjection raw) :
    RescaledRawPudlakToRescaledPudlakStrengthenedConstantProjection raw ρ where
  D := hprojection.D
  D_nonneg := hprojection.D_nonneg
  source_le_target_add := by
    intro n
    exact hprojection.source_le_target_add (ρ n)

structure ExternalPudlakRescaledRawEncodingCertificate where
  raw : ℕ → FormulaCode
  scale : ℕ → ℕ
  transfer_to_rescaled_pudlak :
    RescaledRawPudlakToRescaledPudlakStrengthenedTransfer raw scale

def ExternalPudlakRescaledRawEncodingCertificate.of_transfer
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (htransfer :
      RescaledRawPudlakToRescaledPudlakStrengthenedTransfer raw ρ) :
    ExternalPudlakRescaledRawEncodingCertificate where
  raw := raw
  scale := ρ
  transfer_to_rescaled_pudlak := htransfer

def ExternalPudlakRescaledRawEncodingCertificate.of_projection
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection :
      RescaledRawPudlakToRescaledPudlakStrengthenedProjection raw ρ) :
    ExternalPudlakRescaledRawEncodingCertificate :=
  ExternalPudlakRescaledRawEncodingCertificate.of_transfer
    (rescaled_raw_pudlak_to_rescaled_pudlak_transfer_of_projection
      hprojection)

def ExternalPudlakRescaledRawEncodingCertificate.of_linear_projection
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection :
      RescaledRawPudlakToRescaledPudlakStrengthenedLinearProjection raw ρ) :
    ExternalPudlakRescaledRawEncodingCertificate :=
  ExternalPudlakRescaledRawEncodingCertificate.of_transfer
    (rescaled_raw_pudlak_to_rescaled_pudlak_transfer_of_linear_projection
      hprojection)

def ExternalPudlakRescaledRawEncodingCertificate.of_constant_projection
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection :
      RescaledRawPudlakToRescaledPudlakStrengthenedConstantProjection raw ρ) :
    ExternalPudlakRescaledRawEncodingCertificate :=
  ExternalPudlakRescaledRawEncodingCertificate.of_transfer
    (rescaled_raw_pudlak_to_rescaled_pudlak_transfer_of_constant_projection
      hprojection)

def ExternalPudlakRescaledRawEncodingCertificate.of_pointwise_eq
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hcode : ∀ n : ℕ, raw n = pudlakStrengthenedFiniteConsistencyCode n) :
    ExternalPudlakRescaledRawEncodingCertificate :=
  ExternalPudlakRescaledRawEncodingCertificate.of_projection
    (rescaled_raw_pudlak_to_rescaled_pudlak_projection_of_pointwise_eq
      (ρ := ρ) hcode)

def ExternalPudlakRescaledRawEncodingCertificate.of_raw_projection
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection : RawPudlakToPudlakStrengthenedProjection raw) :
    ExternalPudlakRescaledRawEncodingCertificate :=
  ExternalPudlakRescaledRawEncodingCertificate.of_projection
    (raw_pudlak_rescaled_projection_of_projection
      (ρ := ρ) hprojection)

def ExternalPudlakRescaledRawEncodingCertificate.of_raw_linear_projection
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection : RawPudlakToPudlakStrengthenedLinearProjection raw) :
    ExternalPudlakRescaledRawEncodingCertificate :=
  ExternalPudlakRescaledRawEncodingCertificate.of_linear_projection
    (raw_pudlak_rescaled_linear_projection_of_linear_projection
      (ρ := ρ) hprojection)

def ExternalPudlakRescaledRawEncodingCertificate.of_raw_constant_projection
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection : RawPudlakToPudlakStrengthenedConstantProjection raw) :
    ExternalPudlakRescaledRawEncodingCertificate :=
  ExternalPudlakRescaledRawEncodingCertificate.of_constant_projection
    (raw_pudlak_rescaled_constant_projection_of_constant_projection
      (ρ := ρ) hprojection)

def ExternalPudlakRescaledRawEncodingCertificate.adopted
    (ρ : ℕ → ℕ) :
    ExternalPudlakRescaledRawEncodingCertificate :=
  ExternalPudlakRescaledRawEncodingCertificate.of_pointwise_eq
    (ρ := ρ) adoptedPudlakRawEncoding_eq

def literaturePudlakPARescaledRawEncodingCertificate
    (ρ : ℕ → ℕ) :
    ExternalPudlakRescaledRawEncodingCertificate :=
  ExternalPudlakRescaledRawEncodingCertificate.of_pointwise_eq
    (ρ := ρ) bussPudlakPAFiniteConsistencyRawCode_eq

def ExternalPudlakRawEncodingCertificate.rescale
    (h : ExternalPudlakRawEncodingCertificate) (ρ : ℕ → ℕ)
    (hprojection : RawPudlakToPudlakStrengthenedProjection h.raw) :
    ExternalPudlakRescaledRawEncodingCertificate :=
  ExternalPudlakRescaledRawEncodingCertificate.of_raw_projection
    (ρ := ρ) hprojection

def ExternalPudlakRawEncodingCertificate.rescaleLinear
    (h : ExternalPudlakRawEncodingCertificate) (ρ : ℕ → ℕ)
    (hprojection : RawPudlakToPudlakStrengthenedLinearProjection h.raw) :
    ExternalPudlakRescaledRawEncodingCertificate :=
  ExternalPudlakRescaledRawEncodingCertificate.of_raw_linear_projection
    (ρ := ρ) hprojection

def ExternalPudlakRescaledRawEncodingCertificate.toCalibration
    (h : ExternalPudlakRescaledRawEncodingCertificate) :
    RescaledRawPudlakStrengthenedEncodingCalibration where
  raw := h.raw
  scale := h.scale
  transfer_to_rescaled_pudlak := h.transfer_to_rescaled_pudlak

def ExternalPudlakRescaledRawEncodingCertificate.toLowerBoundSource
    (h : ExternalPudlakRescaledRawEncodingCertificate)
    (hscale : PolynomialCofinalScale h.scale)
    (hlower : StrongRescaledExternalStrengthenedLowerBound h.raw h.scale) :
    RescaledRawPudlakStrengthenedLowerBoundSource where
  raw := h.raw
  scale := h.scale
  scale_properties := hscale
  rescaled_strong_lower_bound := hlower
  calibration := h.toCalibration
  calibration_raw_eq := rfl
  calibration_scale_eq := rfl

structure LiteraturePudlakTheorem5StandardInstance where
  scale : ℕ → ℕ
  scale_properties : PolynomialCofinalScale scale
  rescaled_strong_lower_bound :
    StrongRescaledExternalStrengthenedLowerBound
      bussPudlakPAFiniteConsistencyRawCode scale

def LiteraturePudlakTheorem5StandardInstance.encodingCertificate
    (h : LiteraturePudlakTheorem5StandardInstance) :
    ExternalPudlakRescaledRawEncodingCertificate :=
  literaturePudlakPARescaledRawEncodingCertificate h.scale

def LiteraturePudlakTheorem5StandardInstance.toLowerBoundSource
    (h : LiteraturePudlakTheorem5StandardInstance) :
    RescaledRawPudlakStrengthenedLowerBoundSource :=
  h.encodingCertificate.toLowerBoundSource
    h.scale_properties h.rescaled_strong_lower_bound

def LiteraturePudlakTheorem5StandardInstance.toCalibratedRescaledExternalSource
    (h : LiteraturePudlakTheorem5StandardInstance)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    CalibratedRescaledExternalStrengthenedLowerBoundSource :=
  h.toLowerBoundSource.toCalibratedRescaledExternalSource hpartial

def LiteraturePudlakTheorem5StandardInstance.toNormalForm
    (h : LiteraturePudlakTheorem5StandardInstance)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    PartialConsistencyLowerBoundNormalForm :=
  h.toLowerBoundSource.toNormalForm hpartial

def LiteraturePudlakTheorem5StandardInstance.toNormalFormOfProjection
    (h : LiteraturePudlakTheorem5StandardInstance)
    (hpartial : StrengthenedToPartialConsistencyProjection) :
    PartialConsistencyLowerBoundNormalForm :=
  h.toNormalForm (strengthened_to_partial_transfer_of_projection hpartial)

def LiteraturePudlakTheorem5StandardInstance.toNormalFormOfLinearProjection
    (h : LiteraturePudlakTheorem5StandardInstance)
    (hpartial : StrengthenedToPartialConsistencyLinearProjection) :
    PartialConsistencyLowerBoundNormalForm :=
  h.toNormalForm (strengthened_to_partial_transfer_of_linear_projection hpartial)

def LiteraturePudlakTheorem5StandardInstance.toNormalFormOfConstantProjection
    (h : LiteraturePudlakTheorem5StandardInstance)
    (hpartial : StrengthenedToPartialConsistencyConstantProjection) :
    PartialConsistencyLowerBoundNormalForm :=
  h.toNormalForm (strengthened_to_partial_transfer_of_constant_projection hpartial)

theorem LiteraturePudlakTheorem5StandardInstance.normalForm_code_eq
    (h : LiteraturePudlakTheorem5StandardInstance)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    (h.toNormalForm hpartial).code =
      rescaledBussPudlakPAFiniteConsistencyRawCode h.scale := by
  rfl

theorem LiteraturePudlakTheorem5StandardInstance.normalForm_code_eq_rescaledPudlak
    (h : LiteraturePudlakTheorem5StandardInstance)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (n : ℕ) :
    (h.toNormalForm hpartial).code n =
      rescaledPudlakStrengthenedFiniteConsistencyCode h.scale n := by
  rw [h.normalForm_code_eq hpartial]
  exact rescaledBussPudlakPAFiniteConsistencyRawCode_eq h.scale n

theorem LiteraturePudlakTheorem5StandardInstance.normalForm_transfer_target
    (h : LiteraturePudlakTheorem5StandardInstance)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    StrongLowerBoundTransfer ProofSystem.PA ProofLengthMeasure.symbolSize
      (rescaledBussPudlakPAFiniteConsistencyRawCode h.scale)
      partialConsistencyCode :=
  (h.toNormalForm hpartial).transfer_to_partial

structure LiteraturePudlakTheorem5ScaleData where
  time_constructible_bound : ℕ → ℕ
  exponent : ℕ
  scale : ℕ → ℕ
  scale_eq :
    ∀ n : ℕ, scale n = time_constructible_bound n ^ exponent
  scale_id_le : ∀ n : ℕ, n ≤ scale n
  scale_polynomial_bound :
    is_polynomial_bound (fun n : ℕ => (scale n : ℝ))

def LiteraturePudlakTheorem5ScaleData.scale_properties
    (h : LiteraturePudlakTheorem5ScaleData) :
    PolynomialCofinalScale h.scale :=
  PolynomialCofinalScale.of_id_le_and_polynomial_bound
    h.scale_id_le h.scale_polynomial_bound

def LiteraturePudlakTheorem5ScaleData.rawCode
    (_ : LiteraturePudlakTheorem5ScaleData) : ℕ → FormulaCode :=
  bussPudlakPAFiniteConsistencyRawCode

def LiteraturePudlakTheorem5ScaleData.rescaledRawCode
    (h : LiteraturePudlakTheorem5ScaleData) : ℕ → FormulaCode :=
  rescaledBussPudlakPAFiniteConsistencyRawCode h.scale

def LiteraturePudlakTheorem5ScaleData.powerBoundRawCode
    (h : LiteraturePudlakTheorem5ScaleData) (n : ℕ) : FormulaCode :=
  bussPudlakPAFiniteConsistencyRawCode
    (h.time_constructible_bound n ^ h.exponent)

theorem LiteraturePudlakTheorem5ScaleData.rescaledRawCode_eq_powerBoundRawCode
    (h : LiteraturePudlakTheorem5ScaleData) (n : ℕ) :
    h.rescaledRawCode n = h.powerBoundRawCode n := by
  change
    bussPudlakPAFiniteConsistencyRawCode (h.scale n) =
      bussPudlakPAFiniteConsistencyRawCode
        (h.time_constructible_bound n ^ h.exponent)
  rw [h.scale_eq n]

theorem LiteraturePudlakTheorem5ScaleData.rescaledRawCode_eq_rescaledPudlak
    (h : LiteraturePudlakTheorem5ScaleData) (n : ℕ) :
    h.rescaledRawCode n =
      rescaledPudlakStrengthenedFiniteConsistencyCode h.scale n := by
  exact rescaledBussPudlakPAFiniteConsistencyRawCode_eq h.scale n

theorem LiteraturePudlakTheorem5ScaleData.powerBoundRawCode_eq_rescaledPudlak
    (h : LiteraturePudlakTheorem5ScaleData) (n : ℕ) :
    h.powerBoundRawCode n =
      rescaledPudlakStrengthenedFiniteConsistencyCode h.scale n := by
  rw [← h.rescaledRawCode_eq_powerBoundRawCode n]
  exact h.rescaledRawCode_eq_rescaledPudlak n

def LiteraturePudlakTheorem5ScaleData.encodingCertificate
    (h : LiteraturePudlakTheorem5ScaleData) :
    ExternalPudlakRescaledRawEncodingCertificate :=
  literaturePudlakPARescaledRawEncodingCertificate h.scale

def LiteraturePudlakTheorem5ScaleData.toStandardInstance
    (h : LiteraturePudlakTheorem5ScaleData)
    (hlower :
      StrongRescaledExternalStrengthenedLowerBound h.rawCode h.scale) :
    LiteraturePudlakTheorem5StandardInstance where
  scale := h.scale
  scale_properties := h.scale_properties
  rescaled_strong_lower_bound := hlower

def LiteraturePudlakTheorem5ScaleData.toLowerBoundSource
    (h : LiteraturePudlakTheorem5ScaleData)
    (hlower :
      StrongRescaledExternalStrengthenedLowerBound h.rawCode h.scale) :
    RescaledRawPudlakStrengthenedLowerBoundSource :=
  (h.toStandardInstance hlower).toLowerBoundSource

def LiteraturePudlakTheorem5ScaleData.toNormalForm
    (h : LiteraturePudlakTheorem5ScaleData)
    (hlower :
      StrongRescaledExternalStrengthenedLowerBound h.rawCode h.scale)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    PartialConsistencyLowerBoundNormalForm :=
  (h.toStandardInstance hlower).toNormalForm hpartial

def LiteraturePudlakTheorem5ScaleData.toNormalFormOfProjection
    (h : LiteraturePudlakTheorem5ScaleData)
    (hlower :
      StrongRescaledExternalStrengthenedLowerBound h.rawCode h.scale)
    (hpartial : StrengthenedToPartialConsistencyProjection) :
    PartialConsistencyLowerBoundNormalForm :=
  (h.toStandardInstance hlower).toNormalFormOfProjection hpartial

def LiteraturePudlakTheorem5ScaleData.toNormalFormOfLinearProjection
    (h : LiteraturePudlakTheorem5ScaleData)
    (hlower :
      StrongRescaledExternalStrengthenedLowerBound h.rawCode h.scale)
    (hpartial : StrengthenedToPartialConsistencyLinearProjection) :
    PartialConsistencyLowerBoundNormalForm :=
  (h.toStandardInstance hlower).toNormalFormOfLinearProjection hpartial

def LiteraturePudlakTheorem5ScaleData.toNormalFormOfConstantProjection
    (h : LiteraturePudlakTheorem5ScaleData)
    (hlower :
      StrongRescaledExternalStrengthenedLowerBound h.rawCode h.scale)
    (hpartial : StrengthenedToPartialConsistencyConstantProjection) :
    PartialConsistencyLowerBoundNormalForm :=
  (h.toStandardInstance hlower).toNormalFormOfConstantProjection hpartial

theorem LiteraturePudlakTheorem5ScaleData.standardInstance_scale_eq
    (h : LiteraturePudlakTheorem5ScaleData)
    (hlower :
      StrongRescaledExternalStrengthenedLowerBound h.rawCode h.scale) :
    (h.toStandardInstance hlower).scale = h.scale := by
  rfl

theorem LiteraturePudlakTheorem5ScaleData.normalForm_code_eq_powerBoundRawCode
    (h : LiteraturePudlakTheorem5ScaleData)
    (hlower :
      StrongRescaledExternalStrengthenedLowerBound h.rawCode h.scale)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    (h.toNormalForm hlower hpartial).code = h.powerBoundRawCode := by
  funext n
  exact h.rescaledRawCode_eq_powerBoundRawCode n

theorem LiteraturePudlakTheorem5ScaleData.normalForm_code_eq_rescaledPudlak
    (h : LiteraturePudlakTheorem5ScaleData)
    (hlower :
      StrongRescaledExternalStrengthenedLowerBound h.rawCode h.scale)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (n : ℕ) :
    (h.toNormalForm hlower hpartial).code n =
      rescaledPudlakStrengthenedFiniteConsistencyCode h.scale n := by
  rw [h.normalForm_code_eq_powerBoundRawCode hlower hpartial]
  exact h.powerBoundRawCode_eq_rescaledPudlak n

abbrev LiteraturePudlakTheorem5PowerBoundLowerBound
    (h : LiteraturePudlakTheorem5ScaleData) : Prop :=
  StrongProofLengthLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
    h.powerBoundRawCode

theorem LiteraturePudlakTheorem5ScaleData.powerBoundLowerBound_to_rescaledLowerBound
    (h : LiteraturePudlakTheorem5ScaleData)
    (hlower : LiteraturePudlakTheorem5PowerBoundLowerBound h) :
    StrongRescaledExternalStrengthenedLowerBound h.rawCode h.scale :=
  hlower.congr_symm h.rescaledRawCode_eq_powerBoundRawCode

theorem LiteraturePudlakTheorem5ScaleData.rescaledLowerBound_to_powerBoundLowerBound
    (h : LiteraturePudlakTheorem5ScaleData)
    (hlower :
      StrongRescaledExternalStrengthenedLowerBound h.rawCode h.scale) :
    LiteraturePudlakTheorem5PowerBoundLowerBound h :=
  hlower.congr h.rescaledRawCode_eq_powerBoundRawCode

theorem LiteraturePudlakTheorem5ScaleData.powerBoundLowerBound_iff_rescaledLowerBound
    (h : LiteraturePudlakTheorem5ScaleData) :
    LiteraturePudlakTheorem5PowerBoundLowerBound h ↔
      StrongRescaledExternalStrengthenedLowerBound h.rawCode h.scale :=
  ⟨h.powerBoundLowerBound_to_rescaledLowerBound,
    h.rescaledLowerBound_to_powerBoundLowerBound⟩

structure LiteraturePudlakTheorem5LowerBoundCertificate where
  scale_data : LiteraturePudlakTheorem5ScaleData
  power_bound_lower_bound :
    LiteraturePudlakTheorem5PowerBoundLowerBound scale_data

def LiteraturePudlakTheorem5LowerBoundCertificate.rescaled_strong_lower_bound
    (h : LiteraturePudlakTheorem5LowerBoundCertificate) :
    StrongRescaledExternalStrengthenedLowerBound
      h.scale_data.rawCode h.scale_data.scale :=
  h.scale_data.powerBoundLowerBound_to_rescaledLowerBound
    h.power_bound_lower_bound

structure LiteraturePudlakTheorem5RescaledLowerBoundCertificate where
  scale_data : LiteraturePudlakTheorem5ScaleData
  rescaled_lower_bound :
    StrongRescaledExternalStrengthenedLowerBound
      scale_data.rawCode scale_data.scale

def LiteraturePudlakTheorem5RescaledLowerBoundCertificate.toPowerBoundCertificate
    (h : LiteraturePudlakTheorem5RescaledLowerBoundCertificate) :
    LiteraturePudlakTheorem5LowerBoundCertificate where
  scale_data := h.scale_data
  power_bound_lower_bound :=
    h.scale_data.rescaledLowerBound_to_powerBoundLowerBound
      h.rescaled_lower_bound

theorem LiteraturePudlakTheorem5RescaledLowerBoundCertificate.toPowerBoundCertificate_scale_data
    (h : LiteraturePudlakTheorem5RescaledLowerBoundCertificate) :
    h.toPowerBoundCertificate.scale_data = h.scale_data := by
  rfl

def LiteraturePudlakTheorem5LowerBoundCertificate.toRescaledCertificate
    (h : LiteraturePudlakTheorem5LowerBoundCertificate) :
    LiteraturePudlakTheorem5RescaledLowerBoundCertificate where
  scale_data := h.scale_data
  rescaled_lower_bound := h.rescaled_strong_lower_bound

theorem LiteraturePudlakTheorem5LowerBoundCertificate.toRescaledCertificate_scale_data
    (h : LiteraturePudlakTheorem5LowerBoundCertificate) :
    h.toRescaledCertificate.scale_data = h.scale_data := by
  rfl

theorem LiteraturePudlakTheorem5LowerBoundCertificate.toRescaled_toPowerBound_scale_data
    (h : LiteraturePudlakTheorem5LowerBoundCertificate) :
    h.toRescaledCertificate.toPowerBoundCertificate.scale_data =
      h.scale_data := by
  rfl

theorem LiteraturePudlakTheorem5RescaledLowerBoundCertificate.toPowerBound_toRescaled_scale_data
    (h : LiteraturePudlakTheorem5RescaledLowerBoundCertificate) :
    h.toPowerBoundCertificate.toRescaledCertificate.scale_data =
      h.scale_data := by
  rfl

theorem LiteraturePudlakTheorem5LowerBoundCertificate.toRescaled_toPowerBound_powerBoundRawCode
    (h : LiteraturePudlakTheorem5LowerBoundCertificate) (n : ℕ) :
    h.toRescaledCertificate.toPowerBoundCertificate.scale_data.powerBoundRawCode n =
      h.scale_data.powerBoundRawCode n := by
  rfl

set_option linter.style.longLine false in
theorem LiteraturePudlakTheorem5RescaledLowerBoundCertificate.toPowerBound_toRescaled_rescaledRawCode
    (h : LiteraturePudlakTheorem5RescaledLowerBoundCertificate) (n : ℕ) :
    h.toPowerBoundCertificate.toRescaledCertificate.scale_data.rescaledRawCode n =
      h.scale_data.rescaledRawCode n := by
  rfl

theorem literaturePudlakTheorem5Certificate_nonempty_iff_rescaledCertificate :
    Nonempty LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty LiteraturePudlakTheorem5RescaledLowerBoundCertificate := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.toRescaledCertificate⟩
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.toPowerBoundCertificate⟩

/-- External literature witness for Pudlak theorem 5.

This is intentionally the only theorem-5 mathematical input left opaque: it
asserts the scale data cited from the literature, including its polynomial
cofinality facts. -/
axiom literaturePudlakTheorem5ExternalScaleData :
  LiteraturePudlakTheorem5ScaleData

/-- External literature witness for the theorem-5 lower bound, stated on the
exact rescaled raw PA finite-consistency family and the project proof-length
convention `ProofSystem.PA`/`ProofLengthMeasure.symbolSize`. -/
axiom literaturePudlakTheorem5ExternalRescaledLowerBound :
  StrongRescaledExternalStrengthenedLowerBound
    literaturePudlakTheorem5ExternalScaleData.rawCode
    literaturePudlakTheorem5ExternalScaleData.scale

noncomputable def literaturePudlakTheorem5ExternalRescaledLowerBoundCertificate :
    LiteraturePudlakTheorem5RescaledLowerBoundCertificate where
  scale_data := literaturePudlakTheorem5ExternalScaleData
  rescaled_lower_bound := literaturePudlakTheorem5ExternalRescaledLowerBound

noncomputable def literaturePudlakTheorem5ExternalPowerBoundLowerBound :
    LiteraturePudlakTheorem5PowerBoundLowerBound
      literaturePudlakTheorem5ExternalScaleData :=
  literaturePudlakTheorem5ExternalScaleData.rescaledLowerBound_to_powerBoundLowerBound
    literaturePudlakTheorem5ExternalRescaledLowerBound

noncomputable def literaturePudlakTheorem5ExternalLowerBoundCertificate :
    LiteraturePudlakTheorem5LowerBoundCertificate where
  scale_data := literaturePudlakTheorem5ExternalScaleData
  power_bound_lower_bound :=
    literaturePudlakTheorem5ExternalPowerBoundLowerBound

theorem literaturePudlakTheorem5ExternalRescaledCertificate_toPowerBound :
    literaturePudlakTheorem5ExternalRescaledLowerBoundCertificate.toPowerBoundCertificate =
      literaturePudlakTheorem5ExternalLowerBoundCertificate := by
  rfl

theorem literaturePudlakTheorem5External_rescaledRawCode_eq_powerBoundRawCode
    (n : ℕ) :
    literaturePudlakTheorem5ExternalScaleData.rescaledRawCode n =
      literaturePudlakTheorem5ExternalScaleData.powerBoundRawCode n :=
  literaturePudlakTheorem5ExternalScaleData
    |>.rescaledRawCode_eq_powerBoundRawCode n

theorem literaturePudlakTheorem5External_powerBoundRawCode_eq_rescaledPudlak
    (n : ℕ) :
    literaturePudlakTheorem5ExternalScaleData.powerBoundRawCode n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        literaturePudlakTheorem5ExternalScaleData.scale n :=
  literaturePudlakTheorem5ExternalScaleData
    |>.powerBoundRawCode_eq_rescaledPudlak n

def LiteraturePudlakTheorem5LowerBoundCertificate.toStandardInstance
    (h : LiteraturePudlakTheorem5LowerBoundCertificate) :
    LiteraturePudlakTheorem5StandardInstance :=
  h.scale_data.toStandardInstance h.rescaled_strong_lower_bound

def LiteraturePudlakTheorem5LowerBoundCertificate.toLowerBoundSource
    (h : LiteraturePudlakTheorem5LowerBoundCertificate) :
    RescaledRawPudlakStrengthenedLowerBoundSource :=
  h.toStandardInstance.toLowerBoundSource

def LiteraturePudlakTheorem5LowerBoundCertificate.toNormalForm
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    PartialConsistencyLowerBoundNormalForm :=
  h.toStandardInstance.toNormalForm hpartial

def LiteraturePudlakTheorem5LowerBoundCertificate.toNormalFormOfProjection
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyProjection) :
    PartialConsistencyLowerBoundNormalForm :=
  h.toStandardInstance.toNormalFormOfProjection hpartial

def LiteraturePudlakTheorem5LowerBoundCertificate.toNormalFormOfAcceptedProjection
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hprinciple : PAProofLengthProjectionPrinciple)
    (haccepted : PartialToStrengthenedAcceptedProjection) :
    PartialConsistencyLowerBoundNormalForm :=
  h.toNormalFormOfProjection
    (strengthened_to_partial_projection_of_accepted_projection_principle
      hprinciple haccepted)

def LiteraturePudlakTheorem5LowerBoundCertificate.toNormalFormOfAcceptedProjectionPackage
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpackage : StrengthenedToPartialAcceptedProjectionPackage) :
    PartialConsistencyLowerBoundNormalForm :=
  h.toNormalFormOfProjection hpackage.toProjection

def LiteraturePudlakTheorem5LowerBoundCertificate.toNormalFormOfLinearProjection
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyLinearProjection) :
    PartialConsistencyLowerBoundNormalForm :=
  h.toStandardInstance.toNormalFormOfLinearProjection hpartial

def LiteraturePudlakTheorem5LowerBoundCertificate.toNormalFormOfConstantProjection
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyConstantProjection) :
    PartialConsistencyLowerBoundNormalForm :=
  h.toStandardInstance.toNormalFormOfConstantProjection hpartial

theorem LiteraturePudlakTheorem5LowerBoundCertificate.normalForm_code_eq_powerBoundRawCode
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    (h.toNormalForm hpartial).code = h.scale_data.powerBoundRawCode := by
  exact h.scale_data.normalForm_code_eq_powerBoundRawCode
    h.rescaled_strong_lower_bound hpartial

theorem LiteraturePudlakTheorem5LowerBoundCertificate.normalForm_code_eq_rescaledPudlak
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (n : ℕ) :
    (h.toNormalForm hpartial).code n =
      rescaledPudlakStrengthenedFiniteConsistencyCode h.scale_data.scale n := by
  rw [h.normalForm_code_eq_powerBoundRawCode hpartial]
  exact h.scale_data.powerBoundRawCode_eq_rescaledPudlak n

/-- Short audit package: converting a theorem-5 power-bound certificate to the
rescaled certificate and back preserves the scale data and the audited raw code.
This is only a conjunction of existing field-level round-trip lemmas. -/
theorem audit_theorem5_powerBound_certificateRoundTrip
    (h : LiteraturePudlakTheorem5LowerBoundCertificate) :
    h.toRescaledCertificate.toPowerBoundCertificate.scale_data = h.scale_data ∧
      (∀ n : ℕ,
        h.toRescaledCertificate.toPowerBoundCertificate.scale_data.powerBoundRawCode n =
          h.scale_data.powerBoundRawCode n) := by
  exact ⟨h.toRescaled_toPowerBound_scale_data,
    fun n => h.toRescaled_toPowerBound_powerBoundRawCode n⟩

/-- Short audit package: converting a theorem-5 rescaled certificate to the
power-bound certificate and back preserves the scale data and the audited raw
code. -/
theorem audit_theorem5_rescaled_certificateRoundTrip
    (h : LiteraturePudlakTheorem5RescaledLowerBoundCertificate) :
    h.toPowerBoundCertificate.toRescaledCertificate.scale_data = h.scale_data ∧
      (∀ n : ℕ,
        h.toPowerBoundCertificate.toRescaledCertificate.scale_data.rescaledRawCode n =
          h.scale_data.rescaledRawCode n) := by
  exact ⟨h.toPowerBound_toRescaled_scale_data,
    fun n => h.toPowerBound_toRescaled_rescaledRawCode n⟩

/-- Short audit equivalence: the theorem-5 power-bound certificate and rescaled
certificate presentations are mutually available. -/
theorem audit_theorem5_certificatePresentation_iff_rescaledPresentation :
    Nonempty LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty LiteraturePudlakTheorem5RescaledLowerBoundCertificate :=
  literaturePudlakTheorem5Certificate_nonempty_iff_rescaledCertificate

set_option linter.style.longLine false in
theorem LiteraturePudlakTheorem5RescaledLowerBoundCertificate.toPowerBound_normalForm_code_eq_rescaledPudlak
    (h : LiteraturePudlakTheorem5RescaledLowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (n : ℕ) :
    (h.toPowerBoundCertificate.toNormalForm hpartial).code n =
      rescaledPudlakStrengthenedFiniteConsistencyCode h.scale_data.scale n :=
  h.toPowerBoundCertificate.normalForm_code_eq_rescaledPudlak hpartial n

set_option linter.style.longLine false in
theorem LiteraturePudlakTheorem5LowerBoundCertificate.toRescaled_toPowerBound_normalForm_code_eq_rescaledPudlak
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (n : ℕ) :
    (h.toRescaledCertificate.toPowerBoundCertificate.toNormalForm
        hpartial).code n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        h.scale_data.scale n :=
  h.toRescaledCertificate.toPowerBoundCertificate
    |>.normalForm_code_eq_rescaledPudlak hpartial n

set_option linter.style.longLine false in
theorem LiteraturePudlakTheorem5RescaledLowerBoundCertificate.toPowerBound_toRescaled_normalForm_code_eq_rescaledPudlak
    (h : LiteraturePudlakTheorem5RescaledLowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (n : ℕ) :
    (h.toPowerBoundCertificate.toRescaledCertificate.toPowerBoundCertificate
        |>.toNormalForm hpartial).code n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        h.scale_data.scale n :=
  h.toPowerBoundCertificate.toRescaledCertificate.toPowerBoundCertificate
    |>.normalForm_code_eq_rescaledPudlak hpartial n
