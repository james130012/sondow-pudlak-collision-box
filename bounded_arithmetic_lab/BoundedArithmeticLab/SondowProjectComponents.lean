/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.SondowStructuredCertificate

/-!
# Project Sondow component formulas and codes

This file fixes the audit-facing project formulas for the five Sondow
components.  The component formulas are concrete `BAFormula.atom`s, and the
right-nested conjunction used by `SondowComponentFormulas.target` is coded as
the project `sondowReflectionGraftCode`.

The final section is the narrow bridge from exported main-library component
proof objects into `SondowComponentSizeCertificatesEventually`.  It does not
turn analytic Lean theorems into bounded-arithmetic proofs by fiat; the export
package explicitly supplies the component `BAProofObject`s, their conclusions,
and their size bounds.
-/

namespace BoundedArithmeticLab

def projectComponentAtom (family : FormulaFamily) (n : ℕ) : BAFormula :=
  BAFormula.atom family n

def sondowProductFormula (n : ℕ) : BAFormula :=
  projectComponentAtom FormulaFamily.sondowProduct n

def sondowLogRelationFormula (n : ℕ) : BAFormula :=
  projectComponentAtom FormulaFamily.sondowLogRelation n

def sondowDecompositionFormula (n : ℕ) : BAFormula :=
  projectComponentAtom FormulaFamily.sondowDecomposition n

def sondowThreePowFormula (n : ℕ) : BAFormula :=
  projectComponentAtom FormulaFamily.sondowThreePow n

def sondowPayloadFormula (n : ℕ) : BAFormula :=
  projectComponentAtom FormulaFamily.sondowPayload n

def sondowProjectComponentFormulas : SondowComponentFormulas where
  product := sondowProductFormula
  logRelation := sondowLogRelationFormula
  decomposition := sondowDecompositionFormula
  threePow := sondowThreePowFormula
  payload := sondowPayloadFormula

def unknownProjectFormulaCode : FormulaCode :=
  externalPudlakCode 0

def sondowProjectComponentCode (φ : BAFormula) : FormulaCode :=
  match φ with
  | BAFormula.atom FormulaFamily.sondowProduct n => sondowProductCode n
  | BAFormula.atom FormulaFamily.sondowLogRelation n => sondowLogRelationCode n
  | BAFormula.atom FormulaFamily.sondowDecomposition n => sondowDecompositionCode n
  | BAFormula.atom FormulaFamily.sondowThreePow n => sondowThreePowCode n
  | BAFormula.atom FormulaFamily.sondowPayload n => sondowPayloadCode n
  | BAFormula.and (BAFormula.atom FormulaFamily.sondowProduct nProduct)
      (BAFormula.and (BAFormula.atom FormulaFamily.sondowLogRelation nLog)
        (BAFormula.and (BAFormula.atom FormulaFamily.sondowDecomposition nDecomp)
          (BAFormula.and (BAFormula.atom FormulaFamily.sondowThreePow nThree)
            (BAFormula.atom FormulaFamily.sondowPayload nPayload)))) =>
      if _ : nProduct = nLog ∧ nProduct = nDecomp ∧
          nProduct = nThree ∧ nProduct = nPayload then
        sondowReflectionGraftCode nProduct
      else
        unknownProjectFormulaCode
  | _ => unknownProjectFormulaCode

@[simp] theorem sondowProjectComponentCode_product (n : ℕ) :
    sondowProjectComponentCode (sondowProductFormula n) =
      sondowProductCode n := by
  rfl

@[simp] theorem sondowProjectComponentCode_logRelation (n : ℕ) :
    sondowProjectComponentCode (sondowLogRelationFormula n) =
      sondowLogRelationCode n := by
  rfl

@[simp] theorem sondowProjectComponentCode_decomposition (n : ℕ) :
    sondowProjectComponentCode (sondowDecompositionFormula n) =
      sondowDecompositionCode n := by
  rfl

@[simp] theorem sondowProjectComponentCode_threePow (n : ℕ) :
    sondowProjectComponentCode (sondowThreePowFormula n) =
      sondowThreePowCode n := by
  rfl

@[simp] theorem sondowProjectComponentCode_payload (n : ℕ) :
    sondowProjectComponentCode (sondowPayloadFormula n) =
      sondowPayloadCode n := by
  rfl

@[simp] theorem sondowProjectComponentCode_target (n : ℕ) :
    sondowProjectComponentCode (sondowProjectComponentFormulas.target n) =
      sondowReflectionGraftCode n := by
  simp [sondowProjectComponentCode, SondowComponentFormulas.target,
    sondowProjectComponentFormulas, sondowProductFormula,
    sondowLogRelationFormula, sondowDecompositionFormula,
    sondowThreePowFormula, sondowPayloadFormula, projectComponentAtom]

structure SondowProjectComponentFormulaCodeAlignment
    (components : SondowComponentFormulas) (code : BAFormula → FormulaCode) :
    Prop where
  product_formula_eq :
    ∀ n : ℕ, components.product n = sondowProductFormula n
  logRelation_formula_eq :
    ∀ n : ℕ, components.logRelation n = sondowLogRelationFormula n
  decomposition_formula_eq :
    ∀ n : ℕ, components.decomposition n = sondowDecompositionFormula n
  threePow_formula_eq :
    ∀ n : ℕ, components.threePow n = sondowThreePowFormula n
  payload_formula_eq :
    ∀ n : ℕ, components.payload n = sondowPayloadFormula n
  product_code_eq :
    ∀ n : ℕ, code (components.product n) = sondowProductCode n
  logRelation_code_eq :
    ∀ n : ℕ, code (components.logRelation n) = sondowLogRelationCode n
  decomposition_code_eq :
    ∀ n : ℕ, code (components.decomposition n) = sondowDecompositionCode n
  threePow_code_eq :
    ∀ n : ℕ, code (components.threePow n) = sondowThreePowCode n
  payload_code_eq :
    ∀ n : ℕ, code (components.payload n) = sondowPayloadCode n
  target_code_eq :
    ∀ n : ℕ, code (components.target n) = sondowReflectionGraftCode n

theorem sondowProjectComponentFormulaCodeAlignment :
    SondowProjectComponentFormulaCodeAlignment
      sondowProjectComponentFormulas sondowProjectComponentCode where
  product_formula_eq := by
    intro n
    rfl
  logRelation_formula_eq := by
    intro n
    rfl
  decomposition_formula_eq := by
    intro n
    rfl
  threePow_formula_eq := by
    intro n
    rfl
  payload_formula_eq := by
    intro n
    rfl
  product_code_eq := by
    intro n
    rfl
  logRelation_code_eq := by
    intro n
    rfl
  decomposition_code_eq := by
    intro n
    rfl
  threePow_code_eq := by
    intro n
    rfl
  payload_code_eq := by
    intro n
    rfl
  target_code_eq := by
    intro n
    simp

structure SondowProductLogBlockCertificate where
  productProof : BAProofObject BussS21Axiom
  logProof : BAProofObject BussS21Axiom

structure SondowMainReproofBlockCertificatesEventually
    (components : SondowComponentFormulas) (bounds : SondowComponentBounds) where
  threshold : ℕ
  productLog :
    ∀ n : ℕ, threshold ≤ n → SondowProductLogBlockCertificate
  decompositionProof :
    ∀ n : ℕ, threshold ≤ n → BAProofObject BussS21Axiom
  threePowProof :
    ∀ n : ℕ, threshold ≤ n → BAProofObject BussS21Axiom
  payloadProof :
    ∀ n : ℕ, threshold ≤ n → BAProofObject BussS21Axiom
  product_conclusion :
    ∀ n : ℕ, ∀ hn : threshold ≤ n,
      (productLog n hn).productProof.conclusion = components.product n
  log_conclusion :
    ∀ n : ℕ, ∀ hn : threshold ≤ n,
      (productLog n hn).logProof.conclusion = components.logRelation n
  decomposition_conclusion :
    ∀ n : ℕ, ∀ hn : threshold ≤ n,
      (decompositionProof n hn).conclusion = components.decomposition n
  threePow_conclusion :
    ∀ n : ℕ, ∀ hn : threshold ≤ n,
      (threePowProof n hn).conclusion = components.threePow n
  payload_conclusion :
    ∀ n : ℕ, ∀ hn : threshold ≤ n,
      (payloadProof n hn).conclusion = components.payload n
  product_size_le :
    ∀ n : ℕ, ∀ hn : threshold ≤ n,
      ((productLog n hn).productProof.size : ℝ) ≤ bounds.product n
  log_size_le :
    ∀ n : ℕ, ∀ hn : threshold ≤ n,
      ((productLog n hn).logProof.size : ℝ) ≤ bounds.logRelation n
  decomposition_size_le :
    ∀ n : ℕ, ∀ hn : threshold ≤ n,
      ((decompositionProof n hn).size : ℝ) ≤ bounds.decomposition n
  threePow_size_le :
    ∀ n : ℕ, ∀ hn : threshold ≤ n,
      ((threePowProof n hn).size : ℝ) ≤ bounds.threePow n
  payload_size_le :
    ∀ n : ℕ, ∀ hn : threshold ≤ n,
      ((payloadProof n hn).size : ℝ) ≤ bounds.payload n

namespace SondowMainReproofBlockCertificatesEventually

def toComponentCertificate
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    (h : SondowMainReproofBlockCertificatesEventually components bounds)
    (n : ℕ) (hn : h.threshold ≤ n) :
    SondowComponentCertificate where
  productProof := (h.productLog n hn).productProof
  logProof := (h.productLog n hn).logProof
  decompositionProof := h.decompositionProof n hn
  threePowProof := h.threePowProof n hn
  payloadProof := h.payloadProof n hn

theorem toComponentCertificate_valid
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    (h : SondowMainReproofBlockCertificatesEventually components bounds)
    (n : ℕ) (hn : h.threshold ≤ n) :
    SondowComponentCertificate.ComponentSizeValid components bounds n
      (h.toComponentCertificate n hn) where
  product_conclusion := h.product_conclusion n hn
  log_conclusion := h.log_conclusion n hn
  decomposition_conclusion := h.decomposition_conclusion n hn
  threePow_conclusion := h.threePow_conclusion n hn
  payload_conclusion := h.payload_conclusion n hn
  product_size_le := h.product_size_le n hn
  log_size_le := h.log_size_le n hn
  decomposition_size_le := h.decomposition_size_le n hn
  threePow_size_le := h.threePow_size_le n hn
  payload_size_le := h.payload_size_le n hn

def toSondowComponentSizeCertificatesEventually
    {components : SondowComponentFormulas} {bounds : SondowComponentBounds}
    (h : SondowMainReproofBlockCertificatesEventually components bounds) :
    SondowComponentSizeCertificatesEventually components bounds where
  exists_eventually := by
    refine ⟨h.threshold, ?_⟩
    intro n hn
    exact ⟨h.toComponentCertificate n hn,
      h.toComponentCertificate_valid n hn⟩

end SondowMainReproofBlockCertificatesEventually

abbrev SondowProjectComponentSizeCertificatesEventually
    (bounds : SondowComponentBounds) : Prop :=
  SondowComponentSizeCertificatesEventually sondowProjectComponentFormulas bounds

def SondowMainReproofBlockCertificatesEventually.toProjectComponentSizeCertificatesEventually
    {bounds : SondowComponentBounds}
    (h :
      SondowMainReproofBlockCertificatesEventually
        sondowProjectComponentFormulas bounds) :
    SondowProjectComponentSizeCertificatesEventually bounds :=
  h.toSondowComponentSizeCertificatesEventually

theorem collision_of_project_sondow_component_exports_formula_length_calibrated_pudlak
    {bounds : SondowComponentBounds}
    (hcerts :
      SondowMainReproofBlockCertificatesEventually
        sondowProjectComponentFormulas bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    False :=
  collision_of_sondow_component_size_certificates_formula_length_calibrated_pudlak
    hcerts.toProjectComponentSizeCertificatesEventually calibration

end BoundedArithmeticLab
