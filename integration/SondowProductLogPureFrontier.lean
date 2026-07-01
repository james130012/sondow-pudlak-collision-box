/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowPureFrontierCommon

open BoundedArithmeticLab

namespace SondowMainCheckedCodeBridge
/-!
### Product/log arithmetic pure fragments

These formulas are not the full real-log arithmetization.  They isolate the two
finite arithmetic fragments that can already be represented by atom-free
`BAFormula` syntax: denominator cancellation and the finite exponent-table
compression from the nested product to the grouped product.
-/

def productLogIVar : ℕ := 6100

def productLogJVar : ℕ := 6101

def productLogQuotVar : ℕ := 6102

def productLogDenominatorTargetName : ℕ := 6103

def productLogExponentTableTargetName : ℕ := 6104

def productLogDoubleScale (n : ℕ) : ℕ :=
  2 * _root_.d (2 * n)

def productLogDoubleScaleTerm (n : ℕ) : BATerm :=
  productLogBaNatLiteral (productLogDoubleScale n)

def productLogDenominatorRangeFormula (n : ℕ) : BAFormula :=
  BAFormula.and
    (BAFormula.le
      (BATerm.succ (BATerm.var productLogIVar))
      (BATerm.var productLogJVar))
    (BAFormula.le
      (BATerm.add (BATerm.var productLogIVar)
        (BATerm.var productLogJVar))
      (productLogBaNatLiteral n))

def productLogDividesDoubleScaleFormula (n : ℕ) : BAFormula :=
  BAFormula.existsBounded productLogQuotVar (productLogDoubleScaleTerm n)
    (BAFormula.equal
      (BATerm.mul (BATerm.var productLogJVar)
        (BATerm.var productLogQuotVar))
      (productLogDoubleScaleTerm n))

def productLogDenominatorCancellationFormula (n : ℕ) : BAFormula :=
  BAFormula.forallBounded productLogIVar (productLogBaNatLiteral n)
    (BAFormula.forallBounded productLogJVar (productLogBaNatLiteral n)
      (BAFormula.imp (productLogDenominatorRangeFormula n)
        (productLogDividesDoubleScaleFormula n)))

def productLogDenominatorCancellationTargetFormula (n : ℕ) : BAFormula :=
  polytimeDefinabilityFormula productLogDenominatorTargetName
    (productLogDenominatorCancellationFormula n)

def productLogExponentTableFormula (n : ℕ) : BAFormula :=
  BAFormula.equal
    (productLogBaNatLiteral
      (EulerLimit.SondowProductLog.nestedSondowProductNormalized
        (_root_.d (2 * n)) n))
    (productLogBaNatLiteral
      (EulerLimit.SondowProductLog.sondowProductNormalized
        (_root_.d (2 * n)) n))

def productLogExponentTableTargetFormula (n : ℕ) : BAFormula :=
  polytimeDefinabilityFormula productLogExponentTableTargetName
    (productLogExponentTableFormula n)

def productLogArithmeticTargetFormula (n : ℕ) : BAFormula :=
  BAFormula.and (productLogDenominatorCancellationTargetFormula n)
    (productLogExponentTableTargetFormula n)

theorem productLogDenominatorRange_mem_Icc_iff
    {n i j : ℕ} :
    (i + 1 ≤ j ∧ i + j ≤ n) ↔
      j ∈ Finset.Icc (i + 1) (n - i) := by
  constructor
  · intro h
    exact Finset.mem_Icc.mpr ⟨h.1, by omega⟩
  · intro h
    have hbounds := Finset.mem_Icc.mp h
    omega

theorem productLogDenominatorRangeFormula_eval_iff
    (n : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (productLogDenominatorRangeFormula n) ↔
      env productLogIVar + 1 ≤ env productLogJVar ∧
        env productLogIVar + env productLogJVar ≤ n := by
  simp [productLogDecompositionFormulaEval,
    productLogDecompositionBaFormulaEval,
    productLogDecompositionBaTermEval,
    productLogDenominatorRangeFormula]

theorem productLogDoubleScale_pos (n : ℕ) :
    0 < productLogDoubleScale n := by
  unfold productLogDoubleScale
  exact Nat.mul_pos (by norm_num) (_root_.d_pos (2 * n))

theorem productLogDividesDoubleScaleFormula_eval_iff
    (n : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (productLogDividesDoubleScaleFormula n) ↔
      env productLogJVar ∣ productLogDoubleScale n := by
  constructor
  · intro h
    rcases h with ⟨q, _hqBound, hmul⟩
    refine ⟨q, ?_⟩
    simpa [productLogDecompositionFormulaEval,
      productLogDecompositionBaFormulaEval,
      productLogDecompositionBaTermEval,
      productLogDividesDoubleScaleFormula, productLogDoubleScaleTerm,
      productLogQuotVar, productLogJVar, Function.update] using hmul.symm
  · intro hdvd
    rcases hdvd with ⟨q, hq⟩
    refine ⟨q, ?_, ?_⟩
    · have hscale_pos := productLogDoubleScale_pos n
      by_cases hj : env productLogJVar = 0
      · have hzero : productLogDoubleScale n = 0 := by
          simpa [hj] using hq
        omega
      · have hjpos : 1 ≤ env productLogJVar :=
          Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj)
        have hqle_mul : q ≤ env productLogJVar * q := by
          nlinarith [Nat.mul_le_mul_right q hjpos]
        have hqle : q ≤ productLogDoubleScale n := by
          nlinarith [hqle_mul, hq]
        simpa [productLogDecompositionFormulaEval,
          productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval,
          productLogDividesDoubleScaleFormula, productLogDoubleScaleTerm,
          productLogQuotVar, Function.update] using hqle
    · simpa [productLogDecompositionFormulaEval,
        productLogDecompositionBaFormulaEval,
        productLogDecompositionBaTermEval,
        productLogDividesDoubleScaleFormula, productLogDoubleScaleTerm,
        productLogQuotVar, productLogJVar, Function.update] using hq.symm

theorem productLogDenominatorCancellationFormula_atomFree
    (n : ℕ) :
    productLogDecompositionAtomFree
      (productLogDenominatorCancellationFormula n) := by
  simp [productLogDecompositionAtomFree,
    productLogDenominatorCancellationFormula,
    productLogDenominatorRangeFormula,
    productLogDividesDoubleScaleFormula,
    productLogDecompositionBaFormulaAtomFree]

theorem productLogDenominatorCancellationTargetFormula_atomFree
    (n : ℕ) :
    productLogDecompositionAtomFree
      (productLogDenominatorCancellationTargetFormula n) := by
  simp [productLogDenominatorCancellationTargetFormula,
    polytimeDefinabilityFormula,
    productLogDecompositionAtomFree,
    productLogDenominatorCancellationFormula,
    productLogDenominatorRangeFormula,
    productLogDividesDoubleScaleFormula,
    productLogDecompositionBaFormulaAtomFree]

theorem productLogDenominatorCancellationFormula_eval_iff
    (n : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (productLogDenominatorCancellationFormula n) ↔
      EulerLimit.SondowProductLog.denominatorCancelsFor
        (_root_.d (2 * n)) n := by
  constructor
  · intro h i j hj
    have hi_le : i ≤ n := by
      have hbounds := Finset.mem_Icc.mp hj
      omega
    have hj_le : j ≤ n := by
      have hbounds := Finset.mem_Icc.mp hj
      omega
    have hbody :=
      h i (by simpa using hi_le) j (by simpa using hj_le)
    have hrange :
        productLogDecompositionFormulaEval
          (Function.update (Function.update env productLogIVar i)
            productLogJVar j)
          (productLogDenominatorRangeFormula n) := by
      rw [productLogDenominatorRangeFormula_eval_iff]
      have hiff :
          (i + 1 ≤ j ∧ i + j ≤ n) ↔
            j ∈ Finset.Icc (i + 1) (n - i) :=
        productLogDenominatorRange_mem_Icc_iff
      exact hiff.2 hj
    have hdivFormula := hbody hrange
    have hdvd :
        j ∣ productLogDoubleScale n := by
      have hdiv :=
        (productLogDividesDoubleScaleFormula_eval_iff n
          (Function.update (Function.update env productLogIVar i)
            productLogJVar j)).1 hdivFormula
      simpa [productLogJVar, Function.update] using hdiv
    simpa [productLogDoubleScale] using Nat.mul_div_cancel' hdvd
  · intro h i hi j hj hrange
    have hrange' :
        i + 1 ≤ j ∧ i + j ≤ n := by
      simpa [productLogIVar, productLogJVar, Function.update]
        using
          (productLogDenominatorRangeFormula_eval_iff n
            (Function.update (Function.update env productLogIVar i)
              productLogJVar j)).1 hrange
    have hjMem : j ∈ Finset.Icc (i + 1) (n - i) :=
      productLogDenominatorRange_mem_Icc_iff.1 hrange'
    have hcancel := h hjMem
    have hdvd : j ∣ productLogDoubleScale n := by
      refine ⟨(2 * _root_.d (2 * n)) / j, ?_⟩
      simpa [productLogDoubleScale] using hcancel.symm
    have hdiv :
        productLogDecompositionFormulaEval
          (Function.update (Function.update env productLogIVar i)
            productLogJVar j)
          (productLogDividesDoubleScaleFormula n) :=
      (productLogDividesDoubleScaleFormula_eval_iff n
        (Function.update (Function.update env productLogIVar i)
          productLogJVar j)).2
        (by simpa [productLogJVar, Function.update] using hdvd)
    exact hdiv

theorem productLogDenominatorCancellationTargetFormula_eval_iff
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogDenominatorCancellationTargetFormula n) ↔
      EulerLimit.SondowProductLog.denominatorCancelsFor
        (_root_.d (2 * n)) n := by
  constructor
  · intro h
    rcases h with ⟨value, _hvalue, hbody⟩
    exact
      (productLogDenominatorCancellationFormula_eval_iff n
        (Function.update (fun _idx => n)
          productLogDenominatorTargetName value)).1 hbody
  · intro h
    refine ⟨0, ?_, ?_⟩
    · simp [productLogDecompositionBaTermEval]
    · exact
        (productLogDenominatorCancellationFormula_eval_iff n
          (Function.update (fun _idx => n)
            productLogDenominatorTargetName 0)).2 h

theorem productLogExponentTableFormula_atomFree
    (n : ℕ) :
    productLogDecompositionAtomFree
      (productLogExponentTableFormula n) := by
  simp [productLogExponentTableFormula, productLogDecompositionAtomFree,
    productLogDecompositionBaFormulaAtomFree]

theorem productLogExponentTableTargetFormula_atomFree
    (n : ℕ) :
    productLogDecompositionAtomFree
      (productLogExponentTableTargetFormula n) := by
  simp [productLogExponentTableTargetFormula, polytimeDefinabilityFormula,
    productLogExponentTableFormula, productLogDecompositionAtomFree,
    productLogDecompositionBaFormulaAtomFree]

theorem productLogExponentTableFormula_eval_iff
    (n : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (productLogExponentTableFormula n) ↔
      EulerLimit.SondowProductLog.nestedSondowProductNormalized
          (_root_.d (2 * n)) n =
        EulerLimit.SondowProductLog.sondowProductNormalized
          (_root_.d (2 * n)) n := by
  simp [productLogDecompositionFormulaEval,
    productLogDecompositionBaFormulaEval,
    productLogExponentTableFormula]

theorem productLogExponentTableTargetFormula_eval_iff
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogExponentTableTargetFormula n) ↔
      EulerLimit.SondowProductLog.nestedSondowProductNormalized
          (_root_.d (2 * n)) n =
        EulerLimit.SondowProductLog.sondowProductNormalized
          (_root_.d (2 * n)) n := by
  constructor
  · intro h
    rcases h with ⟨value, _hvalue, hbody⟩
    exact
      (productLogExponentTableFormula_eval_iff n
        (Function.update (fun _idx => n)
          productLogExponentTableTargetName value)).1 hbody
  · intro h
    refine ⟨0, ?_, ?_⟩
    · simp [productLogDecompositionBaTermEval]
    · exact
        (productLogExponentTableFormula_eval_iff n
          (Function.update (fun _idx => n)
            productLogExponentTableTargetName 0)).2 h

theorem productLogDenominatorCancellationTargetFormula_eval_iff_env
    (n : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (productLogDenominatorCancellationTargetFormula n) ↔
      EulerLimit.SondowProductLog.denominatorCancelsFor
        (_root_.d (2 * n)) n := by
  constructor
  · intro h
    rcases h with ⟨value, _hvalue, hbody⟩
    exact
      (productLogDenominatorCancellationFormula_eval_iff n
        (Function.update env productLogDenominatorTargetName value)).1
        hbody
  · intro h
    refine ⟨0, ?_, ?_⟩
    · simp [productLogDecompositionBaTermEval]
    · exact
        (productLogDenominatorCancellationFormula_eval_iff n
          (Function.update env productLogDenominatorTargetName 0)).2 h

theorem productLogExponentTableTargetFormula_eval_iff_env
    (n : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (productLogExponentTableTargetFormula n) ↔
      EulerLimit.SondowProductLog.nestedSondowProductNormalized
          (_root_.d (2 * n)) n =
        EulerLimit.SondowProductLog.sondowProductNormalized
          (_root_.d (2 * n)) n := by
  constructor
  · intro h
    rcases h with ⟨value, _hvalue, hbody⟩
    exact
      (productLogExponentTableFormula_eval_iff n
        (Function.update env productLogExponentTableTargetName value)).1
        hbody
  · intro h
    refine ⟨0, ?_, ?_⟩
    · simp [productLogDecompositionBaTermEval]
    · exact
        (productLogExponentTableFormula_eval_iff n
          (Function.update env productLogExponentTableTargetName 0)).2 h

theorem productLogExponentTableTargetFormula_eval_complete
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogExponentTableTargetFormula n) := by
  exact
    (productLogExponentTableTargetFormula_eval_iff n).2
      (EulerLimit.SondowProductLog.nestedSondowProductNormalized_eq_sondowProductNormalized
        (_root_.d (2 * n)) n)

theorem productLogArithmeticTargetFormula_atomFree
    (n : ℕ) :
    productLogDecompositionAtomFree
      (productLogArithmeticTargetFormula n) := by
  exact
    ⟨productLogDenominatorCancellationTargetFormula_atomFree n,
      productLogExponentTableTargetFormula_atomFree n⟩

theorem productLogArithmeticTargetFormula_eval_iff
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogArithmeticTargetFormula n) ↔
      EulerLimit.SondowProductLog.denominatorCancelsFor
          (_root_.d (2 * n)) n ∧
        EulerLimit.SondowProductLog.nestedSondowProductNormalized
            (_root_.d (2 * n)) n =
          EulerLimit.SondowProductLog.sondowProductNormalized
            (_root_.d (2 * n)) n := by
  simp [productLogArithmeticTargetFormula,
    productLogDecompositionFormulaEval,
    productLogDecompositionBaFormulaEval,
    productLogDenominatorCancellationTargetFormula_eval_iff,
    productLogExponentTableTargetFormula_eval_iff]

def productLogDenominatorCancellationProofObject
    (n : ℕ) : BAProofObject BussS21Axiom :=
  productLogDecompositionPolytimeDefinabilityProofObject productLogDenominatorTargetName
    (productLogDenominatorCancellationFormula n)

def productLogExponentTableProofObject
    (n : ℕ) : BAProofObject BussS21Axiom :=
  productLogDecompositionPolytimeDefinabilityProofObject productLogExponentTableTargetName
    (productLogExponentTableFormula n)

def productLogArithmeticProofObject
    (n : ℕ) : BAProofObject BussS21Axiom :=
  (productLogDenominatorCancellationProofObject n).andIntro
    (productLogExponentTableProofObject n)

theorem productLogArithmeticProofObject_conclusion
    (n : ℕ) :
    (productLogArithmeticProofObject n).conclusion =
      productLogArithmeticTargetFormula n := by
  rfl

theorem productLogArithmeticProofObject_size_plus_two_eq_five
    (n : ℕ) :
    ((((productLogArithmeticProofObject n).size + 2 : ℕ) : ℝ)) = 5 := by
  change (((1 + 1 + 1 + 2 : ℕ) : ℝ)) = 5
  norm_num

structure ProductLogArithmeticPureS21Assembly where
  target : ℕ → BAFormula
  target_eq :
    target = productLogArithmeticTargetFormula
  target_atomFree :
    ∀ n : ℕ, productLogDecompositionAtomFree (target n)
  target_eval_iff_arithmetic_fields :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n) (target n) ↔
        EulerLimit.SondowProductLog.denominatorCancelsFor
            (_root_.d (2 * n)) n ∧
          EulerLimit.SondowProductLog.nestedSondowProductNormalized
              (_root_.d (2 * n)) n =
            EulerLimit.SondowProductLog.sondowProductNormalized
              (_root_.d (2 * n)) n
  proofObject : ℕ → BAProofObject BussS21Axiom
  proofObject_conclusion :
    ∀ n : ℕ, (proofObject n).conclusion = target n
  proofObject_size_plus_two_eq_five :
    ∀ n : ℕ, ((((proofObject n).size + 2 : ℕ) : ℝ)) = 5

def productLogArithmeticPureS21Assembly :
    ProductLogArithmeticPureS21Assembly where
  target := productLogArithmeticTargetFormula
  target_eq := rfl
  target_atomFree := productLogArithmeticTargetFormula_atomFree
  target_eval_iff_arithmetic_fields :=
    productLogArithmeticTargetFormula_eval_iff
  proofObject := productLogArithmeticProofObject
  proofObject_conclusion :=
    productLogArithmeticProofObject_conclusion
  proofObject_size_plus_two_eq_five :=
    productLogArithmeticProofObject_size_plus_two_eq_five

/-- The finite product/log arithmetic fields directly checked by the current
atom-free target.  The expanded source certificate below adds the analytic
completion fields, but its denominator field is exactly this first component. -/
def ProductLogArithmeticFields (n : ℕ) : Prop :=
  EulerLimit.SondowProductLog.denominatorCancelsFor
      (_root_.d (2 * n)) n ∧
    EulerLimit.SondowProductLog.nestedSondowProductNormalized
        (_root_.d (2 * n)) n =
      EulerLimit.SondowProductLog.sondowProductNormalized
        (_root_.d (2 * n)) n

theorem productLogArithmeticTargetFormula_eval_iff_arithmeticFields
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogArithmeticTargetFormula n) ↔
      ProductLogArithmeticFields n := by
  simpa [ProductLogArithmeticFields] using
    productLogArithmeticTargetFormula_eval_iff n

theorem productLogArithmeticTargetFormula_eval_iff_arithmeticFields_env
    (n : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (productLogArithmeticTargetFormula n) ↔
      ProductLogArithmeticFields n := by
  simp [productLogArithmeticTargetFormula, ProductLogArithmeticFields,
    productLogDecompositionFormulaEval, productLogDecompositionBaFormulaEval,
    productLogDenominatorCancellationTargetFormula_eval_iff_env,
    productLogExponentTableTargetFormula_eval_iff_env]

/-- Product/log source certificate split along the actual main-library proof:
finite nested product shape, denominator cancellation, log-product expansion,
and the raw-log-sum calibration to Sondow's `L_n`. -/
structure ProductLogExpandedSourceCertificate (n : ℕ) : Prop where
  denominatorCancels :
    EulerLimit.SondowProductLog.denominatorCancelsFor
      (_root_.d (2 * n)) n
  logExpansion :
    Real.log
        (EulerLimit.SondowProductLog.nestedSondowProductNormalized
          (_root_.d (2 * n)) n : ℝ) =
      (_root_.d (2 * n) : ℝ) *
        EulerLimit.SondowProductLog.rawLLogSum n
  productShape :
    EulerLimit.SondowProductLog.nestedSondowProductNormalized
      (_root_.d (2 * n)) n =
        _root_.sondow_S_explicit n
  rawLogShape :
    EulerLimit.SondowProductLog.rawLLogSum n = _root_.sondow_L n

namespace ProductLogExpandedSourceCertificate

def ofArithmeticFields {n : ℕ}
    (fields : ProductLogArithmeticFields n) :
    ProductLogExpandedSourceCertificate n where
  denominatorCancels := fields.1
  logExpansion :=
    EulerLimit.SondowProductLog.log_nestedSondowProductNormalized_eq_scale_rawLLogSum
      (scale := _root_.d (2 * n)) (n := n) fields.1
  productShape :=
    _root_.nestedSondowProductNormalized_d_eq_sondow_S_explicit n
  rawLogShape := _root_.rawLLogSum_eq_sondow_L n

def ofMainLibrary (n : ℕ) :
    ProductLogExpandedSourceCertificate n :=
  ofArithmeticFields
    ⟨_root_.denominatorCancelsFor_d_two_mul n,
      EulerLimit.SondowProductLog.nestedSondowProductNormalized_eq_sondowProductNormalized
        (_root_.d (2 * n)) n⟩

theorem arithmeticFields_of_certificate
    {n : ℕ} (cert : ProductLogExpandedSourceCertificate n) :
    ProductLogArithmeticFields n :=
  ⟨cert.denominatorCancels,
    EulerLimit.SondowProductLog.nestedSondowProductNormalized_eq_sondowProductNormalized
      (_root_.d (2 * n)) n⟩

theorem nonempty_iff_arithmeticFields (n : ℕ) :
    Nonempty (ProductLogExpandedSourceCertificate n) ↔
      ProductLogArithmeticFields n := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact cert.arithmeticFields_of_certificate
  · intro fields
    exact ⟨ofArithmeticFields fields⟩

theorem source_of_certificate
    {n : ℕ} (cert : ProductLogExpandedSourceCertificate n) :
    _root_.sondow_explicit_product_log_relation_prop n := by
  unfold _root_.sondow_explicit_product_log_relation_prop
  rw [← cert.productShape, ← cert.rawLogShape]
  exact cert.logExpansion

theorem nonempty_iff_source (n : ℕ) :
    Nonempty (ProductLogExpandedSourceCertificate n) ↔
      _root_.sondow_explicit_product_log_relation_prop n := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact cert.source_of_certificate
  · intro _hsource
    exact ⟨ofMainLibrary n⟩

theorem eventual :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty (ProductLogExpandedSourceCertificate n) := by
  exact ⟨0, fun n _hn => ⟨ofMainLibrary n⟩⟩

end ProductLogExpandedSourceCertificate

theorem productLogArithmeticTargetFormula_eval_iff_expanded_source_certificate
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogArithmeticTargetFormula n) ↔
      Nonempty (ProductLogExpandedSourceCertificate n) := by
  exact
    (productLogArithmeticTargetFormula_eval_iff_arithmeticFields n).trans
    (ProductLogExpandedSourceCertificate.nonempty_iff_arithmeticFields
      n).symm

theorem productLogArithmeticTargetFormula_eval_iff_source
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogArithmeticTargetFormula n) ↔
      _root_.sondow_explicit_product_log_relation_prop n :=
  (productLogArithmeticTargetFormula_eval_iff_expanded_source_certificate
    n).trans
    (ProductLogExpandedSourceCertificate.nonempty_iff_source n)

theorem productLogArithmeticPureS21Assembly_eval_iff_source_certificate
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogArithmeticPureS21Assembly.target n) ↔
      Nonempty (ProductLogExpandedSourceCertificate n) := by
  simpa [productLogArithmeticPureS21Assembly] using
    productLogArithmeticTargetFormula_eval_iff_expanded_source_certificate n

theorem productLogArithmeticPureS21Assembly_eval_iff_source
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogArithmeticPureS21Assembly.target n) ↔
      _root_.sondow_explicit_product_log_relation_prop n := by
  simpa [productLogArithmeticPureS21Assembly] using
    productLogArithmeticTargetFormula_eval_iff_source n

def productLogArithmeticBound (_n : ℕ) : ℝ :=
  5

theorem productLogArithmeticBound_poly :
    IsPolynomialBound productLogArithmeticBound := by
  unfold productLogArithmeticBound
  exact IsPolynomialBound.const (5 : ℝ)

/-- Audit record for the product/log completion route.  It keeps the finite
arithmetic target, the expanded source certificate, the source proposition, and
the proof object/size bound connected through explicit equivalences. -/
structure ProductLogCompletionAudit where
  bound : ℕ → ℝ
  bound_poly : IsPolynomialBound bound
  assembly : ProductLogArithmeticPureS21Assembly
  target_eq :
    assembly.target = productLogArithmeticTargetFormula
  target_atomFree :
    ∀ n : ℕ, productLogDecompositionAtomFree (assembly.target n)
  target_eval_iff_arithmeticFields :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (assembly.target n) ↔
        ProductLogArithmeticFields n
  expandedSource_iff_arithmeticFields :
    ∀ n : ℕ,
      Nonempty (ProductLogExpandedSourceCertificate n) ↔
        ProductLogArithmeticFields n
  target_eval_iff_source_certificate :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (assembly.target n) ↔
        Nonempty (ProductLogExpandedSourceCertificate n)
  target_eval_iff_source :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (assembly.target n) ↔
        _root_.sondow_explicit_product_log_relation_prop n
  compile :
    ∀ n : ℕ, Nonempty (ProductLogExpandedSourceCertificate n) →
      BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ n : ℕ,
      ∀ hsource : Nonempty (ProductLogExpandedSourceCertificate n),
        (compile n hsource).conclusion = assembly.target n
  compile_size_plus_two_le :
    ∀ n : ℕ,
      ∀ hsource : Nonempty (ProductLogExpandedSourceCertificate n),
        ((((compile n hsource).size + 2 : ℕ) : ℝ)) ≤ bound n

def productLogCompletionAudit : ProductLogCompletionAudit where
  bound := productLogArithmeticBound
  bound_poly := productLogArithmeticBound_poly
  assembly := productLogArithmeticPureS21Assembly
  target_eq := productLogArithmeticPureS21Assembly.target_eq
  target_atomFree := productLogArithmeticPureS21Assembly.target_atomFree
  target_eval_iff_arithmeticFields := by
    intro n
    simpa [productLogArithmeticPureS21Assembly] using
      productLogArithmeticTargetFormula_eval_iff_arithmeticFields n
  expandedSource_iff_arithmeticFields :=
    ProductLogExpandedSourceCertificate.nonempty_iff_arithmeticFields
  target_eval_iff_source_certificate :=
    productLogArithmeticPureS21Assembly_eval_iff_source_certificate
  target_eval_iff_source :=
    productLogArithmeticPureS21Assembly_eval_iff_source
  compile := by
    intro n _hsource
    exact productLogArithmeticProofObject n
  compile_conclusion := by
    intro n _hsource
    exact productLogArithmeticProofObject_conclusion n
  compile_size_plus_two_le := by
    intro n _hsource
    rw [productLogArithmeticProofObject_size_plus_two_eq_five]
    simp [productLogArithmeticBound]

def productLogProductPureTargetName : ℕ := 6105

def productLogLogRelationPureTargetName : ℕ := 6106

def productLogTaggedIndexFormula (n : ℕ) : BAFormula :=
  BAFormula.equal (productLogBaNatLiteral n) (productLogBaNatLiteral n)

def productLogTaggedBodyTargetFormula (targetName n : ℕ) : BAFormula :=
  polytimeDefinabilityFormula targetName (productLogArithmeticTargetFormula n)

def productLogProductPureTargetFormula (n : ℕ) : BAFormula :=
  BAFormula.and (productLogTaggedIndexFormula n)
    (productLogTaggedBodyTargetFormula productLogProductPureTargetName n)

def productLogLogRelationPureTargetFormula (n : ℕ) : BAFormula :=
  BAFormula.and (productLogTaggedIndexFormula n)
    (productLogTaggedBodyTargetFormula productLogLogRelationPureTargetName n)

def productLogNatLiteral? : BATerm → Option ℕ
  | BATerm.zero => some 0
  | BATerm.succ t => Option.map Nat.succ (productLogNatLiteral? t)
  | _ => none

@[simp] theorem productLogNatLiteral?_productLogBaNatLiteral
    (n : ℕ) :
    productLogNatLiteral? (productLogBaNatLiteral n) = some n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [productLogBaNatLiteral, productLogNatLiteral?, ih]

def productLogSeparatedTargetCode (φ : BAFormula) :
    BoundedArithmeticLab.FormulaCode :=
  match φ with
  | BAFormula.and (BAFormula.equal lhs rhs)
      (BAFormula.existsBounded targetName (BATerm.var boundName) _body) =>
      match productLogNatLiteral? lhs, productLogNatLiteral? rhs with
      | some n, some m =>
          if _h : n = m ∧ targetName = boundName then
            if targetName = productLogProductPureTargetName then
              sondowProductCode n
            else if targetName = productLogLogRelationPureTargetName then
              sondowLogRelationCode n
            else
              externalPudlakCode 0
          else
            externalPudlakCode 0
      | _, _ => externalPudlakCode 0
  | _ => externalPudlakCode 0

theorem productLogSeparatedTargetCode_product (n : ℕ) :
    productLogSeparatedTargetCode
        (productLogProductPureTargetFormula n) =
      sondowProductCode n := by
  simp [productLogSeparatedTargetCode, productLogProductPureTargetFormula,
    productLogTaggedIndexFormula, productLogTaggedBodyTargetFormula,
    polytimeDefinabilityFormula, productLogProductPureTargetName]

theorem productLogSeparatedTargetCode_logRelation (n : ℕ) :
    productLogSeparatedTargetCode
        (productLogLogRelationPureTargetFormula n) =
      sondowLogRelationCode n := by
  simp [productLogSeparatedTargetCode, productLogLogRelationPureTargetFormula,
    productLogTaggedIndexFormula, productLogTaggedBodyTargetFormula,
    polytimeDefinabilityFormula, productLogProductPureTargetName,
    productLogLogRelationPureTargetName]

theorem productLogTaggedIndexFormula_atomFree (n : ℕ) :
    productLogDecompositionAtomFree (productLogTaggedIndexFormula n) := by
  simp [productLogTaggedIndexFormula, productLogDecompositionAtomFree,
    productLogDecompositionBaFormulaAtomFree]

theorem productLogTaggedBodyTargetFormula_atomFree
    (targetName n : ℕ) :
    productLogDecompositionAtomFree
      (productLogTaggedBodyTargetFormula targetName n) := by
  simpa [productLogTaggedBodyTargetFormula, polytimeDefinabilityFormula,
    productLogDecompositionAtomFree, productLogDecompositionBaFormulaAtomFree]
    using productLogArithmeticTargetFormula_atomFree n

theorem productLogProductPureTargetFormula_atomFree (n : ℕ) :
    productLogDecompositionAtomFree
      (productLogProductPureTargetFormula n) := by
  exact
    ⟨productLogTaggedIndexFormula_atomFree n,
      productLogTaggedBodyTargetFormula_atomFree
        productLogProductPureTargetName n⟩

theorem productLogLogRelationPureTargetFormula_atomFree (n : ℕ) :
    productLogDecompositionAtomFree
      (productLogLogRelationPureTargetFormula n) := by
  exact
    ⟨productLogTaggedIndexFormula_atomFree n,
      productLogTaggedBodyTargetFormula_atomFree
        productLogLogRelationPureTargetName n⟩

theorem productLogTaggedIndexFormula_eval
    (n : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
      (productLogTaggedIndexFormula n) := by
  simp [productLogTaggedIndexFormula, productLogDecompositionFormulaEval,
    productLogDecompositionBaFormulaEval]

theorem productLogTaggedBodyTargetFormula_eval_iff_arithmeticFields
    (targetName n : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (productLogTaggedBodyTargetFormula targetName n) ↔
      ProductLogArithmeticFields n := by
  constructor
  · intro h
    rcases h with ⟨value, _hvalue, hbody⟩
    exact
      (productLogArithmeticTargetFormula_eval_iff_arithmeticFields_env
        n (Function.update env targetName value)).1 hbody
  · intro fields
    refine ⟨0, ?_, ?_⟩
    · simp [productLogDecompositionBaTermEval]
    · exact
        (productLogArithmeticTargetFormula_eval_iff_arithmeticFields_env
          n (Function.update env targetName 0)).2 fields

theorem productLogProductPureTargetFormula_eval_iff_arithmeticFields
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogProductPureTargetFormula n) ↔
      ProductLogArithmeticFields n := by
  constructor
  · intro h
    exact
      (productLogTaggedBodyTargetFormula_eval_iff_arithmeticFields
        productLogProductPureTargetName n (fun _idx => n)).1 h.2
  · intro fields
    exact
      ⟨productLogTaggedIndexFormula_eval n (fun _idx => n),
        (productLogTaggedBodyTargetFormula_eval_iff_arithmeticFields
          productLogProductPureTargetName n (fun _idx => n)).2 fields⟩

theorem productLogLogRelationPureTargetFormula_eval_iff_arithmeticFields
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogLogRelationPureTargetFormula n) ↔
      ProductLogArithmeticFields n := by
  constructor
  · intro h
    exact
      (productLogTaggedBodyTargetFormula_eval_iff_arithmeticFields
        productLogLogRelationPureTargetName n (fun _idx => n)).1 h.2
  · intro fields
    exact
      ⟨productLogTaggedIndexFormula_eval n (fun _idx => n),
        (productLogTaggedBodyTargetFormula_eval_iff_arithmeticFields
          productLogLogRelationPureTargetName n (fun _idx => n)).2 fields⟩

theorem productLogProductPureTargetFormula_eval_iff_source (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogProductPureTargetFormula n) ↔
      _root_.sondow_explicit_product_log_relation_prop n :=
  (productLogProductPureTargetFormula_eval_iff_arithmeticFields n).trans
    ((ProductLogExpandedSourceCertificate.nonempty_iff_arithmeticFields
      n).symm.trans
      (ProductLogExpandedSourceCertificate.nonempty_iff_source n))

theorem productLogLogRelationPureTargetFormula_eval_iff_source (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogLogRelationPureTargetFormula n) ↔
      _root_.sondow_explicit_product_log_relation_prop n :=
  (productLogLogRelationPureTargetFormula_eval_iff_arithmeticFields n).trans
    ((ProductLogExpandedSourceCertificate.nonempty_iff_arithmeticFields
      n).symm.trans
      (ProductLogExpandedSourceCertificate.nonempty_iff_source n))

def productLogTaggedIndexProofObject (n : ℕ) :
    BAProofObject BussS21Axiom :=
  productLogDecompositionProofObjectOfAxiom
    (BussS21Axiom.eqRefl (productLogBaNatLiteral n))

def productLogTaggedBodyProofObject (targetName n : ℕ) :
    BAProofObject BussS21Axiom :=
  productLogDecompositionPolytimeDefinabilityProofObject targetName
    (productLogArithmeticTargetFormula n)

def productLogProductPureProofObject (n : ℕ) :
    BAProofObject BussS21Axiom :=
  (productLogTaggedIndexProofObject n).andIntro
    (productLogTaggedBodyProofObject productLogProductPureTargetName n)

def productLogLogRelationPureProofObject (n : ℕ) :
    BAProofObject BussS21Axiom :=
  (productLogTaggedIndexProofObject n).andIntro
    (productLogTaggedBodyProofObject productLogLogRelationPureTargetName n)

theorem productLogProductPureProofObject_conclusion (n : ℕ) :
    (productLogProductPureProofObject n).conclusion =
      productLogProductPureTargetFormula n := by
  rfl

theorem productLogLogRelationPureProofObject_conclusion (n : ℕ) :
    (productLogLogRelationPureProofObject n).conclusion =
      productLogLogRelationPureTargetFormula n := by
  rfl

theorem productLogProductPureProofObject_size_plus_two_eq_five
    (n : ℕ) :
    ((((productLogProductPureProofObject n).size + 2 : ℕ) : ℝ)) = 5 := by
  change (((1 + 1 + 1 + 2 : ℕ) : ℝ)) = 5
  norm_num

theorem productLogLogRelationPureProofObject_size_plus_two_eq_five
    (n : ℕ) :
    ((((productLogLogRelationPureProofObject n).size + 2 : ℕ) : ℝ)) = 5 := by
  change (((1 + 1 + 1 + 2 : ℕ) : ℝ)) = 5
  norm_num

structure ProductLogSeparatedTargetCompletionAudit where
  productTarget : ℕ → BAFormula
  logRelationTarget : ℕ → BAFormula
  code : BAFormula → BoundedArithmeticLab.FormulaCode
  productTarget_eq :
    productTarget = productLogProductPureTargetFormula
  logRelationTarget_eq :
    logRelationTarget = productLogLogRelationPureTargetFormula
  code_product :
    ∀ n : ℕ, code (productTarget n) = sondowProductCode n
  code_logRelation :
    ∀ n : ℕ, code (logRelationTarget n) = sondowLogRelationCode n
  product_atomFree :
    ∀ n : ℕ, productLogDecompositionAtomFree (productTarget n)
  logRelation_atomFree :
    ∀ n : ℕ, productLogDecompositionAtomFree (logRelationTarget n)
  product_eval_iff_source :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (productTarget n) ↔
        _root_.sondow_explicit_product_log_relation_prop n
  logRelation_eval_iff_source :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (logRelationTarget n) ↔
        _root_.sondow_explicit_product_log_relation_prop n
  productProof : ℕ → BAProofObject BussS21Axiom
  logRelationProof : ℕ → BAProofObject BussS21Axiom
  productProof_conclusion :
    ∀ n : ℕ, (productProof n).conclusion = productTarget n
  logRelationProof_conclusion :
    ∀ n : ℕ, (logRelationProof n).conclusion = logRelationTarget n
  product_size_plus_two_le :
    ∀ n : ℕ,
      ((((productProof n).size + 2 : ℕ) : ℝ)) ≤ productLogArithmeticBound n
  logRelation_size_plus_two_le :
    ∀ n : ℕ,
      ((((logRelationProof n).size + 2 : ℕ) : ℝ)) ≤
        productLogArithmeticBound n

def productLogSeparatedTargetCompletionAudit :
    ProductLogSeparatedTargetCompletionAudit where
  productTarget := productLogProductPureTargetFormula
  logRelationTarget := productLogLogRelationPureTargetFormula
  code := productLogSeparatedTargetCode
  productTarget_eq := rfl
  logRelationTarget_eq := rfl
  code_product := productLogSeparatedTargetCode_product
  code_logRelation := productLogSeparatedTargetCode_logRelation
  product_atomFree := productLogProductPureTargetFormula_atomFree
  logRelation_atomFree := productLogLogRelationPureTargetFormula_atomFree
  product_eval_iff_source :=
    productLogProductPureTargetFormula_eval_iff_source
  logRelation_eval_iff_source :=
    productLogLogRelationPureTargetFormula_eval_iff_source
  productProof := productLogProductPureProofObject
  logRelationProof := productLogLogRelationPureProofObject
  productProof_conclusion :=
    productLogProductPureProofObject_conclusion
  logRelationProof_conclusion :=
    productLogLogRelationPureProofObject_conclusion
  product_size_plus_two_le := by
    intro n
    rw [productLogProductPureProofObject_size_plus_two_eq_five]
    simp [productLogArithmeticBound]
  logRelation_size_plus_two_le := by
    intro n
    rw [productLogLogRelationPureProofObject_size_plus_two_eq_five]
    simp [productLogArithmeticBound]

end SondowMainCheckedCodeBridge
