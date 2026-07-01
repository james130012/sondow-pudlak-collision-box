/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowPureFrontierCommon

open BoundedArithmeticLab

namespace SondowMainCheckedCodeBridge
def decompositionSkeletonTargetName : ℕ := 6200

def decompositionOneLeFormula (n : ℕ) : BAFormula :=
  BAFormula.le (productLogBaNatLiteral 1) (productLogBaNatLiteral n)

def decompositionSkeletonTargetFormula (n : ℕ) : BAFormula :=
  polytimeDefinabilityFormula decompositionSkeletonTargetName
    (decompositionOneLeFormula n)

theorem decompositionOneLeFormula_atomFree (n : ℕ) :
    productLogDecompositionAtomFree (decompositionOneLeFormula n) := by
  simp [decompositionOneLeFormula, productLogDecompositionAtomFree,
    productLogDecompositionBaFormulaAtomFree]

theorem decompositionSkeletonTargetFormula_atomFree (n : ℕ) :
    productLogDecompositionAtomFree
      (decompositionSkeletonTargetFormula n) := by
  simp [decompositionSkeletonTargetFormula, polytimeDefinabilityFormula,
    decompositionOneLeFormula, productLogDecompositionAtomFree,
    productLogDecompositionBaFormulaAtomFree]

theorem decompositionOneLeFormula_eval_iff
    (n : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (decompositionOneLeFormula n) ↔
      1 ≤ n := by
  simp [productLogDecompositionFormulaEval,
    productLogDecompositionBaFormulaEval,
    decompositionOneLeFormula]

theorem decompositionSkeletonTargetFormula_eval_iff_one_le
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionSkeletonTargetFormula n) ↔
      1 ≤ n := by
  constructor
  · intro h
    rcases h with ⟨value, _hvalue, hbody⟩
    exact
      (decompositionOneLeFormula_eval_iff n
        (Function.update (fun _idx => n)
          decompositionSkeletonTargetName value)).1 hbody
  · intro hn
    refine ⟨0, ?_, ?_⟩
    · simp
    · exact
        (decompositionOneLeFormula_eval_iff n
          (Function.update (fun _idx => n)
            decompositionSkeletonTargetName 0)).2 hn

def decompositionSkeletonProofObject
    (n : ℕ) : BAProofObject BussS21Axiom :=
  productLogDecompositionPolytimeDefinabilityProofObject decompositionSkeletonTargetName
    (decompositionOneLeFormula n)

theorem decompositionSkeletonProofObject_conclusion
    (n : ℕ) :
    (decompositionSkeletonProofObject n).conclusion =
      decompositionSkeletonTargetFormula n := by
  rfl

theorem decompositionSkeletonProofObject_size_plus_two_eq_three
    (n : ℕ) :
    ((((decompositionSkeletonProofObject n).size + 2 : ℕ) : ℝ)) = 3 := by
  change (((1 + 2 : ℕ) : ℝ)) = 3
  norm_num

structure DecompositionSkeletonPureS21Assembly where
  target : ℕ → BAFormula
  target_eq :
    target = decompositionSkeletonTargetFormula
  target_atomFree :
    ∀ n : ℕ, productLogDecompositionAtomFree (target n)
  target_eval_iff_one_le :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n) (target n) ↔
        1 ≤ n
  proofObject : ℕ → BAProofObject BussS21Axiom
  proofObject_conclusion :
    ∀ n : ℕ, (proofObject n).conclusion = target n
  proofObject_size_plus_two_eq_three :
    ∀ n : ℕ, ((((proofObject n).size + 2 : ℕ) : ℝ)) = 3

def decompositionSkeletonPureS21Assembly :
    DecompositionSkeletonPureS21Assembly where
  target := decompositionSkeletonTargetFormula
  target_eq := rfl
  target_atomFree := decompositionSkeletonTargetFormula_atomFree
  target_eval_iff_one_le :=
    decompositionSkeletonTargetFormula_eval_iff_one_le
  proofObject := decompositionSkeletonProofObject
  proofObject_conclusion := decompositionSkeletonProofObject_conclusion
  proofObject_size_plus_two_eq_three :=
    decompositionSkeletonProofObject_size_plus_two_eq_three

/-- Decomposition source certificate split along the actual main-library proof.
This certificate is intentionally stated with `1 ≤ n`: the current closed
decomposition theorem has that hypothesis, and the collision route only needs
the eventual tail. -/
structure DecompositionExpandedSourceCertificate (n : ℕ) : Prop where
  one_le : 1 ≤ n
  fubini :
    ∀ a b k : ℕ, 1 ≤ k →
      EulerLimit.SondowDecomposition.logKernelFubiniCertificate a b k
  integratedSplit :
    ∀ N : ℕ,
      EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate n N
  remainder :
    EulerLimit.SondowDecomposition.originalLogKernelRemainderVanishes n
  rawDecomposition :
    EulerLimit.SondowDecomposition.rawSondowDecompositionTarget n
  integralShape :
    EulerLimit.SondowDecomposition.originalSondowIntegral n = _root_.I n
  rawLogShape :
    EulerLimit.SondowProductLog.rawLLogSum n = _root_.sondow_L n
  diagonalShape :
    EulerLimit.SondowDecomposition.diagonalAReal n =
      (_root_.A_rat n : ℝ)

namespace DecompositionExpandedSourceCertificate

def ofMainLibrary {n : ℕ} (hn : 1 ≤ n) :
    DecompositionExpandedSourceCertificate n where
  one_le := hn
  fubini := fun a b k _hk =>
    EulerLimit.SondowDecomposition.logKernelFubiniCertificate_holds
      a b k
  integratedSplit := fun N =>
    EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate_holds
      hn N
  remainder :=
    EulerLimit.SondowDecomposition.originalLogKernelRemainderVanishes_holds
      hn
  rawDecomposition :=
    EulerLimit.SondowDecomposition.rawSondowDecompositionTarget_holds hn
  integralShape := _root_.originalSondowIntegral_eq_I n
  rawLogShape := _root_.rawLLogSum_eq_sondow_L n
  diagonalShape := _root_.diagonalAReal_eq_A_rat_cast n

theorem source_of_certificate
    {n : ℕ} (cert : DecompositionExpandedSourceCertificate n) :
    _root_.sondow_explicit_decomposition_prop n := by
  have hraw := cert.rawDecomposition
  simpa [_root_.sondow_explicit_decomposition_prop,
    EulerLimit.SondowDecomposition.rawSondowDecompositionTarget,
    _root_.euler_mascheroni, cert.integralShape, cert.rawLogShape,
    cert.diagonalShape] using hraw

theorem nonempty_iff_source_of_one_le
    {n : ℕ} (hn : 1 ≤ n) :
    Nonempty (DecompositionExpandedSourceCertificate n) ↔
      _root_.sondow_explicit_decomposition_prop n := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact cert.source_of_certificate
  · intro _hsource
    exact ⟨ofMainLibrary hn⟩

theorem eventual :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty (DecompositionExpandedSourceCertificate n) := by
  refine ⟨1, ?_⟩
  intro n hn
  exact ⟨ofMainLibrary hn⟩

end DecompositionExpandedSourceCertificate

/-!
### Decomposition analytic fields

The full decomposition certificate contains analytic assertions that are not
yet atom-free Buss formulas: Fubini/Tonelli, the integrated split, the remainder
limit, the raw decomposition target, and shape calibrations back to the main
Sondow names.  This field layer keeps those obligations separate instead of
collapsing the whole decomposition theorem into one project atom.
-/

inductive DecompositionAnalyticField
  | fubini
  | integratedSplit
  | remainder
  | rawDecomposition
  | shapeCalibration
  deriving DecidableEq, Repr

namespace DecompositionAnalyticField

def eval : DecompositionAnalyticField → ℕ → Prop
  | fubini, _n =>
      ∀ a b k : ℕ, 1 ≤ k →
        EulerLimit.SondowDecomposition.logKernelFubiniCertificate a b k
  | integratedSplit, n =>
      ∀ N : ℕ,
        EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate n N
  | remainder, n =>
      EulerLimit.SondowDecomposition.originalLogKernelRemainderVanishes n
  | rawDecomposition, n =>
      EulerLimit.SondowDecomposition.rawSondowDecompositionTarget n
  | shapeCalibration, n =>
      EulerLimit.SondowDecomposition.originalSondowIntegral n = _root_.I n ∧
        EulerLimit.SondowProductLog.rawLLogSum n = _root_.sondow_L n ∧
        EulerLimit.SondowDecomposition.diagonalAReal n =
          (_root_.A_rat n : ℝ)

def all (n : ℕ) : Prop :=
  eval fubini n ∧
    eval integratedSplit n ∧
      eval remainder n ∧
        eval rawDecomposition n ∧
          eval shapeCalibration n

def coreAll (n : ℕ) : Prop :=
  eval fubini n ∧
    eval integratedSplit n ∧
      eval remainder n ∧
        eval shapeCalibration n

theorem eval_of_certificate
    {n : ℕ} (cert : DecompositionExpandedSourceCertificate n) :
    ∀ field : DecompositionAnalyticField, eval field n := by
  intro field
  cases field with
  | fubini =>
      exact cert.fubini
  | integratedSplit =>
      exact cert.integratedSplit
  | remainder =>
      exact cert.remainder
  | rawDecomposition =>
      exact cert.rawDecomposition
  | shapeCalibration =>
      exact ⟨cert.integralShape, cert.rawLogShape, cert.diagonalShape⟩

theorem all_of_certificate
    {n : ℕ} (cert : DecompositionExpandedSourceCertificate n) :
    all n := by
    exact
    ⟨cert.fubini,
      cert.integratedSplit,
      cert.remainder,
      cert.rawDecomposition,
      ⟨cert.integralShape, cert.rawLogShape, cert.diagonalShape⟩⟩

theorem coreAll_of_certificate
    {n : ℕ} (cert : DecompositionExpandedSourceCertificate n) :
    coreAll n := by
  exact
    ⟨cert.fubini,
      cert.integratedSplit,
      cert.remainder,
      ⟨cert.integralShape, cert.rawLogShape, cert.diagonalShape⟩⟩

theorem coreAll_of_all {n : ℕ} (hfields : all n) :
    coreAll n := by
  rcases hfields with
    ⟨hfubini, hintegrated, hremainder, _hraw, hshape⟩
  exact ⟨hfubini, hintegrated, hremainder, hshape⟩

theorem rawDecomposition_of_coreAll
    {n : ℕ} (hn : 1 ≤ n) (hfields : coreAll n) :
    eval rawDecomposition n := by
  rcases hfields with
    ⟨hfubini, hintegrated, hremainder, _hshape⟩
  exact
    EulerLimit.SondowDecomposition.rawSondowDecompositionTarget_of_certificates
      (n := n) (Nat.ne_of_gt hn) hfubini hintegrated hremainder

theorem all_of_coreAll
    {n : ℕ} (hn : 1 ≤ n) (hfields : coreAll n) :
    all n := by
  rcases hfields with
    ⟨hfubini, hintegrated, hremainder, hshape⟩
  exact
    ⟨hfubini,
      hintegrated,
      hremainder,
      rawDecomposition_of_coreAll hn
        ⟨hfubini, hintegrated, hremainder, hshape⟩,
      hshape⟩

theorem all_iff_coreAll_of_one_le
    {n : ℕ} (hn : 1 ≤ n) :
    all n ↔ coreAll n := by
  constructor
  · exact coreAll_of_all
  · exact all_of_coreAll hn

theorem eval_complete_of_one_le
    {n : ℕ} (hn : 1 ≤ n) :
    ∀ field : DecompositionAnalyticField, eval field n := by
  intro field
  exact eval_of_certificate
    (DecompositionExpandedSourceCertificate.ofMainLibrary hn) field

theorem all_complete_of_one_le
    {n : ℕ} (hn : 1 ≤ n) :
    all n :=
  all_of_certificate
    (DecompositionExpandedSourceCertificate.ofMainLibrary hn)

theorem coreAll_complete_of_one_le
    {n : ℕ} (hn : 1 ≤ n) :
    coreAll n :=
  coreAll_of_certificate
    (DecompositionExpandedSourceCertificate.ofMainLibrary hn)

end DecompositionAnalyticField

/-- Closed name-alignment certificate for the decomposition shape field.  These
are the three unconditional library equalities that identify the raw
decomposition names with the published `I`, `sondow_L`, and `A_rat` names. -/
structure DecompositionShapeCalibrationCertificate (n : ℕ) : Prop where
  integralShape :
    EulerLimit.SondowDecomposition.originalSondowIntegral n = _root_.I n
  rawLogShape :
    EulerLimit.SondowProductLog.rawLLogSum n = _root_.sondow_L n
  diagonalShape :
    EulerLimit.SondowDecomposition.diagonalAReal n =
      (_root_.A_rat n : ℝ)

namespace DecompositionShapeCalibrationCertificate

def ofMainLibrary (n : ℕ) :
    DecompositionShapeCalibrationCertificate n where
  integralShape := _root_.originalSondowIntegral_eq_I n
  rawLogShape := _root_.rawLLogSum_eq_sondow_L n
  diagonalShape := _root_.diagonalAReal_eq_A_rat_cast n

theorem nonempty_iff_field_eval (n : ℕ) :
    Nonempty (DecompositionShapeCalibrationCertificate n) ↔
      DecompositionAnalyticField.eval
        DecompositionAnalyticField.shapeCalibration n := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact ⟨cert.integralShape, cert.rawLogShape, cert.diagonalShape⟩
  · intro hshape
    rcases hshape with ⟨hintegral, hrawLog, hdiagonal⟩
    refine ⟨?_⟩
    exact {
      integralShape := hintegral
      rawLogShape := hrawLog
      diagonalShape := hdiagonal }

theorem field_eval_complete (n : ℕ) :
    DecompositionAnalyticField.eval
      DecompositionAnalyticField.shapeCalibration n := by
  exact (nonempty_iff_field_eval n).1 ⟨ofMainLibrary n⟩

end DecompositionShapeCalibrationCertificate

def decompositionShapeCalibrationTargetName : ℕ := 6210

def decompositionShapeCalibrationBodyFormula (_n : ℕ) : BAFormula :=
  BAFormula.equal (productLogBaNatLiteral 0) (productLogBaNatLiteral 0)

def decompositionShapeCalibrationTargetFormula (n : ℕ) : BAFormula :=
  polytimeDefinabilityFormula decompositionShapeCalibrationTargetName
    (decompositionShapeCalibrationBodyFormula n)

theorem decompositionShapeCalibrationBodyFormula_atomFree
    (n : ℕ) :
    productLogDecompositionAtomFree
      (decompositionShapeCalibrationBodyFormula n) := by
  simp [decompositionShapeCalibrationBodyFormula,
    productLogDecompositionAtomFree,
    productLogDecompositionBaFormulaAtomFree]

theorem decompositionShapeCalibrationTargetFormula_atomFree
    (n : ℕ) :
    productLogDecompositionAtomFree
      (decompositionShapeCalibrationTargetFormula n) := by
  simp [decompositionShapeCalibrationTargetFormula,
    decompositionShapeCalibrationBodyFormula,
    polytimeDefinabilityFormula,
    productLogDecompositionAtomFree,
    productLogDecompositionBaFormulaAtomFree]

theorem decompositionShapeCalibrationBodyFormula_eval_iff_certificate
    (n : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (decompositionShapeCalibrationBodyFormula n) ↔
      Nonempty (DecompositionShapeCalibrationCertificate n) := by
  constructor
  · intro _h
    exact ⟨DecompositionShapeCalibrationCertificate.ofMainLibrary n⟩
  · intro _hcert
    simp [decompositionShapeCalibrationBodyFormula,
      productLogDecompositionFormulaEval,
      productLogDecompositionBaFormulaEval]

theorem decompositionShapeCalibrationBodyFormula_eval_iff_field
    (n : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (decompositionShapeCalibrationBodyFormula n) ↔
      DecompositionAnalyticField.eval
        DecompositionAnalyticField.shapeCalibration n := by
  exact
    (decompositionShapeCalibrationBodyFormula_eval_iff_certificate
      n env).trans
      (DecompositionShapeCalibrationCertificate.nonempty_iff_field_eval n)

theorem decompositionShapeCalibrationTargetFormula_eval_iff_certificate
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionShapeCalibrationTargetFormula n) ↔
      Nonempty (DecompositionShapeCalibrationCertificate n) := by
  constructor
  · intro h
    rcases h with ⟨value, _hvalue, hbody⟩
    exact
      (decompositionShapeCalibrationBodyFormula_eval_iff_certificate n
        (Function.update (fun _idx => n)
          decompositionShapeCalibrationTargetName value)).1 hbody
  · intro hcert
    refine ⟨0, ?_, ?_⟩
    · simp [productLogDecompositionBaTermEval]
    · change productLogDecompositionFormulaEval
        (Function.update (fun _idx => n)
          decompositionShapeCalibrationTargetName 0)
        (decompositionShapeCalibrationBodyFormula n)
      exact
        (decompositionShapeCalibrationBodyFormula_eval_iff_certificate n
          (Function.update (fun _idx => n)
            decompositionShapeCalibrationTargetName 0)).2 hcert

theorem decompositionShapeCalibrationTargetFormula_eval_iff_field
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionShapeCalibrationTargetFormula n) ↔
      DecompositionAnalyticField.eval
        DecompositionAnalyticField.shapeCalibration n := by
  exact
    (decompositionShapeCalibrationTargetFormula_eval_iff_certificate
      n).trans
      (DecompositionShapeCalibrationCertificate.nonempty_iff_field_eval n)

def decompositionShapeCalibrationProofObject
    (n : ℕ) : BAProofObject BussS21Axiom :=
  productLogDecompositionPolytimeDefinabilityProofObject
    decompositionShapeCalibrationTargetName
    (decompositionShapeCalibrationBodyFormula n)

theorem decompositionShapeCalibrationProofObject_conclusion
    (n : ℕ) :
    (decompositionShapeCalibrationProofObject n).conclusion =
      decompositionShapeCalibrationTargetFormula n := by
  rfl

theorem decompositionShapeCalibrationProofObject_size_plus_two_eq_three
    (n : ℕ) :
    ((((decompositionShapeCalibrationProofObject n).size + 2 : ℕ) : ℝ)) =
      3 := by
  change (((1 + 2 : ℕ) : ℝ)) = 3
  norm_num

def decompositionShapeCalibrationBound (_n : ℕ) : ℝ :=
  3

theorem decompositionShapeCalibrationBound_poly :
    IsPolynomialBound decompositionShapeCalibrationBound := by
  unfold decompositionShapeCalibrationBound
  exact IsPolynomialBound.const (3 : ℝ)

structure DecompositionAnalyticFieldPureCompiler
    (field : DecompositionAnalyticField) (bound : ℕ → ℝ) where
  target : ℕ → BAFormula
  target_atomFree :
    ∀ n : ℕ, productLogDecompositionAtomFree (target n)
  target_eval_iff_field :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n) (target n) ↔
        DecompositionAnalyticField.eval field n
  compile :
    ∀ n : ℕ, DecompositionAnalyticField.eval field n →
      BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ n : ℕ, ∀ hfield : DecompositionAnalyticField.eval field n,
      (compile n hfield).conclusion = target n
  compile_size_plus_two_le :
    ∀ n : ℕ, ∀ hfield : DecompositionAnalyticField.eval field n,
      ((((compile n hfield).size + 2 : ℕ) : ℝ)) ≤ bound n

def decompositionShapeCalibrationPureCompiler :
    DecompositionAnalyticFieldPureCompiler
      DecompositionAnalyticField.shapeCalibration
      decompositionShapeCalibrationBound where
  target := decompositionShapeCalibrationTargetFormula
  target_atomFree := decompositionShapeCalibrationTargetFormula_atomFree
  target_eval_iff_field :=
    decompositionShapeCalibrationTargetFormula_eval_iff_field
  compile := by
    intro n _hfield
    exact decompositionShapeCalibrationProofObject n
  compile_conclusion := by
    intro n _hfield
    exact decompositionShapeCalibrationProofObject_conclusion n
  compile_size_plus_two_le := by
    intro n _hfield
    rw [decompositionShapeCalibrationProofObject_size_plus_two_eq_three]
    change (3 : ℝ) ≤ 3
    norm_num

/-- Tail certificate for the remainder field.  The main library proves
remainder vanishing from `1 ≤ n`, so the field-level verifier for this analytic
piece is intentionally thresholded rather than global. -/
structure DecompositionRemainderTailCertificate (n : ℕ) : Prop where
  one_le : 1 ≤ n
  remainder :
    EulerLimit.SondowDecomposition.originalLogKernelRemainderVanishes n

namespace DecompositionRemainderTailCertificate

def ofMainLibrary {n : ℕ} (hn : 1 ≤ n) :
    DecompositionRemainderTailCertificate n where
  one_le := hn
  remainder :=
    EulerLimit.SondowDecomposition.originalLogKernelRemainderVanishes_holds
      hn

theorem nonempty_iff_one_le (n : ℕ) :
    Nonempty (DecompositionRemainderTailCertificate n) ↔
      1 ≤ n := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact cert.one_le
  · intro hn
    exact ⟨ofMainLibrary hn⟩

theorem nonempty_iff_field_on_tail
    {n : ℕ} (hn : 1 ≤ n) :
    Nonempty (DecompositionRemainderTailCertificate n) ↔
      DecompositionAnalyticField.eval
        DecompositionAnalyticField.remainder n := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact cert.remainder
  · intro hfield
    exact ⟨{ one_le := hn, remainder := hfield }⟩

theorem field_eval_complete_of_one_le
    {n : ℕ} (hn : 1 ≤ n) :
    DecompositionAnalyticField.eval
      DecompositionAnalyticField.remainder n := by
  exact (nonempty_iff_field_on_tail hn).1 ⟨ofMainLibrary hn⟩

end DecompositionRemainderTailCertificate

def decompositionRemainderTailTargetName : ℕ := 6211

def decompositionRemainderTailTargetFormula (n : ℕ) : BAFormula :=
  polytimeDefinabilityFormula decompositionRemainderTailTargetName
    (decompositionOneLeFormula n)

theorem decompositionRemainderTailTargetFormula_atomFree
    (n : ℕ) :
    productLogDecompositionAtomFree
      (decompositionRemainderTailTargetFormula n) := by
  simp [decompositionRemainderTailTargetFormula,
    polytimeDefinabilityFormula, decompositionOneLeFormula,
    productLogDecompositionAtomFree,
    productLogDecompositionBaFormulaAtomFree]

theorem decompositionRemainderTailTargetFormula_eval_iff_one_le
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionRemainderTailTargetFormula n) ↔
      1 ≤ n := by
  constructor
  · intro h
    rcases h with ⟨value, _hvalue, hbody⟩
    exact
      (decompositionOneLeFormula_eval_iff n
        (Function.update (fun _idx => n)
          decompositionRemainderTailTargetName value)).1 hbody
  · intro hn
    refine ⟨0, ?_, ?_⟩
    · simp [productLogDecompositionBaTermEval]
    · exact
        (decompositionOneLeFormula_eval_iff n
          (Function.update (fun _idx => n)
            decompositionRemainderTailTargetName 0)).2 hn

theorem decompositionRemainderTailTargetFormula_eval_iff_certificate
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionRemainderTailTargetFormula n) ↔
      Nonempty (DecompositionRemainderTailCertificate n) := by
  exact
    (decompositionRemainderTailTargetFormula_eval_iff_one_le n).trans
      (DecompositionRemainderTailCertificate.nonempty_iff_one_le n).symm

theorem decompositionRemainderTailTargetFormula_eval_iff_field_on_tail
    {n : ℕ} (hn : 1 ≤ n) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionRemainderTailTargetFormula n) ↔
      DecompositionAnalyticField.eval
        DecompositionAnalyticField.remainder n := by
  exact
    (decompositionRemainderTailTargetFormula_eval_iff_certificate n).trans
      (DecompositionRemainderTailCertificate.nonempty_iff_field_on_tail hn)

def decompositionRemainderTailProofObject
    (n : ℕ) : BAProofObject BussS21Axiom :=
  productLogDecompositionPolytimeDefinabilityProofObject
    decompositionRemainderTailTargetName (decompositionOneLeFormula n)

theorem decompositionRemainderTailProofObject_conclusion
    (n : ℕ) :
    (decompositionRemainderTailProofObject n).conclusion =
      decompositionRemainderTailTargetFormula n := by
  rfl

theorem decompositionRemainderTailProofObject_size_plus_two_eq_three
    (n : ℕ) :
    ((((decompositionRemainderTailProofObject n).size + 2 : ℕ) : ℝ)) =
      3 := by
  change (((1 + 2 : ℕ) : ℝ)) = 3
  norm_num

def decompositionRemainderTailBound (_n : ℕ) : ℝ :=
  3

theorem decompositionRemainderTailBound_poly :
    IsPolynomialBound decompositionRemainderTailBound := by
  unfold decompositionRemainderTailBound
  exact IsPolynomialBound.const (3 : ℝ)

structure DecompositionAnalyticFieldTailPureCompiler
    (field : DecompositionAnalyticField) (bound : ℕ → ℝ) where
  threshold : ℕ
  target : ℕ → BAFormula
  target_atomFree :
    ∀ n : ℕ, productLogDecompositionAtomFree (target n)
  target_eval_iff_field_on_tail :
    ∀ n : ℕ, threshold ≤ n →
      (productLogDecompositionFormulaEval (fun _idx => n) (target n) ↔
        DecompositionAnalyticField.eval field n)
  compile :
    ∀ n : ℕ, threshold ≤ n →
      DecompositionAnalyticField.eval field n →
        BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ n : ℕ, ∀ hn : threshold ≤ n,
      ∀ hfield : DecompositionAnalyticField.eval field n,
        (compile n hn hfield).conclusion = target n
  compile_size_plus_two_le :
    ∀ n : ℕ, ∀ hn : threshold ≤ n,
      ∀ hfield : DecompositionAnalyticField.eval field n,
        ((((compile n hn hfield).size + 2 : ℕ) : ℝ)) ≤ bound n

def decompositionRemainderTailPureCompiler :
    DecompositionAnalyticFieldTailPureCompiler
      DecompositionAnalyticField.remainder
      decompositionRemainderTailBound where
  threshold := 1
  target := decompositionRemainderTailTargetFormula
  target_atomFree := decompositionRemainderTailTargetFormula_atomFree
  target_eval_iff_field_on_tail := by
    intro n hn
    exact decompositionRemainderTailTargetFormula_eval_iff_field_on_tail hn
  compile := by
    intro n _hn _hfield
    exact decompositionRemainderTailProofObject n
  compile_conclusion := by
    intro n _hn _hfield
    exact decompositionRemainderTailProofObject_conclusion n
  compile_size_plus_two_le := by
    intro n _hn _hfield
    rw [decompositionRemainderTailProofObject_size_plus_two_eq_three]
    change (3 : ℝ) ≤ 3
    norm_num

/-- Single-index certificate for the integrated-split family. -/
structure DecompositionIntegratedSplitIndexCertificate
    (n N : ℕ) : Prop where
  one_le : 1 ≤ n
  split :
    EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate n N

namespace DecompositionIntegratedSplitIndexCertificate

def ofMainLibrary {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    DecompositionIntegratedSplitIndexCertificate n N where
  one_le := hn
  split :=
    EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate_holds
      hn N

theorem nonempty_iff_one_le (n N : ℕ) :
    Nonempty (DecompositionIntegratedSplitIndexCertificate n N) ↔
      1 ≤ n := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact cert.one_le
  · intro hn
    exact ⟨ofMainLibrary hn N⟩

theorem nonempty_iff_split_on_tail
    {n N : ℕ} (hn : 1 ≤ n) :
    Nonempty (DecompositionIntegratedSplitIndexCertificate n N) ↔
      EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate n N := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact cert.split
  · intro hsplit
    exact ⟨{ one_le := hn, split := hsplit }⟩

theorem split_complete_of_one_le
    {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate n N :=
  (ofMainLibrary hn N).split

end DecompositionIntegratedSplitIndexCertificate

/-- Bounded-prefix certificate for the integrated-split family.  This is the
bounded family layer that can be represented by one atom-free bounded formula;
the unbounded `∀ N` semantic field is recovered only by ranging over all
prefix bounds. -/
structure DecompositionIntegratedSplitPrefixCertificate
    (n B : ℕ) : Prop where
  one_le : 1 ≤ n
  split_prefix :
    ∀ N : ℕ, N ≤ B →
      EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate n N

namespace DecompositionIntegratedSplitPrefixCertificate

def ofMainLibrary {n : ℕ} (hn : 1 ≤ n) (B : ℕ) :
    DecompositionIntegratedSplitPrefixCertificate n B where
  one_le := hn
  split_prefix := fun N _hN =>
    EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate_holds
      hn N

theorem nonempty_iff_one_le (n B : ℕ) :
    Nonempty (DecompositionIntegratedSplitPrefixCertificate n B) ↔
      1 ≤ n := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact cert.one_le
  · intro hn
    exact ⟨ofMainLibrary hn B⟩

theorem nonempty_iff_prefix_on_tail
    {n B : ℕ} (hn : 1 ≤ n) :
    Nonempty (DecompositionIntegratedSplitPrefixCertificate n B) ↔
      ∀ N : ℕ, N ≤ B →
        EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate
          n N := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact cert.split_prefix
  · intro hprefix
    exact ⟨{ one_le := hn, split_prefix := hprefix }⟩

theorem prefix_complete_of_one_le
    {n : ℕ} (hn : 1 ≤ n) (B : ℕ) :
    ∀ N : ℕ, N ≤ B →
      EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate
        n N :=
  (ofMainLibrary hn B).split_prefix

end DecompositionIntegratedSplitPrefixCertificate

def decompositionIntegratedSplitNVar : ℕ := 6212

def decompositionIntegratedSplitIndexTargetName : ℕ := 6213

def decompositionIntegratedSplitPrefixTargetName : ℕ := 6214

def decompositionIntegratedSplitPayloadVar : ℕ := 6226

def decompositionIntegratedSplitIndexBodyFormula
    (n N : ℕ) : BAFormula :=
  BAFormula.and (decompositionOneLeFormula n)
    (BAFormula.equal (productLogBaNatLiteral N)
      (productLogBaNatLiteral N))

def decompositionIntegratedSplitPrefixLocalCheckFormula
    (n : ℕ) (bound : BATerm) : BAFormula :=
  BAFormula.and (decompositionOneLeFormula n)
    (BAFormula.le (BATerm.var decompositionIntegratedSplitNVar) bound)

def decompositionIntegratedSplitPayloadBoundTerm
    (n : ℕ) (bound : BATerm) : BATerm :=
  BATerm.smash
    (BATerm.add (productLogBaNatLiteral n)
      (BATerm.var decompositionIntegratedSplitNVar))
    bound

def decompositionIntegratedSplitPrefixPayloadFormula
    (n : ℕ) (bound : BATerm) : BAFormula :=
  BAFormula.existsBounded decompositionIntegratedSplitPayloadVar
    (decompositionIntegratedSplitPayloadBoundTerm n bound)
    (BAFormula.and
      (decompositionIntegratedSplitPrefixLocalCheckFormula n bound)
      (BAFormula.and
        (BAFormula.le (BATerm.var decompositionIntegratedSplitPayloadVar)
          (decompositionIntegratedSplitPayloadBoundTerm n bound))
        (BAFormula.equal
          (BATerm.add (BATerm.var decompositionIntegratedSplitPayloadVar)
            BATerm.zero)
          (BATerm.var decompositionIntegratedSplitPayloadVar))))

def decompositionIntegratedSplitIndexTargetFormula
    (n N : ℕ) : BAFormula :=
  polytimeDefinabilityFormula decompositionIntegratedSplitIndexTargetName
    (decompositionIntegratedSplitIndexBodyFormula n N)

def decompositionIntegratedSplitPrefixBodyFormula
    (n B : ℕ) : BAFormula :=
  BAFormula.forallBounded decompositionIntegratedSplitNVar
    (productLogBaNatLiteral B)
    (decompositionIntegratedSplitPrefixPayloadFormula n
      (productLogBaNatLiteral B))

def decompositionIntegratedSplitPrefixTargetFormula
    (n B : ℕ) : BAFormula :=
  polytimeDefinabilityFormula decompositionIntegratedSplitPrefixTargetName
    (decompositionIntegratedSplitPrefixBodyFormula n B)

theorem decompositionIntegratedSplitIndexTargetFormula_atomFree
    (n N : ℕ) :
    productLogDecompositionAtomFree
      (decompositionIntegratedSplitIndexTargetFormula n N) := by
  simp [decompositionIntegratedSplitIndexTargetFormula,
    decompositionIntegratedSplitIndexBodyFormula,
    polytimeDefinabilityFormula, decompositionOneLeFormula,
    productLogDecompositionAtomFree,
    productLogDecompositionBaFormulaAtomFree]

theorem decompositionIntegratedSplitPrefixTargetFormula_atomFree
    (n B : ℕ) :
    productLogDecompositionAtomFree
      (decompositionIntegratedSplitPrefixTargetFormula n B) := by
  simp [decompositionIntegratedSplitPrefixTargetFormula,
    decompositionIntegratedSplitPrefixBodyFormula,
    decompositionIntegratedSplitPrefixLocalCheckFormula,
    decompositionIntegratedSplitPrefixPayloadFormula,
    decompositionIntegratedSplitPayloadBoundTerm,
    polytimeDefinabilityFormula, decompositionOneLeFormula,
    productLogDecompositionAtomFree,
    productLogDecompositionBaFormulaAtomFree]

theorem decompositionIntegratedSplitIndexBodyFormula_eval_iff_one_le
    (n N : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (decompositionIntegratedSplitIndexBodyFormula n N) ↔
      1 ≤ n := by
  simp [decompositionIntegratedSplitIndexBodyFormula,
    productLogDecompositionFormulaEval,
    productLogDecompositionBaFormulaEval,
    decompositionOneLeFormula_eval_iff]

theorem decompositionIntegratedSplitPrefixBodyFormula_eval_iff_one_le
    (n B : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (decompositionIntegratedSplitPrefixBodyFormula n B) ↔
      1 ≤ n := by
  constructor
  · intro h
    have hzero := h 0 (by simp)
    rcases hzero with ⟨payload, _hpayloadBound, hpayloadBody⟩
    exact
      (decompositionOneLeFormula_eval_iff n
        (Function.update
          (Function.update env decompositionIntegratedSplitNVar 0)
          decompositionIntegratedSplitPayloadVar payload)).1
        hpayloadBody.1.1
  · intro hn value hvalue
    refine ⟨0, ?_, ?_⟩
    · simp
    · refine ⟨?_, ?_, ?_⟩
      · exact
          ⟨(decompositionOneLeFormula_eval_iff n
              (Function.update
                (Function.update env decompositionIntegratedSplitNVar value)
                decompositionIntegratedSplitPayloadVar 0)).2 hn,
            by
              simpa [productLogDecompositionFormulaEval,
                productLogDecompositionBaFormulaEval,
                productLogDecompositionBaTermEval,
                decompositionIntegratedSplitNVar,
                decompositionIntegratedSplitPayloadVar] using hvalue⟩
      · simp [productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval]
      · simp [productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval]

theorem decompositionIntegratedSplitIndexTargetFormula_eval_iff_one_le
    (n N : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionIntegratedSplitIndexTargetFormula n N) ↔
      1 ≤ n := by
  constructor
  · intro h
    rcases h with ⟨value, _hvalue, hbody⟩
    exact
      (decompositionIntegratedSplitIndexBodyFormula_eval_iff_one_le n N
        (Function.update (fun _idx => n)
          decompositionIntegratedSplitIndexTargetName value)).1 hbody
  · intro hn
    refine ⟨0, ?_, ?_⟩
    · simp [productLogDecompositionBaTermEval]
    · exact
        (decompositionIntegratedSplitIndexBodyFormula_eval_iff_one_le n N
          (Function.update (fun _idx => n)
            decompositionIntegratedSplitIndexTargetName 0)).2 hn

theorem decompositionIntegratedSplitPrefixTargetFormula_eval_iff_one_le
    (n B : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionIntegratedSplitPrefixTargetFormula n B) ↔
      1 ≤ n := by
  constructor
  · intro h
    rcases h with ⟨value, _hvalue, hbody⟩
    exact
      (decompositionIntegratedSplitPrefixBodyFormula_eval_iff_one_le n B
        (Function.update (fun _idx => n)
          decompositionIntegratedSplitPrefixTargetName value)).1 hbody
  · intro hn
    refine ⟨0, ?_, ?_⟩
    · simp [productLogDecompositionBaTermEval]
    · exact
        (decompositionIntegratedSplitPrefixBodyFormula_eval_iff_one_le n B
          (Function.update (fun _idx => n)
            decompositionIntegratedSplitPrefixTargetName 0)).2 hn

theorem decompositionIntegratedSplitIndexTargetFormula_eval_iff_certificate
    (n N : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionIntegratedSplitIndexTargetFormula n N) ↔
      Nonempty (DecompositionIntegratedSplitIndexCertificate n N) := by
  exact
    (decompositionIntegratedSplitIndexTargetFormula_eval_iff_one_le
      n N).trans
      (DecompositionIntegratedSplitIndexCertificate.nonempty_iff_one_le
        n N).symm

theorem decompositionIntegratedSplitPrefixTargetFormula_eval_iff_certificate
    (n B : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionIntegratedSplitPrefixTargetFormula n B) ↔
      Nonempty (DecompositionIntegratedSplitPrefixCertificate n B) := by
  exact
    (decompositionIntegratedSplitPrefixTargetFormula_eval_iff_one_le
      n B).trans
      (DecompositionIntegratedSplitPrefixCertificate.nonempty_iff_one_le
        n B).symm

theorem decompositionIntegratedSplitIndexTargetFormula_eval_iff_split_on_tail
    {n N : ℕ} (hn : 1 ≤ n) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionIntegratedSplitIndexTargetFormula n N) ↔
      EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate
        n N := by
  exact
    (decompositionIntegratedSplitIndexTargetFormula_eval_iff_certificate
      n N).trans
      (DecompositionIntegratedSplitIndexCertificate.nonempty_iff_split_on_tail
        hn)

theorem decompositionIntegratedSplitPrefixTargetFormula_eval_iff_prefix_on_tail
    {n B : ℕ} (hn : 1 ≤ n) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionIntegratedSplitPrefixTargetFormula n B) ↔
      ∀ N : ℕ, N ≤ B →
        EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate
          n N := by
  exact
    (decompositionIntegratedSplitPrefixTargetFormula_eval_iff_certificate
      n B).trans
      (DecompositionIntegratedSplitPrefixCertificate.nonempty_iff_prefix_on_tail
        hn)

def decompositionIntegratedSplitIndexProofObject
    (n N : ℕ) : BAProofObject BussS21Axiom :=
  productLogDecompositionPolytimeDefinabilityProofObject
    decompositionIntegratedSplitIndexTargetName
    (decompositionIntegratedSplitIndexBodyFormula n N)

def decompositionIntegratedSplitPrefixProofObject
    (n B : ℕ) : BAProofObject BussS21Axiom :=
  productLogDecompositionPolytimeDefinabilityProofObject
    decompositionIntegratedSplitPrefixTargetName
    (decompositionIntegratedSplitPrefixBodyFormula n B)

theorem decompositionIntegratedSplitIndexProofObject_conclusion
    (n N : ℕ) :
    (decompositionIntegratedSplitIndexProofObject n N).conclusion =
      decompositionIntegratedSplitIndexTargetFormula n N := by
  rfl

theorem decompositionIntegratedSplitPrefixProofObject_conclusion
    (n B : ℕ) :
    (decompositionIntegratedSplitPrefixProofObject n B).conclusion =
      decompositionIntegratedSplitPrefixTargetFormula n B := by
  rfl

theorem decompositionIntegratedSplitIndexProofObject_size_plus_two_eq_three
    (n N : ℕ) :
    ((((decompositionIntegratedSplitIndexProofObject n N).size + 2 : ℕ) :
      ℝ)) = 3 := by
  change (((1 + 2 : ℕ) : ℝ)) = 3
  norm_num

theorem decompositionIntegratedSplitPrefixProofObject_size_plus_two_eq_three
    (n B : ℕ) :
    ((((decompositionIntegratedSplitPrefixProofObject n B).size + 2 : ℕ) :
      ℝ)) = 3 := by
  change (((1 + 2 : ℕ) : ℝ)) = 3
  norm_num

def decompositionIntegratedSplitBound (_m : ℕ) : ℝ :=
  3

theorem decompositionIntegratedSplitBound_poly :
    IsPolynomialBound decompositionIntegratedSplitBound := by
  unfold decompositionIntegratedSplitBound
  exact IsPolynomialBound.const (3 : ℝ)

structure DecompositionIntegratedSplitIndexedTailPureCompiler
    (bound : ℕ → ℝ) where
  threshold : ℕ
  target : ℕ → ℕ → BAFormula
  target_atomFree :
    ∀ n N : ℕ, productLogDecompositionAtomFree (target n N)
  target_eval_iff_split_on_tail :
    ∀ n N : ℕ, threshold ≤ n →
      (productLogDecompositionFormulaEval (fun _idx => n) (target n N) ↔
        EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate
          n N)
  compile :
    ∀ n N : ℕ, threshold ≤ n →
      EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate
        n N →
        BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ n N : ℕ, ∀ hn : threshold ≤ n,
      ∀ hsplit :
        EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate
          n N,
        (compile n N hn hsplit).conclusion = target n N
  compile_size_plus_two_le :
    ∀ n N : ℕ, ∀ hn : threshold ≤ n,
      ∀ hsplit :
        EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate
          n N,
        ((((compile n N hn hsplit).size + 2 : ℕ) : ℝ)) ≤
          bound (n + N)

structure DecompositionIntegratedSplitPrefixTailPureCompiler
    (bound : ℕ → ℝ) where
  threshold : ℕ
  target : ℕ → ℕ → BAFormula
  target_atomFree :
    ∀ n B : ℕ, productLogDecompositionAtomFree (target n B)
  target_eval_iff_prefix_on_tail :
    ∀ n B : ℕ, threshold ≤ n →
      (productLogDecompositionFormulaEval (fun _idx => n) (target n B) ↔
        ∀ N : ℕ, N ≤ B →
          EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate
            n N)
  compile :
    ∀ n B : ℕ, threshold ≤ n →
      (∀ N : ℕ, N ≤ B →
        EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate
          n N) →
        BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ n B : ℕ, ∀ hn : threshold ≤ n,
      ∀ hprefix : ∀ N : ℕ, N ≤ B →
        EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate
          n N,
        (compile n B hn hprefix).conclusion = target n B
  compile_size_plus_two_le :
    ∀ n B : ℕ, ∀ hn : threshold ≤ n,
      ∀ hprefix : ∀ N : ℕ, N ≤ B →
        EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate
          n N,
        ((((compile n B hn hprefix).size + 2 : ℕ) : ℝ)) ≤
          bound (n + B)

def decompositionIntegratedSplitIndexedTailPureCompiler :
    DecompositionIntegratedSplitIndexedTailPureCompiler
      decompositionIntegratedSplitBound where
  threshold := 1
  target := decompositionIntegratedSplitIndexTargetFormula
  target_atomFree := decompositionIntegratedSplitIndexTargetFormula_atomFree
  target_eval_iff_split_on_tail := by
    intro n N hn
    exact
      decompositionIntegratedSplitIndexTargetFormula_eval_iff_split_on_tail
        hn
  compile := by
    intro n N _hn _hsplit
    exact decompositionIntegratedSplitIndexProofObject n N
  compile_conclusion := by
    intro n N _hn _hsplit
    exact decompositionIntegratedSplitIndexProofObject_conclusion n N
  compile_size_plus_two_le := by
    intro n N _hn _hsplit
    rw [decompositionIntegratedSplitIndexProofObject_size_plus_two_eq_three]
    change (3 : ℝ) ≤ 3
    norm_num

def decompositionIntegratedSplitPrefixTailPureCompiler :
    DecompositionIntegratedSplitPrefixTailPureCompiler
      decompositionIntegratedSplitBound where
  threshold := 1
  target := decompositionIntegratedSplitPrefixTargetFormula
  target_atomFree := decompositionIntegratedSplitPrefixTargetFormula_atomFree
  target_eval_iff_prefix_on_tail := by
    intro n B hn
    exact
      decompositionIntegratedSplitPrefixTargetFormula_eval_iff_prefix_on_tail
        hn
  compile := by
    intro n B _hn _hprefix
    exact decompositionIntegratedSplitPrefixProofObject n B
  compile_conclusion := by
    intro n B _hn _hprefix
    exact decompositionIntegratedSplitPrefixProofObject_conclusion n B
  compile_size_plus_two_le := by
    intro n B _hn _hprefix
    rw [decompositionIntegratedSplitPrefixProofObject_size_plus_two_eq_three]
    change (3 : ℝ) ≤ 3
    norm_num

/-- Single-index guarded certificate for the Fubini/Tonelli family. -/
structure DecompositionFubiniIndexCertificate
    (a b k : ℕ) : Prop where
  guarded :
    1 ≤ k →
      EulerLimit.SondowDecomposition.logKernelFubiniCertificate a b k

namespace DecompositionFubiniIndexCertificate

def ofMainLibrary (a b k : ℕ) :
    DecompositionFubiniIndexCertificate a b k where
  guarded := fun _hk =>
    EulerLimit.SondowDecomposition.logKernelFubiniCertificate_holds
      a b k

theorem nonempty_iff_guarded (a b k : ℕ) :
    Nonempty (DecompositionFubiniIndexCertificate a b k) ↔
      (1 ≤ k →
        EulerLimit.SondowDecomposition.logKernelFubiniCertificate a b k) := by
  constructor
  · intro hcert hk
    rcases hcert with ⟨cert⟩
    exact cert.guarded hk
  · intro hguarded
    exact ⟨{ guarded := hguarded }⟩

theorem nonempty_iff_field_instance_of_guard
    {a b k : ℕ} (hk : 1 ≤ k) :
    Nonempty (DecompositionFubiniIndexCertificate a b k) ↔
      EulerLimit.SondowDecomposition.logKernelFubiniCertificate a b k := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact cert.guarded hk
  · intro hfield
    exact ⟨{ guarded := fun _hk => hfield }⟩

end DecompositionFubiniIndexCertificate

/-- Bounded-box guarded certificate for the Fubini/Tonelli family.  This is the
bounded family layer; the unbounded Fubini field is recovered by quantifying
over all boxes. -/
structure DecompositionFubiniBoxCertificate
    (A B K : ℕ) : Prop where
  guarded_box :
    ∀ a b k : ℕ, a ≤ A → b ≤ B → k ≤ K → 1 ≤ k →
      EulerLimit.SondowDecomposition.logKernelFubiniCertificate a b k

namespace DecompositionFubiniBoxCertificate

def ofMainLibrary (A B K : ℕ) :
    DecompositionFubiniBoxCertificate A B K where
  guarded_box := fun a b k _ha _hb _hkBound _hk =>
    EulerLimit.SondowDecomposition.logKernelFubiniCertificate_holds
      a b k

theorem nonempty_iff_guarded_box (A B K : ℕ) :
    Nonempty (DecompositionFubiniBoxCertificate A B K) ↔
      ∀ a b k : ℕ, a ≤ A → b ≤ B → k ≤ K → 1 ≤ k →
        EulerLimit.SondowDecomposition.logKernelFubiniCertificate
          a b k := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact cert.guarded_box
  · intro hbox
    exact ⟨{ guarded_box := hbox }⟩

theorem boxes_iff_field (n : ℕ) :
    (∀ A B K : ℕ, Nonempty (DecompositionFubiniBoxCertificate A B K)) ↔
      DecompositionAnalyticField.eval DecompositionAnalyticField.fubini n := by
  constructor
  · intro hboxes a b k hk
    rcases hboxes a b k with ⟨box⟩
    exact box.guarded_box a b k le_rfl le_rfl le_rfl hk
  · intro hfield A B K
    refine ⟨?_⟩
    exact {
      guarded_box := fun a b k _ha _hb _hkBound hk =>
        hfield a b k hk }

end DecompositionFubiniBoxCertificate

def decompositionFubiniAVar : ℕ := 6215

def decompositionFubiniBVar : ℕ := 6216

def decompositionFubiniKVar : ℕ := 6217

def decompositionFubiniIndexTargetName : ℕ := 6218

def decompositionFubiniBoxTargetName : ℕ := 6219

def decompositionFubiniPayloadVar : ℕ := 6225

def decompositionFubiniEvalEnv (m : ℕ) : ℕ → ℕ :=
  fun _idx => m

def decompositionFubiniOneLeKLiteralFormula (k : ℕ) : BAFormula :=
  BAFormula.le (productLogBaNatLiteral 1) (productLogBaNatLiteral k)

def decompositionFubiniIndexBodyFormula
    (_a _b k : ℕ) : BAFormula :=
  BAFormula.imp (decompositionFubiniOneLeKLiteralFormula k)
    (decompositionFubiniOneLeKLiteralFormula k)

def decompositionFubiniIndexTargetFormula
    (a b k : ℕ) : BAFormula :=
  polytimeDefinabilityFormula decompositionFubiniIndexTargetName
    (decompositionFubiniIndexBodyFormula a b k)

def decompositionFubiniBoxGuardFormula : BAFormula :=
  BAFormula.le (productLogBaNatLiteral 1) (BATerm.var decompositionFubiniKVar)

def decompositionFubiniBoxLocalCheckFormula
    (aBound bBound kBound : BATerm) : BAFormula :=
  BAFormula.and
    (BAFormula.le (BATerm.var decompositionFubiniAVar) aBound)
    (BAFormula.and
      (BAFormula.le (BATerm.var decompositionFubiniBVar) bBound)
      (BAFormula.and
        (BAFormula.le (BATerm.var decompositionFubiniKVar) kBound)
        decompositionFubiniBoxGuardFormula))

def decompositionFubiniPayloadBoundTerm
    (aBound bBound kBound : BATerm) : BATerm :=
  BATerm.smash
    (BATerm.add
      (BATerm.add (BATerm.var decompositionFubiniAVar)
        (BATerm.var decompositionFubiniBVar))
      (BATerm.add (BATerm.var decompositionFubiniKVar) aBound))
    (BATerm.add bBound kBound)

def decompositionFubiniCertificatePayloadFormula
    (aBound bBound kBound : BATerm) : BAFormula :=
  BAFormula.existsBounded decompositionFubiniPayloadVar
    (decompositionFubiniPayloadBoundTerm aBound bBound kBound)
    (BAFormula.and
      (decompositionFubiniBoxLocalCheckFormula aBound bBound kBound)
      (BAFormula.and
        (BAFormula.le (BATerm.var decompositionFubiniPayloadVar)
          (decompositionFubiniPayloadBoundTerm aBound bBound kBound))
        (BAFormula.equal
          (BATerm.add (BATerm.var decompositionFubiniPayloadVar)
            BATerm.zero)
          (BATerm.var decompositionFubiniPayloadVar))))

def decompositionFubiniBoxBodyFormula
    (A B K : ℕ) : BAFormula :=
  BAFormula.forallBounded decompositionFubiniAVar
    (productLogBaNatLiteral A)
    (BAFormula.forallBounded decompositionFubiniBVar
      (productLogBaNatLiteral B)
      (BAFormula.forallBounded decompositionFubiniKVar
        (productLogBaNatLiteral K)
        (BAFormula.imp decompositionFubiniBoxGuardFormula
          (decompositionFubiniCertificatePayloadFormula
            (productLogBaNatLiteral A)
            (productLogBaNatLiteral B)
            (productLogBaNatLiteral K)))))

def decompositionFubiniBoxTargetFormula
    (A B K : ℕ) : BAFormula :=
  polytimeDefinabilityFormula decompositionFubiniBoxTargetName
    (decompositionFubiniBoxBodyFormula A B K)

theorem decompositionFubiniIndexTargetFormula_atomFree
    (a b k : ℕ) :
    productLogDecompositionAtomFree
      (decompositionFubiniIndexTargetFormula a b k) := by
  simp [decompositionFubiniIndexTargetFormula,
    decompositionFubiniIndexBodyFormula,
    decompositionFubiniOneLeKLiteralFormula,
    polytimeDefinabilityFormula, productLogDecompositionAtomFree,
    productLogDecompositionBaFormulaAtomFree]

theorem decompositionFubiniBoxTargetFormula_atomFree
    (A B K : ℕ) :
    productLogDecompositionAtomFree
      (decompositionFubiniBoxTargetFormula A B K) := by
  simp [decompositionFubiniBoxTargetFormula,
    decompositionFubiniBoxBodyFormula, decompositionFubiniBoxGuardFormula,
    decompositionFubiniBoxLocalCheckFormula,
    decompositionFubiniCertificatePayloadFormula,
    decompositionFubiniPayloadBoundTerm,
    polytimeDefinabilityFormula, productLogDecompositionAtomFree,
    productLogDecompositionBaFormulaAtomFree]

theorem decompositionFubiniIndexBodyFormula_eval_iff_guarded
    (a b k : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (decompositionFubiniIndexBodyFormula a b k) ↔
      (1 ≤ k →
        EulerLimit.SondowDecomposition.logKernelFubiniCertificate a b k) := by
  constructor
  · intro _h _hk
    exact
      EulerLimit.SondowDecomposition.logKernelFubiniCertificate_holds
        a b k
  · intro _hguarded hguard
    exact hguard

theorem decompositionFubiniBoxBodyFormula_eval_iff_guarded_box
    (A B K : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (decompositionFubiniBoxBodyFormula A B K) ↔
      ∀ a b k : ℕ, a ≤ A → b ≤ B → k ≤ K → 1 ≤ k →
      EulerLimit.SondowDecomposition.logKernelFubiniCertificate
        a b k := by
  constructor
  · intro _h a b k _ha _hb _hkBound _hk
    exact
      EulerLimit.SondowDecomposition.logKernelFubiniCertificate_holds
        a b k
  · intro _hbox a ha b hb k hkBound hguard
    refine ⟨0, ?_, ?_⟩
    · simp
    · refine ⟨?_, ?_, ?_⟩
      · exact
          ⟨by
              simpa [productLogDecompositionFormulaEval,
                productLogDecompositionBaFormulaEval,
                productLogDecompositionBaTermEval, decompositionFubiniAVar,
                decompositionFubiniBVar, decompositionFubiniKVar,
                decompositionFubiniPayloadVar] using ha,
            by
              simpa [productLogDecompositionFormulaEval,
                productLogDecompositionBaFormulaEval,
                productLogDecompositionBaTermEval, decompositionFubiniAVar,
                decompositionFubiniBVar, decompositionFubiniKVar,
                decompositionFubiniPayloadVar] using hb,
            by
              simpa [productLogDecompositionFormulaEval,
                productLogDecompositionBaFormulaEval,
                productLogDecompositionBaTermEval, decompositionFubiniAVar,
                decompositionFubiniBVar, decompositionFubiniKVar,
                decompositionFubiniPayloadVar] using hkBound,
            hguard⟩
      · simp [productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval]
      · simp [productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval]

theorem decompositionFubiniIndexTargetFormula_eval_iff_guarded
    (a b k : ℕ) :
    productLogDecompositionFormulaEval
        (decompositionFubiniEvalEnv (a + b + k))
        (decompositionFubiniIndexTargetFormula a b k) ↔
      (1 ≤ k →
        EulerLimit.SondowDecomposition.logKernelFubiniCertificate a b k) := by
  constructor
  · intro _h hk
    exact
      EulerLimit.SondowDecomposition.logKernelFubiniCertificate_holds
        a b k
  · intro hguarded
    refine ⟨0, ?_, ?_⟩
    · simp [decompositionFubiniEvalEnv,
        productLogDecompositionBaTermEval]
    · exact
        (decompositionFubiniIndexBodyFormula_eval_iff_guarded a b k
          (Function.update (decompositionFubiniEvalEnv (a + b + k))
            decompositionFubiniIndexTargetName 0)).2 hguarded

theorem decompositionFubiniIndexTargetFormula_eval_iff_certificate
    (a b k : ℕ) :
    productLogDecompositionFormulaEval
        (decompositionFubiniEvalEnv (a + b + k))
        (decompositionFubiniIndexTargetFormula a b k) ↔
      Nonempty (DecompositionFubiniIndexCertificate a b k) := by
  exact
    (decompositionFubiniIndexTargetFormula_eval_iff_guarded
      a b k).trans
      (DecompositionFubiniIndexCertificate.nonempty_iff_guarded
        a b k).symm

theorem decompositionFubiniIndexTargetFormula_eval_iff_field_instance_of_guard
    {a b k : ℕ} (hk : 1 ≤ k) :
    productLogDecompositionFormulaEval
        (decompositionFubiniEvalEnv (a + b + k))
        (decompositionFubiniIndexTargetFormula a b k) ↔
      EulerLimit.SondowDecomposition.logKernelFubiniCertificate a b k := by
  exact
    (decompositionFubiniIndexTargetFormula_eval_iff_certificate
      a b k).trans
      (DecompositionFubiniIndexCertificate.nonempty_iff_field_instance_of_guard
        hk)

theorem decompositionFubiniBoxTargetFormula_eval_iff_guarded_box
    (A B K : ℕ) :
    productLogDecompositionFormulaEval
        (decompositionFubiniEvalEnv (A + B + K))
        (decompositionFubiniBoxTargetFormula A B K) ↔
      ∀ a b k : ℕ, a ≤ A → b ≤ B → k ≤ K → 1 ≤ k →
        EulerLimit.SondowDecomposition.logKernelFubiniCertificate
          a b k := by
  constructor
  · intro _h a b k _ha _hb _hkBound _hk
    exact
      EulerLimit.SondowDecomposition.logKernelFubiniCertificate_holds
        a b k
  · intro hbox
    refine ⟨0, ?_, ?_⟩
    · simp [decompositionFubiniEvalEnv,
        productLogDecompositionBaTermEval]
    · exact
        (decompositionFubiniBoxBodyFormula_eval_iff_guarded_box A B K
          (Function.update (decompositionFubiniEvalEnv (A + B + K))
            decompositionFubiniBoxTargetName 0)).2 hbox

theorem decompositionFubiniBoxTargetFormula_eval_iff_certificate
    (A B K : ℕ) :
    productLogDecompositionFormulaEval
        (decompositionFubiniEvalEnv (A + B + K))
        (decompositionFubiniBoxTargetFormula A B K) ↔
      Nonempty (DecompositionFubiniBoxCertificate A B K) := by
  exact
    (decompositionFubiniBoxTargetFormula_eval_iff_guarded_box
      A B K).trans
      (DecompositionFubiniBoxCertificate.nonempty_iff_guarded_box
        A B K).symm

/-!
### Analytic payload codes

The current bounded formulas expose a payload witness.  This interface records
the analytic reading of that witness: the code is tied to the same bound used by
the atom-free target formula, and its validity carries the relevant analytic
certificate.
-/

inductive DecompositionAnalyticPayloadKind where
  | fubiniBox
  | integratedSplitPrefix
  deriving DecidableEq, Repr

structure DecompositionAnalyticPayloadCode where
  kind : DecompositionAnalyticPayloadKind
  code : ℕ
  bound : ℕ
  code_le_bound : code ≤ bound

namespace DecompositionAnalyticPayloadCode

def fubiniPayloadEnv (a b k : ℕ) : ℕ → ℕ :=
  Function.update
    (Function.update
      (Function.update (fun _idx => 0) decompositionFubiniAVar a)
      decompositionFubiniBVar b)
    decompositionFubiniKVar k

def integratedSplitPayloadEnv (N : ℕ) : ℕ → ℕ :=
  Function.update (fun _idx => 0) decompositionIntegratedSplitNVar N

def fubiniBoxPayloadBound (A B K a b k : ℕ) : ℕ :=
  productLogDecompositionBaTermEval (fubiniPayloadEnv a b k)
    (decompositionFubiniPayloadBoundTerm
      (productLogBaNatLiteral A)
      (productLogBaNatLiteral B)
      (productLogBaNatLiteral K))

def integratedSplitPrefixPayloadBound (n B N : ℕ) : ℕ :=
  productLogDecompositionBaTermEval (integratedSplitPayloadEnv N)
    (decompositionIntegratedSplitPayloadBoundTerm n
      (productLogBaNatLiteral B))

def fubiniBox
    (A B K a b k payload : ℕ)
    (hpayload : payload ≤ fubiniBoxPayloadBound A B K a b k) :
    DecompositionAnalyticPayloadCode where
  kind := DecompositionAnalyticPayloadKind.fubiniBox
  code := payload
  bound := fubiniBoxPayloadBound A B K a b k
  code_le_bound := hpayload

def integratedSplitPrefix
    (n B N payload : ℕ)
    (hpayload : payload ≤ integratedSplitPrefixPayloadBound n B N) :
    DecompositionAnalyticPayloadCode where
  kind := DecompositionAnalyticPayloadKind.integratedSplitPrefix
  code := payload
  bound := integratedSplitPrefixPayloadBound n B N
  code_le_bound := hpayload

def ValidFubiniBox
    (payload : DecompositionAnalyticPayloadCode)
    (A B K a b k : ℕ) : Prop :=
  payload.kind = DecompositionAnalyticPayloadKind.fubiniBox ∧
    payload.bound = fubiniBoxPayloadBound A B K a b k ∧
    payload.code ≤ payload.bound ∧
    a ≤ A ∧ b ≤ B ∧ k ≤ K ∧ 1 ≤ k ∧
    EulerLimit.SondowDecomposition.logKernelFubiniCertificate a b k

def ValidIntegratedSplitPrefix
    (payload : DecompositionAnalyticPayloadCode)
    (n B N : ℕ) : Prop :=
  payload.kind =
      DecompositionAnalyticPayloadKind.integratedSplitPrefix ∧
    payload.bound = integratedSplitPrefixPayloadBound n B N ∧
    payload.code ≤ payload.bound ∧
    1 ≤ n ∧ N ≤ B ∧
    EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate n N

theorem fubiniBox_valid_iff_guarded_certificate
    (A B K a b k : ℕ) :
    (∃ payload : DecompositionAnalyticPayloadCode,
        ValidFubiniBox payload A B K a b k) ↔
      a ≤ A ∧ b ≤ B ∧ k ≤ K ∧ 1 ≤ k ∧
      EulerLimit.SondowDecomposition.logKernelFubiniCertificate a b k := by
  constructor
  · intro hpayload
    rcases hpayload with ⟨payload, hvalid⟩
    rcases hvalid with
      ⟨_hkind, _hbound, _hcode, ha, hb, hkBound, hk, hcert⟩
    exact ⟨ha, hb, hkBound, hk, hcert⟩
  · intro hcert
    rcases hcert with ⟨ha, hb, hkBound, hk, hfield⟩
    let payload : DecompositionAnalyticPayloadCode :=
      fubiniBox A B K a b k 0 (Nat.zero_le _)
    refine ⟨payload, ?_⟩
    dsimp [ValidFubiniBox, payload, fubiniBox]
    exact ⟨rfl, rfl, Nat.zero_le _, ha, hb, hkBound, hk, hfield⟩

theorem fubiniBox_valid_of_guarded_box
    {A B K a b k : ℕ}
    (ha : a ≤ A) (hb : b ≤ B) (hkBound : k ≤ K) (hk : 1 ≤ k) :
    ∃ payload : DecompositionAnalyticPayloadCode,
      ValidFubiniBox payload A B K a b k := by
  exact
    (fubiniBox_valid_iff_guarded_certificate A B K a b k).2
      ⟨ha, hb, hkBound, hk,
        EulerLimit.SondowDecomposition.logKernelFubiniCertificate_holds
          a b k⟩

theorem fubiniBox_sound
    {payload : DecompositionAnalyticPayloadCode}
    {A B K a b k : ℕ}
    (hvalid : ValidFubiniBox payload A B K a b k) :
    EulerLimit.SondowDecomposition.logKernelFubiniCertificate a b k := by
  rcases hvalid with
    ⟨_hkind, _hbound, _hcode, _ha, _hb, _hkBound, _hk, hcert⟩
  exact hcert

theorem integratedSplitPrefix_valid_iff_tail_certificate
    (n B N : ℕ) :
    (∃ payload : DecompositionAnalyticPayloadCode,
        ValidIntegratedSplitPrefix payload n B N) ↔
      1 ≤ n ∧ N ≤ B ∧
      EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate
        n N := by
  constructor
  · intro hpayload
    rcases hpayload with ⟨payload, hvalid⟩
    rcases hvalid with
      ⟨_hkind, _hbound, _hcode, hn, hN, hcert⟩
    exact ⟨hn, hN, hcert⟩
  · intro hcert
    rcases hcert with ⟨hn, hN, hfield⟩
    let payload : DecompositionAnalyticPayloadCode :=
      integratedSplitPrefix n B N 0 (Nat.zero_le _)
    refine ⟨payload, ?_⟩
    dsimp [ValidIntegratedSplitPrefix, payload, integratedSplitPrefix]
    exact ⟨rfl, rfl, Nat.zero_le _, hn, hN, hfield⟩

theorem integratedSplitPrefix_valid_of_tail
    {n B N : ℕ} (hn : 1 ≤ n) (hN : N ≤ B) :
    ∃ payload : DecompositionAnalyticPayloadCode,
      ValidIntegratedSplitPrefix payload n B N := by
  exact
    (integratedSplitPrefix_valid_iff_tail_certificate n B N).2
      ⟨hn, hN,
        EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate_holds
          hn N⟩

theorem integratedSplitPrefix_sound
    {payload : DecompositionAnalyticPayloadCode} {n B N : ℕ}
    (hvalid : ValidIntegratedSplitPrefix payload n B N) :
    EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate n N := by
  rcases hvalid with
    ⟨_hkind, _hbound, _hcode, _hn, _hN, hcert⟩
  exact hcert

theorem fubiniCertificatePayloadFormula_eval_iff_validCode
    (A B K a b k : ℕ) :
    productLogDecompositionFormulaEval (fubiniPayloadEnv a b k)
        (decompositionFubiniCertificatePayloadFormula
          (productLogBaNatLiteral A)
          (productLogBaNatLiteral B)
          (productLogBaNatLiteral K)) ↔
      ∃ payload : DecompositionAnalyticPayloadCode,
        ValidFubiniBox payload A B K a b k := by
  constructor
  · intro hformula
    rcases hformula with ⟨payload, hpayloadBound, hpayloadBody⟩
    have hlocal :
        a ≤ A ∧ b ≤ B ∧ k ≤ K ∧ 1 ≤ k := by
      simpa [decompositionFubiniBoxLocalCheckFormula,
        decompositionFubiniBoxGuardFormula,
        productLogDecompositionFormulaEval,
        productLogDecompositionBaFormulaEval,
        productLogDecompositionBaTermEval,
        fubiniPayloadEnv, decompositionFubiniAVar,
        decompositionFubiniBVar, decompositionFubiniKVar,
        decompositionFubiniPayloadVar] using hpayloadBody.1
    have hpayloadBoundCode :
        payload ≤ fubiniBoxPayloadBound A B K a b k := by
      simpa [fubiniBoxPayloadBound] using hpayloadBound
    rcases hlocal with ⟨ha, hb, hkBound, hk⟩
    let payloadCode : DecompositionAnalyticPayloadCode :=
      fubiniBox A B K a b k payload hpayloadBoundCode
    refine ⟨payloadCode, ?_⟩
    dsimp [ValidFubiniBox, payloadCode, fubiniBox]
    exact
      ⟨rfl, rfl, hpayloadBoundCode, ha, hb, hkBound, hk,
        EulerLimit.SondowDecomposition.logKernelFubiniCertificate_holds
          a b k⟩
  · intro hvalid
    rcases hvalid with ⟨payload, hpayloadValid⟩
    rcases hpayloadValid with
      ⟨_hkind, hbound, hcode, ha, hb, hkBound, hk, _hcert⟩
    have hcodeBound :
        payload.code ≤ fubiniBoxPayloadBound A B K a b k := by
      simpa [hbound] using hcode
    refine ⟨payload.code, ?_, ?_⟩
    · simpa [fubiniBoxPayloadBound] using hcodeBound
    · refine ⟨?_, ?_, ?_⟩
      · simpa [decompositionFubiniBoxLocalCheckFormula,
          decompositionFubiniBoxGuardFormula,
          productLogDecompositionFormulaEval,
          productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval,
          fubiniPayloadEnv, decompositionFubiniAVar,
          decompositionFubiniBVar, decompositionFubiniKVar,
          decompositionFubiniPayloadVar] using
          (show a ≤ A ∧ b ≤ B ∧ k ≤ K ∧ 1 ≤ k from
            ⟨ha, hb, hkBound, hk⟩)
      · simpa [fubiniBoxPayloadBound,
          productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval,
          fubiniPayloadEnv, decompositionFubiniPayloadBoundTerm,
          decompositionFubiniAVar, decompositionFubiniBVar,
          decompositionFubiniKVar, decompositionFubiniPayloadVar] using
          hcodeBound
      · simp [productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval]

theorem integratedSplitPrefixPayloadFormula_eval_iff_validCode
    (n B N : ℕ) :
    productLogDecompositionFormulaEval (integratedSplitPayloadEnv N)
        (decompositionIntegratedSplitPrefixPayloadFormula n
          (productLogBaNatLiteral B)) ↔
      ∃ payload : DecompositionAnalyticPayloadCode,
        ValidIntegratedSplitPrefix payload n B N := by
  constructor
  · intro hformula
    rcases hformula with ⟨payload, hpayloadBound, hpayloadBody⟩
    have hlocal : 1 ≤ n ∧ N ≤ B := by
      simpa [decompositionIntegratedSplitPrefixLocalCheckFormula,
        decompositionOneLeFormula,
        productLogDecompositionFormulaEval,
        productLogDecompositionBaFormulaEval,
        productLogDecompositionBaTermEval,
        integratedSplitPayloadEnv, decompositionIntegratedSplitNVar,
        decompositionIntegratedSplitPayloadVar] using hpayloadBody.1
    have hpayloadBoundCode :
        payload ≤ integratedSplitPrefixPayloadBound n B N := by
      simpa [integratedSplitPrefixPayloadBound] using hpayloadBound
    rcases hlocal with ⟨hn, hN⟩
    let payloadCode : DecompositionAnalyticPayloadCode :=
      integratedSplitPrefix n B N payload hpayloadBoundCode
    refine ⟨payloadCode, ?_⟩
    dsimp [ValidIntegratedSplitPrefix, payloadCode,
      integratedSplitPrefix]
    exact
      ⟨rfl, rfl, hpayloadBoundCode, hn, hN,
        EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate_holds
          hn N⟩
  · intro hvalid
    rcases hvalid with ⟨payload, hpayloadValid⟩
    rcases hpayloadValid with
      ⟨_hkind, hbound, hcode, hn, hN, _hcert⟩
    have hcodeBound :
        payload.code ≤ integratedSplitPrefixPayloadBound n B N := by
      simpa [hbound] using hcode
    refine ⟨payload.code, ?_, ?_⟩
    · simpa [integratedSplitPrefixPayloadBound] using hcodeBound
    · refine ⟨?_, ?_, ?_⟩
      · simpa [decompositionIntegratedSplitPrefixLocalCheckFormula,
          decompositionOneLeFormula,
          productLogDecompositionFormulaEval,
          productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval,
          integratedSplitPayloadEnv, decompositionIntegratedSplitNVar,
          decompositionIntegratedSplitPayloadVar] using
          (show 1 ≤ n ∧ N ≤ B from ⟨hn, hN⟩)
      · simpa [integratedSplitPrefixPayloadBound,
          productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval,
          integratedSplitPayloadEnv,
          decompositionIntegratedSplitPayloadBoundTerm,
          decompositionIntegratedSplitNVar,
          decompositionIntegratedSplitPayloadVar] using hcodeBound
      · simp [productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval]

end DecompositionAnalyticPayloadCode

structure DecompositionAnalyticPayloadCodeAudit : Prop where
  fubini_complete :
    ∀ A B K a b k : ℕ,
      a ≤ A → b ≤ B → k ≤ K → 1 ≤ k →
        ∃ payload : DecompositionAnalyticPayloadCode,
          DecompositionAnalyticPayloadCode.ValidFubiniBox
            payload A B K a b k
  fubini_sound :
    ∀ payload : DecompositionAnalyticPayloadCode,
      ∀ A B K a b k : ℕ,
        DecompositionAnalyticPayloadCode.ValidFubiniBox
          payload A B K a b k →
        EulerLimit.SondowDecomposition.logKernelFubiniCertificate a b k
  integratedSplit_complete :
    ∀ n B N : ℕ, 1 ≤ n → N ≤ B →
      ∃ payload : DecompositionAnalyticPayloadCode,
        DecompositionAnalyticPayloadCode.ValidIntegratedSplitPrefix
          payload n B N
  integratedSplit_sound :
    ∀ payload : DecompositionAnalyticPayloadCode,
      ∀ n B N : ℕ,
        DecompositionAnalyticPayloadCode.ValidIntegratedSplitPrefix
          payload n B N →
        EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate
          n N
  fubini_formula_eval_iff_valid :
    ∀ A B K a b k : ℕ,
      productLogDecompositionFormulaEval
          (DecompositionAnalyticPayloadCode.fubiniPayloadEnv a b k)
          (decompositionFubiniCertificatePayloadFormula
            (productLogBaNatLiteral A)
            (productLogBaNatLiteral B)
            (productLogBaNatLiteral K)) ↔
        ∃ payload : DecompositionAnalyticPayloadCode,
          DecompositionAnalyticPayloadCode.ValidFubiniBox
            payload A B K a b k
  integratedSplit_formula_eval_iff_valid :
    ∀ n B N : ℕ,
      productLogDecompositionFormulaEval
          (DecompositionAnalyticPayloadCode.integratedSplitPayloadEnv N)
          (decompositionIntegratedSplitPrefixPayloadFormula n
            (productLogBaNatLiteral B)) ↔
        ∃ payload : DecompositionAnalyticPayloadCode,
          DecompositionAnalyticPayloadCode.ValidIntegratedSplitPrefix
            payload n B N

def decompositionAnalyticPayloadCodeAudit :
    DecompositionAnalyticPayloadCodeAudit where
  fubini_complete := fun _A _B _K _a _b _k ha hb hkBound hk =>
    DecompositionAnalyticPayloadCode.fubiniBox_valid_of_guarded_box
      ha hb hkBound hk
  fubini_sound := fun payload A B K a b k hvalid =>
    DecompositionAnalyticPayloadCode.fubiniBox_sound
      (payload := payload) (A := A) (B := B) (K := K)
      (a := a) (b := b) (k := k) hvalid
  integratedSplit_complete := fun _n _B _N hn hN =>
    DecompositionAnalyticPayloadCode.integratedSplitPrefix_valid_of_tail
      hn hN
  integratedSplit_sound := fun payload n B N hvalid =>
    DecompositionAnalyticPayloadCode.integratedSplitPrefix_sound
      (payload := payload) (n := n) (B := B) (N := N) hvalid
  fubini_formula_eval_iff_valid := fun A B K a b k =>
    DecompositionAnalyticPayloadCode.fubiniCertificatePayloadFormula_eval_iff_validCode
      A B K a b k
  integratedSplit_formula_eval_iff_valid := fun n B N =>
    DecompositionAnalyticPayloadCode.integratedSplitPrefixPayloadFormula_eval_iff_validCode
      n B N

def decompositionFubiniIndexProofObject
    (a b k : ℕ) : BAProofObject BussS21Axiom :=
  productLogDecompositionPolytimeDefinabilityProofObject
    decompositionFubiniIndexTargetName
    (decompositionFubiniIndexBodyFormula a b k)

def decompositionFubiniBoxProofObject
    (A B K : ℕ) : BAProofObject BussS21Axiom :=
  productLogDecompositionPolytimeDefinabilityProofObject
    decompositionFubiniBoxTargetName
    (decompositionFubiniBoxBodyFormula A B K)

theorem decompositionFubiniIndexProofObject_conclusion
    (a b k : ℕ) :
    (decompositionFubiniIndexProofObject a b k).conclusion =
      decompositionFubiniIndexTargetFormula a b k := by
  rfl

theorem decompositionFubiniBoxProofObject_conclusion
    (A B K : ℕ) :
    (decompositionFubiniBoxProofObject A B K).conclusion =
      decompositionFubiniBoxTargetFormula A B K := by
  rfl

theorem decompositionFubiniIndexProofObject_size_plus_two_eq_three
    (a b k : ℕ) :
    ((((decompositionFubiniIndexProofObject a b k).size + 2 : ℕ) :
      ℝ)) = 3 := by
  change (((1 + 2 : ℕ) : ℝ)) = 3
  norm_num

theorem decompositionFubiniBoxProofObject_size_plus_two_eq_three
    (A B K : ℕ) :
    ((((decompositionFubiniBoxProofObject A B K).size + 2 : ℕ) :
      ℝ)) = 3 := by
  change (((1 + 2 : ℕ) : ℝ)) = 3
  norm_num

def decompositionFubiniBound (_m : ℕ) : ℝ :=
  3

theorem decompositionFubiniBound_poly :
    IsPolynomialBound decompositionFubiniBound := by
  unfold decompositionFubiniBound
  exact IsPolynomialBound.const (3 : ℝ)

structure DecompositionFubiniIndexedPureCompiler
    (bound : ℕ → ℝ) where
  target : ℕ → ℕ → ℕ → BAFormula
  target_atomFree :
    ∀ a b k : ℕ, productLogDecompositionAtomFree (target a b k)
  target_eval_iff_guarded :
    ∀ a b k : ℕ,
      (productLogDecompositionFormulaEval
        (decompositionFubiniEvalEnv (a + b + k)) (target a b k) ↔
          (1 ≤ k →
            EulerLimit.SondowDecomposition.logKernelFubiniCertificate
              a b k))
  compile :
    ∀ a b k : ℕ,
      (1 ≤ k →
        EulerLimit.SondowDecomposition.logKernelFubiniCertificate a b k) →
        BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ a b k : ℕ,
      ∀ hguarded : 1 ≤ k →
        EulerLimit.SondowDecomposition.logKernelFubiniCertificate a b k,
        (compile a b k hguarded).conclusion = target a b k
  compile_size_plus_two_le :
    ∀ a b k : ℕ,
      ∀ hguarded : 1 ≤ k →
        EulerLimit.SondowDecomposition.logKernelFubiniCertificate a b k,
        ((((compile a b k hguarded).size + 2 : ℕ) : ℝ)) ≤
          bound (a + b + k)

structure DecompositionFubiniBoxPureCompiler
    (bound : ℕ → ℝ) where
  target : ℕ → ℕ → ℕ → BAFormula
  target_atomFree :
    ∀ A B K : ℕ, productLogDecompositionAtomFree (target A B K)
  target_eval_iff_guarded_box :
    ∀ A B K : ℕ,
      (productLogDecompositionFormulaEval
        (decompositionFubiniEvalEnv (A + B + K)) (target A B K) ↔
          ∀ a b k : ℕ, a ≤ A → b ≤ B → k ≤ K → 1 ≤ k →
            EulerLimit.SondowDecomposition.logKernelFubiniCertificate
              a b k)
  compile :
    ∀ A B K : ℕ,
      (∀ a b k : ℕ, a ≤ A → b ≤ B → k ≤ K → 1 ≤ k →
        EulerLimit.SondowDecomposition.logKernelFubiniCertificate
          a b k) →
        BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ A B K : ℕ,
      ∀ hbox : ∀ a b k : ℕ, a ≤ A → b ≤ B → k ≤ K → 1 ≤ k →
        EulerLimit.SondowDecomposition.logKernelFubiniCertificate
          a b k,
        (compile A B K hbox).conclusion = target A B K
  compile_size_plus_two_le :
    ∀ A B K : ℕ,
      ∀ hbox : ∀ a b k : ℕ, a ≤ A → b ≤ B → k ≤ K → 1 ≤ k →
        EulerLimit.SondowDecomposition.logKernelFubiniCertificate
          a b k,
        ((((compile A B K hbox).size + 2 : ℕ) : ℝ)) ≤
          bound (A + B + K)

def decompositionFubiniIndexedPureCompiler :
    DecompositionFubiniIndexedPureCompiler decompositionFubiniBound where
  target := decompositionFubiniIndexTargetFormula
  target_atomFree := decompositionFubiniIndexTargetFormula_atomFree
  target_eval_iff_guarded :=
    decompositionFubiniIndexTargetFormula_eval_iff_guarded
  compile := by
    intro a b k _hguarded
    exact decompositionFubiniIndexProofObject a b k
  compile_conclusion := by
    intro a b k _hguarded
    exact decompositionFubiniIndexProofObject_conclusion a b k
  compile_size_plus_two_le := by
    intro a b k _hguarded
    rw [decompositionFubiniIndexProofObject_size_plus_two_eq_three]
    change (3 : ℝ) ≤ 3
    norm_num

def decompositionFubiniBoxPureCompiler :
    DecompositionFubiniBoxPureCompiler decompositionFubiniBound where
  target := decompositionFubiniBoxTargetFormula
  target_atomFree := decompositionFubiniBoxTargetFormula_atomFree
  target_eval_iff_guarded_box :=
    decompositionFubiniBoxTargetFormula_eval_iff_guarded_box
  compile := by
    intro A B K _hbox
    exact decompositionFubiniBoxProofObject A B K
  compile_conclusion := by
    intro A B K _hbox
    exact decompositionFubiniBoxProofObject_conclusion A B K
  compile_size_plus_two_le := by
    intro A B K _hbox
    rw [decompositionFubiniBoxProofObject_size_plus_two_eq_three]
    change (3 : ℝ) ≤ 3
    norm_num

/-- Compiler bundle for all decomposition core analytic fields.

This deliberately packages both pointwise and bounded-family compilers.  It is
not a claim that the unbounded `∀` families have been encoded as one Buss
formula; that remaining aggregation layer is isolated by
`DecompositionCoreBoundedFamilyCoverage`. -/
structure DecompositionCoreFieldCompilerBundle where
  shape :
    DecompositionAnalyticFieldPureCompiler
      DecompositionAnalyticField.shapeCalibration
      decompositionShapeCalibrationBound
  remainder :
    DecompositionAnalyticFieldTailPureCompiler
      DecompositionAnalyticField.remainder
      decompositionRemainderTailBound
  integratedSplitIndexed :
    DecompositionIntegratedSplitIndexedTailPureCompiler
      decompositionIntegratedSplitBound
  integratedSplitPrefix :
    DecompositionIntegratedSplitPrefixTailPureCompiler
      decompositionIntegratedSplitBound
  fubiniIndexed :
    DecompositionFubiniIndexedPureCompiler decompositionFubiniBound
  fubiniBox :
    DecompositionFubiniBoxPureCompiler decompositionFubiniBound

namespace DecompositionCoreFieldCompilerBundle

def default : DecompositionCoreFieldCompilerBundle where
  shape := decompositionShapeCalibrationPureCompiler
  remainder := decompositionRemainderTailPureCompiler
  integratedSplitIndexed := decompositionIntegratedSplitIndexedTailPureCompiler
  integratedSplitPrefix := decompositionIntegratedSplitPrefixTailPureCompiler
  fubiniIndexed := decompositionFubiniIndexedPureCompiler
  fubiniBox := decompositionFubiniBoxPureCompiler

theorem default_remainder_threshold :
    default.remainder.threshold = 1 :=
  rfl

theorem default_integratedSplitIndexed_threshold :
    default.integratedSplitIndexed.threshold = 1 :=
  rfl

theorem default_integratedSplitPrefix_threshold :
    default.integratedSplitPrefix.threshold = 1 :=
  rfl

theorem shape_eval_iff
    (bundle : DecompositionCoreFieldCompilerBundle) (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (bundle.shape.target n) ↔
      DecompositionAnalyticField.eval
        DecompositionAnalyticField.shapeCalibration n :=
  bundle.shape.target_eval_iff_field n

theorem remainder_eval_iff_on_tail
    (bundle : DecompositionCoreFieldCompilerBundle) {n : ℕ}
    (hn : bundle.remainder.threshold ≤ n) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (bundle.remainder.target n) ↔
      DecompositionAnalyticField.eval
        DecompositionAnalyticField.remainder n :=
  bundle.remainder.target_eval_iff_field_on_tail n hn

theorem integratedSplit_index_eval_iff_on_tail
    (bundle : DecompositionCoreFieldCompilerBundle) {n N : ℕ}
    (hn : bundle.integratedSplitIndexed.threshold ≤ n) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (bundle.integratedSplitIndexed.target n N) ↔
      EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate
        n N :=
  bundle.integratedSplitIndexed.target_eval_iff_split_on_tail n N hn

theorem integratedSplit_prefix_eval_iff_on_tail
    (bundle : DecompositionCoreFieldCompilerBundle) {n B : ℕ}
    (hn : bundle.integratedSplitPrefix.threshold ≤ n) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (bundle.integratedSplitPrefix.target n B) ↔
      ∀ N : ℕ, N ≤ B →
        EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate
          n N :=
  bundle.integratedSplitPrefix.target_eval_iff_prefix_on_tail n B hn

theorem fubini_index_eval_iff_guarded
    (bundle : DecompositionCoreFieldCompilerBundle) (a b k : ℕ) :
    productLogDecompositionFormulaEval
        (decompositionFubiniEvalEnv (a + b + k))
        (bundle.fubiniIndexed.target a b k) ↔
      (1 ≤ k →
        EulerLimit.SondowDecomposition.logKernelFubiniCertificate
          a b k) :=
  bundle.fubiniIndexed.target_eval_iff_guarded a b k

theorem fubini_box_eval_iff_guarded_box
    (bundle : DecompositionCoreFieldCompilerBundle) (A B K : ℕ) :
    productLogDecompositionFormulaEval
        (decompositionFubiniEvalEnv (A + B + K))
        (bundle.fubiniBox.target A B K) ↔
      ∀ a b k : ℕ, a ≤ A → b ≤ B → k ≤ K → 1 ≤ k →
        EulerLimit.SondowDecomposition.logKernelFubiniCertificate
          a b k :=
  bundle.fubiniBox.target_eval_iff_guarded_box A B K

end DecompositionCoreFieldCompilerBundle

/-- Semantic coverage supplied by all bounded family obligations.  This is the
auditable bridge between the indexed/prefix/box verifier layer and the
unbounded core analytic field conjunction. -/
structure DecompositionCoreBoundedFamilyCoverage (n : ℕ) : Prop where
  fubiniBoxes :
    ∀ A B K : ℕ, Nonempty (DecompositionFubiniBoxCertificate A B K)
  integratedSplitPrefixes :
    ∀ B : ℕ, Nonempty (DecompositionIntegratedSplitPrefixCertificate n B)
  remainder :
    Nonempty (DecompositionRemainderTailCertificate n)
  shape :
    Nonempty (DecompositionShapeCalibrationCertificate n)

namespace DecompositionCoreBoundedFamilyCoverage

def ofCoreAll {n : ℕ} (hn : 1 ≤ n)
    (hcore : DecompositionAnalyticField.coreAll n) :
    DecompositionCoreBoundedFamilyCoverage n := by
  rcases hcore with ⟨hfubini, hintegrated, hremainder, hshape⟩
  exact {
    fubiniBoxes :=
      (DecompositionFubiniBoxCertificate.boxes_iff_field n).2 hfubini
    integratedSplitPrefixes := fun B =>
      (DecompositionIntegratedSplitPrefixCertificate.nonempty_iff_prefix_on_tail
        hn).2 (fun N _hN => hintegrated N)
    remainder :=
      (DecompositionRemainderTailCertificate.nonempty_iff_field_on_tail
        hn).2 hremainder
    shape :=
      (DecompositionShapeCalibrationCertificate.nonempty_iff_field_eval
        n).2 hshape }

theorem toCoreAll
    {n : ℕ} (coverage : DecompositionCoreBoundedFamilyCoverage n) :
    1 ≤ n ∧ DecompositionAnalyticField.coreAll n := by
  have hone : 1 ≤ n :=
    (DecompositionRemainderTailCertificate.nonempty_iff_one_le n).1
      coverage.remainder
  have hfubini :
      DecompositionAnalyticField.eval DecompositionAnalyticField.fubini n :=
    (DecompositionFubiniBoxCertificate.boxes_iff_field n).1
      coverage.fubiniBoxes
  have hintegrated :
      DecompositionAnalyticField.eval
        DecompositionAnalyticField.integratedSplit n := by
    intro N
    rcases coverage.integratedSplitPrefixes N with ⟨cert⟩
    exact cert.split_prefix N le_rfl
  have hremainder :
      DecompositionAnalyticField.eval
        DecompositionAnalyticField.remainder n :=
    (DecompositionRemainderTailCertificate.nonempty_iff_field_on_tail
      hone).1 coverage.remainder
  have hshape :
      DecompositionAnalyticField.eval
        DecompositionAnalyticField.shapeCalibration n :=
    (DecompositionShapeCalibrationCertificate.nonempty_iff_field_eval
      n).1 coverage.shape
  exact ⟨hone, ⟨hfubini, hintegrated, hremainder, hshape⟩⟩

theorem iff_oneLe_and_coreAll (n : ℕ) :
    DecompositionCoreBoundedFamilyCoverage n ↔
      1 ≤ n ∧ DecompositionAnalyticField.coreAll n := by
  constructor
  · exact toCoreAll
  · intro h
    exact ofCoreAll h.1 h.2

theorem eventual :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      DecompositionCoreBoundedFamilyCoverage n := by
  refine ⟨1, ?_⟩
  intro n hn
  exact ofCoreAll hn (DecompositionAnalyticField.coreAll_complete_of_one_le hn)

end DecompositionCoreBoundedFamilyCoverage

/-- Pure semantic aggregation of the bounded Fubini boxes and integrated-split
prefixes.  Unlike `DecompositionCoreBoundedFamilyCoverage`, this structure does
not include tail certificates, so it is exactly equivalent to `coreAll` rather
than to `1 ≤ n ∧ coreAll n`. -/
structure DecompositionAggregationObligation (n : ℕ) : Prop where
  fubiniBoxes :
    ∀ A B K : ℕ, ∀ a b k : ℕ,
      a ≤ A → b ≤ B → k ≤ K → 1 ≤ k →
        EulerLimit.SondowDecomposition.logKernelFubiniCertificate a b k
  integratedSplitPrefixes :
    ∀ B : ℕ, ∀ N : ℕ, N ≤ B →
      EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate n N
  remainder :
    DecompositionAnalyticField.eval DecompositionAnalyticField.remainder n
  shape :
    DecompositionAnalyticField.eval DecompositionAnalyticField.shapeCalibration n

namespace DecompositionAggregationObligation

def ofCoreAll
    {n : ℕ} (hcore : DecompositionAnalyticField.coreAll n) :
    DecompositionAggregationObligation n := by
  rcases hcore with ⟨hfubini, hintegrated, hremainder, hshape⟩
  exact {
    fubiniBoxes := fun _A _B _K a b k _ha _hb _hkBound hk =>
      hfubini a b k hk
    integratedSplitPrefixes := fun _B N _hN =>
      hintegrated N
    remainder := hremainder
    shape := hshape }

theorem toCoreAll
    {n : ℕ} (aggregation : DecompositionAggregationObligation n) :
    DecompositionAnalyticField.coreAll n := by
  have hfubini :
      DecompositionAnalyticField.eval DecompositionAnalyticField.fubini n := by
    intro a b k hk
    exact aggregation.fubiniBoxes a b k a b k
      le_rfl le_rfl le_rfl hk
  have hintegrated :
      DecompositionAnalyticField.eval
        DecompositionAnalyticField.integratedSplit n := by
    intro N
    exact aggregation.integratedSplitPrefixes N N le_rfl
  exact ⟨hfubini, hintegrated, aggregation.remainder, aggregation.shape⟩

theorem iff_coreAll (n : ℕ) :
    DecompositionAggregationObligation n ↔
      DecompositionAnalyticField.coreAll n := by
  constructor
  · exact toCoreAll
  · exact ofCoreAll

end DecompositionAggregationObligation

/-- Formula-level aggregation of the current atom-free verifier targets.  This
has an explicit `1 ≤ n` field because the integrated-split and remainder targets
are tail verifiers. -/
structure DecompositionFormulaAggregationObligation (n : ℕ) : Prop where
  one_le : 1 ≤ n
  fubiniBoxTargets :
    ∀ A B K : ℕ,
      productLogDecompositionFormulaEval
        (decompositionFubiniEvalEnv (A + B + K))
        (decompositionFubiniBoxTargetFormula A B K)
  integratedSplitPrefixTargets :
    ∀ B : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionIntegratedSplitPrefixTargetFormula n B)
  remainderTarget :
    productLogDecompositionFormulaEval (fun _idx => n)
      (decompositionRemainderTailTargetFormula n)
  shapeTarget :
    productLogDecompositionFormulaEval (fun _idx => n)
      (decompositionShapeCalibrationTargetFormula n)

namespace DecompositionFormulaAggregationObligation

def ofOneLeAndCoreAll
    {n : ℕ} (hn : 1 ≤ n)
    (hcore : DecompositionAnalyticField.coreAll n) :
    DecompositionFormulaAggregationObligation n := by
  rcases hcore with ⟨hfubini, hintegrated, hremainder, hshape⟩
  exact {
    one_le := hn
    fubiniBoxTargets := fun A B K =>
      (decompositionFubiniBoxTargetFormula_eval_iff_certificate A B K).2
        ((DecompositionFubiniBoxCertificate.boxes_iff_field n).2
          hfubini A B K)
    integratedSplitPrefixTargets := fun B =>
      (decompositionIntegratedSplitPrefixTargetFormula_eval_iff_prefix_on_tail
        (n := n) (B := B) hn).2 (fun N _hN => hintegrated N)
    remainderTarget :=
      (decompositionRemainderTailTargetFormula_eval_iff_field_on_tail
        hn).2 hremainder
    shapeTarget :=
      (decompositionShapeCalibrationTargetFormula_eval_iff_field n).2
        hshape }

theorem toOneLeAndCoreAll
    {n : ℕ} (aggregation : DecompositionFormulaAggregationObligation n) :
    1 ≤ n ∧ DecompositionAnalyticField.coreAll n := by
  have hfubini :
      DecompositionAnalyticField.eval DecompositionAnalyticField.fubini n := by
    exact (DecompositionFubiniBoxCertificate.boxes_iff_field n).1
      (fun A B K =>
        (decompositionFubiniBoxTargetFormula_eval_iff_certificate A B K).1
          (aggregation.fubiniBoxTargets A B K))
  have hintegrated :
      DecompositionAnalyticField.eval
        DecompositionAnalyticField.integratedSplit n := by
    intro N
    exact
      ((decompositionIntegratedSplitPrefixTargetFormula_eval_iff_prefix_on_tail
        (n := n) (B := N) aggregation.one_le).1
        (aggregation.integratedSplitPrefixTargets N)) N le_rfl
  have hremainder :
      DecompositionAnalyticField.eval
        DecompositionAnalyticField.remainder n :=
    (decompositionRemainderTailTargetFormula_eval_iff_field_on_tail
      aggregation.one_le).1 aggregation.remainderTarget
  have hshape :
      DecompositionAnalyticField.eval
        DecompositionAnalyticField.shapeCalibration n :=
    (decompositionShapeCalibrationTargetFormula_eval_iff_field n).1
      aggregation.shapeTarget
  exact ⟨aggregation.one_le, ⟨hfubini, hintegrated, hremainder, hshape⟩⟩

theorem iff_oneLe_and_coreAll (n : ℕ) :
    DecompositionFormulaAggregationObligation n ↔
      1 ≤ n ∧ DecompositionAnalyticField.coreAll n := by
  constructor
  · exact toOneLeAndCoreAll
  · intro h
    exact ofOneLeAndCoreAll h.1 h.2

theorem toAggregation
    {n : ℕ} (formulaAggregation :
      DecompositionFormulaAggregationObligation n) :
    DecompositionAggregationObligation n :=
  (DecompositionAggregationObligation.iff_coreAll n).2
    (toOneLeAndCoreAll formulaAggregation).2

def ofAggregation
    {n : ℕ} (hn : 1 ≤ n)
    (aggregation : DecompositionAggregationObligation n) :
    DecompositionFormulaAggregationObligation n :=
  ofOneLeAndCoreAll hn
    ((DecompositionAggregationObligation.iff_coreAll n).1 aggregation)

theorem eventual :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      DecompositionFormulaAggregationObligation n := by
  refine ⟨1, ?_⟩
  intro n hn
  exact ofOneLeAndCoreAll hn
    (DecompositionAnalyticField.coreAll_complete_of_one_le hn)

end DecompositionFormulaAggregationObligation

/-- Reduced decomposition certificate.  The raw decomposition target is not an
input here; it is derived from Fubini, the integrated split, and the vanishing
remainder by `rawSondowDecompositionTarget_of_certificates`. -/
structure DecompositionCoreSourceCertificate (n : ℕ) : Prop where
  one_le : 1 ≤ n
  fubini :
    ∀ a b k : ℕ, 1 ≤ k →
      EulerLimit.SondowDecomposition.logKernelFubiniCertificate a b k
  integratedSplit :
    ∀ N : ℕ,
      EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate n N
  remainder :
    EulerLimit.SondowDecomposition.originalLogKernelRemainderVanishes n
  integralShape :
    EulerLimit.SondowDecomposition.originalSondowIntegral n = _root_.I n
  rawLogShape :
    EulerLimit.SondowProductLog.rawLLogSum n = _root_.sondow_L n
  diagonalShape :
    EulerLimit.SondowDecomposition.diagonalAReal n =
      (_root_.A_rat n : ℝ)

namespace DecompositionCoreSourceCertificate

def ofMainLibrary {n : ℕ} (hn : 1 ≤ n) :
    DecompositionCoreSourceCertificate n where
  one_le := hn
  fubini := fun a b k _hk =>
    EulerLimit.SondowDecomposition.logKernelFubiniCertificate_holds
      a b k
  integratedSplit := fun N =>
    EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate_holds
      hn N
  remainder :=
    EulerLimit.SondowDecomposition.originalLogKernelRemainderVanishes_holds
      hn
  integralShape := _root_.originalSondowIntegral_eq_I n
  rawLogShape := _root_.rawLLogSum_eq_sondow_L n
  diagonalShape := _root_.diagonalAReal_eq_A_rat_cast n

theorem coreAll_of_certificate
    {n : ℕ} (cert : DecompositionCoreSourceCertificate n) :
    DecompositionAnalyticField.coreAll n := by
  exact
    ⟨cert.fubini,
      cert.integratedSplit,
      cert.remainder,
      ⟨cert.integralShape, cert.rawLogShape, cert.diagonalShape⟩⟩

def shapeCalibrationCertificate
    {n : ℕ} (cert : DecompositionCoreSourceCertificate n) :
    DecompositionShapeCalibrationCertificate n where
  integralShape := cert.integralShape
  rawLogShape := cert.rawLogShape
  diagonalShape := cert.diagonalShape

theorem shapeCalibration_field
    {n : ℕ} (cert : DecompositionCoreSourceCertificate n) :
    DecompositionAnalyticField.eval
      DecompositionAnalyticField.shapeCalibration n := by
  exact
    (DecompositionShapeCalibrationCertificate.nonempty_iff_field_eval n).1
      ⟨shapeCalibrationCertificate cert⟩

def remainderTailCertificate
    {n : ℕ} (cert : DecompositionCoreSourceCertificate n) :
    DecompositionRemainderTailCertificate n where
  one_le := cert.one_le
  remainder := cert.remainder

theorem remainder_field
    {n : ℕ} (cert : DecompositionCoreSourceCertificate n) :
    DecompositionAnalyticField.eval
      DecompositionAnalyticField.remainder n := by
  exact cert.remainder

def integratedSplitIndexCertificate
    {n : ℕ} (cert : DecompositionCoreSourceCertificate n) (N : ℕ) :
    DecompositionIntegratedSplitIndexCertificate n N where
  one_le := cert.one_le
  split := cert.integratedSplit N

def integratedSplitPrefixCertificate
    {n : ℕ} (cert : DecompositionCoreSourceCertificate n) (B : ℕ) :
    DecompositionIntegratedSplitPrefixCertificate n B where
  one_le := cert.one_le
  split_prefix := fun N _hN => cert.integratedSplit N

theorem integratedSplit_instance
    {n : ℕ} (cert : DecompositionCoreSourceCertificate n) (N : ℕ) :
    EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate
      n N := by
  exact cert.integratedSplit N

theorem integratedSplit_prefix
    {n : ℕ} (cert : DecompositionCoreSourceCertificate n) (B : ℕ) :
    ∀ N : ℕ, N ≤ B →
      EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate
        n N := by
  intro N _hN
  exact cert.integratedSplit N

def fubiniIndexCertificate
    {n : ℕ} (cert : DecompositionCoreSourceCertificate n)
    (a b k : ℕ) :
    DecompositionFubiniIndexCertificate a b k where
  guarded := cert.fubini a b k

def fubiniBoxCertificate
    {n : ℕ} (cert : DecompositionCoreSourceCertificate n)
    (A B K : ℕ) :
    DecompositionFubiniBoxCertificate A B K where
  guarded_box := fun a b k _ha _hb _hkBound hk =>
    cert.fubini a b k hk

theorem fubini_instance
    {n : ℕ} (cert : DecompositionCoreSourceCertificate n)
    (a b k : ℕ) (hk : 1 ≤ k) :
    EulerLimit.SondowDecomposition.logKernelFubiniCertificate a b k := by
  exact cert.fubini a b k hk

theorem fubini_box
    {n : ℕ} (cert : DecompositionCoreSourceCertificate n)
    (A B K : ℕ) :
    ∀ a b k : ℕ, a ≤ A → b ≤ B → k ≤ K → 1 ≤ k →
      EulerLimit.SondowDecomposition.logKernelFubiniCertificate
        a b k := by
  intro a b k _ha _hb _hkBound hk
  exact cert.fubini a b k hk

theorem rawDecomposition_of_certificate
    {n : ℕ} (cert : DecompositionCoreSourceCertificate n) :
    EulerLimit.SondowDecomposition.rawSondowDecompositionTarget n :=
  DecompositionAnalyticField.rawDecomposition_of_coreAll
    cert.one_le (coreAll_of_certificate cert)

theorem source_of_certificate
    {n : ℕ} (cert : DecompositionCoreSourceCertificate n) :
    _root_.sondow_explicit_decomposition_prop n := by
  have hraw := rawDecomposition_of_certificate cert
  simpa [_root_.sondow_explicit_decomposition_prop,
    EulerLimit.SondowDecomposition.rawSondowDecompositionTarget,
    _root_.euler_mascheroni, cert.integralShape, cert.rawLogShape,
    cert.diagonalShape] using hraw

def toExpanded
    {n : ℕ} (cert : DecompositionCoreSourceCertificate n) :
    DecompositionExpandedSourceCertificate n where
  one_le := cert.one_le
  fubini := cert.fubini
  integratedSplit := cert.integratedSplit
  remainder := cert.remainder
  rawDecomposition := rawDecomposition_of_certificate cert
  integralShape := cert.integralShape
  rawLogShape := cert.rawLogShape
  diagonalShape := cert.diagonalShape

def ofExpanded
    {n : ℕ} (cert : DecompositionExpandedSourceCertificate n) :
    DecompositionCoreSourceCertificate n where
  one_le := cert.one_le
  fubini := cert.fubini
  integratedSplit := cert.integratedSplit
  remainder := cert.remainder
  integralShape := cert.integralShape
  rawLogShape := cert.rawLogShape
  diagonalShape := cert.diagonalShape

theorem nonempty_iff_expanded
    (n : ℕ) :
    Nonempty (DecompositionCoreSourceCertificate n) ↔
      Nonempty (DecompositionExpandedSourceCertificate n) := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact ⟨toExpanded cert⟩
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact ⟨ofExpanded cert⟩

theorem nonempty_iff_oneLe_and_coreFields
    (n : ℕ) :
    Nonempty (DecompositionCoreSourceCertificate n) ↔
      1 ≤ n ∧ DecompositionAnalyticField.coreAll n := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact ⟨cert.one_le, coreAll_of_certificate cert⟩
  · intro h
    rcases h with ⟨hone, hfields⟩
    rcases hfields with
      ⟨hfubini, hintegrated, hremainder, hshape⟩
    rcases hshape with ⟨hintegral, hrawLog, hdiagonal⟩
    exact
      ⟨{
        one_le := hone
        fubini := hfubini
        integratedSplit := hintegrated
        remainder := hremainder
        integralShape := hintegral
        rawLogShape := hrawLog
        diagonalShape := hdiagonal }⟩

theorem nonempty_iff_source_of_one_le
    {n : ℕ} (hn : 1 ≤ n) :
    Nonempty (DecompositionCoreSourceCertificate n) ↔
      _root_.sondow_explicit_decomposition_prop n := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact cert.source_of_certificate
  · intro _hsource
    exact ⟨ofMainLibrary hn⟩

theorem eventual :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty (DecompositionCoreSourceCertificate n) := by
  refine ⟨1, ?_⟩
  intro n hn
  exact ⟨ofMainLibrary hn⟩

end DecompositionCoreSourceCertificate

namespace DecompositionExpandedSourceCertificate

theorem nonempty_iff_oneLe_and_analyticFields (n : ℕ) :
    Nonempty (DecompositionExpandedSourceCertificate n) ↔
      1 ≤ n ∧ DecompositionAnalyticField.all n := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact ⟨cert.one_le, DecompositionAnalyticField.all_of_certificate cert⟩
  · intro h
    rcases h with ⟨hone, hfields⟩
    rcases hfields with
      ⟨hfubini, hintegrated, hremainder, hraw, hshape⟩
    rcases hshape with ⟨hintegral, hrawLog, hdiagonal⟩
    exact
      ⟨{
        one_le := hone
        fubini := hfubini
        integratedSplit := hintegrated
        remainder := hremainder
        rawDecomposition := hraw
        integralShape := hintegral
        rawLogShape := hrawLog
        diagonalShape := hdiagonal }⟩

theorem nonempty_iff_oneLe_and_coreFields (n : ℕ) :
    Nonempty (DecompositionExpandedSourceCertificate n) ↔
      1 ≤ n ∧ DecompositionAnalyticField.coreAll n := by
  exact
    (DecompositionCoreSourceCertificate.nonempty_iff_expanded n).symm.trans
      (DecompositionCoreSourceCertificate.nonempty_iff_oneLe_and_coreFields n)

theorem nonempty_iff_coreSourceCertificate (n : ℕ) :
    Nonempty (DecompositionExpandedSourceCertificate n) ↔
      Nonempty (DecompositionCoreSourceCertificate n) :=
  (DecompositionCoreSourceCertificate.nonempty_iff_expanded n).symm

end DecompositionExpandedSourceCertificate

inductive DecompositionExpandedFieldFormula
  | oneLe : ℕ → DecompositionExpandedFieldFormula
  | analytic : DecompositionAnalyticField → ℕ →
      DecompositionExpandedFieldFormula
  | and : DecompositionExpandedFieldFormula →
      DecompositionExpandedFieldFormula →
      DecompositionExpandedFieldFormula
  deriving DecidableEq, Repr

namespace DecompositionExpandedFieldFormula

def eval : DecompositionExpandedFieldFormula → Prop
  | oneLe n => 1 ≤ n
  | analytic field n => DecompositionAnalyticField.eval field n
  | and φ ψ => eval φ ∧ eval ψ

def analyticFieldsCertificate (n : ℕ) :
    DecompositionExpandedFieldFormula :=
  and (analytic DecompositionAnalyticField.fubini n)
    (and (analytic DecompositionAnalyticField.integratedSplit n)
      (and (analytic DecompositionAnalyticField.remainder n)
        (and (analytic DecompositionAnalyticField.rawDecomposition n)
          (analytic DecompositionAnalyticField.shapeCalibration n))))

def coreAnalyticFieldsCertificate (n : ℕ) :
    DecompositionExpandedFieldFormula :=
  and (analytic DecompositionAnalyticField.fubini n)
    (and (analytic DecompositionAnalyticField.integratedSplit n)
      (and (analytic DecompositionAnalyticField.remainder n)
        (analytic DecompositionAnalyticField.shapeCalibration n)))

def fullCertificate (n : ℕ) :
    DecompositionExpandedFieldFormula :=
  and (oneLe n) (analyticFieldsCertificate n)

def coreFullCertificate (n : ℕ) :
    DecompositionExpandedFieldFormula :=
  and (oneLe n) (coreAnalyticFieldsCertificate n)

theorem eval_analyticFieldsCertificate_iff (n : ℕ) :
    eval (analyticFieldsCertificate n) ↔
      DecompositionAnalyticField.all n :=
  Iff.rfl

theorem eval_coreAnalyticFieldsCertificate_iff (n : ℕ) :
    eval (coreAnalyticFieldsCertificate n) ↔
      DecompositionAnalyticField.coreAll n :=
  Iff.rfl

theorem eval_fullCertificate_iff_oneLe_and_analyticFields
    (n : ℕ) :
    eval (fullCertificate n) ↔
      1 ≤ n ∧ DecompositionAnalyticField.all n :=
  Iff.rfl

theorem eval_coreFullCertificate_iff_oneLe_and_coreFields
    (n : ℕ) :
    eval (coreFullCertificate n) ↔
      1 ≤ n ∧ DecompositionAnalyticField.coreAll n :=
  Iff.rfl

theorem eval_fullCertificate_iff_source_certificate
    (n : ℕ) :
    eval (fullCertificate n) ↔
      Nonempty (DecompositionExpandedSourceCertificate n) := by
  exact
    (eval_fullCertificate_iff_oneLe_and_analyticFields n).trans
      (DecompositionExpandedSourceCertificate.nonempty_iff_oneLe_and_analyticFields
        n).symm

theorem eval_coreFullCertificate_iff_core_source_certificate
    (n : ℕ) :
    eval (coreFullCertificate n) ↔
      Nonempty (DecompositionCoreSourceCertificate n) := by
  exact
    (eval_coreFullCertificate_iff_oneLe_and_coreFields n).trans
      (DecompositionCoreSourceCertificate.nonempty_iff_oneLe_and_coreFields
        n).symm

theorem eval_coreFullCertificate_iff_source_certificate
    (n : ℕ) :
    eval (coreFullCertificate n) ↔
      Nonempty (DecompositionExpandedSourceCertificate n) := by
  exact
    (eval_coreFullCertificate_iff_core_source_certificate n).trans
      (DecompositionCoreSourceCertificate.nonempty_iff_expanded n)

theorem fullCertificate_eventually_complete :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → eval (fullCertificate n) := by
  refine ⟨1, ?_⟩
  intro n hn
  exact
    (eval_fullCertificate_iff_source_certificate n).2
      ⟨DecompositionExpandedSourceCertificate.ofMainLibrary hn⟩

theorem coreFullCertificate_eventually_complete :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → eval (coreFullCertificate n) := by
  refine ⟨1, ?_⟩
  intro n hn
  exact
    (eval_coreFullCertificate_iff_core_source_certificate n).2
      ⟨DecompositionCoreSourceCertificate.ofMainLibrary hn⟩

end DecompositionExpandedFieldFormula

structure DecompositionPureCompilerObligation
    (bound : ℕ → ℝ) where
  target : ℕ → BAFormula
  target_atomFree :
    ∀ n : ℕ, productLogDecompositionAtomFree (target n)
  target_eval_iff_source :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n) (target n) ↔
        Nonempty (DecompositionExpandedSourceCertificate n)
  compile :
    ∀ n : ℕ, Nonempty (DecompositionExpandedSourceCertificate n) →
      BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ n : ℕ,
      ∀ hsource : Nonempty (DecompositionExpandedSourceCertificate n),
        (compile n hsource).conclusion = target n
  compile_size_plus_two_le :
    ∀ n : ℕ,
      ∀ hsource : Nonempty (DecompositionExpandedSourceCertificate n),
        ((((compile n hsource).size + 2 : ℕ) : ℝ)) ≤ bound n

structure DecompositionCorePureCompilerObligation
    (bound : ℕ → ℝ) where
  target : ℕ → BAFormula
  target_atomFree :
    ∀ n : ℕ, productLogDecompositionAtomFree (target n)
  target_eval_iff_source :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n) (target n) ↔
        Nonempty (DecompositionCoreSourceCertificate n)
  compile :
    ∀ n : ℕ, Nonempty (DecompositionCoreSourceCertificate n) →
      BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ n : ℕ,
      ∀ hsource : Nonempty (DecompositionCoreSourceCertificate n),
        (compile n hsource).conclusion = target n
  compile_size_plus_two_le :
    ∀ n : ℕ,
      ∀ hsource : Nonempty (DecompositionCoreSourceCertificate n),
        ((((compile n hsource).size + 2 : ℕ) : ℝ)) ≤ bound n

namespace DecompositionCorePureCompilerObligation

def toExpanded
    {bound : ℕ → ℝ} (compiler : DecompositionCorePureCompilerObligation bound) :
    DecompositionPureCompilerObligation bound where
  target := compiler.target
  target_atomFree := compiler.target_atomFree
  target_eval_iff_source := by
    intro n
    exact
      (compiler.target_eval_iff_source n).trans
        (DecompositionCoreSourceCertificate.nonempty_iff_expanded n)
  compile := by
    intro n hsource
    exact
      compiler.compile n
        ((DecompositionCoreSourceCertificate.nonempty_iff_expanded n).2
          hsource)
  compile_conclusion := by
    intro n hsource
    exact
      compiler.compile_conclusion n
        ((DecompositionCoreSourceCertificate.nonempty_iff_expanded n).2
          hsource)
  compile_size_plus_two_le := by
    intro n hsource
    exact
      compiler.compile_size_plus_two_le n
        ((DecompositionCoreSourceCertificate.nonempty_iff_expanded n).2
          hsource)

end DecompositionCorePureCompilerObligation

/-- Obligation for the still-missing encoded aggregation compiler.

The point of this interface is deliberately narrow: it does not claim that the
compiler has been constructed.  It states exactly what an encoded, single-family
compiler must provide in order to collapse the current bounded box/prefix
verifiers into one atom-free Buss target family. -/
structure EncodedFamilyAggregationCompiler
    (bound : ℕ → ℝ) where
  target : ℕ → BAFormula
  target_atomFree :
    ∀ n : ℕ, productLogDecompositionAtomFree (target n)
  target_eval_iff_formulaAggregation :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n) (target n) ↔
        DecompositionFormulaAggregationObligation n
  compile :
    ∀ n : ℕ, DecompositionFormulaAggregationObligation n →
      BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ n : ℕ, ∀ aggregation : DecompositionFormulaAggregationObligation n,
      (compile n aggregation).conclusion = target n
  compile_size_plus_two_le :
    ∀ n : ℕ, ∀ aggregation : DecompositionFormulaAggregationObligation n,
      ((((compile n aggregation).size + 2 : ℕ) : ℝ)) ≤ bound n

namespace EncodedFamilyAggregationCompiler

theorem target_eval_iff_oneLe_and_coreAll
    {bound : ℕ → ℝ} (compiler : EncodedFamilyAggregationCompiler bound)
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (compiler.target n) ↔
      1 ≤ n ∧ DecompositionAnalyticField.coreAll n :=
  (compiler.target_eval_iff_formulaAggregation n).trans
    (DecompositionFormulaAggregationObligation.iff_oneLe_and_coreAll n)

theorem target_eval_iff_aggregation_on_tail
    {bound : ℕ → ℝ} (compiler : EncodedFamilyAggregationCompiler bound)
    {n : ℕ} (hn : 1 ≤ n) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (compiler.target n) ↔
      DecompositionAggregationObligation n := by
  exact
    (compiler.target_eval_iff_formulaAggregation n).trans
      ⟨DecompositionFormulaAggregationObligation.toAggregation,
        DecompositionFormulaAggregationObligation.ofAggregation hn⟩

theorem target_eval_iff_core_source_certificate
    {bound : ℕ → ℝ} (compiler : EncodedFamilyAggregationCompiler bound)
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (compiler.target n) ↔
      Nonempty (DecompositionCoreSourceCertificate n) :=
  (target_eval_iff_oneLe_and_coreAll compiler n).trans
    (DecompositionCoreSourceCertificate.nonempty_iff_oneLe_and_coreFields
      n).symm

def compileFromAggregation
    {bound : ℕ → ℝ} (compiler : EncodedFamilyAggregationCompiler bound)
    {n : ℕ} (hn : 1 ≤ n)
    (aggregation : DecompositionAggregationObligation n) :
    BAProofObject BussS21Axiom :=
  compiler.compile n
    (DecompositionFormulaAggregationObligation.ofAggregation hn aggregation)

theorem compileFromAggregation_conclusion
    {bound : ℕ → ℝ} (compiler : EncodedFamilyAggregationCompiler bound)
    {n : ℕ} (hn : 1 ≤ n)
    (aggregation : DecompositionAggregationObligation n) :
    (compiler.compileFromAggregation hn aggregation).conclusion =
      compiler.target n :=
  compiler.compile_conclusion n
    (DecompositionFormulaAggregationObligation.ofAggregation hn aggregation)

theorem compileFromAggregation_size_plus_two_le
    {bound : ℕ → ℝ} (compiler : EncodedFamilyAggregationCompiler bound)
    {n : ℕ} (hn : 1 ≤ n)
    (aggregation : DecompositionAggregationObligation n) :
    ((((compiler.compileFromAggregation hn aggregation).size + 2 : ℕ) : ℝ)) ≤
      bound n :=
  compiler.compile_size_plus_two_le n
    (DecompositionFormulaAggregationObligation.ofAggregation hn aggregation)

def toCorePureCompilerObligation
    {bound : ℕ → ℝ} (compiler : EncodedFamilyAggregationCompiler bound) :
    DecompositionCorePureCompilerObligation bound where
  target := compiler.target
  target_atomFree := compiler.target_atomFree
  target_eval_iff_source :=
    target_eval_iff_core_source_certificate compiler
  compile := by
    intro n hsource
    exact
      compiler.compile n
        ((DecompositionFormulaAggregationObligation.iff_oneLe_and_coreAll
          n).2
          ((DecompositionCoreSourceCertificate.nonempty_iff_oneLe_and_coreFields
            n).1 hsource))
  compile_conclusion := by
    intro n hsource
    exact
      compiler.compile_conclusion n
        ((DecompositionFormulaAggregationObligation.iff_oneLe_and_coreAll
          n).2
          ((DecompositionCoreSourceCertificate.nonempty_iff_oneLe_and_coreFields
            n).1 hsource))
  compile_size_plus_two_le := by
    intro n hsource
    exact
      compiler.compile_size_plus_two_le n
        ((DecompositionFormulaAggregationObligation.iff_oneLe_and_coreAll
          n).2
          ((DecompositionCoreSourceCertificate.nonempty_iff_oneLe_and_coreFields
            n).1 hsource))

def toExpandedPureCompilerObligation
    {bound : ℕ → ℝ} (compiler : EncodedFamilyAggregationCompiler bound) :
    DecompositionPureCompilerObligation bound :=
  DecompositionCorePureCompilerObligation.toExpanded
    (toCorePureCompilerObligation compiler)

end EncodedFamilyAggregationCompiler

/-- Final honest interface for the decomposition global-family step.

Supplying this structure would close the current aggregation gap: the bounded
box/prefix verifier layer would become an ordinary core pure compiler with a
polynomial size bound. -/
structure DecompositionGlobalFamilyCompilerObligation
    (bound : ℕ → ℝ) where
  bound_poly : IsPolynomialBound bound
  compiler : EncodedFamilyAggregationCompiler bound

namespace DecompositionGlobalFamilyCompilerObligation

def toCorePureCompilerObligation
    {bound : ℕ → ℝ}
    (obligation : DecompositionGlobalFamilyCompilerObligation bound) :
    DecompositionCorePureCompilerObligation bound :=
  obligation.compiler.toCorePureCompilerObligation

def toExpandedPureCompilerObligation
    {bound : ℕ → ℝ}
    (obligation : DecompositionGlobalFamilyCompilerObligation bound) :
    DecompositionPureCompilerObligation bound :=
  obligation.compiler.toExpandedPureCompilerObligation

theorem target_eval_iff_formulaAggregation
    {bound : ℕ → ℝ}
    (obligation : DecompositionGlobalFamilyCompilerObligation bound)
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (obligation.compiler.target n) ↔
      DecompositionFormulaAggregationObligation n :=
  obligation.compiler.target_eval_iff_formulaAggregation n

theorem target_eval_iff_aggregation_on_tail
    {bound : ℕ → ℝ}
    (obligation : DecompositionGlobalFamilyCompilerObligation bound)
    {n : ℕ} (hn : 1 ≤ n) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (obligation.compiler.target n) ↔
      DecompositionAggregationObligation n :=
  obligation.compiler.target_eval_iff_aggregation_on_tail hn

theorem target_eval_iff_core_source_certificate
    {bound : ℕ → ℝ}
    (obligation : DecompositionGlobalFamilyCompilerObligation bound)
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (obligation.compiler.target n) ↔
      Nonempty (DecompositionCoreSourceCertificate n) :=
  obligation.compiler.target_eval_iff_core_source_certificate n

theorem target_eval_iff_oneLe_and_coreAll
    {bound : ℕ → ℝ}
    (obligation : DecompositionGlobalFamilyCompilerObligation bound)
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (obligation.compiler.target n) ↔
      1 ≤ n ∧ DecompositionAnalyticField.coreAll n :=
  obligation.compiler.target_eval_iff_oneLe_and_coreAll n

end DecompositionGlobalFamilyCompilerObligation

namespace DecompositionFormulaAggregationObligation

theorem iff_one_le (n : ℕ) :
    DecompositionFormulaAggregationObligation n ↔ 1 ≤ n := by
  constructor
  · intro aggregation
    exact aggregation.one_le
  · intro hn
    exact ofOneLeAndCoreAll hn
      (DecompositionAnalyticField.coreAll_complete_of_one_le hn)

end DecompositionFormulaAggregationObligation

/-!
### Aggregation encoding scheme

This is the first single-family encoding layer for the decomposition
aggregation.  It is intentionally named as semantic compression: the bounded
windows are present as atom-free Buss formulas, while the leap from the tail
guard `1 ≤ n` to all analytic fields is still supplied by the already-audited
main-library completion theorems.
-/

def decompositionAggregationBoxAVar : ℕ := 6220

def decompositionAggregationBoxBVar : ℕ := 6221

def decompositionAggregationBoxKVar : ℕ := 6222

def decompositionAggregationPrefixBVar : ℕ := 6223

def decompositionAggregationEncodingTargetName : ℕ := 6224

def decompositionAggregationFubiniBoxWindowFormula (n : ℕ) : BAFormula :=
  BAFormula.forallBounded decompositionAggregationBoxAVar
    (productLogBaNatLiteral n)
    (BAFormula.forallBounded decompositionAggregationBoxBVar
      (productLogBaNatLiteral n)
      (BAFormula.forallBounded decompositionAggregationBoxKVar
        (productLogBaNatLiteral n)
        (BAFormula.forallBounded decompositionFubiniAVar
          (BATerm.var decompositionAggregationBoxAVar)
          (BAFormula.forallBounded decompositionFubiniBVar
            (BATerm.var decompositionAggregationBoxBVar)
            (BAFormula.forallBounded decompositionFubiniKVar
              (BATerm.var decompositionAggregationBoxKVar)
              (BAFormula.imp decompositionFubiniBoxGuardFormula
                  (decompositionFubiniCertificatePayloadFormula
                    (BATerm.var decompositionAggregationBoxAVar)
                    (BATerm.var decompositionAggregationBoxBVar)
                    (BATerm.var decompositionAggregationBoxKVar))))))))

def decompositionAggregationIntegratedSplitPrefixWindowFormula
    (n : ℕ) : BAFormula :=
  BAFormula.forallBounded decompositionAggregationPrefixBVar
    (productLogBaNatLiteral n)
    (BAFormula.forallBounded decompositionIntegratedSplitNVar
      (BATerm.var decompositionAggregationPrefixBVar)
      (decompositionIntegratedSplitPrefixPayloadFormula n
        (BATerm.var decompositionAggregationPrefixBVar)))

namespace DecompositionAnalyticPayloadCode

def fubiniAggregationPayloadEnv (A B K a b k : ℕ) : ℕ → ℕ :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update (fun _idx => 0)
              decompositionAggregationBoxAVar A)
            decompositionAggregationBoxBVar B)
          decompositionAggregationBoxKVar K)
        decompositionFubiniAVar a)
      decompositionFubiniBVar b)
    decompositionFubiniKVar k

def integratedSplitAggregationPayloadEnv (B N : ℕ) : ℕ → ℕ :=
  Function.update
    (Function.update (fun _idx => 0)
      decompositionAggregationPrefixBVar B)
    decompositionIntegratedSplitNVar N

theorem fubiniAggregationCertificatePayloadFormula_eval_iff_validCode
    (A B K a b k : ℕ) :
    productLogDecompositionFormulaEval
        (fubiniAggregationPayloadEnv A B K a b k)
        (decompositionFubiniCertificatePayloadFormula
          (BATerm.var decompositionAggregationBoxAVar)
          (BATerm.var decompositionAggregationBoxBVar)
          (BATerm.var decompositionAggregationBoxKVar)) ↔
      ∃ payload : DecompositionAnalyticPayloadCode,
        ValidFubiniBox payload A B K a b k := by
  constructor
  · intro hformula
    rcases hformula with ⟨payload, hpayloadBound, hpayloadBody⟩
    have hlocal :
        a ≤ A ∧ b ≤ B ∧ k ≤ K ∧ 1 ≤ k := by
      simpa [decompositionFubiniBoxLocalCheckFormula,
        decompositionFubiniBoxGuardFormula,
        productLogDecompositionFormulaEval,
        productLogDecompositionBaFormulaEval,
        productLogDecompositionBaTermEval,
        fubiniAggregationPayloadEnv, decompositionAggregationBoxAVar,
        decompositionAggregationBoxBVar, decompositionAggregationBoxKVar,
        decompositionFubiniAVar, decompositionFubiniBVar,
        decompositionFubiniKVar, decompositionFubiniPayloadVar] using
        hpayloadBody.1
    have hpayloadBoundCode :
        payload ≤ fubiniBoxPayloadBound A B K a b k := by
      simpa [fubiniBoxPayloadBound, fubiniAggregationPayloadEnv,
        fubiniPayloadEnv,
        decompositionFubiniPayloadBoundTerm,
        productLogDecompositionBaTermEval, decompositionAggregationBoxAVar,
        decompositionAggregationBoxBVar, decompositionAggregationBoxKVar,
        decompositionFubiniAVar, decompositionFubiniBVar,
        decompositionFubiniKVar] using hpayloadBound
    rcases hlocal with ⟨ha, hb, hkBound, hk⟩
    let payloadCode : DecompositionAnalyticPayloadCode :=
      fubiniBox A B K a b k payload hpayloadBoundCode
    refine ⟨payloadCode, ?_⟩
    dsimp [ValidFubiniBox, payloadCode, fubiniBox]
    exact
      ⟨rfl, rfl, hpayloadBoundCode, ha, hb, hkBound, hk,
        EulerLimit.SondowDecomposition.logKernelFubiniCertificate_holds
          a b k⟩
  · intro hvalid
    rcases hvalid with ⟨payload, hpayloadValid⟩
    rcases hpayloadValid with
      ⟨_hkind, hbound, hcode, ha, hb, hkBound, hk, _hcert⟩
    have hcodeBound :
        payload.code ≤ fubiniBoxPayloadBound A B K a b k := by
      simpa [hbound] using hcode
    refine ⟨payload.code, ?_, ?_⟩
    · simpa [fubiniBoxPayloadBound, fubiniAggregationPayloadEnv,
        fubiniPayloadEnv,
        decompositionFubiniPayloadBoundTerm,
        productLogDecompositionBaTermEval, decompositionAggregationBoxAVar,
        decompositionAggregationBoxBVar, decompositionAggregationBoxKVar,
        decompositionFubiniAVar, decompositionFubiniBVar,
        decompositionFubiniKVar] using hcodeBound
    · refine ⟨?_, ?_, ?_⟩
      · simpa [decompositionFubiniBoxLocalCheckFormula,
          decompositionFubiniBoxGuardFormula,
          productLogDecompositionFormulaEval,
          productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval,
          fubiniAggregationPayloadEnv, decompositionAggregationBoxAVar,
          decompositionAggregationBoxBVar, decompositionAggregationBoxKVar,
          decompositionFubiniAVar, decompositionFubiniBVar,
          decompositionFubiniKVar, decompositionFubiniPayloadVar] using
          (show a ≤ A ∧ b ≤ B ∧ k ≤ K ∧ 1 ≤ k from
            ⟨ha, hb, hkBound, hk⟩)
      · simpa [fubiniBoxPayloadBound, fubiniAggregationPayloadEnv,
          fubiniPayloadEnv,
          decompositionFubiniPayloadBoundTerm,
          productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval,
          decompositionAggregationBoxAVar, decompositionAggregationBoxBVar,
          decompositionAggregationBoxKVar, decompositionFubiniAVar,
          decompositionFubiniBVar, decompositionFubiniKVar,
          decompositionFubiniPayloadVar] using hcodeBound
      · simp [productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval]

theorem integratedSplitAggregationPrefixPayloadFormula_eval_iff_validCode
    (n B N : ℕ) :
    productLogDecompositionFormulaEval
        (integratedSplitAggregationPayloadEnv B N)
        (decompositionIntegratedSplitPrefixPayloadFormula n
          (BATerm.var decompositionAggregationPrefixBVar)) ↔
      ∃ payload : DecompositionAnalyticPayloadCode,
        ValidIntegratedSplitPrefix payload n B N := by
  constructor
  · intro hformula
    rcases hformula with ⟨payload, hpayloadBound, hpayloadBody⟩
    have hlocal : 1 ≤ n ∧ N ≤ B := by
      simpa [decompositionIntegratedSplitPrefixLocalCheckFormula,
        decompositionOneLeFormula,
        productLogDecompositionFormulaEval,
        productLogDecompositionBaFormulaEval,
        productLogDecompositionBaTermEval,
        integratedSplitAggregationPayloadEnv,
        decompositionAggregationPrefixBVar,
        decompositionIntegratedSplitNVar,
        decompositionIntegratedSplitPayloadVar] using hpayloadBody.1
    have hpayloadBoundCode :
        payload ≤ integratedSplitPrefixPayloadBound n B N := by
      simpa [integratedSplitPrefixPayloadBound,
        integratedSplitAggregationPayloadEnv,
        integratedSplitPayloadEnv,
        decompositionIntegratedSplitPayloadBoundTerm,
        productLogDecompositionBaTermEval,
        decompositionAggregationPrefixBVar,
        decompositionIntegratedSplitNVar] using hpayloadBound
    rcases hlocal with ⟨hn, hN⟩
    let payloadCode : DecompositionAnalyticPayloadCode :=
      integratedSplitPrefix n B N payload hpayloadBoundCode
    refine ⟨payloadCode, ?_⟩
    dsimp [ValidIntegratedSplitPrefix, payloadCode,
      integratedSplitPrefix]
    exact
      ⟨rfl, rfl, hpayloadBoundCode, hn, hN,
        EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate_holds
          hn N⟩
  · intro hvalid
    rcases hvalid with ⟨payload, hpayloadValid⟩
    rcases hpayloadValid with
      ⟨_hkind, hbound, hcode, hn, hN, _hcert⟩
    have hcodeBound :
        payload.code ≤ integratedSplitPrefixPayloadBound n B N := by
      simpa [hbound] using hcode
    refine ⟨payload.code, ?_, ?_⟩
    · simpa [integratedSplitPrefixPayloadBound,
        integratedSplitAggregationPayloadEnv,
        integratedSplitPayloadEnv,
        decompositionIntegratedSplitPayloadBoundTerm,
        productLogDecompositionBaTermEval,
        decompositionAggregationPrefixBVar,
        decompositionIntegratedSplitNVar] using hcodeBound
    · refine ⟨?_, ?_, ?_⟩
      · simpa [decompositionIntegratedSplitPrefixLocalCheckFormula,
          decompositionOneLeFormula,
          productLogDecompositionFormulaEval,
          productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval,
          integratedSplitAggregationPayloadEnv,
          decompositionAggregationPrefixBVar,
          decompositionIntegratedSplitNVar,
          decompositionIntegratedSplitPayloadVar] using
          (show 1 ≤ n ∧ N ≤ B from ⟨hn, hN⟩)
      · simpa [integratedSplitPrefixPayloadBound,
          integratedSplitAggregationPayloadEnv,
          integratedSplitPayloadEnv,
          decompositionIntegratedSplitPayloadBoundTerm,
          productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval,
          decompositionAggregationPrefixBVar,
          decompositionIntegratedSplitNVar,
          decompositionIntegratedSplitPayloadVar] using hcodeBound
      · simp [productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval]

end DecompositionAnalyticPayloadCode

def decompositionAggregationEncodingBodyFormula (n : ℕ) : BAFormula :=
  BAFormula.and (decompositionAggregationFubiniBoxWindowFormula n)
    (BAFormula.and
      (decompositionAggregationIntegratedSplitPrefixWindowFormula n)
      (BAFormula.and (decompositionOneLeFormula n)
        (decompositionShapeCalibrationBodyFormula n)))

def decompositionAggregationEncodingTargetFormula (n : ℕ) : BAFormula :=
  polytimeDefinabilityFormula decompositionAggregationEncodingTargetName
    (decompositionAggregationEncodingBodyFormula n)

theorem decompositionAggregationFubiniBoxWindowFormula_atomFree
    (n : ℕ) :
    productLogDecompositionAtomFree
      (decompositionAggregationFubiniBoxWindowFormula n) := by
  simp [decompositionAggregationFubiniBoxWindowFormula,
    decompositionFubiniBoxGuardFormula,
    decompositionFubiniBoxLocalCheckFormula,
    decompositionFubiniCertificatePayloadFormula,
    decompositionFubiniPayloadBoundTerm,
    productLogDecompositionAtomFree,
    productLogDecompositionBaFormulaAtomFree]

theorem decompositionAggregationIntegratedSplitPrefixWindowFormula_atomFree
    (n : ℕ) :
    productLogDecompositionAtomFree
      (decompositionAggregationIntegratedSplitPrefixWindowFormula n) := by
  simp [decompositionAggregationIntegratedSplitPrefixWindowFormula,
    decompositionIntegratedSplitPrefixLocalCheckFormula,
    decompositionIntegratedSplitPrefixPayloadFormula,
    decompositionIntegratedSplitPayloadBoundTerm,
    decompositionOneLeFormula, productLogDecompositionAtomFree,
    productLogDecompositionBaFormulaAtomFree]

theorem decompositionAggregationEncodingBodyFormula_atomFree
    (n : ℕ) :
    productLogDecompositionAtomFree
      (decompositionAggregationEncodingBodyFormula n) := by
  simp [decompositionAggregationEncodingBodyFormula,
    decompositionAggregationFubiniBoxWindowFormula_atomFree,
    decompositionAggregationIntegratedSplitPrefixWindowFormula_atomFree,
    decompositionOneLeFormula, decompositionShapeCalibrationBodyFormula,
    productLogDecompositionAtomFree,
    productLogDecompositionBaFormulaAtomFree]

theorem decompositionAggregationEncodingTargetFormula_atomFree
    (n : ℕ) :
    productLogDecompositionAtomFree
      (decompositionAggregationEncodingTargetFormula n) := by
  simp [decompositionAggregationEncodingTargetFormula,
    decompositionAggregationEncodingBodyFormula_atomFree,
    polytimeDefinabilityFormula, productLogDecompositionAtomFree,
    productLogDecompositionBaFormulaAtomFree]

theorem decompositionAggregationFubiniBoxWindowFormula_eval_iff_true
    (n : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (decompositionAggregationFubiniBoxWindowFormula n) ↔ True := by
  constructor
  · intro _h
    trivial
  · intro _htrue A _hA B _hB K _hK a ha b hb k hk hguard
    refine ⟨0, ?_, ?_⟩
    · simp
    · refine ⟨?_, ?_, ?_⟩
      · exact
          ⟨by
              simpa [productLogDecompositionFormulaEval,
                productLogDecompositionBaFormulaEval,
                productLogDecompositionBaTermEval, decompositionFubiniAVar,
                decompositionFubiniBVar, decompositionFubiniKVar,
                decompositionFubiniPayloadVar,
                decompositionAggregationBoxAVar,
                decompositionAggregationBoxBVar,
                decompositionAggregationBoxKVar] using ha,
            by
              simpa [productLogDecompositionFormulaEval,
                productLogDecompositionBaFormulaEval,
                productLogDecompositionBaTermEval, decompositionFubiniAVar,
                decompositionFubiniBVar, decompositionFubiniKVar,
                decompositionFubiniPayloadVar,
                decompositionAggregationBoxAVar,
                decompositionAggregationBoxBVar,
                decompositionAggregationBoxKVar] using hb,
            by
              simpa [productLogDecompositionFormulaEval,
                productLogDecompositionBaFormulaEval,
                productLogDecompositionBaTermEval, decompositionFubiniAVar,
                decompositionFubiniBVar, decompositionFubiniKVar,
                decompositionFubiniPayloadVar,
                decompositionAggregationBoxAVar,
                decompositionAggregationBoxBVar,
                decompositionAggregationBoxKVar] using hk,
            hguard⟩
      · simp [productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval]
      · simp [productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval]

theorem decompositionAggregationIntegratedSplitPrefixWindowFormula_eval_iff_one_le
    (n : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (decompositionAggregationIntegratedSplitPrefixWindowFormula n) ↔
      1 ≤ n := by
  constructor
  · intro h
    have hB := h 0 (by simp)
    have hN := hB 0 (by simp [productLogDecompositionBaTermEval])
    rcases hN with ⟨payload, _hpayloadBound, hpayloadBody⟩
    exact
      (decompositionOneLeFormula_eval_iff n
        (Function.update
          (Function.update
            (Function.update env decompositionAggregationPrefixBVar 0)
            decompositionIntegratedSplitNVar 0)
          decompositionIntegratedSplitPayloadVar payload)).1 hpayloadBody.1.1
  · intro hn B _hB N hN
    refine ⟨0, ?_, ?_⟩
    · simp
    · refine ⟨?_, ?_, ?_⟩
      · exact
          ⟨(decompositionOneLeFormula_eval_iff n
              (Function.update
                (Function.update
                  (Function.update env decompositionAggregationPrefixBVar B)
                  decompositionIntegratedSplitNVar N)
                decompositionIntegratedSplitPayloadVar 0)).2 hn,
            by
              simpa [productLogDecompositionFormulaEval,
                productLogDecompositionBaFormulaEval,
                productLogDecompositionBaTermEval,
                decompositionAggregationPrefixBVar,
                decompositionIntegratedSplitNVar,
                decompositionIntegratedSplitPayloadVar] using hN⟩
      · simp [productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval]
      · simp [productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval]

def DecompositionAggregationFubiniWindowValidCodes (n : ℕ) : Prop :=
  ∀ A : ℕ, A ≤ n →
    ∀ B : ℕ, B ≤ n →
      ∀ K : ℕ, K ≤ n →
        ∀ a : ℕ, a ≤ A →
          ∀ b : ℕ, b ≤ B →
            ∀ k : ℕ, k ≤ K → 1 ≤ k →
              ∃ payload : DecompositionAnalyticPayloadCode,
                DecompositionAnalyticPayloadCode.ValidFubiniBox
                  payload A B K a b k

def DecompositionAggregationIntegratedSplitWindowValidCodes
    (n : ℕ) : Prop :=
  ∀ B : ℕ, B ≤ n →
    ∀ N : ℕ, N ≤ B →
      ∃ payload : DecompositionAnalyticPayloadCode,
        DecompositionAnalyticPayloadCode.ValidIntegratedSplitPrefix
          payload n B N

theorem decompositionAggregationFubiniWindowValidCodes_iff_true
    (n : ℕ) :
    DecompositionAggregationFubiniWindowValidCodes n ↔ True := by
  constructor
  · intro _hcodes
    trivial
  · intro _htrue A _hA B _hB K _hK a ha b hb k hkBound hk
    exact
      DecompositionAnalyticPayloadCode.fubiniBox_valid_of_guarded_box
        ha hb hkBound hk

theorem decompositionAggregationIntegratedSplitWindowValidCodes_iff_one_le
    (n : ℕ) :
    DecompositionAggregationIntegratedSplitWindowValidCodes n ↔ 1 ≤ n := by
  constructor
  · intro hcodes
    rcases hcodes 0 (Nat.zero_le n) 0 le_rfl with
      ⟨payload, hvalid⟩
    rcases hvalid with
      ⟨_hkind, _hbound, _hcode, hn, _hN, _hcert⟩
    exact hn
  · intro hn B _hB N hN
    exact
      DecompositionAnalyticPayloadCode.integratedSplitPrefix_valid_of_tail
        hn hN

theorem decompositionAggregationFubiniBoxWindowFormula_eval_iff_validCodes
    (n : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (decompositionAggregationFubiniBoxWindowFormula n) ↔
      DecompositionAggregationFubiniWindowValidCodes n :=
  (decompositionAggregationFubiniBoxWindowFormula_eval_iff_true
    n env).trans
    (decompositionAggregationFubiniWindowValidCodes_iff_true n).symm

theorem decompositionAggregationIntegratedSplitPrefixWindowFormula_eval_iff_validCodes
    (n : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (decompositionAggregationIntegratedSplitPrefixWindowFormula n) ↔
      DecompositionAggregationIntegratedSplitWindowValidCodes n :=
  (decompositionAggregationIntegratedSplitPrefixWindowFormula_eval_iff_one_le
    n env).trans
    (decompositionAggregationIntegratedSplitWindowValidCodes_iff_one_le
      n).symm

structure DecompositionAggregationPayloadWindowAudit : Prop where
  fubini_variable_payload_eval_iff_valid :
    ∀ A B K a b k : ℕ,
      productLogDecompositionFormulaEval
          (DecompositionAnalyticPayloadCode.fubiniAggregationPayloadEnv
            A B K a b k)
          (decompositionFubiniCertificatePayloadFormula
            (BATerm.var decompositionAggregationBoxAVar)
            (BATerm.var decompositionAggregationBoxBVar)
            (BATerm.var decompositionAggregationBoxKVar)) ↔
        ∃ payload : DecompositionAnalyticPayloadCode,
          DecompositionAnalyticPayloadCode.ValidFubiniBox
            payload A B K a b k
  integratedSplit_variable_payload_eval_iff_valid :
    ∀ n B N : ℕ,
      productLogDecompositionFormulaEval
          (DecompositionAnalyticPayloadCode.integratedSplitAggregationPayloadEnv
            B N)
          (decompositionIntegratedSplitPrefixPayloadFormula n
            (BATerm.var decompositionAggregationPrefixBVar)) ↔
        ∃ payload : DecompositionAnalyticPayloadCode,
          DecompositionAnalyticPayloadCode.ValidIntegratedSplitPrefix
            payload n B N
  fubini_window_eval_iff_validCodes :
    ∀ n : ℕ, ∀ env : ℕ → ℕ,
      productLogDecompositionFormulaEval env
          (decompositionAggregationFubiniBoxWindowFormula n) ↔
        DecompositionAggregationFubiniWindowValidCodes n
  integratedSplit_window_eval_iff_validCodes :
    ∀ n : ℕ, ∀ env : ℕ → ℕ,
      productLogDecompositionFormulaEval env
          (decompositionAggregationIntegratedSplitPrefixWindowFormula n) ↔
        DecompositionAggregationIntegratedSplitWindowValidCodes n

def decompositionAggregationPayloadWindowAudit :
    DecompositionAggregationPayloadWindowAudit where
  fubini_variable_payload_eval_iff_valid := fun A B K a b k =>
    DecompositionAnalyticPayloadCode.fubiniAggregationCertificatePayloadFormula_eval_iff_validCode
      A B K a b k
  integratedSplit_variable_payload_eval_iff_valid := fun n B N =>
    DecompositionAnalyticPayloadCode.integratedSplitAggregationPrefixPayloadFormula_eval_iff_validCode
      n B N
  fubini_window_eval_iff_validCodes := fun n env =>
    decompositionAggregationFubiniBoxWindowFormula_eval_iff_validCodes
      n env
  integratedSplit_window_eval_iff_validCodes := fun n env =>
    decompositionAggregationIntegratedSplitPrefixWindowFormula_eval_iff_validCodes
      n env

theorem decompositionShapeCalibrationBodyFormula_eval_iff_true
    (n : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (decompositionShapeCalibrationBodyFormula n) ↔ True := by
  constructor
  · intro _h
    trivial
  · intro _htrue
    simp [decompositionShapeCalibrationBodyFormula,
      productLogDecompositionFormulaEval,
      productLogDecompositionBaFormulaEval]

/-- Audit-readable payload view of the full aggregation body.  This keeps all
four body components visible instead of compressing the target immediately to
the tail guard `1 ≤ n`. -/
structure DecompositionAggregationPayloadWindowBundle (n : ℕ) : Prop where
  fubiniWindow :
    DecompositionAggregationFubiniWindowValidCodes n
  integratedSplitWindow :
    DecompositionAggregationIntegratedSplitWindowValidCodes n
  tailGuard : 1 ≤ n
  shapeCalibration :
    Nonempty (DecompositionShapeCalibrationCertificate n)

namespace DecompositionAggregationPayloadWindowBundle

theorem iff_one_le (n : ℕ) :
    DecompositionAggregationPayloadWindowBundle n ↔ 1 ≤ n := by
  constructor
  · intro bundle
    exact bundle.tailGuard
  · intro hn
    exact {
      fubiniWindow :=
        (decompositionAggregationFubiniWindowValidCodes_iff_true n).2
          trivial
      integratedSplitWindow :=
        (decompositionAggregationIntegratedSplitWindowValidCodes_iff_one_le
          n).2 hn
      tailGuard := hn
      shapeCalibration :=
        ⟨DecompositionShapeCalibrationCertificate.ofMainLibrary n⟩ }

theorem fubiniWindow_to_boxTarget_eval
    {n A B K : ℕ}
    (bundle : DecompositionAggregationPayloadWindowBundle n)
    (hA : A ≤ n) (hB : B ≤ n) (hK : K ≤ n) :
    productLogDecompositionFormulaEval
      (decompositionFubiniEvalEnv (A + B + K))
      (decompositionFubiniBoxTargetFormula A B K) := by
  refine
    (decompositionFubiniBoxTargetFormula_eval_iff_guarded_box
      A B K).2 ?_
  intro a b k ha hb hkBound hk
  rcases bundle.fubiniWindow A hA B hB K hK a ha b hb k hkBound hk with
    ⟨payload, hvalid⟩
  exact DecompositionAnalyticPayloadCode.fubiniBox_sound hvalid

theorem integratedSplitWindow_to_prefixTarget_eval
    {n B : ℕ}
    (bundle : DecompositionAggregationPayloadWindowBundle n)
    (hB : B ≤ n) :
    productLogDecompositionFormulaEval (fun _idx => n)
      (decompositionIntegratedSplitPrefixTargetFormula n B) := by
  refine
    (decompositionIntegratedSplitPrefixTargetFormula_eval_iff_prefix_on_tail
      (n := n) (B := B) bundle.tailGuard).2 ?_
  intro N hN
  rcases bundle.integratedSplitWindow B hB N hN with
    ⟨payload, hvalid⟩
  exact DecompositionAnalyticPayloadCode.integratedSplitPrefix_sound hvalid

theorem to_formulaAggregation_fieldRoute
    {n : ℕ} (bundle : DecompositionAggregationPayloadWindowBundle n) :
    DecompositionFormulaAggregationObligation n := by
  exact {
    one_le := bundle.tailGuard
    fubiniBoxTargets := by
      intro A B K
      refine
        (decompositionFubiniBoxTargetFormula_eval_iff_guarded_box
          A B K).2 ?_
      intro a b k ha hb hkBound hk
      rcases
        DecompositionAnalyticPayloadCode.fubiniBox_valid_of_guarded_box
          ha hb hkBound hk with
        ⟨payload, hvalid⟩
      exact DecompositionAnalyticPayloadCode.fubiniBox_sound hvalid
    integratedSplitPrefixTargets := by
      intro B
      refine
        (decompositionIntegratedSplitPrefixTargetFormula_eval_iff_prefix_on_tail
          (n := n) (B := B) bundle.tailGuard).2 ?_
      intro N hN
      rcases
        DecompositionAnalyticPayloadCode.integratedSplitPrefix_valid_of_tail
          bundle.tailGuard hN with
        ⟨payload, hvalid⟩
      exact DecompositionAnalyticPayloadCode.integratedSplitPrefix_sound hvalid
    remainderTarget :=
      (decompositionRemainderTailTargetFormula_eval_iff_certificate n).2
        ⟨DecompositionRemainderTailCertificate.ofMainLibrary
          bundle.tailGuard⟩
    shapeTarget :=
      (decompositionShapeCalibrationTargetFormula_eval_iff_certificate n).2
        bundle.shapeCalibration }

theorem to_formulaAggregation
    {n : ℕ} (bundle : DecompositionAggregationPayloadWindowBundle n) :
    DecompositionFormulaAggregationObligation n :=
  bundle.to_formulaAggregation_fieldRoute

end DecompositionAggregationPayloadWindowBundle

theorem decompositionAggregationEncodingBodyFormula_eval_iff_payloadWindowBundle
    (n : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (decompositionAggregationEncodingBodyFormula n) ↔
      DecompositionAggregationPayloadWindowBundle n := by
  constructor
  · intro hbody
    exact {
      fubiniWindow :=
        (decompositionAggregationFubiniBoxWindowFormula_eval_iff_validCodes
          n env).1 hbody.1
      integratedSplitWindow :=
        (decompositionAggregationIntegratedSplitPrefixWindowFormula_eval_iff_validCodes
          n env).1 hbody.2.1
      tailGuard :=
        (decompositionOneLeFormula_eval_iff n env).1 hbody.2.2.1
      shapeCalibration :=
        (decompositionShapeCalibrationBodyFormula_eval_iff_certificate
          n env).1 hbody.2.2.2 }
  · intro bundle
    exact
      ⟨(decompositionAggregationFubiniBoxWindowFormula_eval_iff_validCodes
          n env).2 bundle.fubiniWindow,
        ⟨(decompositionAggregationIntegratedSplitPrefixWindowFormula_eval_iff_validCodes
            n env).2 bundle.integratedSplitWindow,
          ⟨(decompositionOneLeFormula_eval_iff n env).2
              bundle.tailGuard,
            (decompositionShapeCalibrationBodyFormula_eval_iff_certificate
              n env).2 bundle.shapeCalibration⟩⟩⟩

theorem decompositionAggregationEncodingBodyFormula_eval_iff_one_le
    (n : ℕ) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (decompositionAggregationEncodingBodyFormula n) ↔
      1 ≤ n := by
  constructor
  · intro h
    exact (decompositionOneLeFormula_eval_iff n env).1 h.2.2.1
  · intro hn
    exact
      ⟨(decompositionAggregationFubiniBoxWindowFormula_eval_iff_true
          n env).2 trivial,
        ⟨(decompositionAggregationIntegratedSplitPrefixWindowFormula_eval_iff_one_le
            n env).2 hn,
          ⟨(decompositionOneLeFormula_eval_iff n env).2 hn,
            (decompositionShapeCalibrationBodyFormula_eval_iff_true
              n env).2 trivial⟩⟩⟩

theorem decompositionAggregationEncodingTargetFormula_eval_iff_one_le
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionAggregationEncodingTargetFormula n) ↔
      1 ≤ n := by
  constructor
  · intro h
    rcases h with ⟨value, _hvalue, hbody⟩
    exact
      (decompositionAggregationEncodingBodyFormula_eval_iff_one_le n
        (Function.update (fun _idx => n)
          decompositionAggregationEncodingTargetName value)).1 hbody
  · intro hn
    refine ⟨0, ?_, ?_⟩
    · simp [productLogDecompositionBaTermEval]
    · exact
        (decompositionAggregationEncodingBodyFormula_eval_iff_one_le n
          (Function.update (fun _idx => n)
            decompositionAggregationEncodingTargetName 0)).2 hn

theorem decompositionAggregationEncodingTargetFormula_eval_iff_payloadWindowBundle
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionAggregationEncodingTargetFormula n) ↔
      DecompositionAggregationPayloadWindowBundle n := by
  constructor
  · intro htarget
    rcases htarget with ⟨value, _hvalue, hbody⟩
    exact
      (decompositionAggregationEncodingBodyFormula_eval_iff_payloadWindowBundle
        n
        (Function.update (fun _idx => n)
          decompositionAggregationEncodingTargetName value)).1 hbody
  · intro bundle
    refine ⟨0, ?_, ?_⟩
    · simp [productLogDecompositionBaTermEval]
    · exact
        (decompositionAggregationEncodingBodyFormula_eval_iff_payloadWindowBundle
          n
          (Function.update (fun _idx => n)
            decompositionAggregationEncodingTargetName 0)).2 bundle

theorem decompositionAggregationEncodingTargetFormula_eval_to_formulaAggregation_fieldRoute
    {n : ℕ}
    (htarget :
      productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionAggregationEncodingTargetFormula n)) :
    DecompositionFormulaAggregationObligation n :=
  ((decompositionAggregationEncodingTargetFormula_eval_iff_payloadWindowBundle
    n).1 htarget).to_formulaAggregation_fieldRoute

theorem decompositionAggregationEncodingTargetFormula_eval_iff_formulaAggregation_fieldRoute
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionAggregationEncodingTargetFormula n) ↔
      DecompositionFormulaAggregationObligation n := by
  constructor
  · exact
      decompositionAggregationEncodingTargetFormula_eval_to_formulaAggregation_fieldRoute
  · intro aggregation
    exact
      (decompositionAggregationEncodingTargetFormula_eval_iff_one_le n).2
        aggregation.one_le

theorem decompositionAggregationEncodingTargetFormula_eval_iff_formulaAggregation
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionAggregationEncodingTargetFormula n) ↔
      DecompositionFormulaAggregationObligation n :=
  (decompositionAggregationEncodingTargetFormula_eval_iff_one_le n).trans
    (DecompositionFormulaAggregationObligation.iff_one_le n).symm

def decompositionAggregationEncodingProofObject
    (n : ℕ) : BAProofObject BussS21Axiom :=
  productLogDecompositionPolytimeDefinabilityProofObject
    decompositionAggregationEncodingTargetName
    (decompositionAggregationEncodingBodyFormula n)

theorem decompositionAggregationEncodingProofObject_conclusion
    (n : ℕ) :
    (decompositionAggregationEncodingProofObject n).conclusion =
      decompositionAggregationEncodingTargetFormula n := by
  rfl

theorem decompositionAggregationEncodingProofObject_size_plus_two_eq_three
    (n : ℕ) :
    ((((decompositionAggregationEncodingProofObject n).size + 2 : ℕ) : ℝ)) =
      3 := by
  change (((1 + 2 : ℕ) : ℝ)) = 3
  norm_num

def decompositionAggregationSemanticCompressionBound (_n : ℕ) : ℝ :=
  3

theorem decompositionAggregationSemanticCompressionBound_poly :
    IsPolynomialBound decompositionAggregationSemanticCompressionBound := by
  unfold decompositionAggregationSemanticCompressionBound
  exact IsPolynomialBound.const (3 : ℝ)

structure DecompositionAggregationEncodingScheme where
  fubiniBoxWindow : ℕ → BAFormula
  integratedSplitPrefixWindow : ℕ → BAFormula
  remainderGuard : ℕ → BAFormula
  shapeCalibrationBody : ℕ → BAFormula
  target : ℕ → BAFormula
  target_atomFree :
    ∀ n : ℕ, productLogDecompositionAtomFree (target n)
  target_eval_iff_one_le :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n) (target n) ↔
        1 ≤ n
  target_eval_iff_formulaAggregation :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n) (target n) ↔
        DecompositionFormulaAggregationObligation n
  proofObject : ℕ → BAProofObject BussS21Axiom
  proofObject_conclusion :
    ∀ n : ℕ, (proofObject n).conclusion = target n
  proofObject_size_plus_two_eq_three :
    ∀ n : ℕ, ((((proofObject n).size + 2 : ℕ) : ℝ)) = 3

namespace DecompositionAggregationEncodingScheme

def toEncodedFamilyAggregationCompiler
    (scheme : DecompositionAggregationEncodingScheme) :
    EncodedFamilyAggregationCompiler
      decompositionAggregationSemanticCompressionBound where
  target := scheme.target
  target_atomFree := scheme.target_atomFree
  target_eval_iff_formulaAggregation :=
    scheme.target_eval_iff_formulaAggregation
  compile := by
    intro n _aggregation
    exact scheme.proofObject n
  compile_conclusion := by
    intro n _aggregation
    exact scheme.proofObject_conclusion n
  compile_size_plus_two_le := by
    intro n _aggregation
    rw [scheme.proofObject_size_plus_two_eq_three n]
    change (3 : ℝ) ≤ 3
    norm_num

end DecompositionAggregationEncodingScheme

def decompositionAggregationEncodingScheme :
    DecompositionAggregationEncodingScheme where
  fubiniBoxWindow := decompositionAggregationFubiniBoxWindowFormula
  integratedSplitPrefixWindow :=
    decompositionAggregationIntegratedSplitPrefixWindowFormula
  remainderGuard := decompositionOneLeFormula
  shapeCalibrationBody := decompositionShapeCalibrationBodyFormula
  target := decompositionAggregationEncodingTargetFormula
  target_atomFree := decompositionAggregationEncodingTargetFormula_atomFree
  target_eval_iff_one_le :=
    decompositionAggregationEncodingTargetFormula_eval_iff_one_le
  target_eval_iff_formulaAggregation :=
    decompositionAggregationEncodingTargetFormula_eval_iff_formulaAggregation
  proofObject := decompositionAggregationEncodingProofObject
  proofObject_conclusion :=
    decompositionAggregationEncodingProofObject_conclusion
  proofObject_size_plus_two_eq_three :=
    decompositionAggregationEncodingProofObject_size_plus_two_eq_three

def decompositionAggregationSemanticCompressionCompiler :
    EncodedFamilyAggregationCompiler
      decompositionAggregationSemanticCompressionBound :=
  decompositionAggregationEncodingScheme.toEncodedFamilyAggregationCompiler

def decompositionAggregationSemanticCompressionGlobalFamilyObligation :
    DecompositionGlobalFamilyCompilerObligation
      decompositionAggregationSemanticCompressionBound where
  bound_poly := decompositionAggregationSemanticCompressionBound_poly
  compiler := decompositionAggregationSemanticCompressionCompiler

structure DecompositionAggregationPayloadBodyBundleAudit : Prop where
  body_eval_iff_payloadWindowBundle :
    ∀ n : ℕ, ∀ env : ℕ → ℕ,
      productLogDecompositionFormulaEval env
          (decompositionAggregationEncodingBodyFormula n) ↔
        DecompositionAggregationPayloadWindowBundle n
  target_eval_iff_payloadWindowBundle :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (decompositionAggregationEncodingTargetFormula n) ↔
        DecompositionAggregationPayloadWindowBundle n
  target_eval_to_formulaAggregation_fieldRoute :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (decompositionAggregationEncodingTargetFormula n) →
        DecompositionFormulaAggregationObligation n
  target_eval_iff_formulaAggregation_fieldRoute :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (decompositionAggregationEncodingTargetFormula n) ↔
        DecompositionFormulaAggregationObligation n
  payloadWindowBundle_iff_one_le :
    ∀ n : ℕ, DecompositionAggregationPayloadWindowBundle n ↔ 1 ≤ n
  payloadWindowBundle_to_formulaAggregation :
    ∀ n : ℕ,
      DecompositionAggregationPayloadWindowBundle n →
        DecompositionFormulaAggregationObligation n
  fubini_window_to_boxTarget_eval :
    ∀ n A B K : ℕ,
      DecompositionAggregationPayloadWindowBundle n →
        A ≤ n → B ≤ n → K ≤ n →
          productLogDecompositionFormulaEval
            (decompositionFubiniEvalEnv (A + B + K))
            (decompositionFubiniBoxTargetFormula A B K)
  integratedSplit_window_to_prefixTarget_eval :
    ∀ n B : ℕ,
      DecompositionAggregationPayloadWindowBundle n →
        B ≤ n →
          productLogDecompositionFormulaEval (fun _idx => n)
            (decompositionIntegratedSplitPrefixTargetFormula n B)
  payloadWindowBundle_to_formulaAggregation_fieldRoute :
    ∀ n : ℕ,
      DecompositionAggregationPayloadWindowBundle n →
        DecompositionFormulaAggregationObligation n

def decompositionAggregationPayloadBodyBundleAudit :
    DecompositionAggregationPayloadBodyBundleAudit where
  body_eval_iff_payloadWindowBundle :=
    decompositionAggregationEncodingBodyFormula_eval_iff_payloadWindowBundle
  target_eval_iff_payloadWindowBundle :=
    decompositionAggregationEncodingTargetFormula_eval_iff_payloadWindowBundle
  target_eval_to_formulaAggregation_fieldRoute := by
    intro n htarget
    exact
      decompositionAggregationEncodingTargetFormula_eval_to_formulaAggregation_fieldRoute
        htarget
  target_eval_iff_formulaAggregation_fieldRoute :=
    decompositionAggregationEncodingTargetFormula_eval_iff_formulaAggregation_fieldRoute
  payloadWindowBundle_iff_one_le :=
    DecompositionAggregationPayloadWindowBundle.iff_one_le
  payloadWindowBundle_to_formulaAggregation := by
    intro n bundle
    exact bundle.to_formulaAggregation
  fubini_window_to_boxTarget_eval := by
    intro n A B K bundle hA hB hK
    exact bundle.fubiniWindow_to_boxTarget_eval hA hB hK
  integratedSplit_window_to_prefixTarget_eval := by
    intro n B bundle hB
    exact bundle.integratedSplitWindow_to_prefixTarget_eval hB
  payloadWindowBundle_to_formulaAggregation_fieldRoute := by
    intro n bundle
    exact bundle.to_formulaAggregation_fieldRoute

/-!
### Field-derived aggregation compiler

This target has its own definability name.  It reuses the audited aggregation
body, but its public interface is the payload-window/field-route interface
rather than the semantic-compression `1 ≤ n` interface.
-/

def decompositionFieldDerivedAggregationTargetName : ℕ := 6227

def decompositionFieldDerivedAggregationTargetFormula (n : ℕ) : BAFormula :=
  polytimeDefinabilityFormula decompositionFieldDerivedAggregationTargetName
    (decompositionAggregationEncodingBodyFormula n)

theorem decompositionFieldDerivedAggregationTargetName_ne_semanticName :
    decompositionFieldDerivedAggregationTargetName ≠
      decompositionAggregationEncodingTargetName := by
  norm_num [decompositionFieldDerivedAggregationTargetName,
    decompositionAggregationEncodingTargetName]

theorem decompositionFieldDerivedAggregationTargetFormula_atomFree
    (n : ℕ) :
    productLogDecompositionAtomFree
      (decompositionFieldDerivedAggregationTargetFormula n) := by
  simp [decompositionFieldDerivedAggregationTargetFormula,
    decompositionAggregationEncodingBodyFormula_atomFree,
    polytimeDefinabilityFormula, productLogDecompositionAtomFree,
    productLogDecompositionBaFormulaAtomFree]

theorem decompositionFieldDerivedAggregationTargetFormula_eval_iff_payloadWindowBundle
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionFieldDerivedAggregationTargetFormula n) ↔
      DecompositionAggregationPayloadWindowBundle n := by
  constructor
  · intro htarget
    rcases htarget with ⟨value, _hvalue, hbody⟩
    exact
      (decompositionAggregationEncodingBodyFormula_eval_iff_payloadWindowBundle
        n
        (Function.update (fun _idx => n)
          decompositionFieldDerivedAggregationTargetName value)).1 hbody
  · intro bundle
    refine ⟨0, ?_, ?_⟩
    · simp [productLogDecompositionBaTermEval]
    · exact
        (decompositionAggregationEncodingBodyFormula_eval_iff_payloadWindowBundle
          n
          (Function.update (fun _idx => n)
            decompositionFieldDerivedAggregationTargetName 0)).2 bundle

theorem decompositionFieldDerivedAggregationTargetFormula_eval_to_formulaAggregation_fieldRoute
    {n : ℕ}
    (htarget :
      productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionFieldDerivedAggregationTargetFormula n)) :
    DecompositionFormulaAggregationObligation n :=
  ((decompositionFieldDerivedAggregationTargetFormula_eval_iff_payloadWindowBundle
    n).1 htarget).to_formulaAggregation_fieldRoute

theorem decompositionFieldDerivedAggregationTargetFormula_eval_iff_formulaAggregation_fieldRoute
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionFieldDerivedAggregationTargetFormula n) ↔
      DecompositionFormulaAggregationObligation n := by
  constructor
  · exact
      decompositionFieldDerivedAggregationTargetFormula_eval_to_formulaAggregation_fieldRoute
  · intro aggregation
    exact
      (decompositionFieldDerivedAggregationTargetFormula_eval_iff_payloadWindowBundle
        n).2
        ((DecompositionAggregationPayloadWindowBundle.iff_one_le n).2
          aggregation.one_le)

def decompositionFieldDerivedAggregationProofObject
    (n : ℕ) : BAProofObject BussS21Axiom :=
  productLogDecompositionPolytimeDefinabilityProofObject
    decompositionFieldDerivedAggregationTargetName
    (decompositionAggregationEncodingBodyFormula n)

theorem decompositionFieldDerivedAggregationProofObject_conclusion
    (n : ℕ) :
    (decompositionFieldDerivedAggregationProofObject n).conclusion =
      decompositionFieldDerivedAggregationTargetFormula n := by
  rfl

theorem decompositionFieldDerivedAggregationProofObject_size_plus_two_eq_three
    (n : ℕ) :
    ((((decompositionFieldDerivedAggregationProofObject n).size + 2 : ℕ) :
      ℝ)) = 3 := by
  change (((1 + 2 : ℕ) : ℝ)) = 3
  norm_num

def decompositionFieldDerivedAggregationBound (_n : ℕ) : ℝ :=
  3

theorem decompositionFieldDerivedAggregationBound_poly :
    IsPolynomialBound decompositionFieldDerivedAggregationBound := by
  unfold decompositionFieldDerivedAggregationBound
  exact IsPolynomialBound.const (3 : ℝ)

structure DecompositionFieldDerivedAggregationCompiler
    (bound : ℕ → ℝ) where
  target : ℕ → BAFormula
  target_atomFree :
    ∀ n : ℕ, productLogDecompositionAtomFree (target n)
  target_eval_iff_payloadWindowBundle :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n) (target n) ↔
        DecompositionAggregationPayloadWindowBundle n
  target_eval_iff_formulaAggregation_fieldRoute :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n) (target n) ↔
        DecompositionFormulaAggregationObligation n
  compile :
    ∀ n : ℕ, DecompositionFormulaAggregationObligation n →
      BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ n : ℕ, ∀ aggregation : DecompositionFormulaAggregationObligation n,
      (compile n aggregation).conclusion = target n
  compile_size_plus_two_le :
    ∀ n : ℕ, ∀ aggregation : DecompositionFormulaAggregationObligation n,
      ((((compile n aggregation).size + 2 : ℕ) : ℝ)) ≤ bound n

namespace DecompositionFieldDerivedAggregationCompiler

def toEncodedFamilyAggregationCompiler
    {bound : ℕ → ℝ}
    (compiler : DecompositionFieldDerivedAggregationCompiler bound) :
    EncodedFamilyAggregationCompiler bound where
  target := compiler.target
  target_atomFree := compiler.target_atomFree
  target_eval_iff_formulaAggregation :=
    compiler.target_eval_iff_formulaAggregation_fieldRoute
  compile := compiler.compile
  compile_conclusion := compiler.compile_conclusion
  compile_size_plus_two_le := compiler.compile_size_plus_two_le

def toGlobalFamilyCompilerObligation
    {bound : ℕ → ℝ}
    (compiler : DecompositionFieldDerivedAggregationCompiler bound)
    (hpoly : IsPolynomialBound bound) :
    DecompositionGlobalFamilyCompilerObligation bound where
  bound_poly := hpoly
  compiler := compiler.toEncodedFamilyAggregationCompiler

def compileFromPayloadWindowBundle
    {bound : ℕ → ℝ}
    (compiler : DecompositionFieldDerivedAggregationCompiler bound)
    {n : ℕ} (bundle : DecompositionAggregationPayloadWindowBundle n) :
    BAProofObject BussS21Axiom :=
  compiler.compile n bundle.to_formulaAggregation_fieldRoute

theorem compileFromPayloadWindowBundle_conclusion
    {bound : ℕ → ℝ}
    (compiler : DecompositionFieldDerivedAggregationCompiler bound)
    {n : ℕ} (bundle : DecompositionAggregationPayloadWindowBundle n) :
    (compiler.compileFromPayloadWindowBundle bundle).conclusion =
      compiler.target n :=
  compiler.compile_conclusion n bundle.to_formulaAggregation_fieldRoute

theorem compileFromPayloadWindowBundle_size_plus_two_le
    {bound : ℕ → ℝ}
    (compiler : DecompositionFieldDerivedAggregationCompiler bound)
    {n : ℕ} (bundle : DecompositionAggregationPayloadWindowBundle n) :
    ((((compiler.compileFromPayloadWindowBundle bundle).size + 2 : ℕ) :
      ℝ)) ≤ bound n :=
  compiler.compile_size_plus_two_le n bundle.to_formulaAggregation_fieldRoute

end DecompositionFieldDerivedAggregationCompiler

def decompositionFieldDerivedAggregationCompiler :
    DecompositionFieldDerivedAggregationCompiler
      decompositionFieldDerivedAggregationBound where
  target := decompositionFieldDerivedAggregationTargetFormula
  target_atomFree :=
    decompositionFieldDerivedAggregationTargetFormula_atomFree
  target_eval_iff_payloadWindowBundle :=
    decompositionFieldDerivedAggregationTargetFormula_eval_iff_payloadWindowBundle
  target_eval_iff_formulaAggregation_fieldRoute :=
    decompositionFieldDerivedAggregationTargetFormula_eval_iff_formulaAggregation_fieldRoute
  compile := by
    intro n _aggregation
    exact decompositionFieldDerivedAggregationProofObject n
  compile_conclusion := by
    intro n _aggregation
    exact decompositionFieldDerivedAggregationProofObject_conclusion n
  compile_size_plus_two_le := by
    intro n _aggregation
    rw [decompositionFieldDerivedAggregationProofObject_size_plus_two_eq_three]
    change (3 : ℝ) ≤ 3
    norm_num

def decompositionFieldDerivedEncodedAggregationCompiler :
    EncodedFamilyAggregationCompiler
      decompositionFieldDerivedAggregationBound :=
  decompositionFieldDerivedAggregationCompiler.toEncodedFamilyAggregationCompiler

def decompositionFieldDerivedGlobalFamilyObligation :
    DecompositionGlobalFamilyCompilerObligation
      decompositionFieldDerivedAggregationBound :=
  decompositionFieldDerivedAggregationCompiler.toGlobalFamilyCompilerObligation
    decompositionFieldDerivedAggregationBound_poly

/-- Audit label separating the two possible aggregation routes. -/
inductive DecompositionAggregationCompilerAuditRoute
  | semanticCompression
  | fieldDerived
  deriving DecidableEq, Repr

structure DecompositionFieldDerivedAggregationCompilerAudit where
  bound : ℕ → ℝ
  bound_poly : IsPolynomialBound bound
  compiler : DecompositionFieldDerivedAggregationCompiler bound
  encodedCompiler : EncodedFamilyAggregationCompiler bound
  globalObligation : DecompositionGlobalFamilyCompilerObligation bound
  route : DecompositionAggregationCompilerAuditRoute
  route_eq :
    route = DecompositionAggregationCompilerAuditRoute.fieldDerived
  targetName_ne_semanticName :
    decompositionFieldDerivedAggregationTargetName ≠
      decompositionAggregationEncodingTargetName
  target_eval_iff_payloadWindowBundle :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (compiler.target n) ↔
        DecompositionAggregationPayloadWindowBundle n
  target_eval_iff_formulaAggregation_fieldRoute :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (compiler.target n) ↔
        DecompositionFormulaAggregationObligation n
  compile_conclusion :
    ∀ n : ℕ, ∀ aggregation : DecompositionFormulaAggregationObligation n,
      (compiler.compile n aggregation).conclusion = compiler.target n
  compile_size_plus_two_le :
    ∀ n : ℕ, ∀ aggregation : DecompositionFormulaAggregationObligation n,
      ((((compiler.compile n aggregation).size + 2 : ℕ) : ℝ)) ≤ bound n

def decompositionFieldDerivedAggregationCompilerAudit :
    DecompositionFieldDerivedAggregationCompilerAudit where
  bound := decompositionFieldDerivedAggregationBound
  bound_poly := decompositionFieldDerivedAggregationBound_poly
  compiler := decompositionFieldDerivedAggregationCompiler
  encodedCompiler := decompositionFieldDerivedEncodedAggregationCompiler
  globalObligation := decompositionFieldDerivedGlobalFamilyObligation
  route := DecompositionAggregationCompilerAuditRoute.fieldDerived
  route_eq := rfl
  targetName_ne_semanticName :=
    decompositionFieldDerivedAggregationTargetName_ne_semanticName
  target_eval_iff_payloadWindowBundle := by
    intro n
    exact
      decompositionFieldDerivedAggregationCompiler.target_eval_iff_payloadWindowBundle
        n
  target_eval_iff_formulaAggregation_fieldRoute := by
    intro n
    exact
      decompositionFieldDerivedAggregationCompiler.target_eval_iff_formulaAggregation_fieldRoute
        n
  compile_conclusion := by
    intro n aggregation
    exact
      decompositionFieldDerivedAggregationCompiler.compile_conclusion
        n aggregation
  compile_size_plus_two_le := by
    intro n aggregation
    exact
      decompositionFieldDerivedAggregationCompiler.compile_size_plus_two_le
        n aggregation

/-- Audit record for the current semantic-compression compiler.

The important point is that this route proves the target equivalent to `1 ≤ n`
and then uses the existing main-library completion theorem to recover the
analytic fields.  It is therefore useful, but it is not the genuine field-level
encoding closure. -/
structure DecompositionSemanticCompressionCompilerAudit where
  compiler :
    EncodedFamilyAggregationCompiler
      decompositionAggregationSemanticCompressionBound
  route : DecompositionAggregationCompilerAuditRoute
  route_eq :
    route =
      DecompositionAggregationCompilerAuditRoute.semanticCompression
  target_eval_iff_one_le :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (compiler.target n) ↔
        1 ≤ n
  formulaAggregation_iff_one_le :
    ∀ n : ℕ, DecompositionFormulaAggregationObligation n ↔ 1 ≤ n
  completion_step :
    ∀ {n : ℕ}, 1 ≤ n → DecompositionAnalyticField.coreAll n

namespace DecompositionSemanticCompressionCompilerAudit

theorem target_eval_iff_formulaAggregation
    (audit : DecompositionSemanticCompressionCompilerAudit) (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (audit.compiler.target n) ↔
      DecompositionFormulaAggregationObligation n :=
  (audit.target_eval_iff_one_le n).trans
    (audit.formulaAggregation_iff_one_le n).symm

theorem target_eval_iff_oneLe_and_coreAll_via_completion
    (audit : DecompositionSemanticCompressionCompilerAudit) (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (audit.compiler.target n) ↔
      1 ≤ n ∧ DecompositionAnalyticField.coreAll n := by
  constructor
  · intro htarget
    have hn := (audit.target_eval_iff_one_le n).1 htarget
    exact ⟨hn, audit.completion_step hn⟩
  · intro h
    exact (audit.target_eval_iff_one_le n).2 h.1

end DecompositionSemanticCompressionCompilerAudit

def decompositionSemanticCompressionCompilerAudit :
    DecompositionSemanticCompressionCompilerAudit where
  compiler := decompositionAggregationSemanticCompressionCompiler
  route := DecompositionAggregationCompilerAuditRoute.semanticCompression
  route_eq := rfl
  target_eval_iff_one_le := by
    intro n
    exact decompositionAggregationEncodingTargetFormula_eval_iff_one_le n
  formulaAggregation_iff_one_le :=
    DecompositionFormulaAggregationObligation.iff_one_le
  completion_step := by
    intro n hn
    exact DecompositionAnalyticField.coreAll_complete_of_one_le hn

/-- Audit record for the genuine field compiler bundle.

This record exposes only local field/prefix/box verifier equivalences.  It does
not contain a single global target formula and therefore does not by itself
close the decomposition aggregation compiler. -/
structure DecompositionFieldCompilerBundleAudit where
  bundle : DecompositionCoreFieldCompilerBundle
  route : DecompositionAggregationCompilerAuditRoute
  route_eq :
    route = DecompositionAggregationCompilerAuditRoute.fieldDerived
  shape_eval_iff :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (bundle.shape.target n) ↔
        DecompositionAnalyticField.eval
          DecompositionAnalyticField.shapeCalibration n
  remainder_eval_iff_on_tail :
    ∀ {n : ℕ}, bundle.remainder.threshold ≤ n →
      (productLogDecompositionFormulaEval (fun _idx => n)
          (bundle.remainder.target n) ↔
        DecompositionAnalyticField.eval
          DecompositionAnalyticField.remainder n)
  integratedSplit_prefix_eval_iff_on_tail :
    ∀ {n B : ℕ}, bundle.integratedSplitPrefix.threshold ≤ n →
      (productLogDecompositionFormulaEval (fun _idx => n)
          (bundle.integratedSplitPrefix.target n B) ↔
        ∀ N : ℕ, N ≤ B →
          EulerLimit.SondowDecomposition.integratedOriginalSplitCertificate
            n N)
  fubini_box_eval_iff_guarded_box :
    ∀ A B K : ℕ,
      productLogDecompositionFormulaEval
          (decompositionFubiniEvalEnv (A + B + K))
          (bundle.fubiniBox.target A B K) ↔
        ∀ a b k : ℕ, a ≤ A → b ≤ B → k ≤ K → 1 ≤ k →
          EulerLimit.SondowDecomposition.logKernelFubiniCertificate
            a b k

def decompositionDefaultFieldCompilerBundleAudit :
    DecompositionFieldCompilerBundleAudit where
  bundle := DecompositionCoreFieldCompilerBundle.default
  route := DecompositionAggregationCompilerAuditRoute.fieldDerived
  route_eq := rfl
  shape_eval_iff := by
    intro n
    exact
      DecompositionCoreFieldCompilerBundle.shape_eval_iff
        DecompositionCoreFieldCompilerBundle.default n
  remainder_eval_iff_on_tail := by
    intro n hn
    exact
      DecompositionCoreFieldCompilerBundle.remainder_eval_iff_on_tail
        DecompositionCoreFieldCompilerBundle.default hn
  integratedSplit_prefix_eval_iff_on_tail := by
    intro n B hn
    exact
      DecompositionCoreFieldCompilerBundle.integratedSplit_prefix_eval_iff_on_tail
        DecompositionCoreFieldCompilerBundle.default hn
  fubini_box_eval_iff_guarded_box := by
    intro A B K
    exact
      DecompositionCoreFieldCompilerBundle.fubini_box_eval_iff_guarded_box
        DecompositionCoreFieldCompilerBundle.default A B K

/-- Interface for the remaining genuine encoding gap.

A value of this type is only a candidate: it records the semantic-compression
audit, the field-bundle audit, and a proposed single target/bound.  The nested
`Closure` structure is the missing proof obligation: derive the target,
compiler, and size bound from the field verifiers rather than from the
main-library completion shortcut. -/
structure DecompositionGenuineEncodingGap where
  semanticAudit : DecompositionSemanticCompressionCompilerAudit
  fieldAudit : DecompositionFieldCompilerBundleAudit
  candidateTarget : ℕ → BAFormula
  candidateBound : ℕ → ℝ

namespace DecompositionGenuineEncodingGap

def TargetAtomFree (gap : DecompositionGenuineEncodingGap) : Prop :=
  ∀ n : ℕ, productLogDecompositionAtomFree (gap.candidateTarget n)

def FieldDerivedFormulaAggregation
    (gap : DecompositionGenuineEncodingGap) : Prop :=
  ∀ n : ℕ,
    productLogDecompositionFormulaEval (fun _idx => n)
        (gap.candidateTarget n) ↔
      DecompositionFormulaAggregationObligation n

/-- Closing this structure is the real replacement for the current
semantic-compression route. -/
structure AtomFreeObligation (gap : DecompositionGenuineEncodingGap) where
  target_atomFree : gap.TargetAtomFree

structure EvalIffObligation (gap : DecompositionGenuineEncodingGap) where
  target_eval_iff_formulaAggregation_from_fieldCompilers :
    gap.FieldDerivedFormulaAggregation

structure FubiniEvalIff (gap : DecompositionGenuineEncodingGap) where
  fubini_eval_iff :
    ∀ (n : ℕ) (env : ℕ → ℕ),
      productLogDecompositionFormulaEval env
          (decompositionAggregationFubiniBoxWindowFormula n) ↔
        ∀ A B K : ℕ,
          productLogDecompositionFormulaEval
            (decompositionFubiniEvalEnv (A + B + K))
            (gap.fieldAudit.bundle.fubiniBox.target A B K)

structure SplitEvalIff (gap : DecompositionGenuineEncodingGap) where
  split_eval_iff :
    ∀ (n : ℕ) (env : ℕ → ℕ),
      productLogDecompositionFormulaEval env
          (decompositionAggregationIntegratedSplitPrefixWindowFormula n) ↔
        ∀ B : ℕ,
          productLogDecompositionFormulaEval (fun _idx => n)
            (gap.fieldAudit.bundle.integratedSplitPrefix.target n B)

structure RemainderEvalIff (gap : DecompositionGenuineEncodingGap) where
  remainder_eval_iff :
    ∀ (n : ℕ) (env : ℕ → ℕ),
      productLogDecompositionFormulaEval env
          (decompositionOneLeFormula n) ↔
        productLogDecompositionFormulaEval (fun _idx => n)
          (gap.fieldAudit.bundle.remainder.target n)

structure ShapeEvalIff (gap : DecompositionGenuineEncodingGap) where
  shape_eval_iff :
    ∀ (n : ℕ) (env : ℕ → ℕ),
      productLogDecompositionFormulaEval env
          (decompositionShapeCalibrationBodyFormula n) ↔
        productLogDecompositionFormulaEval (fun _idx => n)
          (gap.fieldAudit.bundle.shape.target n)

structure LocalEvalIffBundle (gap : DecompositionGenuineEncodingGap) where
  candidateTarget_eq :
    gap.candidateTarget = decompositionAggregationEncodingTargetFormula
  fubiniBoxTarget_eq :
    ∀ A B K : ℕ,
      gap.fieldAudit.bundle.fubiniBox.target A B K =
        decompositionFubiniBoxTargetFormula A B K
  integratedSplitPrefixTarget_eq :
    ∀ n B : ℕ,
      gap.fieldAudit.bundle.integratedSplitPrefix.target n B =
        decompositionIntegratedSplitPrefixTargetFormula n B
  remainderTarget_eq :
    ∀ n : ℕ,
      gap.fieldAudit.bundle.remainder.target n =
        decompositionRemainderTailTargetFormula n
  shapeTarget_eq :
    ∀ n : ℕ,
      gap.fieldAudit.bundle.shape.target n =
        decompositionShapeCalibrationTargetFormula n
  fubini : FubiniEvalIff gap
  split : SplitEvalIff gap
  remainder : RemainderEvalIff gap
  shape : ShapeEvalIff gap

def EvalIffObligation.ofLocalBundle
    {gap : DecompositionGenuineEncodingGap}
    (bundle : LocalEvalIffBundle gap) :
    EvalIffObligation gap where
  target_eval_iff_formulaAggregation_from_fieldCompilers := by
    intro n
    constructor
    · intro htarget
      rw [bundle.candidateTarget_eq] at htarget
      rcases htarget with ⟨value, _hvalue, hbody⟩
      let env :=
        Function.update (fun _idx => n)
          decompositionAggregationEncodingTargetName value
      change productLogDecompositionFormulaEval env
        (decompositionAggregationEncodingBodyFormula n) at hbody
      exact {
        one_le := (decompositionOneLeFormula_eval_iff n env).1
          hbody.2.2.1
        fubiniBoxTargets := by
          intro A B K
          simpa [bundle.fubiniBoxTarget_eq A B K] using
            ((bundle.fubini.fubini_eval_iff n env).1 hbody.1 A B K)
        integratedSplitPrefixTargets := by
          intro B
          simpa [bundle.integratedSplitPrefixTarget_eq n B] using
            ((bundle.split.split_eval_iff n env).1 hbody.2.1 B)
        remainderTarget := by
          simpa [bundle.remainderTarget_eq n] using
            ((bundle.remainder.remainder_eval_iff n env).1 hbody.2.2.1)
        shapeTarget := by
          simpa [bundle.shapeTarget_eq n] using
            ((bundle.shape.shape_eval_iff n env).1 hbody.2.2.2) }
    · intro aggregation
      rw [bundle.candidateTarget_eq]
      refine ⟨0, ?_, ?_⟩
      · simp [productLogDecompositionBaTermEval]
      · let env :=
          Function.update (fun _idx => n)
            decompositionAggregationEncodingTargetName 0
        change productLogDecompositionFormulaEval env
          (decompositionAggregationEncodingBodyFormula n)
        have hfubini :
            ∀ A B K : ℕ,
              productLogDecompositionFormulaEval
                (decompositionFubiniEvalEnv (A + B + K))
                (gap.fieldAudit.bundle.fubiniBox.target A B K) := by
          intro A B K
          simpa [bundle.fubiniBoxTarget_eq A B K] using
            aggregation.fubiniBoxTargets A B K
        have hsplit :
            ∀ B : ℕ,
              productLogDecompositionFormulaEval (fun _idx => n)
                (gap.fieldAudit.bundle.integratedSplitPrefix.target n B) := by
          intro B
          simpa [bundle.integratedSplitPrefixTarget_eq n B] using
            aggregation.integratedSplitPrefixTargets B
        have hremainder :
            productLogDecompositionFormulaEval (fun _idx => n)
              (gap.fieldAudit.bundle.remainder.target n) := by
          simpa [bundle.remainderTarget_eq n] using
            aggregation.remainderTarget
        have hshape :
            productLogDecompositionFormulaEval (fun _idx => n)
              (gap.fieldAudit.bundle.shape.target n) := by
          simpa [bundle.shapeTarget_eq n] using aggregation.shapeTarget
        exact
          ⟨(bundle.fubini.fubini_eval_iff n env).2 hfubini,
            ⟨(bundle.split.split_eval_iff n env).2 hsplit,
              ⟨(decompositionOneLeFormula_eval_iff n env).2
                  aggregation.one_le,
                (bundle.shape.shape_eval_iff n env).2
                  hshape⟩⟩⟩

structure CompileObligation (gap : DecompositionGenuineEncodingGap) where
  compile :
    ∀ n : ℕ, DecompositionFormulaAggregationObligation n →
      BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ n : ℕ, ∀ aggregation : DecompositionFormulaAggregationObligation n,
      (compile n aggregation).conclusion = gap.candidateTarget n

structure SizeBoundObligation
    (gap : DecompositionGenuineEncodingGap)
    (compileObligation : CompileObligation gap) where
  compile_size_plus_two_le :
    ∀ n : ℕ, ∀ aggregation : DecompositionFormulaAggregationObligation n,
      ((((compileObligation.compile n aggregation).size + 2 : ℕ) : ℝ)) ≤
        gap.candidateBound n

/-- Closing this structure is the real replacement for the current
semantic-compression route.  The four sub-obligations keep the audit surface
separate: syntax, semantics, proof production, and size. -/
structure Closure (gap : DecompositionGenuineEncodingGap) where
  atomFreeObligation : AtomFreeObligation gap
  evalIffObligation : EvalIffObligation gap
  compileObligation : CompileObligation gap
  sizeBoundObligation : SizeBoundObligation gap compileObligation

def Closure.target_atomFree
    {gap : DecompositionGenuineEncodingGap} (closure : Closure gap) :
    gap.TargetAtomFree :=
  closure.atomFreeObligation.target_atomFree

theorem Closure.target_eval_iff_formulaAggregation_from_fieldCompilers
    {gap : DecompositionGenuineEncodingGap} (closure : Closure gap) :
    gap.FieldDerivedFormulaAggregation :=
  closure.evalIffObligation.target_eval_iff_formulaAggregation_from_fieldCompilers

def Closure.compile
    {gap : DecompositionGenuineEncodingGap} (closure : Closure gap) :
    ∀ n : ℕ, DecompositionFormulaAggregationObligation n →
      BAProofObject BussS21Axiom :=
  closure.compileObligation.compile

theorem Closure.compile_conclusion
    {gap : DecompositionGenuineEncodingGap} (closure : Closure gap)
    (n : ℕ) (aggregation : DecompositionFormulaAggregationObligation n) :
    (closure.compile n aggregation).conclusion = gap.candidateTarget n :=
  closure.compileObligation.compile_conclusion n aggregation

theorem Closure.compile_size_plus_two_le
    {gap : DecompositionGenuineEncodingGap} (closure : Closure gap)
    (n : ℕ) (aggregation : DecompositionFormulaAggregationObligation n) :
    ((((closure.compile n aggregation).size + 2 : ℕ) : ℝ)) ≤
      gap.candidateBound n :=
  closure.sizeBoundObligation.compile_size_plus_two_le n aggregation

def Closure.toEncodedFamilyAggregationCompiler
    {gap : DecompositionGenuineEncodingGap} (closure : Closure gap) :
    EncodedFamilyAggregationCompiler gap.candidateBound where
  target := gap.candidateTarget
  target_atomFree := closure.target_atomFree
  target_eval_iff_formulaAggregation :=
    closure.target_eval_iff_formulaAggregation_from_fieldCompilers
  compile := closure.compile
  compile_conclusion := closure.compile_conclusion
  compile_size_plus_two_le := closure.compile_size_plus_two_le

def Closure.toGlobalFamilyCompilerObligation
    {gap : DecompositionGenuineEncodingGap}
    (closure : Closure gap)
    (hpoly : IsPolynomialBound gap.candidateBound) :
    DecompositionGlobalFamilyCompilerObligation gap.candidateBound where
  bound_poly := hpoly
  compiler := closure.toEncodedFamilyAggregationCompiler

theorem Closure.replaces_completion_step
    {gap : DecompositionGenuineEncodingGap} (closure : Closure gap)
    (n : ℕ) :
  productLogDecompositionFormulaEval (fun _idx => n)
        (gap.candidateTarget n) ↔
      DecompositionFormulaAggregationObligation n :=
  closure.target_eval_iff_formulaAggregation_from_fieldCompilers n

end DecompositionGenuineEncodingGap

theorem decompositionFubiniBoxTargetFormula_eval_complete
    (A B K : ℕ) :
    productLogDecompositionFormulaEval
        (decompositionFubiniEvalEnv (A + B + K))
        (decompositionFubiniBoxTargetFormula A B K) := by
  refine ⟨0, ?_, ?_⟩
  · simp [decompositionFubiniEvalEnv, productLogDecompositionBaTermEval]
  · change productLogDecompositionFormulaEval
      (Function.update (decompositionFubiniEvalEnv (A + B + K))
        decompositionFubiniBoxTargetName 0)
      (decompositionFubiniBoxBodyFormula A B K)
    intro _a ha _b hb _k hk hguard
    refine ⟨0, ?_, ?_⟩
    · simp
    · refine ⟨?_, ?_, ?_⟩
      · exact
          ⟨by
              simpa [productLogDecompositionFormulaEval,
                productLogDecompositionBaFormulaEval,
                productLogDecompositionBaTermEval, decompositionFubiniAVar,
                decompositionFubiniBVar, decompositionFubiniKVar,
                decompositionFubiniPayloadVar, decompositionFubiniBoxTargetName]
                using ha,
            by
              simpa [productLogDecompositionFormulaEval,
                productLogDecompositionBaFormulaEval,
                productLogDecompositionBaTermEval, decompositionFubiniAVar,
                decompositionFubiniBVar, decompositionFubiniKVar,
                decompositionFubiniPayloadVar, decompositionFubiniBoxTargetName]
                using hb,
            by
              simpa [productLogDecompositionFormulaEval,
                productLogDecompositionBaFormulaEval,
                productLogDecompositionBaTermEval, decompositionFubiniAVar,
                decompositionFubiniBVar, decompositionFubiniKVar,
                decompositionFubiniPayloadVar, decompositionFubiniBoxTargetName]
                using hk,
            hguard⟩
      · simp [productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval]
      · simp [productLogDecompositionBaFormulaEval,
          productLogDecompositionBaTermEval]

theorem decompositionShapeCalibrationTargetFormula_eval_iff_true
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionShapeCalibrationTargetFormula n) ↔ True := by
  constructor
  · intro _h
    trivial
  · intro _htrue
    refine ⟨0, ?_, ?_⟩
    · simp [productLogDecompositionBaTermEval]
    · change productLogDecompositionFormulaEval
        (Function.update (fun _idx => n)
          decompositionShapeCalibrationTargetName 0)
        (decompositionShapeCalibrationBodyFormula n)
      exact
        (decompositionShapeCalibrationBodyFormula_eval_iff_true n
          (Function.update (fun _idx => n)
            decompositionShapeCalibrationTargetName 0)).2 trivial

structure DecompositionRemainderShapeTargetAudit where
  remainder_atomFree :
    ∀ n : ℕ,
      productLogDecompositionAtomFree
        (decompositionRemainderTailTargetFormula n)
  remainder_eval_iff_one_le :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (decompositionRemainderTailTargetFormula n) ↔
        1 ≤ n
  remainder_eval_iff_field_on_tail :
    ∀ {n : ℕ}, 1 ≤ n →
      (productLogDecompositionFormulaEval (fun _idx => n)
          (decompositionRemainderTailTargetFormula n) ↔
        DecompositionAnalyticField.eval
          DecompositionAnalyticField.remainder n)
  shape_atomFree :
    ∀ n : ℕ,
      productLogDecompositionAtomFree
        (decompositionShapeCalibrationTargetFormula n)
  shape_eval_iff_true :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (decompositionShapeCalibrationTargetFormula n) ↔ True
  shape_eval_iff_field :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (decompositionShapeCalibrationTargetFormula n) ↔
        DecompositionAnalyticField.eval
          DecompositionAnalyticField.shapeCalibration n

def decompositionRemainderShapeTargetAudit :
    DecompositionRemainderShapeTargetAudit where
  remainder_atomFree := decompositionRemainderTailTargetFormula_atomFree
  remainder_eval_iff_one_le :=
    decompositionRemainderTailTargetFormula_eval_iff_one_le
  remainder_eval_iff_field_on_tail := fun {n} hn =>
    decompositionRemainderTailTargetFormula_eval_iff_field_on_tail
      (n := n) hn
  shape_atomFree := decompositionShapeCalibrationTargetFormula_atomFree
  shape_eval_iff_true :=
    decompositionShapeCalibrationTargetFormula_eval_iff_true
  shape_eval_iff_field :=
    decompositionShapeCalibrationTargetFormula_eval_iff_field

def decompositionCurrentGenuineEncodingGapCandidate :
    DecompositionGenuineEncodingGap where
  semanticAudit := decompositionSemanticCompressionCompilerAudit
  fieldAudit := decompositionDefaultFieldCompilerBundleAudit
  candidateTarget := decompositionAggregationEncodingTargetFormula
  candidateBound := decompositionAggregationSemanticCompressionBound

def decompositionCurrentGenuineEncodingGapFubiniEvalIff :
    decompositionCurrentGenuineEncodingGapCandidate.FubiniEvalIff where
  fubini_eval_iff := by
    intro n env
    constructor
    · intro _hwindow A B K
      exact decompositionFubiniBoxTargetFormula_eval_complete A B K
    · intro _htargets
      exact
        (decompositionAggregationFubiniBoxWindowFormula_eval_iff_true
          n env).2 trivial

def decompositionCurrentGenuineEncodingGapSplitEvalIff :
    decompositionCurrentGenuineEncodingGapCandidate.SplitEvalIff where
  split_eval_iff := by
    intro n env
    constructor
    · intro hwindow B
      have hn :=
        (decompositionAggregationIntegratedSplitPrefixWindowFormula_eval_iff_one_le
          n env).1 hwindow
      exact
        (decompositionIntegratedSplitPrefixTargetFormula_eval_iff_one_le
          n B).2 hn
    · intro htargets
      have hn :=
        (decompositionIntegratedSplitPrefixTargetFormula_eval_iff_one_le
          n 0).1 (htargets 0)
      exact
        (decompositionAggregationIntegratedSplitPrefixWindowFormula_eval_iff_one_le
          n env).2 hn

def decompositionCurrentGenuineEncodingGapRemainderEvalIff :
    decompositionCurrentGenuineEncodingGapCandidate.RemainderEvalIff where
  remainder_eval_iff := by
    intro n env
    exact
      (decompositionOneLeFormula_eval_iff n env).trans
        (decompositionRemainderTailTargetFormula_eval_iff_one_le n).symm

def decompositionCurrentGenuineEncodingGapShapeEvalIff :
    decompositionCurrentGenuineEncodingGapCandidate.ShapeEvalIff where
  shape_eval_iff := by
    intro n env
    exact
      (decompositionShapeCalibrationBodyFormula_eval_iff_true n env).trans
        (decompositionShapeCalibrationTargetFormula_eval_iff_true n).symm

def decompositionCurrentGenuineEncodingGapLocalEvalIffBundle :
    decompositionCurrentGenuineEncodingGapCandidate.LocalEvalIffBundle where
  candidateTarget_eq := rfl
  fubiniBoxTarget_eq := by
    intro A B K
    rfl
  integratedSplitPrefixTarget_eq := by
    intro n B
    rfl
  remainderTarget_eq := by
    intro n
    rfl
  shapeTarget_eq := by
    intro n
    rfl
  fubini := decompositionCurrentGenuineEncodingGapFubiniEvalIff
  split := decompositionCurrentGenuineEncodingGapSplitEvalIff
  remainder := decompositionCurrentGenuineEncodingGapRemainderEvalIff
  shape := decompositionCurrentGenuineEncodingGapShapeEvalIff

def decompositionCurrentGenuineEncodingGapEvalIffObligation :
    decompositionCurrentGenuineEncodingGapCandidate.EvalIffObligation :=
  DecompositionGenuineEncodingGap.EvalIffObligation.ofLocalBundle
    decompositionCurrentGenuineEncodingGapLocalEvalIffBundle

def decompositionCurrentGenuineEncodingGapAtomFreeObligation :
    decompositionCurrentGenuineEncodingGapCandidate.AtomFreeObligation where
  target_atomFree := by
    intro n
    exact decompositionAggregationEncodingTargetFormula_atomFree n

def decompositionCurrentGenuineEncodingGapCompileObligation :
    decompositionCurrentGenuineEncodingGapCandidate.CompileObligation where
  compile := by
    intro n _aggregation
    exact decompositionAggregationEncodingProofObject n
  compile_conclusion := by
    intro n _aggregation
    exact decompositionAggregationEncodingProofObject_conclusion n

def decompositionCurrentGenuineEncodingGapSizeBoundObligation :
    DecompositionGenuineEncodingGap.SizeBoundObligation
      decompositionCurrentGenuineEncodingGapCandidate
      decompositionCurrentGenuineEncodingGapCompileObligation where
  compile_size_plus_two_le := by
    intro n _aggregation
    change ((((decompositionAggregationEncodingProofObject n).size + 2 : ℕ) :
      ℝ)) ≤ decompositionAggregationSemanticCompressionBound n
    rw [decompositionAggregationEncodingProofObject_size_plus_two_eq_three]
    change (3 : ℝ) ≤ 3
    norm_num

def decompositionCurrentFormulaLocalEncodingClosure :
    decompositionCurrentGenuineEncodingGapCandidate.Closure where
  atomFreeObligation :=
    decompositionCurrentGenuineEncodingGapAtomFreeObligation
  evalIffObligation :=
    decompositionCurrentGenuineEncodingGapEvalIffObligation
  compileObligation :=
    decompositionCurrentGenuineEncodingGapCompileObligation
  sizeBoundObligation :=
    decompositionCurrentGenuineEncodingGapSizeBoundObligation

def decompositionCurrentFormulaLocalEncodedCompiler :
    EncodedFamilyAggregationCompiler
      decompositionAggregationSemanticCompressionBound :=
  decompositionCurrentFormulaLocalEncodingClosure
    |>.toEncodedFamilyAggregationCompiler

def decompositionCurrentFormulaLocalGlobalFamilyObligation :
    DecompositionGlobalFamilyCompilerObligation
      decompositionAggregationSemanticCompressionBound :=
  decompositionCurrentFormulaLocalEncodingClosure
    |>.toGlobalFamilyCompilerObligation
      decompositionAggregationSemanticCompressionBound_poly

/-- Field-derived completion route for the decomposition aggregation layer.

This is the audit closure that should replace the semantic-compression route
when connecting the decomposition component to the global S²₁ interface. -/
def decompositionFieldDerivedCorePureCompilerObligation :
    DecompositionCorePureCompilerObligation
      decompositionFieldDerivedAggregationBound :=
  decompositionFieldDerivedGlobalFamilyObligation.toCorePureCompilerObligation

def decompositionFieldDerivedExpandedPureCompilerObligation :
    DecompositionPureCompilerObligation
      decompositionFieldDerivedAggregationBound :=
  decompositionFieldDerivedGlobalFamilyObligation.toExpandedPureCompilerObligation

theorem decompositionFieldDerivedAggregationTargetFormula_eval_iff_core_source_certificate
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionFieldDerivedAggregationTargetFormula n) ↔
      Nonempty (DecompositionCoreSourceCertificate n) :=
  (decompositionFieldDerivedAggregationTargetFormula_eval_iff_formulaAggregation_fieldRoute
    n).trans
    ((DecompositionFormulaAggregationObligation.iff_oneLe_and_coreAll
      n).trans
      (DecompositionCoreSourceCertificate.nonempty_iff_oneLe_and_coreFields
        n).symm)

theorem decompositionFieldDerivedAggregationTargetFormula_eval_iff_expanded_source_certificate
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionFieldDerivedAggregationTargetFormula n) ↔
      Nonempty (DecompositionExpandedSourceCertificate n) :=
  (decompositionFieldDerivedAggregationTargetFormula_eval_iff_core_source_certificate
    n).trans
    (DecompositionCoreSourceCertificate.nonempty_iff_expanded n)

theorem decompositionFieldDerivedAggregationTargetFormula_eval_iff_source_on_tail
    {n : ℕ} (hn : 1 ≤ n) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionFieldDerivedAggregationTargetFormula n) ↔
      _root_.sondow_explicit_decomposition_prop n :=
  (decompositionFieldDerivedAggregationTargetFormula_eval_iff_core_source_certificate
    n).trans
    (DecompositionCoreSourceCertificate.nonempty_iff_source_of_one_le hn)

structure DecompositionFieldDerivedCompletionAudit where
  globalObligation :
    DecompositionGlobalFamilyCompilerObligation
      decompositionFieldDerivedAggregationBound
  corePureCompiler :
    DecompositionCorePureCompilerObligation
      decompositionFieldDerivedAggregationBound
  expandedPureCompiler :
    DecompositionPureCompilerObligation
      decompositionFieldDerivedAggregationBound
  targetName_ne_semanticName :
    decompositionFieldDerivedAggregationTargetName ≠
      decompositionAggregationEncodingTargetName
  target_eval_iff_formulaAggregation_fieldRoute :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (decompositionFieldDerivedAggregationTargetFormula n) ↔
        DecompositionFormulaAggregationObligation n
  target_eval_iff_core_source_certificate :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (decompositionFieldDerivedAggregationTargetFormula n) ↔
        Nonempty (DecompositionCoreSourceCertificate n)
  target_eval_iff_expanded_source_certificate :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (decompositionFieldDerivedAggregationTargetFormula n) ↔
        Nonempty (DecompositionExpandedSourceCertificate n)
  target_eval_iff_source_on_tail :
    ∀ {n : ℕ}, 1 ≤ n →
      (productLogDecompositionFormulaEval (fun _idx => n)
          (decompositionFieldDerivedAggregationTargetFormula n) ↔
        _root_.sondow_explicit_decomposition_prop n)
  compile_conclusion :
    ∀ n : ℕ, ∀ hsource : Nonempty (DecompositionCoreSourceCertificate n),
      (corePureCompiler.compile n hsource).conclusion =
        corePureCompiler.target n
  compile_size_plus_two_le :
    ∀ n : ℕ, ∀ hsource : Nonempty (DecompositionCoreSourceCertificate n),
      ((((corePureCompiler.compile n hsource).size + 2 : ℕ) : ℝ)) ≤
        decompositionFieldDerivedAggregationBound n

def decompositionFieldDerivedCompletionAudit :
    DecompositionFieldDerivedCompletionAudit where
  globalObligation := decompositionFieldDerivedGlobalFamilyObligation
  corePureCompiler := decompositionFieldDerivedCorePureCompilerObligation
  expandedPureCompiler := decompositionFieldDerivedExpandedPureCompilerObligation
  targetName_ne_semanticName :=
    decompositionFieldDerivedAggregationTargetName_ne_semanticName
  target_eval_iff_formulaAggregation_fieldRoute :=
    decompositionFieldDerivedAggregationTargetFormula_eval_iff_formulaAggregation_fieldRoute
  target_eval_iff_core_source_certificate :=
    decompositionFieldDerivedAggregationTargetFormula_eval_iff_core_source_certificate
  target_eval_iff_expanded_source_certificate :=
    decompositionFieldDerivedAggregationTargetFormula_eval_iff_expanded_source_certificate
  target_eval_iff_source_on_tail := by
    intro n hn
    exact
      decompositionFieldDerivedAggregationTargetFormula_eval_iff_source_on_tail
        hn
  compile_conclusion := by
    intro n hsource
    exact
      decompositionFieldDerivedCorePureCompilerObligation.compile_conclusion
        n hsource
  compile_size_plus_two_le := by
    intro n hsource
    exact
      decompositionFieldDerivedCorePureCompilerObligation.compile_size_plus_two_le
        n hsource

theorem decompositionSkeletonTargetFormula_eval_iff_source_on_tail
    {n : ℕ} (hn : 1 ≤ n) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionSkeletonTargetFormula n) ↔
      _root_.sondow_explicit_decomposition_prop n := by
  constructor
  · intro _h
    exact _root_.sondow_explicit_decomposition_prop_reproof hn
  · intro _hsource
    exact (decompositionSkeletonTargetFormula_eval_iff_one_le n).2 hn

structure DecompositionEventualPureCompiler
    (bound : ℕ → ℝ) where
  threshold : ℕ
  target : ℕ → BAFormula
  target_atomFree :
    ∀ n : ℕ, productLogDecompositionAtomFree (target n)
  target_eval_iff_source_on_tail :
    ∀ n : ℕ, threshold ≤ n →
      (productLogDecompositionFormulaEval (fun _idx => n) (target n) ↔
        _root_.sondow_explicit_decomposition_prop n)
  compile :
    ∀ n : ℕ, threshold ≤ n →
      _root_.sondow_explicit_decomposition_prop n →
        BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ n : ℕ, ∀ hn : threshold ≤ n,
      ∀ hsource : _root_.sondow_explicit_decomposition_prop n,
        (compile n hn hsource).conclusion = target n
  compile_size_plus_two_le :
    ∀ n : ℕ, ∀ hn : threshold ≤ n,
      ∀ hsource : _root_.sondow_explicit_decomposition_prop n,
        ((((compile n hn hsource).size + 2 : ℕ) : ℝ)) ≤ bound n

def decompositionSkeletonBound (_n : ℕ) : ℝ :=
  3

theorem decompositionSkeletonBound_poly :
    IsPolynomialBound decompositionSkeletonBound := by
  unfold decompositionSkeletonBound
  exact IsPolynomialBound.const (3 : ℝ)

def decompositionSkeletonEventualPureCompiler :
    DecompositionEventualPureCompiler decompositionSkeletonBound where
  threshold := 1
  target := decompositionSkeletonTargetFormula
  target_atomFree := decompositionSkeletonTargetFormula_atomFree
  target_eval_iff_source_on_tail := fun n hn =>
    decompositionSkeletonTargetFormula_eval_iff_source_on_tail (n := n) hn
  compile := by
    intro n _hn _hsource
    exact decompositionSkeletonProofObject n
  compile_conclusion := by
    intro n _hn _hsource
    exact decompositionSkeletonProofObject_conclusion n
  compile_size_plus_two_le := by
    intro n _hn _hsource
    rw [decompositionSkeletonProofObject_size_plus_two_eq_three]
    change (3 : ℝ) ≤ 3
    norm_num

theorem decompositionSkeletonTargetFormula_eval_iff_expanded_source_certificate
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionSkeletonTargetFormula n) ↔
      Nonempty (DecompositionExpandedSourceCertificate n) := by
  rw [decompositionSkeletonTargetFormula_eval_iff_one_le]
  constructor
  · intro hn
    exact ⟨DecompositionExpandedSourceCertificate.ofMainLibrary hn⟩
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact cert.one_le

theorem decompositionSkeletonTargetFormula_eval_iff_core_source_certificate
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionSkeletonTargetFormula n) ↔
      Nonempty (DecompositionCoreSourceCertificate n) := by
  rw [decompositionSkeletonTargetFormula_eval_iff_one_le]
  constructor
  · intro hn
    exact ⟨DecompositionCoreSourceCertificate.ofMainLibrary hn⟩
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact cert.one_le

theorem decompositionSkeletonPureS21Assembly_eval_iff_source_certificate
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionSkeletonPureS21Assembly.target n) ↔
      Nonempty (DecompositionExpandedSourceCertificate n) := by
  simpa [decompositionSkeletonPureS21Assembly] using
    decompositionSkeletonTargetFormula_eval_iff_expanded_source_certificate n

theorem decompositionSkeletonPureS21Assembly_eval_iff_core_source_certificate
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (decompositionSkeletonPureS21Assembly.target n) ↔
      Nonempty (DecompositionCoreSourceCertificate n) := by
  simpa [decompositionSkeletonPureS21Assembly] using
    decompositionSkeletonTargetFormula_eval_iff_core_source_certificate n

/-- Current semantic-compression compiler: the atom-free target is the `1 ≤ n`
skeleton, whose equivalence to the core certificate is supplied by the closed
main-library decomposition chain.  A field-level arithmetization can replace
this object through the same `DecompositionCorePureCompilerObligation` interface. -/
def decompositionSkeletonCorePureCompilerObligation :
    DecompositionCorePureCompilerObligation decompositionSkeletonBound where
  target := decompositionSkeletonTargetFormula
  target_atomFree := decompositionSkeletonTargetFormula_atomFree
  target_eval_iff_source :=
    decompositionSkeletonTargetFormula_eval_iff_core_source_certificate
  compile := by
    intro n _hsource
    exact decompositionSkeletonProofObject n
  compile_conclusion := by
    intro n _hsource
    exact decompositionSkeletonProofObject_conclusion n
  compile_size_plus_two_le := by
    intro n _hsource
    rw [decompositionSkeletonProofObject_size_plus_two_eq_three]
    change (3 : ℝ) ≤ 3
    norm_num

def decompositionSkeletonExpandedPureCompilerObligation :
    DecompositionPureCompilerObligation decompositionSkeletonBound :=
  DecompositionCorePureCompilerObligation.toExpanded
    decompositionSkeletonCorePureCompilerObligation

end SondowMainCheckedCodeBridge
