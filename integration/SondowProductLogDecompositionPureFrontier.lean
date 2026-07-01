/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProductLogPureFrontier
import integration.SondowDecompositionPureFrontier

open BoundedArithmeticLab

namespace SondowMainCheckedCodeBridge
/-!
## Product/log and decomposition combined pure-certificate adapter

This file only combines the separately checked product/log and decomposition
frontiers.  The component-level S21 work lives in the dedicated modules.
-/
inductive ProductLogDecompositionSourcePrimitive
  | product
  | logRelation
  | decomposition
  deriving DecidableEq, Repr

namespace ProductLogDecompositionSourcePrimitive

def eval : ProductLogDecompositionSourcePrimitive → ℕ → Prop
  | product, n => _root_.sondow_explicit_product_log_relation_prop n
  | logRelation, n => _root_.sondow_explicit_product_log_relation_prop n
  | decomposition, n => _root_.sondow_explicit_decomposition_prop n

def sourceCode :
    ProductLogDecompositionSourcePrimitive → ℕ →
      BoundedArithmeticLab.FormulaCode
  | product, n => sondowProductCode n
  | logRelation, n => sondowLogRelationCode n
  | decomposition, n => sondowDecompositionCode n

def projectAtomTarget :
    ProductLogDecompositionSourcePrimitive → ℕ → BAFormula
  | product, n => sondowProjectComponentFormulas.product n
  | logRelation, n => sondowProjectComponentFormulas.logRelation n
  | decomposition, n => sondowProjectComponentFormulas.decomposition n

def sourceBound
    (bounds : SondowComponentBounds) :
    ProductLogDecompositionSourcePrimitive → ℕ → ℝ
  | product, n => bounds.product n
  | logRelation, n => bounds.logRelation n
  | decomposition, n => bounds.decomposition n

theorem product_eval_iff_logRelation_eval (n : ℕ) :
    eval product n ↔ eval logRelation n :=
  Iff.rfl

theorem product_eval_complete (n : ℕ) :
    eval product n :=
  _root_.sondow_explicit_product_log_relation_prop_reproof n

theorem logRelation_eval_complete (n : ℕ) :
    eval logRelation n :=
  _root_.sondow_explicit_product_log_relation_prop_reproof n

theorem decomposition_eval_complete_of_one_le
    {n : ℕ} (hn : 1 ≤ n) :
    eval decomposition n :=
  _root_.sondow_explicit_decomposition_prop_reproof hn

theorem all_sources_eventually_complete :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      eval product n ∧ eval logRelation n ∧ eval decomposition n := by
  refine ⟨1, ?_⟩
  intro n hn
  exact
    ⟨product_eval_complete n,
      logRelation_eval_complete n,
      decomposition_eval_complete_of_one_le hn⟩

theorem projectAtomTarget_not_atomFree
    (p : ProductLogDecompositionSourcePrimitive) (n : ℕ) :
    ¬ productLogDecompositionAtomFree (projectAtomTarget p n) := by
  cases p <;> intro h <;> cases h

end ProductLogDecompositionSourcePrimitive

inductive ProductLogDecompositionExpandedFormula
  | primitive : ProductLogDecompositionSourcePrimitive → ℕ →
      ProductLogDecompositionExpandedFormula
  | and : ProductLogDecompositionExpandedFormula →
      ProductLogDecompositionExpandedFormula →
      ProductLogDecompositionExpandedFormula
  deriving DecidableEq, Repr

namespace ProductLogDecompositionExpandedFormula

def eval : ProductLogDecompositionExpandedFormula → Prop
  | primitive p n => ProductLogDecompositionSourcePrimitive.eval p n
  | and φ ψ => eval φ ∧ eval ψ

def productCertificate (n : ℕ) :
    ProductLogDecompositionExpandedFormula :=
  primitive ProductLogDecompositionSourcePrimitive.product n

def logRelationCertificate (n : ℕ) :
    ProductLogDecompositionExpandedFormula :=
  primitive ProductLogDecompositionSourcePrimitive.logRelation n

def decompositionCertificate (n : ℕ) :
    ProductLogDecompositionExpandedFormula :=
  primitive ProductLogDecompositionSourcePrimitive.decomposition n

def allThreeCertificate (n : ℕ) :
    ProductLogDecompositionExpandedFormula :=
  and (productCertificate n)
    (and (logRelationCertificate n) (decompositionCertificate n))

theorem eval_productCertificate_iff (n : ℕ) :
    eval (productCertificate n) ↔
      _root_.sondow_explicit_product_log_relation_prop n :=
  Iff.rfl

theorem eval_logRelationCertificate_iff (n : ℕ) :
    eval (logRelationCertificate n) ↔
      _root_.sondow_explicit_product_log_relation_prop n :=
  Iff.rfl

theorem eval_decompositionCertificate_iff (n : ℕ) :
    eval (decompositionCertificate n) ↔
      _root_.sondow_explicit_decomposition_prop n :=
  Iff.rfl

theorem eval_allThreeCertificate_iff (n : ℕ) :
    eval (allThreeCertificate n) ↔
      _root_.sondow_explicit_product_log_relation_prop n ∧
        _root_.sondow_explicit_product_log_relation_prop n ∧
        _root_.sondow_explicit_decomposition_prop n :=
  Iff.rfl

theorem allThreeCertificate_eventually_complete :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → eval (allThreeCertificate n) := by
  rcases
    ProductLogDecompositionSourcePrimitive.all_sources_eventually_complete with
    ⟨N, hN⟩
  exact ⟨N, fun n hn => hN n hn⟩

end ProductLogDecompositionExpandedFormula

/-- Audit label for the decomposition component selected by the combined
product/log/decomposition frontier.  The skeleton route is kept as a named
legacy possibility, but the exported frontier below chooses the field-derived
completion route. -/
inductive ProductLogDecompositionDecompositionRoute
  | skeletonSemanticCompression
  | fieldDerivedCompletion
  deriving DecidableEq, Repr

inductive ProductLogDecompositionProductLogRoute
  | arithmeticCompletion
  deriving DecidableEq, Repr

/-- Closed compiler data for the product/log branches of
`ProductLogDecompositionPureCompiler`.  This deliberately stops before the
decomposition branch, whose code-alignment problem is separate from the
product/log separated-target construction. -/
structure ProductLogDecompositionProductLogBranchCompiler where
  productBound : ℕ → ℝ
  logRelationBound : ℕ → ℝ
  productBound_poly : IsPolynomialBound productBound
  logRelationBound_poly : IsPolynomialBound logRelationBound
  target : ProductLogDecompositionSourcePrimitive → ℕ → BAFormula
  code : BAFormula → BoundedArithmeticLab.FormulaCode
  target_product_eq :
    ∀ n : ℕ,
      target ProductLogDecompositionSourcePrimitive.product n =
        productLogSeparatedTargetCompletionAudit.productTarget n
  target_logRelation_eq :
    ∀ n : ℕ,
      target ProductLogDecompositionSourcePrimitive.logRelation n =
        productLogSeparatedTargetCompletionAudit.logRelationTarget n
  product_atomFree :
    ∀ n : ℕ,
      productLogDecompositionAtomFree
        (target ProductLogDecompositionSourcePrimitive.product n)
  logRelation_atomFree :
    ∀ n : ℕ,
      productLogDecompositionAtomFree
        (target ProductLogDecompositionSourcePrimitive.logRelation n)
  product_eval_iff_source :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (target ProductLogDecompositionSourcePrimitive.product n) ↔
        ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.product n
  logRelation_eval_iff_source :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (target ProductLogDecompositionSourcePrimitive.logRelation n) ↔
        ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.logRelation n
  product_formula_code_eq :
    ∀ n : ℕ,
      code (target ProductLogDecompositionSourcePrimitive.product n) =
        ProductLogDecompositionSourcePrimitive.sourceCode
          ProductLogDecompositionSourcePrimitive.product n
  logRelation_formula_code_eq :
    ∀ n : ℕ,
      code (target ProductLogDecompositionSourcePrimitive.logRelation n) =
        ProductLogDecompositionSourcePrimitive.sourceCode
          ProductLogDecompositionSourcePrimitive.logRelation n
  product_compile :
    ∀ n : ℕ,
      ProductLogDecompositionSourcePrimitive.eval
        ProductLogDecompositionSourcePrimitive.product n →
        BAProofObject BussS21Axiom
  logRelation_compile :
    ∀ n : ℕ,
      ProductLogDecompositionSourcePrimitive.eval
        ProductLogDecompositionSourcePrimitive.logRelation n →
        BAProofObject BussS21Axiom
  product_compile_conclusion :
    ∀ n : ℕ,
      ∀ hp : ProductLogDecompositionSourcePrimitive.eval
        ProductLogDecompositionSourcePrimitive.product n,
        (product_compile n hp).conclusion =
          target ProductLogDecompositionSourcePrimitive.product n
  logRelation_compile_conclusion :
    ∀ n : ℕ,
      ∀ hp : ProductLogDecompositionSourcePrimitive.eval
        ProductLogDecompositionSourcePrimitive.logRelation n,
        (logRelation_compile n hp).conclusion =
          target ProductLogDecompositionSourcePrimitive.logRelation n
  product_size_plus_two_le :
    ∀ n : ℕ,
      ∀ hp : ProductLogDecompositionSourcePrimitive.eval
        ProductLogDecompositionSourcePrimitive.product n,
        ((((product_compile n hp).size + 2 : ℕ) : ℝ)) ≤ productBound n
  logRelation_size_plus_two_le :
    ∀ n : ℕ,
      ∀ hp : ProductLogDecompositionSourcePrimitive.eval
        ProductLogDecompositionSourcePrimitive.logRelation n,
        ((((logRelation_compile n hp).size + 2 : ℕ) : ℝ)) ≤
          logRelationBound n

def productLogDecompositionProductLogBranchTarget :
    ProductLogDecompositionSourcePrimitive → ℕ → BAFormula
  | ProductLogDecompositionSourcePrimitive.product, n =>
      productLogSeparatedTargetCompletionAudit.productTarget n
  | ProductLogDecompositionSourcePrimitive.logRelation, n =>
      productLogSeparatedTargetCompletionAudit.logRelationTarget n
  | ProductLogDecompositionSourcePrimitive.decomposition, n =>
      productLogSeparatedTargetCompletionAudit.productTarget n

def productLogDecompositionProductLogBranchCompiler :
    ProductLogDecompositionProductLogBranchCompiler where
  productBound := productLogArithmeticBound
  logRelationBound := productLogArithmeticBound
  productBound_poly := productLogArithmeticBound_poly
  logRelationBound_poly := productLogArithmeticBound_poly
  target := productLogDecompositionProductLogBranchTarget
  code := productLogSeparatedTargetCompletionAudit.code
  target_product_eq := by
    intro n
    rfl
  target_logRelation_eq := by
    intro n
    rfl
  product_atomFree := by
    intro n
    exact productLogSeparatedTargetCompletionAudit.product_atomFree n
  logRelation_atomFree := by
    intro n
    exact productLogSeparatedTargetCompletionAudit.logRelation_atomFree n
  product_eval_iff_source := by
    intro n
    exact productLogSeparatedTargetCompletionAudit.product_eval_iff_source n
  logRelation_eval_iff_source := by
    intro n
    exact productLogSeparatedTargetCompletionAudit.logRelation_eval_iff_source n
  product_formula_code_eq := by
    intro n
    exact productLogSeparatedTargetCompletionAudit.code_product n
  logRelation_formula_code_eq := by
    intro n
    exact productLogSeparatedTargetCompletionAudit.code_logRelation n
  product_compile := by
    intro n _hp
    exact productLogSeparatedTargetCompletionAudit.productProof n
  logRelation_compile := by
    intro n _hp
    exact productLogSeparatedTargetCompletionAudit.logRelationProof n
  product_compile_conclusion := by
    intro n _hp
    exact productLogSeparatedTargetCompletionAudit.productProof_conclusion n
  logRelation_compile_conclusion := by
    intro n _hp
    exact productLogSeparatedTargetCompletionAudit.logRelationProof_conclusion n
  product_size_plus_two_le := by
    intro n _hp
    exact productLogSeparatedTargetCompletionAudit.product_size_plus_two_le n
  logRelation_size_plus_two_le := by
    intro n _hp
    exact
      productLogSeparatedTargetCompletionAudit.logRelation_size_plus_two_le n

def productLogDecompositionPureTargetName : ℕ := 6107

def productLogDecompositionPureTargetFormula (n : ℕ) : BAFormula :=
  BAFormula.and (productLogTaggedIndexFormula n)
    (polytimeDefinabilityFormula productLogDecompositionPureTargetName
      (decompositionFieldDerivedAggregationTargetFormula n))

theorem productLogDecompositionPureTargetFormula_atomFree (n : ℕ) :
    productLogDecompositionAtomFree
      (productLogDecompositionPureTargetFormula n) := by
  exact
    ⟨productLogTaggedIndexFormula_atomFree n,
      by
        simpa [productLogDecompositionPureTargetFormula,
          polytimeDefinabilityFormula, productLogDecompositionAtomFree,
          productLogDecompositionBaFormulaAtomFree]
          using
            decompositionFieldDerivedAggregationTargetFormula_atomFree n⟩

theorem decompositionFieldDerivedAggregationTargetFormula_eval_iff_source_on_tail_env
    {n : ℕ} (hn : 1 ≤ n) (env : ℕ → ℕ) :
    productLogDecompositionFormulaEval env
        (decompositionFieldDerivedAggregationTargetFormula n) ↔
      _root_.sondow_explicit_decomposition_prop n := by
  constructor
  · intro htarget
    rcases htarget with ⟨value, _hvalue, hbody⟩
    have hbundle :
        DecompositionAggregationPayloadWindowBundle n :=
      (decompositionAggregationEncodingBodyFormula_eval_iff_payloadWindowBundle
        n
        (Function.update env decompositionFieldDerivedAggregationTargetName
          value)).1 hbody
    have haggregation :
        DecompositionFormulaAggregationObligation n :=
      hbundle.to_formulaAggregation_fieldRoute
    have hfields :
        1 ≤ n ∧ DecompositionAnalyticField.coreAll n :=
      (DecompositionFormulaAggregationObligation.iff_oneLe_and_coreAll
        n).1 haggregation
    have hcore :
        Nonempty (DecompositionCoreSourceCertificate n) :=
      (DecompositionCoreSourceCertificate.nonempty_iff_oneLe_and_coreFields
        n).2
        ⟨hn, hfields.2⟩
    exact
      (DecompositionCoreSourceCertificate.nonempty_iff_source_of_one_le
        hn).1 hcore
  · intro hsource
    have hcore :
        Nonempty (DecompositionCoreSourceCertificate n) :=
      (DecompositionCoreSourceCertificate.nonempty_iff_source_of_one_le
        hn).2 hsource
    have hfields :
        1 ≤ n ∧ DecompositionAnalyticField.coreAll n :=
      (DecompositionCoreSourceCertificate.nonempty_iff_oneLe_and_coreFields
        n).1 hcore
    have hbundle :
        DecompositionAggregationPayloadWindowBundle n :=
      (DecompositionAggregationPayloadWindowBundle.iff_one_le n).2
        hfields.1
    refine ⟨0, ?_, ?_⟩
    · simp [productLogDecompositionBaTermEval]
    · exact
        (decompositionAggregationEncodingBodyFormula_eval_iff_payloadWindowBundle
          n
          (Function.update env decompositionFieldDerivedAggregationTargetName
            0)).2 hbundle

theorem productLogDecompositionPureTargetFormula_eval_iff_source_on_tail
    {n : ℕ} (hn : 1 ≤ n) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogDecompositionPureTargetFormula n) ↔
      _root_.sondow_explicit_decomposition_prop n := by
  constructor
  · intro htarget
    rcases htarget with ⟨_hindex, hbody⟩
    rcases hbody with ⟨value, _hvalue, htargetBody⟩
    exact
      (decompositionFieldDerivedAggregationTargetFormula_eval_iff_source_on_tail_env
        hn
        (Function.update (fun _idx => n)
          productLogDecompositionPureTargetName value)).1
        htargetBody
  · intro hsource
    exact
      ⟨productLogTaggedIndexFormula_eval n (fun _idx => n),
        ⟨0, by simp [productLogDecompositionBaTermEval],
          (decompositionFieldDerivedAggregationTargetFormula_eval_iff_source_on_tail_env
            hn
            (Function.update (fun _idx => n)
              productLogDecompositionPureTargetName 0)).2 hsource⟩⟩

def productLogDecompositionPureProofObject (n : ℕ) :
    BAProofObject BussS21Axiom :=
  (productLogTaggedIndexProofObject n).andIntro
    (productLogDecompositionPolytimeDefinabilityProofObject
      productLogDecompositionPureTargetName
      (decompositionFieldDerivedAggregationTargetFormula n))

theorem productLogDecompositionPureProofObject_conclusion (n : ℕ) :
    (productLogDecompositionPureProofObject n).conclusion =
      productLogDecompositionPureTargetFormula n := by
  rfl

theorem productLogDecompositionPureProofObject_size_plus_two_eq_five
    (n : ℕ) :
    ((((productLogDecompositionPureProofObject n).size + 2 : ℕ) : ℝ)) = 5 := by
  change (((1 + 1 + 1 + 2 : ℕ) : ℝ)) = 5
  norm_num

def productLogDecompositionPureBound (_n : ℕ) : ℝ :=
  5

theorem productLogDecompositionPureBound_poly :
    IsPolynomialBound productLogDecompositionPureBound := by
  unfold productLogDecompositionPureBound
  exact IsPolynomialBound.const (5 : ℝ)

def productLogDecompositionFullCodeRouter
    (φ : BAFormula) : BoundedArithmeticLab.FormulaCode :=
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
            else if targetName = productLogDecompositionPureTargetName then
              sondowDecompositionCode n
            else
              externalPudlakCode 0
          else
            externalPudlakCode 0
      | _, _ => externalPudlakCode 0
  | _ => externalPudlakCode 0

theorem productLogDecompositionFullCodeRouter_product (n : ℕ) :
    productLogDecompositionFullCodeRouter
        (productLogSeparatedTargetCompletionAudit.productTarget n) =
      sondowProductCode n := by
  simp [productLogDecompositionFullCodeRouter,
    productLogSeparatedTargetCompletionAudit,
    productLogProductPureTargetFormula, productLogTaggedIndexFormula,
    productLogTaggedBodyTargetFormula, polytimeDefinabilityFormula,
    productLogProductPureTargetName]

theorem productLogDecompositionFullCodeRouter_logRelation (n : ℕ) :
    productLogDecompositionFullCodeRouter
        (productLogSeparatedTargetCompletionAudit.logRelationTarget n) =
      sondowLogRelationCode n := by
  simp [productLogDecompositionFullCodeRouter,
    productLogSeparatedTargetCompletionAudit,
    productLogLogRelationPureTargetFormula, productLogTaggedIndexFormula,
    productLogTaggedBodyTargetFormula, polytimeDefinabilityFormula,
    productLogProductPureTargetName, productLogLogRelationPureTargetName]

theorem productLogDecompositionFullCodeRouter_decomposition (n : ℕ) :
    productLogDecompositionFullCodeRouter
        (productLogDecompositionPureTargetFormula n) =
      sondowDecompositionCode n := by
  simp [productLogDecompositionFullCodeRouter,
    productLogDecompositionPureTargetFormula, productLogTaggedIndexFormula,
    polytimeDefinabilityFormula, productLogProductPureTargetName,
    productLogLogRelationPureTargetName, productLogDecompositionPureTargetName]

def productLogDecompositionTailPureTarget :
    ProductLogDecompositionSourcePrimitive → ℕ → BAFormula
  | ProductLogDecompositionSourcePrimitive.product, n =>
      productLogSeparatedTargetCompletionAudit.productTarget n
  | ProductLogDecompositionSourcePrimitive.logRelation, n =>
      productLogSeparatedTargetCompletionAudit.logRelationTarget n
  | ProductLogDecompositionSourcePrimitive.decomposition, n =>
      productLogDecompositionPureTargetFormula n

def productLogDecompositionTailPureBounds :
    SondowComponentBounds where
  product := productLogArithmeticBound
  logRelation := productLogArithmeticBound
  decomposition := productLogDecompositionPureBound
  threePow := fun _n => 0
  payload := fun _n => 0
  product_poly := productLogArithmeticBound_poly
  log_poly := productLogArithmeticBound_poly
  decomposition_poly := productLogDecompositionPureBound_poly
  threePow_poly := IsPolynomialBound.const (0 : ℝ)
  payload_poly := IsPolynomialBound.const (0 : ℝ)

structure ProductLogDecompositionTailPureCompiler
    (bounds : SondowComponentBounds) where
  threshold : ℕ
  target : ProductLogDecompositionSourcePrimitive → ℕ → BAFormula
  code : BAFormula → BoundedArithmeticLab.FormulaCode
  target_atomFree :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      productLogDecompositionAtomFree (target p n)
  target_eval_iff_source_on_tail :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      threshold ≤ n →
        (productLogDecompositionFormulaEval (fun _idx => n)
            (target p n) ↔
          ProductLogDecompositionSourcePrimitive.eval p n)
  formula_code_eq :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      code (target p n) =
        ProductLogDecompositionSourcePrimitive.sourceCode p n
  compile :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      threshold ≤ n →
        ProductLogDecompositionSourcePrimitive.eval p n →
          BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      ∀ hn : threshold ≤ n,
      ∀ hp : ProductLogDecompositionSourcePrimitive.eval p n,
        (compile p n hn hp).conclusion = target p n
  compile_size_plus_two_le :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      ∀ hn : threshold ≤ n,
      ∀ hp : ProductLogDecompositionSourcePrimitive.eval p n,
        ((((compile p n hn hp).size + 2 : ℕ) : ℝ)) ≤
          ProductLogDecompositionSourcePrimitive.sourceBound bounds p n

def productLogDecompositionTailPureCompiler :
    ProductLogDecompositionTailPureCompiler
      productLogDecompositionTailPureBounds where
  threshold := 1
  target := productLogDecompositionTailPureTarget
  code := productLogDecompositionFullCodeRouter
  target_atomFree := by
    intro p n
    cases p
    · exact productLogSeparatedTargetCompletionAudit.product_atomFree n
    · exact productLogSeparatedTargetCompletionAudit.logRelation_atomFree n
    · exact productLogDecompositionPureTargetFormula_atomFree n
  target_eval_iff_source_on_tail := by
    intro p n hn
    cases p
    · exact productLogSeparatedTargetCompletionAudit.product_eval_iff_source n
    · exact productLogSeparatedTargetCompletionAudit.logRelation_eval_iff_source n
    · exact productLogDecompositionPureTargetFormula_eval_iff_source_on_tail hn
  formula_code_eq := by
    intro p n
    cases p
    · exact productLogDecompositionFullCodeRouter_product n
    · exact productLogDecompositionFullCodeRouter_logRelation n
    · exact productLogDecompositionFullCodeRouter_decomposition n
  compile := by
    intro p n _hn _hp
    cases p
    · exact productLogSeparatedTargetCompletionAudit.productProof n
    · exact productLogSeparatedTargetCompletionAudit.logRelationProof n
    · exact productLogDecompositionPureProofObject n
  compile_conclusion := by
    intro p n _hn _hp
    cases p
    · exact productLogSeparatedTargetCompletionAudit.productProof_conclusion n
    · exact productLogSeparatedTargetCompletionAudit.logRelationProof_conclusion n
    · exact productLogDecompositionPureProofObject_conclusion n
  compile_size_plus_two_le := by
    intro p n _hn _hp
    cases p
    · exact productLogSeparatedTargetCompletionAudit.product_size_plus_two_le n
    · exact productLogSeparatedTargetCompletionAudit.logRelation_size_plus_two_le n
    · rw [productLogDecompositionPureProofObject_size_plus_two_eq_five]
      simp [ProductLogDecompositionSourcePrimitive.sourceBound,
        productLogDecompositionTailPureBounds, productLogDecompositionPureBound]

def productLogDecompositionTailTargetsEval
    {bounds : SondowComponentBounds}
    (compiler : ProductLogDecompositionTailPureCompiler bounds)
    (n : ℕ) : Prop :=
  productLogDecompositionFormulaEval (fun _idx => n)
      (compiler.target ProductLogDecompositionSourcePrimitive.product n) ∧
    productLogDecompositionFormulaEval (fun _idx => n)
      (compiler.target ProductLogDecompositionSourcePrimitive.logRelation n) ∧
    productLogDecompositionFormulaEval (fun _idx => n)
      (compiler.target ProductLogDecompositionSourcePrimitive.decomposition n)

namespace ProductLogDecompositionTailPureCompiler

theorem targets_eval_iff_sources_on_tail
    {bounds : SondowComponentBounds}
    (compiler : ProductLogDecompositionTailPureCompiler bounds)
    {n : ℕ} (hn : compiler.threshold ≤ n) :
    productLogDecompositionTailTargetsEval compiler n ↔
      ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.product n ∧
        ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.logRelation n ∧
        ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.decomposition n := by
  constructor
  · intro htargets
    exact
      ⟨(compiler.target_eval_iff_source_on_tail
          ProductLogDecompositionSourcePrimitive.product n hn).1
          htargets.1,
        (compiler.target_eval_iff_source_on_tail
          ProductLogDecompositionSourcePrimitive.logRelation n hn).1
          htargets.2.1,
        (compiler.target_eval_iff_source_on_tail
          ProductLogDecompositionSourcePrimitive.decomposition n hn).1
          htargets.2.2⟩
  · intro hsources
    exact
      ⟨(compiler.target_eval_iff_source_on_tail
          ProductLogDecompositionSourcePrimitive.product n hn).2
          hsources.1,
        (compiler.target_eval_iff_source_on_tail
          ProductLogDecompositionSourcePrimitive.logRelation n hn).2
          hsources.2.1,
        (compiler.target_eval_iff_source_on_tail
          ProductLogDecompositionSourcePrimitive.decomposition n hn).2
          hsources.2.2⟩

theorem targets_eval_iff_allThreeCertificate_on_tail
    {bounds : SondowComponentBounds}
    (compiler : ProductLogDecompositionTailPureCompiler bounds)
    {n : ℕ} (hn : compiler.threshold ≤ n) :
    productLogDecompositionTailTargetsEval compiler n ↔
      ProductLogDecompositionExpandedFormula.eval
        (ProductLogDecompositionExpandedFormula.allThreeCertificate n) :=
  (compiler.targets_eval_iff_sources_on_tail hn).trans
    (ProductLogDecompositionExpandedFormula.eval_allThreeCertificate_iff
      n).symm

structure ProofTriple
    {bounds : SondowComponentBounds}
    (compiler : ProductLogDecompositionTailPureCompiler bounds)
    (n : ℕ) where
  tail : compiler.threshold ≤ n
  productProof : BAProofObject BussS21Axiom
  logRelationProof : BAProofObject BussS21Axiom
  decompositionProof : BAProofObject BussS21Axiom
  product_conclusion :
    productProof.conclusion =
      compiler.target ProductLogDecompositionSourcePrimitive.product n
  logRelation_conclusion :
    logRelationProof.conclusion =
      compiler.target ProductLogDecompositionSourcePrimitive.logRelation n
  decomposition_conclusion :
    decompositionProof.conclusion =
      compiler.target ProductLogDecompositionSourcePrimitive.decomposition n
  product_size_plus_two_le :
    ((((productProof.size + 2 : ℕ) : ℝ)) ≤ bounds.product n)
  logRelation_size_plus_two_le :
    ((((logRelationProof.size + 2 : ℕ) : ℝ)) ≤ bounds.logRelation n)
  decomposition_size_plus_two_le :
    ((((decompositionProof.size + 2 : ℕ) : ℝ)) ≤
      bounds.decomposition n)

def proofTriple
    {bounds : SondowComponentBounds}
    (compiler : ProductLogDecompositionTailPureCompiler bounds)
    (n : ℕ)
    (hn : compiler.threshold ≤ n)
    (hsources :
      ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.product n ∧
        ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.logRelation n ∧
        ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.decomposition n) :
    ProofTriple compiler n where
  tail := hn
  productProof :=
    compiler.compile ProductLogDecompositionSourcePrimitive.product n hn
      hsources.1
  logRelationProof :=
    compiler.compile ProductLogDecompositionSourcePrimitive.logRelation n hn
      hsources.2.1
  decompositionProof :=
    compiler.compile ProductLogDecompositionSourcePrimitive.decomposition n hn
      hsources.2.2
  product_conclusion :=
    compiler.compile_conclusion
      ProductLogDecompositionSourcePrimitive.product n hn hsources.1
  logRelation_conclusion :=
    compiler.compile_conclusion
      ProductLogDecompositionSourcePrimitive.logRelation n hn hsources.2.1
  decomposition_conclusion :=
    compiler.compile_conclusion
      ProductLogDecompositionSourcePrimitive.decomposition n hn hsources.2.2
  product_size_plus_two_le := by
    simpa [ProductLogDecompositionSourcePrimitive.sourceBound] using
      compiler.compile_size_plus_two_le
        ProductLogDecompositionSourcePrimitive.product n hn hsources.1
  logRelation_size_plus_two_le := by
    simpa [ProductLogDecompositionSourcePrimitive.sourceBound] using
      compiler.compile_size_plus_two_le
        ProductLogDecompositionSourcePrimitive.logRelation n hn hsources.2.1
  decomposition_size_plus_two_le := by
    simpa [ProductLogDecompositionSourcePrimitive.sourceBound] using
      compiler.compile_size_plus_two_le
        ProductLogDecompositionSourcePrimitive.decomposition n hn hsources.2.2

theorem proofTriple_eventually_of_threshold_one
    {bounds : SondowComponentBounds}
    (compiler : ProductLogDecompositionTailPureCompiler bounds)
    (hthreshold : compiler.threshold = 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty (ProofTriple compiler n) := by
  refine ⟨1, ?_⟩
  intro n hn
  have htail : compiler.threshold ≤ n := by
    simpa [hthreshold] using hn
  have hsources :
      ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.product n ∧
        ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.logRelation n ∧
        ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.decomposition n := by
    exact
      ⟨ProductLogDecompositionSourcePrimitive.product_eval_complete n,
        ProductLogDecompositionSourcePrimitive.logRelation_eval_complete n,
        ProductLogDecompositionSourcePrimitive.decomposition_eval_complete_of_one_le
          hn⟩
  exact ⟨compiler.proofTriple n htail hsources⟩

theorem targets_eval_eventually_of_threshold_one
    {bounds : SondowComponentBounds}
    (compiler : ProductLogDecompositionTailPureCompiler bounds)
    (hthreshold : compiler.threshold = 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      productLogDecompositionTailTargetsEval compiler n := by
  refine ⟨1, ?_⟩
  intro n hn
  have htail : compiler.threshold ≤ n := by
    simpa [hthreshold] using hn
  have hsources :
      ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.product n ∧
        ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.logRelation n ∧
        ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.decomposition n := by
    exact
      ⟨ProductLogDecompositionSourcePrimitive.product_eval_complete n,
        ProductLogDecompositionSourcePrimitive.logRelation_eval_complete n,
        ProductLogDecompositionSourcePrimitive.decomposition_eval_complete_of_one_le
          hn⟩
  exact (compiler.targets_eval_iff_sources_on_tail htail).2 hsources

end ProductLogDecompositionTailPureCompiler

structure ProductLogDecompositionTailCompletionAudit where
  compiler :
    ProductLogDecompositionTailPureCompiler
      productLogDecompositionTailPureBounds
  compiler_eq :
    compiler = productLogDecompositionTailPureCompiler
  threshold_eq_one :
    compiler.threshold = 1
  target_eq :
    compiler.target = productLogDecompositionTailPureTarget
  code_eq :
    compiler.code = productLogDecompositionFullCodeRouter
  target_atomFree :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      productLogDecompositionAtomFree (compiler.target p n)
  target_eval_iff_source_on_tail :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      compiler.threshold ≤ n →
        (productLogDecompositionFormulaEval (fun _idx => n)
            (compiler.target p n) ↔
          ProductLogDecompositionSourcePrimitive.eval p n)
  targets_eval_iff_sources_on_tail :
    ∀ n : ℕ, compiler.threshold ≤ n →
      (productLogDecompositionTailTargetsEval compiler n ↔
        ProductLogDecompositionSourcePrimitive.eval
            ProductLogDecompositionSourcePrimitive.product n ∧
          ProductLogDecompositionSourcePrimitive.eval
            ProductLogDecompositionSourcePrimitive.logRelation n ∧
          ProductLogDecompositionSourcePrimitive.eval
            ProductLogDecompositionSourcePrimitive.decomposition n)
  targets_eval_iff_allThreeCertificate_on_tail :
    ∀ n : ℕ, compiler.threshold ≤ n →
      (productLogDecompositionTailTargetsEval compiler n ↔
        ProductLogDecompositionExpandedFormula.eval
          (ProductLogDecompositionExpandedFormula.allThreeCertificate n))
  formula_code_eq :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      compiler.code (compiler.target p n) =
        ProductLogDecompositionSourcePrimitive.sourceCode p n
  compile_conclusion :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      ∀ hn : compiler.threshold ≤ n,
      ∀ hp : ProductLogDecompositionSourcePrimitive.eval p n,
        (compiler.compile p n hn hp).conclusion = compiler.target p n
  compile_size_plus_two_le :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      ∀ hn : compiler.threshold ≤ n,
      ∀ hp : ProductLogDecompositionSourcePrimitive.eval p n,
        ((((compiler.compile p n hn hp).size + 2 : ℕ) : ℝ)) ≤
          ProductLogDecompositionSourcePrimitive.sourceBound
            productLogDecompositionTailPureBounds p n
  proofTriple_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (ProductLogDecompositionTailPureCompiler.ProofTriple compiler n)
  targets_eval_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      productLogDecompositionTailTargetsEval compiler n

def productLogDecompositionTailCompletionAudit :
    ProductLogDecompositionTailCompletionAudit where
  compiler := productLogDecompositionTailPureCompiler
  compiler_eq := rfl
  threshold_eq_one := rfl
  target_eq := rfl
  code_eq := rfl
  target_atomFree :=
    productLogDecompositionTailPureCompiler.target_atomFree
  target_eval_iff_source_on_tail :=
    productLogDecompositionTailPureCompiler.target_eval_iff_source_on_tail
  targets_eval_iff_sources_on_tail := by
    intro n
    exact
      productLogDecompositionTailPureCompiler.targets_eval_iff_sources_on_tail
        (n := n)
  targets_eval_iff_allThreeCertificate_on_tail := by
    intro n
    exact
      productLogDecompositionTailPureCompiler
        |>.targets_eval_iff_allThreeCertificate_on_tail (n := n)
  formula_code_eq :=
    productLogDecompositionTailPureCompiler.formula_code_eq
  compile_conclusion :=
    productLogDecompositionTailPureCompiler.compile_conclusion
  compile_size_plus_two_le :=
    productLogDecompositionTailPureCompiler.compile_size_plus_two_le
  proofTriple_eventually :=
    ProductLogDecompositionTailPureCompiler.proofTriple_eventually_of_threshold_one
      productLogDecompositionTailPureCompiler rfl
  targets_eval_eventually :=
    ProductLogDecompositionTailPureCompiler.targets_eval_eventually_of_threshold_one
      productLogDecompositionTailPureCompiler rfl

structure ProductLogDecompositionPartialPureFrontier where
  productLogArithmetic : ProductLogArithmeticPureS21Assembly
  productLogCompletion : ProductLogCompletionAudit
  productLogSeparatedCompletion : ProductLogSeparatedTargetCompletionAudit
  productLogBranchCompiler :
    ProductLogDecompositionProductLogBranchCompiler
  tailPureCompiler :
    ProductLogDecompositionTailPureCompiler
      productLogDecompositionTailPureBounds
  tailCompletion :
    ProductLogDecompositionTailCompletionAudit
  productLogRoute : ProductLogDecompositionProductLogRoute
  productLogRoute_eq :
    productLogRoute =
      ProductLogDecompositionProductLogRoute.arithmeticCompletion
  productLogArithmetic_eq_completionAssembly :
    productLogArithmetic = productLogCompletion.assembly
  productLogBranchCompiler_eq :
    productLogBranchCompiler =
      productLogDecompositionProductLogBranchCompiler
  tailPureCompiler_eq :
    tailPureCompiler =
      productLogDecompositionTailPureCompiler
  tailCompletion_eq :
    tailCompletion =
      productLogDecompositionTailCompletionAudit
  tailCompletion_compiler_eq :
    tailCompletion.compiler = tailPureCompiler
  decompositionCompletion : DecompositionFieldDerivedCompletionAudit
  decompositionRoute : ProductLogDecompositionDecompositionRoute
  decompositionRoute_eq :
    decompositionRoute =
      ProductLogDecompositionDecompositionRoute.fieldDerivedCompletion
  decomposition_globalObligation_is_fieldDerived :
    decompositionCompletion.globalObligation =
      decompositionFieldDerivedGlobalFamilyObligation
  decomposition_targetName_ne_semanticName :
    decompositionFieldDerivedAggregationTargetName ≠
      decompositionAggregationEncodingTargetName
  productLog_eval_iff_source_certificate :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (productLogArithmetic.target n) ↔
        Nonempty (ProductLogExpandedSourceCertificate n)
  productLog_eval_iff_source :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (productLogArithmetic.target n) ↔
        _root_.sondow_explicit_product_log_relation_prop n
  productSeparated_product_code :
    ∀ n : ℕ,
      productLogSeparatedCompletion.code
          (productLogSeparatedCompletion.productTarget n) =
        sondowProductCode n
  productSeparated_logRelation_code :
    ∀ n : ℕ,
      productLogSeparatedCompletion.code
          (productLogSeparatedCompletion.logRelationTarget n) =
        sondowLogRelationCode n
  productSeparated_product_eval_iff_source :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (productLogSeparatedCompletion.productTarget n) ↔
        _root_.sondow_explicit_product_log_relation_prop n
  productSeparated_logRelation_eval_iff_source :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (productLogSeparatedCompletion.logRelationTarget n) ↔
        _root_.sondow_explicit_product_log_relation_prop n
  productBranch_formula_code_eq :
    ∀ n : ℕ,
      productLogBranchCompiler.code
          (productLogBranchCompiler.target
            ProductLogDecompositionSourcePrimitive.product n) =
        ProductLogDecompositionSourcePrimitive.sourceCode
          ProductLogDecompositionSourcePrimitive.product n
  logRelationBranch_formula_code_eq :
    ∀ n : ℕ,
      productLogBranchCompiler.code
          (productLogBranchCompiler.target
            ProductLogDecompositionSourcePrimitive.logRelation n) =
        ProductLogDecompositionSourcePrimitive.sourceCode
          ProductLogDecompositionSourcePrimitive.logRelation n
  productBranch_eval_iff_source :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (productLogBranchCompiler.target
            ProductLogDecompositionSourcePrimitive.product n) ↔
        ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.product n
  logRelationBranch_eval_iff_source :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (productLogBranchCompiler.target
            ProductLogDecompositionSourcePrimitive.logRelation n) ↔
        ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.logRelation n
  tail_formula_code_eq :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      tailPureCompiler.code (tailPureCompiler.target p n) =
        ProductLogDecompositionSourcePrimitive.sourceCode p n
  tail_eval_iff_source_on_tail :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      tailPureCompiler.threshold ≤ n →
        (productLogDecompositionFormulaEval (fun _idx => n)
            (tailPureCompiler.target p n) ↔
          ProductLogDecompositionSourcePrimitive.eval p n)
  tail_compile_conclusion :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      ∀ hn : tailPureCompiler.threshold ≤ n,
      ∀ hp : ProductLogDecompositionSourcePrimitive.eval p n,
        (tailPureCompiler.compile p n hn hp).conclusion =
          tailPureCompiler.target p n
  tail_size_plus_two_le :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      ∀ hn : tailPureCompiler.threshold ≤ n,
      ∀ hp : ProductLogDecompositionSourcePrimitive.eval p n,
        ((((tailPureCompiler.compile p n hn hp).size + 2 : ℕ) : ℝ)) ≤
          ProductLogDecompositionSourcePrimitive.sourceBound
            productLogDecompositionTailPureBounds p n
  tail_targets_eval_iff_sources_on_tail :
    ∀ n : ℕ, tailPureCompiler.threshold ≤ n →
      (productLogDecompositionTailTargetsEval tailPureCompiler n ↔
        ProductLogDecompositionSourcePrimitive.eval
            ProductLogDecompositionSourcePrimitive.product n ∧
          ProductLogDecompositionSourcePrimitive.eval
            ProductLogDecompositionSourcePrimitive.logRelation n ∧
          ProductLogDecompositionSourcePrimitive.eval
            ProductLogDecompositionSourcePrimitive.decomposition n)
  tail_targets_eval_iff_allThreeCertificate_on_tail :
    ∀ n : ℕ, tailPureCompiler.threshold ≤ n →
      (productLogDecompositionTailTargetsEval tailPureCompiler n ↔
        ProductLogDecompositionExpandedFormula.eval
          (ProductLogDecompositionExpandedFormula.allThreeCertificate n))
  tail_proofTriple_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (ProductLogDecompositionTailPureCompiler.ProofTriple
          tailPureCompiler n)
  tail_targets_eval_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      productLogDecompositionTailTargetsEval tailPureCompiler n
  decomposition_eval_iff_source_certificate :
    ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n)
          (decompositionCompletion.expandedPureCompiler.target n) ↔
        Nonempty (DecompositionExpandedSourceCertificate n)
  decomposition_eval_iff_source_on_tail :
    ∀ {n : ℕ}, 1 ≤ n →
      (productLogDecompositionFormulaEval (fun _idx => n)
          (decompositionCompletion.corePureCompiler.target n) ↔
        _root_.sondow_explicit_decomposition_prop n)

def productLogDecompositionPartialPureFrontier :
    ProductLogDecompositionPartialPureFrontier where
  productLogArithmetic := productLogArithmeticPureS21Assembly
  productLogCompletion := productLogCompletionAudit
  productLogSeparatedCompletion := productLogSeparatedTargetCompletionAudit
  productLogBranchCompiler := productLogDecompositionProductLogBranchCompiler
  tailPureCompiler := productLogDecompositionTailPureCompiler
  tailCompletion := productLogDecompositionTailCompletionAudit
  productLogRoute :=
    ProductLogDecompositionProductLogRoute.arithmeticCompletion
  productLogRoute_eq := rfl
  productLogArithmetic_eq_completionAssembly := rfl
  productLogBranchCompiler_eq := rfl
  tailPureCompiler_eq := rfl
  tailCompletion_eq := rfl
  tailCompletion_compiler_eq := rfl
  decompositionCompletion := decompositionFieldDerivedCompletionAudit
  decompositionRoute :=
    ProductLogDecompositionDecompositionRoute.fieldDerivedCompletion
  decompositionRoute_eq := rfl
  decomposition_globalObligation_is_fieldDerived := rfl
  decomposition_targetName_ne_semanticName :=
    decompositionFieldDerivedAggregationTargetName_ne_semanticName
  productLog_eval_iff_source_certificate :=
    productLogArithmeticPureS21Assembly_eval_iff_source_certificate
  productLog_eval_iff_source :=
    productLogArithmeticPureS21Assembly_eval_iff_source
  productSeparated_product_code :=
    productLogSeparatedTargetCompletionAudit.code_product
  productSeparated_logRelation_code :=
    productLogSeparatedTargetCompletionAudit.code_logRelation
  productSeparated_product_eval_iff_source :=
    productLogSeparatedTargetCompletionAudit.product_eval_iff_source
  productSeparated_logRelation_eval_iff_source :=
    productLogSeparatedTargetCompletionAudit.logRelation_eval_iff_source
  productBranch_formula_code_eq :=
    productLogDecompositionProductLogBranchCompiler.product_formula_code_eq
  logRelationBranch_formula_code_eq :=
    productLogDecompositionProductLogBranchCompiler.logRelation_formula_code_eq
  productBranch_eval_iff_source :=
    productLogDecompositionProductLogBranchCompiler.product_eval_iff_source
  logRelationBranch_eval_iff_source :=
    productLogDecompositionProductLogBranchCompiler.logRelation_eval_iff_source
  tail_formula_code_eq := productLogDecompositionTailPureCompiler.formula_code_eq
  tail_eval_iff_source_on_tail :=
    productLogDecompositionTailPureCompiler.target_eval_iff_source_on_tail
  tail_compile_conclusion :=
    productLogDecompositionTailPureCompiler.compile_conclusion
  tail_size_plus_two_le :=
    productLogDecompositionTailPureCompiler.compile_size_plus_two_le
  tail_targets_eval_iff_sources_on_tail := by
    intro n
    exact
      productLogDecompositionTailPureCompiler.targets_eval_iff_sources_on_tail
        (n := n)
  tail_targets_eval_iff_allThreeCertificate_on_tail := by
    intro n
    exact
      productLogDecompositionTailPureCompiler
        |>.targets_eval_iff_allThreeCertificate_on_tail (n := n)
  tail_proofTriple_eventually :=
    productLogDecompositionTailCompletionAudit.proofTriple_eventually
  tail_targets_eval_eventually :=
    productLogDecompositionTailCompletionAudit.targets_eval_eventually
  decomposition_eval_iff_source_certificate := by
    intro n
    exact
      decompositionFieldDerivedCompletionAudit.expandedPureCompiler.target_eval_iff_source
        n
  decomposition_eval_iff_source_on_tail := by
    intro n hn
    exact
      (decompositionFieldDerivedCompletionAudit.corePureCompiler.target_eval_iff_source
        n).trans
        (DecompositionCoreSourceCertificate.nonempty_iff_source_of_one_le hn)

theorem productLogDecompositionPartialPureFrontier_uses_fieldDerivedCompletion :
    productLogDecompositionPartialPureFrontier.decompositionRoute =
      ProductLogDecompositionDecompositionRoute.fieldDerivedCompletion :=
  productLogDecompositionPartialPureFrontier.decompositionRoute_eq

theorem productLogDecompositionPartialPureFrontier_uses_productLogArithmeticCompletion :
    productLogDecompositionPartialPureFrontier.productLogRoute =
      ProductLogDecompositionProductLogRoute.arithmeticCompletion :=
  productLogDecompositionPartialPureFrontier.productLogRoute_eq

theorem productLogDecompositionPartialPureFrontier_productLog_eval_iff_source
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogDecompositionPartialPureFrontier.productLogArithmetic.target
          n) ↔
      _root_.sondow_explicit_product_log_relation_prop n :=
  productLogDecompositionPartialPureFrontier.productLog_eval_iff_source n

theorem productLogDecompositionPartialPureFrontier_product_code
    (n : ℕ) :
    productLogDecompositionPartialPureFrontier.productLogSeparatedCompletion.code
        (productLogDecompositionPartialPureFrontier.productLogSeparatedCompletion.productTarget
          n) =
      sondowProductCode n :=
  productLogDecompositionPartialPureFrontier.productSeparated_product_code n

theorem productLogDecompositionPartialPureFrontier_logRelation_code
    (n : ℕ) :
    productLogDecompositionPartialPureFrontier.productLogSeparatedCompletion.code
        (productLogDecompositionPartialPureFrontier.productLogSeparatedCompletion.logRelationTarget
          n) =
      sondowLogRelationCode n :=
  productLogDecompositionPartialPureFrontier.productSeparated_logRelation_code
    n

theorem productLogDecompositionPartialPureFrontier_productTarget_eval_iff_source
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogDecompositionPartialPureFrontier.productLogSeparatedCompletion.productTarget
          n) ↔
      _root_.sondow_explicit_product_log_relation_prop n :=
  productLogDecompositionPartialPureFrontier.productSeparated_product_eval_iff_source
    n

theorem productLogDecompositionPartialPureFrontier_logRelationTarget_eval_iff_source
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogDecompositionPartialPureFrontier.productLogSeparatedCompletion.logRelationTarget
          n) ↔
      _root_.sondow_explicit_product_log_relation_prop n :=
  productLogDecompositionPartialPureFrontier.productSeparated_logRelation_eval_iff_source
    n

theorem productLogDecompositionPartialPureFrontier_productBranch_formula_code_eq
    (n : ℕ) :
    productLogDecompositionPartialPureFrontier.productLogBranchCompiler.code
        (productLogDecompositionPartialPureFrontier.productLogBranchCompiler.target
          ProductLogDecompositionSourcePrimitive.product n) =
      ProductLogDecompositionSourcePrimitive.sourceCode
        ProductLogDecompositionSourcePrimitive.product n :=
  productLogDecompositionPartialPureFrontier.productBranch_formula_code_eq n

theorem productLogDecompositionPartialPureFrontier_logRelationBranch_formula_code_eq
    (n : ℕ) :
    productLogDecompositionPartialPureFrontier.productLogBranchCompiler.code
        (productLogDecompositionPartialPureFrontier.productLogBranchCompiler.target
          ProductLogDecompositionSourcePrimitive.logRelation n) =
      ProductLogDecompositionSourcePrimitive.sourceCode
        ProductLogDecompositionSourcePrimitive.logRelation n :=
  productLogDecompositionPartialPureFrontier.logRelationBranch_formula_code_eq
    n

theorem productLogDecompositionPartialPureFrontier_productBranch_eval_iff_source
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogDecompositionPartialPureFrontier.productLogBranchCompiler.target
          ProductLogDecompositionSourcePrimitive.product n) ↔
      ProductLogDecompositionSourcePrimitive.eval
        ProductLogDecompositionSourcePrimitive.product n :=
  productLogDecompositionPartialPureFrontier.productBranch_eval_iff_source n

theorem productLogDecompositionPartialPureFrontier_logRelationBranch_eval_iff_source
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogDecompositionPartialPureFrontier.productLogBranchCompiler.target
          ProductLogDecompositionSourcePrimitive.logRelation n) ↔
      ProductLogDecompositionSourcePrimitive.eval
        ProductLogDecompositionSourcePrimitive.logRelation n :=
  productLogDecompositionPartialPureFrontier.logRelationBranch_eval_iff_source
    n

theorem productLogDecompositionPartialPureFrontier_productBranch_compile_conclusion
    (n : ℕ)
    (hp : ProductLogDecompositionSourcePrimitive.eval
      ProductLogDecompositionSourcePrimitive.product n) :
    (productLogDecompositionPartialPureFrontier.productLogBranchCompiler.product_compile
      n hp).conclusion =
      productLogDecompositionPartialPureFrontier.productLogBranchCompiler.target
        ProductLogDecompositionSourcePrimitive.product n :=
  productLogDecompositionPartialPureFrontier.productLogBranchCompiler.product_compile_conclusion
    n hp

theorem productLogDecompositionPartialPureFrontier_logRelationBranch_compile_conclusion
    (n : ℕ)
    (hp : ProductLogDecompositionSourcePrimitive.eval
      ProductLogDecompositionSourcePrimitive.logRelation n) :
    (productLogDecompositionPartialPureFrontier.productLogBranchCompiler.logRelation_compile
      n hp).conclusion =
      productLogDecompositionPartialPureFrontier.productLogBranchCompiler.target
        ProductLogDecompositionSourcePrimitive.logRelation n :=
  productLogDecompositionPartialPureFrontier.productLogBranchCompiler.logRelation_compile_conclusion
    n hp

theorem productLogDecompositionPartialPureFrontier_productBranch_size_plus_two_le
    (n : ℕ)
    (hp : ProductLogDecompositionSourcePrimitive.eval
      ProductLogDecompositionSourcePrimitive.product n) :
    ((((productLogDecompositionPartialPureFrontier.productLogBranchCompiler.product_compile
      n hp).size + 2 : ℕ) : ℝ)) ≤
      productLogDecompositionPartialPureFrontier.productLogBranchCompiler.productBound
        n :=
  productLogDecompositionPartialPureFrontier.productLogBranchCompiler.product_size_plus_two_le
    n hp

theorem productLogDecompositionPartialPureFrontier_logRelationBranch_size_plus_two_le
    (n : ℕ)
    (hp : ProductLogDecompositionSourcePrimitive.eval
      ProductLogDecompositionSourcePrimitive.logRelation n) :
    ((((productLogDecompositionPartialPureFrontier.productLogBranchCompiler.logRelation_compile
      n hp).size + 2 : ℕ) : ℝ)) ≤
      productLogDecompositionPartialPureFrontier.productLogBranchCompiler.logRelationBound
        n :=
  productLogDecompositionPartialPureFrontier.productLogBranchCompiler.logRelation_size_plus_two_le
    n hp

theorem productLogDecompositionPartialPureFrontier_tail_formula_code_eq
    (p : ProductLogDecompositionSourcePrimitive) (n : ℕ) :
    productLogDecompositionPartialPureFrontier.tailPureCompiler.code
        (productLogDecompositionPartialPureFrontier.tailPureCompiler.target
          p n) =
      ProductLogDecompositionSourcePrimitive.sourceCode p n :=
  productLogDecompositionPartialPureFrontier.tail_formula_code_eq p n

theorem productLogDecompositionPartialPureFrontier_tail_eval_iff_source_on_tail
    (p : ProductLogDecompositionSourcePrimitive) {n : ℕ}
    (hn :
      productLogDecompositionPartialPureFrontier.tailPureCompiler.threshold ≤
        n) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogDecompositionPartialPureFrontier.tailPureCompiler.target
          p n) ↔
      ProductLogDecompositionSourcePrimitive.eval p n :=
  productLogDecompositionPartialPureFrontier.tail_eval_iff_source_on_tail
    p n hn

theorem productLogDecompositionPartialPureFrontier_tail_compile_conclusion
    (p : ProductLogDecompositionSourcePrimitive) (n : ℕ)
    (hn :
      productLogDecompositionPartialPureFrontier.tailPureCompiler.threshold ≤
        n)
    (hp : ProductLogDecompositionSourcePrimitive.eval p n) :
    (productLogDecompositionPartialPureFrontier.tailPureCompiler.compile
      p n hn hp).conclusion =
      productLogDecompositionPartialPureFrontier.tailPureCompiler.target
        p n :=
  productLogDecompositionPartialPureFrontier.tail_compile_conclusion
    p n hn hp

theorem productLogDecompositionPartialPureFrontier_tail_size_plus_two_le
    (p : ProductLogDecompositionSourcePrimitive) (n : ℕ)
    (hn :
      productLogDecompositionPartialPureFrontier.tailPureCompiler.threshold ≤
        n)
    (hp : ProductLogDecompositionSourcePrimitive.eval p n) :
    ((((productLogDecompositionPartialPureFrontier.tailPureCompiler.compile
      p n hn hp).size + 2 : ℕ) : ℝ)) ≤
      ProductLogDecompositionSourcePrimitive.sourceBound
        productLogDecompositionTailPureBounds p n :=
  productLogDecompositionPartialPureFrontier.tail_size_plus_two_le p n hn hp

theorem productLogDecompositionPartialPureFrontier_uses_tailCompletion :
    productLogDecompositionPartialPureFrontier.tailCompletion =
      productLogDecompositionTailCompletionAudit :=
  productLogDecompositionPartialPureFrontier.tailCompletion_eq

theorem productLogDecompositionPartialPureFrontier_tailCompletion_compiler_eq :
    productLogDecompositionPartialPureFrontier.tailCompletion.compiler =
      productLogDecompositionPartialPureFrontier.tailPureCompiler :=
  productLogDecompositionPartialPureFrontier.tailCompletion_compiler_eq

theorem productLogDecompositionPartialPureFrontier_tail_targets_eval_iff_sources_on_tail
    {n : ℕ}
    (hn :
      productLogDecompositionPartialPureFrontier.tailPureCompiler.threshold ≤
        n) :
    productLogDecompositionTailTargetsEval
        productLogDecompositionPartialPureFrontier.tailPureCompiler n ↔
      ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.product n ∧
        ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.logRelation n ∧
        ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.decomposition n :=
  productLogDecompositionPartialPureFrontier.tail_targets_eval_iff_sources_on_tail
    (n := n) hn

theorem productLogDecompositionPartialPureFrontier_tail_targets_eval_iff_allThreeCertificate_on_tail
    {n : ℕ}
    (hn :
      productLogDecompositionPartialPureFrontier.tailPureCompiler.threshold ≤
        n) :
    productLogDecompositionTailTargetsEval
        productLogDecompositionPartialPureFrontier.tailPureCompiler n ↔
      ProductLogDecompositionExpandedFormula.eval
        (ProductLogDecompositionExpandedFormula.allThreeCertificate n) :=
  productLogDecompositionPartialPureFrontier.tail_targets_eval_iff_allThreeCertificate_on_tail
    (n := n) hn

theorem productLogDecompositionPartialPureFrontier_tail_proofTriple_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (ProductLogDecompositionTailPureCompiler.ProofTriple
          productLogDecompositionPartialPureFrontier.tailPureCompiler n) :=
  productLogDecompositionPartialPureFrontier.tail_proofTriple_eventually

theorem productLogDecompositionPartialPureFrontier_tail_targets_eval_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      productLogDecompositionTailTargetsEval
        productLogDecompositionPartialPureFrontier.tailPureCompiler n :=
  productLogDecompositionPartialPureFrontier.tail_targets_eval_eventually

theorem productLogDecompositionTailCompletionAudit_targets_eval_iff_sources_on_tail
    {n : ℕ}
    (hn : productLogDecompositionTailCompletionAudit.compiler.threshold ≤ n) :
    productLogDecompositionTailTargetsEval
        productLogDecompositionTailCompletionAudit.compiler n ↔
      ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.product n ∧
        ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.logRelation n ∧
        ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.decomposition n :=
  productLogDecompositionTailCompletionAudit.targets_eval_iff_sources_on_tail
    (n := n) hn

theorem productLogDecompositionTailCompletionAudit_targets_eval_iff_allThreeCertificate_on_tail
    {n : ℕ}
    (hn : productLogDecompositionTailCompletionAudit.compiler.threshold ≤ n) :
    productLogDecompositionTailTargetsEval
        productLogDecompositionTailCompletionAudit.compiler n ↔
      ProductLogDecompositionExpandedFormula.eval
        (ProductLogDecompositionExpandedFormula.allThreeCertificate n) :=
  productLogDecompositionTailCompletionAudit.targets_eval_iff_allThreeCertificate_on_tail
    (n := n) hn

theorem productLogDecompositionTailCompletionAudit_proofTriple_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (ProductLogDecompositionTailPureCompiler.ProofTriple
          productLogDecompositionTailCompletionAudit.compiler n) :=
  productLogDecompositionTailCompletionAudit.proofTriple_eventually

theorem productLogDecompositionTailCompletionAudit_targets_eval_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      productLogDecompositionTailTargetsEval
        productLogDecompositionTailCompletionAudit.compiler n :=
  productLogDecompositionTailCompletionAudit.targets_eval_eventually

theorem productLogDecompositionPartialPureFrontier_decomposition_eval_iff_source_on_tail
    {n : ℕ} (hn : 1 ≤ n) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (productLogDecompositionPartialPureFrontier.decompositionCompletion.corePureCompiler.target
          n) ↔
      _root_.sondow_explicit_decomposition_prop n :=
  productLogDecompositionPartialPureFrontier.decomposition_eval_iff_source_on_tail
    (n := n) hn

theorem productCertificate_eval_iff_expanded_source_certificate
    (n : ℕ) :
    ProductLogDecompositionExpandedFormula.eval
        (ProductLogDecompositionExpandedFormula.productCertificate n) ↔
      Nonempty (ProductLogExpandedSourceCertificate n) := by
  rw [ProductLogDecompositionExpandedFormula.eval_productCertificate_iff,
    ProductLogExpandedSourceCertificate.nonempty_iff_source]

theorem logRelationCertificate_eval_iff_expanded_source_certificate
    (n : ℕ) :
    ProductLogDecompositionExpandedFormula.eval
        (ProductLogDecompositionExpandedFormula.logRelationCertificate n) ↔
      Nonempty (ProductLogExpandedSourceCertificate n) := by
  rw [ProductLogDecompositionExpandedFormula.eval_logRelationCertificate_iff,
    ProductLogExpandedSourceCertificate.nonempty_iff_source]

theorem decompositionCertificate_eval_iff_expanded_source_certificate_of_one_le
    {n : ℕ} (hn : 1 ≤ n) :
    ProductLogDecompositionExpandedFormula.eval
        (ProductLogDecompositionExpandedFormula.decompositionCertificate n) ↔
      Nonempty (DecompositionExpandedSourceCertificate n) := by
  rw [ProductLogDecompositionExpandedFormula.eval_decompositionCertificate_iff,
    DecompositionExpandedSourceCertificate.nonempty_iff_source_of_one_le hn]

theorem allThreeCertificate_eventually_expanded_source_certificates :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty (ProductLogExpandedSourceCertificate n) ∧
        Nonempty (ProductLogExpandedSourceCertificate n) ∧
        Nonempty (DecompositionExpandedSourceCertificate n) := by
  refine ⟨1, ?_⟩
  intro n hn
  exact
    ⟨⟨ProductLogExpandedSourceCertificate.ofMainLibrary n⟩,
      ⟨ProductLogExpandedSourceCertificate.ofMainLibrary n⟩,
      ⟨DecompositionExpandedSourceCertificate.ofMainLibrary hn⟩⟩

/-- The product/log/decomposition source certificates as one auditable bundle.
`productCert` and `logRelationCert` currently have the same source theorem but
remain separate fields because the proof-complexity side has two different
formula codes. -/
structure ProductLogDecompositionExpandedSourceCertificateBundle
    (n : ℕ) : Prop where
  productCert : ProductLogExpandedSourceCertificate n
  logRelationCert : ProductLogExpandedSourceCertificate n
  decompositionCert : DecompositionExpandedSourceCertificate n

namespace ProductLogDecompositionExpandedSourceCertificateBundle

def ofMainLibrary {n : ℕ} (hn : 1 ≤ n) :
    ProductLogDecompositionExpandedSourceCertificateBundle n where
  productCert := ProductLogExpandedSourceCertificate.ofMainLibrary n
  logRelationCert := ProductLogExpandedSourceCertificate.ofMainLibrary n
  decompositionCert :=
    DecompositionExpandedSourceCertificate.ofMainLibrary hn

theorem eval_allThree_of_bundle
    {n : ℕ}
    (bundle : ProductLogDecompositionExpandedSourceCertificateBundle n) :
    ProductLogDecompositionExpandedFormula.eval
      (ProductLogDecompositionExpandedFormula.allThreeCertificate n) := by
  exact
    ⟨bundle.productCert.source_of_certificate,
      bundle.logRelationCert.source_of_certificate,
      bundle.decompositionCert.source_of_certificate⟩

theorem nonempty_iff_eval_allThree_of_one_le
    {n : ℕ} (hn : 1 ≤ n) :
    Nonempty (ProductLogDecompositionExpandedSourceCertificateBundle n) ↔
      ProductLogDecompositionExpandedFormula.eval
        (ProductLogDecompositionExpandedFormula.allThreeCertificate n) := by
  constructor
  · intro hbundle
    rcases hbundle with ⟨bundle⟩
    exact bundle.eval_allThree_of_bundle
  · intro heval
    rcases
      (ProductLogDecompositionExpandedFormula.eval_allThreeCertificate_iff
        n).1 heval with
      ⟨hproduct, hlog, hdecomp⟩
    exact
      ⟨{
        productCert :=
          Classical.choice
            ((ProductLogExpandedSourceCertificate.nonempty_iff_source n).2
              hproduct)
        logRelationCert :=
          Classical.choice
            ((ProductLogExpandedSourceCertificate.nonempty_iff_source n).2
              hlog)
        decompositionCert :=
          Classical.choice
            ((DecompositionExpandedSourceCertificate.nonempty_iff_source_of_one_le
              hn).2 hdecomp) }⟩

theorem eventual :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (ProductLogDecompositionExpandedSourceCertificateBundle n) := by
  exact
    ⟨1, fun n hn => ⟨ofMainLibrary hn⟩⟩

end ProductLogDecompositionExpandedSourceCertificateBundle

structure ProductLogDecompositionProjectTailS21CompletionAudit where
  frontier : ProductLogDecompositionPartialPureFrontier
  frontier_eq :
    frontier = productLogDecompositionPartialPureFrontier
  tailCompletion_eq :
    frontier.tailCompletion = productLogDecompositionTailCompletionAudit
  threshold_eq_one :
    frontier.tailPureCompiler.threshold = 1
  target_atomFree :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      productLogDecompositionAtomFree (frontier.tailPureCompiler.target p n)
  formula_code_eq :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      frontier.tailPureCompiler.code (frontier.tailPureCompiler.target p n) =
        ProductLogDecompositionSourcePrimitive.sourceCode p n
  target_eval_iff_source_on_tail :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      frontier.tailPureCompiler.threshold ≤ n →
        (productLogDecompositionFormulaEval (fun _idx => n)
            (frontier.tailPureCompiler.target p n) ↔
          ProductLogDecompositionSourcePrimitive.eval p n)
  targets_eval_iff_allThreeCertificate_on_tail :
    ∀ n : ℕ, frontier.tailPureCompiler.threshold ≤ n →
      (productLogDecompositionTailTargetsEval frontier.tailPureCompiler n ↔
        ProductLogDecompositionExpandedFormula.eval
          (ProductLogDecompositionExpandedFormula.allThreeCertificate n))
  targets_eval_iff_expandedSourceBundle_on_tail :
    ∀ n : ℕ, frontier.tailPureCompiler.threshold ≤ n →
      (productLogDecompositionTailTargetsEval frontier.tailPureCompiler n ↔
        Nonempty (ProductLogDecompositionExpandedSourceCertificateBundle n))
  targets_eval_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      productLogDecompositionTailTargetsEval frontier.tailPureCompiler n
  proofTriple_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (ProductLogDecompositionTailPureCompiler.ProofTriple
          frontier.tailPureCompiler n)
  compile_conclusion :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      ∀ hn : frontier.tailPureCompiler.threshold ≤ n,
      ∀ hp : ProductLogDecompositionSourcePrimitive.eval p n,
        (frontier.tailPureCompiler.compile p n hn hp).conclusion =
          frontier.tailPureCompiler.target p n
  compile_size_plus_two_le :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      ∀ hn : frontier.tailPureCompiler.threshold ≤ n,
      ∀ hp : ProductLogDecompositionSourcePrimitive.eval p n,
        ((((frontier.tailPureCompiler.compile p n hn hp).size + 2 : ℕ) : ℝ)) ≤
          ProductLogDecompositionSourcePrimitive.sourceBound
            productLogDecompositionTailPureBounds p n

def productLogDecompositionProjectTailS21CompletionAudit :
    ProductLogDecompositionProjectTailS21CompletionAudit where
  frontier := productLogDecompositionPartialPureFrontier
  frontier_eq := rfl
  tailCompletion_eq := rfl
  threshold_eq_one := rfl
  target_atomFree :=
    productLogDecompositionTailPureCompiler.target_atomFree
  formula_code_eq :=
    productLogDecompositionPartialPureFrontier.tail_formula_code_eq
  target_eval_iff_source_on_tail :=
    productLogDecompositionPartialPureFrontier.tail_eval_iff_source_on_tail
  targets_eval_iff_allThreeCertificate_on_tail :=
    productLogDecompositionPartialPureFrontier
      |>.tail_targets_eval_iff_allThreeCertificate_on_tail
  targets_eval_iff_expandedSourceBundle_on_tail := by
    intro n hn
    have hone : 1 ≤ n := by
      simpa [productLogDecompositionPartialPureFrontier,
        productLogDecompositionTailPureCompiler] using hn
    exact
      (productLogDecompositionPartialPureFrontier
        |>.tail_targets_eval_iff_allThreeCertificate_on_tail
          (n := n) hn).trans
        (ProductLogDecompositionExpandedSourceCertificateBundle.nonempty_iff_eval_allThree_of_one_le
          hone).symm
  targets_eval_eventually :=
    productLogDecompositionPartialPureFrontier.tail_targets_eval_eventually
  proofTriple_eventually :=
    productLogDecompositionPartialPureFrontier.tail_proofTriple_eventually
  compile_conclusion :=
    productLogDecompositionPartialPureFrontier.tail_compile_conclusion
  compile_size_plus_two_le :=
    productLogDecompositionPartialPureFrontier.tail_size_plus_two_le

theorem productLogDecompositionProjectTailS21CompletionAudit_targets_eval_iff_expandedSourceBundle_on_tail
    {n : ℕ}
    (hn :
      productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.threshold ≤
        n) :
    productLogDecompositionTailTargetsEval
        productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler
        n ↔
      Nonempty (ProductLogDecompositionExpandedSourceCertificateBundle n) :=
  productLogDecompositionProjectTailS21CompletionAudit
    |>.targets_eval_iff_expandedSourceBundle_on_tail (n := n) hn

theorem productLogDecompositionProjectTailS21CompletionAudit_targets_eval_iff_allThreeCertificate_on_tail
    {n : ℕ}
    (hn :
      productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.threshold ≤
        n) :
    productLogDecompositionTailTargetsEval
        productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler
        n ↔
      ProductLogDecompositionExpandedFormula.eval
        (ProductLogDecompositionExpandedFormula.allThreeCertificate n) :=
  productLogDecompositionProjectTailS21CompletionAudit
    |>.targets_eval_iff_allThreeCertificate_on_tail (n := n) hn

theorem productLogDecompositionProjectTailS21CompletionAudit_targets_eval_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      productLogDecompositionTailTargetsEval
        productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler
        n :=
  productLogDecompositionProjectTailS21CompletionAudit.targets_eval_eventually

theorem productLogDecompositionProjectTailS21CompletionAudit_proofTriple_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (ProductLogDecompositionTailPureCompiler.ProofTriple
          productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler
          n) :=
  productLogDecompositionProjectTailS21CompletionAudit.proofTriple_eventually

theorem productLogDecompositionProjectTailS21CompletionAudit_threshold_eq_one :
    productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.threshold =
      1 :=
  productLogDecompositionProjectTailS21CompletionAudit.threshold_eq_one

theorem productLogDecompositionProjectTailS21CompletionAudit_formula_code_eq
    (p : ProductLogDecompositionSourcePrimitive) (n : ℕ) :
    productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.code
        (productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.target
          p n) =
      ProductLogDecompositionSourcePrimitive.sourceCode p n :=
  productLogDecompositionProjectTailS21CompletionAudit.formula_code_eq p n

theorem productLogDecompositionProjectTailS21CompletionAudit_compile_conclusion
    (p : ProductLogDecompositionSourcePrimitive) (n : ℕ)
    (hn :
      productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.threshold ≤
        n)
    (hp : ProductLogDecompositionSourcePrimitive.eval p n) :
    (productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.compile
      p n hn hp).conclusion =
      productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.target
        p n :=
  productLogDecompositionProjectTailS21CompletionAudit.compile_conclusion
    p n hn hp

theorem productLogDecompositionProjectTailS21CompletionAudit_compile_size_plus_two_le
    (p : ProductLogDecompositionSourcePrimitive) (n : ℕ)
    (hn :
      productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.threshold ≤
        n)
    (hp : ProductLogDecompositionSourcePrimitive.eval p n) :
    ((((productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.compile
      p n hn hp).size + 2 : ℕ) : ℝ)) ≤
      ProductLogDecompositionSourcePrimitive.sourceBound
        productLogDecompositionTailPureBounds p n :=
  productLogDecompositionProjectTailS21CompletionAudit.compile_size_plus_two_le
    p n hn hp

structure ProductLogDecompositionUnconditionalTailS21CompilerAlignment :
    Prop where
  frontier_eq :
    productLogDecompositionProjectTailS21CompletionAudit.frontier =
      productLogDecompositionPartialPureFrontier
  tailCompletion_eq :
    productLogDecompositionProjectTailS21CompletionAudit.frontier.tailCompletion =
      productLogDecompositionTailCompletionAudit
  threshold_eq_one :
    productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.threshold =
      1
  target_atomFree :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      productLogDecompositionAtomFree
        (productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.target
          p n)
  formula_code_eq :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.code
          (productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.target
            p n) =
        ProductLogDecompositionSourcePrimitive.sourceCode p n
  target_eval_iff_source_on_tail :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.threshold ≤
          n →
        (productLogDecompositionFormulaEval (fun _idx => n)
            (productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.target
              p n) ↔
          ProductLogDecompositionSourcePrimitive.eval p n)
  targets_eval_iff_allThreeCertificate_on_tail :
    ∀ n : ℕ,
      productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.threshold ≤
          n →
        (productLogDecompositionTailTargetsEval
            productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler
            n ↔
          ProductLogDecompositionExpandedFormula.eval
            (ProductLogDecompositionExpandedFormula.allThreeCertificate n))
  targets_eval_iff_expandedSourceBundle_on_tail :
    ∀ n : ℕ,
      productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.threshold ≤
          n →
        (productLogDecompositionTailTargetsEval
            productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler
            n ↔
          Nonempty (ProductLogDecompositionExpandedSourceCertificateBundle n))
  targets_eval_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      productLogDecompositionTailTargetsEval
        productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler
        n
  proofTriple_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (ProductLogDecompositionTailPureCompiler.ProofTriple
          productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler
          n)
  compile_conclusion :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      ∀ hn :
        productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.threshold ≤
          n,
      ∀ hp : ProductLogDecompositionSourcePrimitive.eval p n,
        (productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.compile
          p n hn hp).conclusion =
          productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.target
            p n
  compile_size_plus_two_le :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      ∀ hn :
        productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.threshold ≤
          n,
      ∀ hp : ProductLogDecompositionSourcePrimitive.eval p n,
        ((((productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.compile
          p n hn hp).size + 2 : ℕ) : ℝ)) ≤
          ProductLogDecompositionSourcePrimitive.sourceBound
            productLogDecompositionTailPureBounds p n

theorem productLogDecomposition_unconditionalTailS21CompilerAlignment :
    ProductLogDecompositionUnconditionalTailS21CompilerAlignment where
  frontier_eq :=
    productLogDecompositionProjectTailS21CompletionAudit.frontier_eq
  tailCompletion_eq :=
    productLogDecompositionProjectTailS21CompletionAudit.tailCompletion_eq
  threshold_eq_one :=
    productLogDecompositionProjectTailS21CompletionAudit.threshold_eq_one
  target_atomFree :=
    productLogDecompositionProjectTailS21CompletionAudit.target_atomFree
  formula_code_eq :=
    productLogDecompositionProjectTailS21CompletionAudit.formula_code_eq
  target_eval_iff_source_on_tail :=
    productLogDecompositionProjectTailS21CompletionAudit.target_eval_iff_source_on_tail
  targets_eval_iff_allThreeCertificate_on_tail :=
    productLogDecompositionProjectTailS21CompletionAudit
      |>.targets_eval_iff_allThreeCertificate_on_tail
  targets_eval_iff_expandedSourceBundle_on_tail :=
    productLogDecompositionProjectTailS21CompletionAudit
      |>.targets_eval_iff_expandedSourceBundle_on_tail
  targets_eval_eventually :=
    productLogDecompositionProjectTailS21CompletionAudit.targets_eval_eventually
  proofTriple_eventually :=
    productLogDecompositionProjectTailS21CompletionAudit.proofTriple_eventually
  compile_conclusion :=
    productLogDecompositionProjectTailS21CompletionAudit.compile_conclusion
  compile_size_plus_two_le :=
    productLogDecompositionProjectTailS21CompletionAudit.compile_size_plus_two_le

theorem productLogDecomposition_unconditionalTailS21CompilerAlignment_targets_eval_iff_expandedSourceBundle_on_tail
    {n : ℕ}
    (hn :
      productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler.threshold ≤
        n) :
    productLogDecompositionTailTargetsEval
        productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler
        n ↔
      Nonempty (ProductLogDecompositionExpandedSourceCertificateBundle n) :=
  productLogDecomposition_unconditionalTailS21CompilerAlignment
    |>.targets_eval_iff_expandedSourceBundle_on_tail n hn

theorem productLogDecomposition_unconditionalTailS21CompilerAlignment_targets_eval_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      productLogDecompositionTailTargetsEval
        productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler
        n :=
  productLogDecomposition_unconditionalTailS21CompilerAlignment.targets_eval_eventually

theorem productLogDecomposition_unconditionalTailS21CompilerAlignment_proofTriple_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (ProductLogDecompositionTailPureCompiler.ProofTriple
          productLogDecompositionProjectTailS21CompletionAudit.frontier.tailPureCompiler
          n) :=
  productLogDecomposition_unconditionalTailS21CompilerAlignment.proofTriple_eventually

/-- Exact pure compiler obligation for the product/log/decomposition analytic
sources on all natural indices.  The project-level result above closes the
unconditional tail/eventual S²₁ route; this stronger all-index interface is kept
separate because the decomposition theorem is stated on `1 ≤ n`. -/
structure ProductLogDecompositionPureCompiler
    (bounds : SondowComponentBounds) where
  target : ProductLogDecompositionSourcePrimitive → ℕ → BAFormula
  code : BAFormula → BoundedArithmeticLab.FormulaCode
  target_atomFree :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      productLogDecompositionAtomFree (target p n)
  target_eval_iff_source :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      productLogDecompositionFormulaEval (fun _idx => n) (target p n) ↔
        ProductLogDecompositionSourcePrimitive.eval p n
  formula_code_eq :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      code (target p n) =
        ProductLogDecompositionSourcePrimitive.sourceCode p n
  compile :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      ProductLogDecompositionSourcePrimitive.eval p n →
        BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      ∀ hp : ProductLogDecompositionSourcePrimitive.eval p n,
        (compile p n hp).conclusion = target p n
  compile_size_plus_two_le :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      ∀ hp : ProductLogDecompositionSourcePrimitive.eval p n,
        ((((compile p n hp).size + 2 : ℕ) : ℝ)) ≤
          ProductLogDecompositionSourcePrimitive.sourceBound bounds p n

namespace ProductLogDecompositionPureCompiler

theorem cannot_use_project_atoms_as_pure_targets
    {bounds : SondowComponentBounds}
    (compiler : ProductLogDecompositionPureCompiler bounds)
    (hproject :
      ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
        compiler.target p n =
          ProductLogDecompositionSourcePrimitive.projectAtomTarget p n) :
    False := by
  have hfree :
      productLogDecompositionAtomFree
        (ProductLogDecompositionSourcePrimitive.projectAtomTarget
          ProductLogDecompositionSourcePrimitive.product 0) := by
    simpa [hproject ProductLogDecompositionSourcePrimitive.product 0]
      using
        compiler.target_atomFree
          ProductLogDecompositionSourcePrimitive.product 0
  exact
    ProductLogDecompositionSourcePrimitive.projectAtomTarget_not_atomFree
        ProductLogDecompositionSourcePrimitive.product 0 hfree

structure ProofTriple
    {bounds : SondowComponentBounds}
    (compiler : ProductLogDecompositionPureCompiler bounds)
    (n : ℕ) where
  productProof : BAProofObject BussS21Axiom
  logRelationProof : BAProofObject BussS21Axiom
  decompositionProof : BAProofObject BussS21Axiom
  product_conclusion :
    productProof.conclusion =
      compiler.target ProductLogDecompositionSourcePrimitive.product n
  logRelation_conclusion :
    logRelationProof.conclusion =
      compiler.target ProductLogDecompositionSourcePrimitive.logRelation n
  decomposition_conclusion :
    decompositionProof.conclusion =
      compiler.target ProductLogDecompositionSourcePrimitive.decomposition n
  product_size_plus_two_le :
    ((((productProof.size + 2 : ℕ) : ℝ)) ≤ bounds.product n)
  logRelation_size_plus_two_le :
    ((((logRelationProof.size + 2 : ℕ) : ℝ)) ≤ bounds.logRelation n)
  decomposition_size_plus_two_le :
    ((((decompositionProof.size + 2 : ℕ) : ℝ)) ≤
      bounds.decomposition n)

def proofTriple
    {bounds : SondowComponentBounds}
    (compiler : ProductLogDecompositionPureCompiler bounds)
    (n : ℕ)
    (hsources :
      ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.product n ∧
        ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.logRelation n ∧
        ProductLogDecompositionSourcePrimitive.eval
          ProductLogDecompositionSourcePrimitive.decomposition n) :
    ProofTriple compiler n where
  productProof :=
    compiler.compile ProductLogDecompositionSourcePrimitive.product n
      hsources.1
  logRelationProof :=
    compiler.compile ProductLogDecompositionSourcePrimitive.logRelation n
      hsources.2.1
  decompositionProof :=
    compiler.compile ProductLogDecompositionSourcePrimitive.decomposition n
      hsources.2.2
  product_conclusion :=
    compiler.compile_conclusion
      ProductLogDecompositionSourcePrimitive.product n hsources.1
  logRelation_conclusion :=
    compiler.compile_conclusion
      ProductLogDecompositionSourcePrimitive.logRelation n hsources.2.1
  decomposition_conclusion :=
    compiler.compile_conclusion
      ProductLogDecompositionSourcePrimitive.decomposition n hsources.2.2
  product_size_plus_two_le :=
    compiler.compile_size_plus_two_le
      ProductLogDecompositionSourcePrimitive.product n hsources.1
  logRelation_size_plus_two_le :=
    compiler.compile_size_plus_two_le
      ProductLogDecompositionSourcePrimitive.logRelation n hsources.2.1
  decomposition_size_plus_two_le :=
    compiler.compile_size_plus_two_le
      ProductLogDecompositionSourcePrimitive.decomposition n hsources.2.2

def proofTripleOfBundle
    {bounds : SondowComponentBounds}
    (compiler : ProductLogDecompositionPureCompiler bounds)
    {n : ℕ}
    (bundle : ProductLogDecompositionExpandedSourceCertificateBundle n) :
    ProofTriple compiler n :=
  compiler.proofTriple n
    ⟨bundle.productCert.source_of_certificate,
      bundle.logRelationCert.source_of_certificate,
      bundle.decompositionCert.source_of_certificate⟩

theorem proofTripleOfBundle_eventually
    {bounds : SondowComponentBounds}
    (compiler : ProductLogDecompositionPureCompiler bounds) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty (ProofTriple compiler n) := by
  rcases
    ProductLogDecompositionExpandedSourceCertificateBundle.eventual with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  rcases hN n hn with ⟨bundle⟩
  exact ⟨compiler.proofTripleOfBundle bundle⟩

theorem proofTriple_eventually
    {bounds : SondowComponentBounds}
    (compiler : ProductLogDecompositionPureCompiler bounds) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty (ProofTriple compiler n) := by
  rcases
    ProductLogDecompositionSourcePrimitive.all_sources_eventually_complete with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact ⟨compiler.proofTriple n (hN n hn)⟩

theorem product_target_semantics_iff
    {bounds : SondowComponentBounds}
    (compiler : ProductLogDecompositionPureCompiler bounds)
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (compiler.target ProductLogDecompositionSourcePrimitive.product n) ↔
      _root_.sondow_explicit_product_log_relation_prop n :=
  compiler.target_eval_iff_source
    ProductLogDecompositionSourcePrimitive.product n

theorem logRelation_target_semantics_iff
    {bounds : SondowComponentBounds}
    (compiler : ProductLogDecompositionPureCompiler bounds)
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (compiler.target
          ProductLogDecompositionSourcePrimitive.logRelation n) ↔
      _root_.sondow_explicit_product_log_relation_prop n :=
  compiler.target_eval_iff_source
    ProductLogDecompositionSourcePrimitive.logRelation n

theorem decomposition_target_semantics_iff
    {bounds : SondowComponentBounds}
    (compiler : ProductLogDecompositionPureCompiler bounds)
    (n : ℕ) :
    productLogDecompositionFormulaEval (fun _idx => n)
        (compiler.target
          ProductLogDecompositionSourcePrimitive.decomposition n) ↔
      _root_.sondow_explicit_decomposition_prop n :=
  compiler.target_eval_iff_source
    ProductLogDecompositionSourcePrimitive.decomposition n

end ProductLogDecompositionPureCompiler


end SondowMainCheckedCodeBridge
