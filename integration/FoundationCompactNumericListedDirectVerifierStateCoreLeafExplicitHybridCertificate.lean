import integration.FoundationCompactNumericListedDirectVerifierStateCoreExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveOptionBoolExplicitHybridCertificate

/-!
# Explicit leaf certificates for verifier state cores

This module closes the two natural-list slices, both binary-size equations,
both area inequalities, and the elementary status equalities at a fixed
24-coordinate state environment.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierStateCoreLeafExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectVerifierStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveOptionBoolExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryLengthValuationContextCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

theorem compactNumericVerifierStateProofSliceAtEnvironmentFormula_eq_closed
    (values : Fin 24 -> Nat) :
    compactNumericVerifierStateProofSliceAtEnvironmentFormula values =
      compactAdditiveNatListSliceClosedFormula
        (values 0) (values 1) (values 2) (values 3) (values 6) (values 5) := by
  unfold compactNumericVerifierStateProofSliceAtEnvironmentFormula
  unfold compactAdditiveNatListSliceClosedFormula
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar,
        compactNumericVerifierStateEnvironmentTerms]
  · intro coordinate
    exact Empty.elim coordinate

theorem
    compactNumericVerifierStateCertificateSliceAtEnvironmentFormula_eq_closed
    (values : Fin 24 -> Nat) :
    compactNumericVerifierStateCertificateSliceAtEnvironmentFormula values =
      compactAdditiveNatListSliceClosedFormula
        (values 0) (values 1) (values 2) (values 5) (values 8) (values 7) := by
  unfold compactNumericVerifierStateCertificateSliceAtEnvironmentFormula
  unfold compactAdditiveNatListSliceClosedFormula
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar,
        compactNumericVerifierStateEnvironmentTerms]
  · intro coordinate
    exact Empty.elim coordinate

noncomputable def
    compactNumericVerifierStateProofSliceExplicitHybridCertificate
    (values : Fin 24 -> Nat) (bodyStart : Nat)
    (hbodyBound : bodyStart ≤ values 2)
    (hheader : CompactAdditiveListHeader
      (values 0) (values 1) (values 2) (values 3) (values 6) bodyStart)
    (hfinish : values 5 = bodyStart + values 6) :
    HybridCertificate
      (compactNumericVerifierStateProofSliceAtEnvironmentFormula values) := by
  rw [compactNumericVerifierStateProofSliceAtEnvironmentFormula_eq_closed]
  exact compactAdditiveNatListSliceExplicitHybridCertificate
    (values 0) (values 1) (values 2) (values 3) (values 6) (values 5)
    bodyStart hbodyBound hheader hfinish

noncomputable def
    compactNumericVerifierStateCertificateSliceExplicitHybridCertificate
    (values : Fin 24 -> Nat) (bodyStart : Nat)
    (hbodyBound : bodyStart ≤ values 2)
    (hheader : CompactAdditiveListHeader
      (values 0) (values 1) (values 2) (values 5) (values 8) bodyStart)
    (hfinish : values 7 = bodyStart + values 8) :
    HybridCertificate
      (compactNumericVerifierStateCertificateSliceAtEnvironmentFormula
        values) := by
  rw [
    compactNumericVerifierStateCertificateSliceAtEnvironmentFormula_eq_closed]
  exact compactAdditiveNatListSliceExplicitHybridCertificate
    (values 0) (values 1) (values 2) (values 5) (values 8) (values 7)
    bodyStart hbodyBound hheader hfinish

private def compactNatSizeClosedFormula
    (size value : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNatSizeDef.val) ⇜
    ![shortBinaryNumeralTerm size, shortBinaryNumeralTerm value]

private theorem compactNatSizeClosedFormula_eq_binaryLength
    (size value : Nat) :
    compactNatSizeClosedFormula size value =
      binaryLengthAtValuationFormula
        (shortBinaryNumeralTerm size) (shortBinaryNumeralTerm value) := by
  unfold compactNatSizeClosedFormula
  unfold compactNatSizeDef
  unfold binaryLengthAtValuationFormula
  rfl

private noncomputable def compactNatSizeExplicitHybridCertificate
    (size value : Nat) (hsize : size = Nat.size value) :
    HybridCertificate (compactNatSizeClosedFormula size value) := by
  rw [compactNatSizeClosedFormula_eq_binaryLength]
  exact .binaryLength zeroValuation
    (shortBinaryNumeralTerm size) (shortBinaryNumeralTerm value) (by
      simpa [termValue_shortBinaryNumeralTerm] using hsize)

theorem
    compactNumericVerifierStateTaskBoundarySizeAtEnvironmentFormula_eq_closed
    (values : Fin 24 -> Nat) :
    compactNumericVerifierStateTaskBoundarySizeAtEnvironmentFormula values =
      compactNatSizeClosedFormula (values 18) (values 11) := by
  unfold compactNumericVerifierStateTaskBoundarySizeAtEnvironmentFormula
  unfold compactNatSizeClosedFormula
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar,
        compactNumericVerifierStateEnvironmentTerms]
  · intro coordinate
    exact Empty.elim coordinate

theorem
    compactNumericVerifierStateValueBoundarySizeAtEnvironmentFormula_eq_closed
    (values : Fin 24 -> Nat) :
    compactNumericVerifierStateValueBoundarySizeAtEnvironmentFormula values =
      compactNatSizeClosedFormula (values 19) (values 14) := by
  unfold compactNumericVerifierStateValueBoundarySizeAtEnvironmentFormula
  unfold compactNatSizeClosedFormula
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar,
        compactNumericVerifierStateEnvironmentTerms]
  · intro coordinate
    exact Empty.elim coordinate

noncomputable def
    compactNumericVerifierStateTaskBoundarySizeExplicitHybridCertificate
    (values : Fin 24 -> Nat)
    (hsize : values 18 = Nat.size (values 11)) :
    HybridCertificate
      (compactNumericVerifierStateTaskBoundarySizeAtEnvironmentFormula
        values) := by
  rw [
    compactNumericVerifierStateTaskBoundarySizeAtEnvironmentFormula_eq_closed]
  exact compactNatSizeExplicitHybridCertificate
    (values 18) (values 11) hsize

noncomputable def
    compactNumericVerifierStateValueBoundarySizeExplicitHybridCertificate
    (values : Fin 24 -> Nat)
    (hsize : values 19 = Nat.size (values 14)) :
    HybridCertificate
      (compactNumericVerifierStateValueBoundarySizeAtEnvironmentFormula
        values) := by
  rw [
    compactNumericVerifierStateValueBoundarySizeAtEnvironmentFormula_eq_closed]
  exact compactNatSizeExplicitHybridCertificate
    (values 19) (values 14) hsize

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left * !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Mul.mul ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Mul.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticMul
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left * !!right’ =
      termValue valuation left * termValue valuation right := by
  rw [arithmeticMulTerm_eq_func]
  exact termValue_mul valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem termValue_arithmeticZero (valuation : Nat -> Nat) :
    termValue valuation (‘0’ : ValuationTerm) = 0 := by
  exact termValue_zero valuation ![]

private noncomputable def valuationLeCertificate
    (leftTerm rightTerm : ValuationTerm)
    (hle : termValue zeroValuation leftTerm ≤
      termValue zeroValuation rightTerm) :
    HybridCertificate “!!leftTerm ≤ !!rightTerm” := by
  if heq : termValue zeroValuation leftTerm =
      termValue zeroValuation rightTerm then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq ![leftTerm, rightTerm] heq
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : termValue zeroValuation leftTerm <
        termValue zeroValuation rightTerm := Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt ![leftTerm, rightTerm] hlt
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

noncomputable def
    compactNumericVerifierStateTaskBoundaryBoundExplicitHybridCertificate
    (values : Fin 24 -> Nat)
    (hbound : values 18 ≤ (values 10 + 1) * values 2) :
    HybridCertificate
      (compactNumericVerifierStateTaskBoundaryBoundAtEnvironmentFormula
        values) := by
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm (values 10)) + 1) *
      !!(shortBinaryNumeralTerm (values 2))’
  let direct := valuationLeCertificate
    (shortBinaryNumeralTerm (values 18)) rightTerm (by
      simpa [rightTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticMul,
        termValue_arithmeticOne] using hbound)
  simpa [compactNumericVerifierStateTaskBoundaryBoundAtEnvironmentFormula,
    compactNumericVerifierStateTaskBoundaryBoundRawFormula,
    compactNumericVerifierStateEnvironmentTerms, rightTerm] using direct

noncomputable def
    compactNumericVerifierStateValueBoundaryBoundExplicitHybridCertificate
    (values : Fin 24 -> Nat)
    (hbound : values 19 ≤ (values 13 + 1) * values 2) :
    HybridCertificate
      (compactNumericVerifierStateValueBoundaryBoundAtEnvironmentFormula
        values) := by
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm (values 13)) + 1) *
      !!(shortBinaryNumeralTerm (values 2))’
  let direct := valuationLeCertificate
    (shortBinaryNumeralTerm (values 19)) rightTerm (by
      simpa [rightTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticMul,
        termValue_arithmeticOne] using hbound)
  simpa [compactNumericVerifierStateValueBoundaryBoundAtEnvironmentFormula,
    compactNumericVerifierStateValueBoundaryBoundRawFormula,
    compactNumericVerifierStateEnvironmentTerms, rightTerm] using direct

private noncomputable def valuationEqCertificate
    (leftTerm rightTerm : ValuationTerm)
    (heq : termValue zeroValuation leftTerm =
      termValue zeroValuation rightTerm) :
    HybridCertificate “!!leftTerm = !!rightTerm” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq ![leftTerm, rightTerm] heq
  exact .cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

noncomputable def
    compactNumericVerifierStateStatusTagZeroExplicitHybridCertificate
    (values : Fin 24 -> Nat) (htag : values 15 = 0) :
    HybridCertificate
      (compactNumericVerifierStateStatusTagZeroAtEnvironmentFormula values) := by
  let direct := valuationEqCertificate
    (shortBinaryNumeralTerm (values 15)) (‘0’ : ValuationTerm) (by
      change termValue zeroValuation (shortBinaryNumeralTerm (values 15)) =
        termValue zeroValuation (‘0’ : ValuationTerm)
      simpa [termValue_shortBinaryNumeralTerm,
        termValue_arithmeticZero] using htag)
  simpa [compactNumericVerifierStateStatusTagZeroAtEnvironmentFormula,
    compactNumericVerifierStateStatusTagZeroRawFormula,
    compactNumericVerifierStateEnvironmentTerms] using direct

noncomputable def
    compactNumericVerifierStateStatusTagOneExplicitHybridCertificate
    (values : Fin 24 -> Nat) (htag : values 15 = 1) :
    HybridCertificate
      (compactNumericVerifierStateStatusTagOneAtEnvironmentFormula values) := by
  let direct := valuationEqCertificate
    (shortBinaryNumeralTerm (values 15)) (‘1’ : ValuationTerm) (by
      change termValue zeroValuation (shortBinaryNumeralTerm (values 15)) =
        termValue zeroValuation (‘1’ : ValuationTerm)
      simpa [termValue_shortBinaryNumeralTerm,
        termValue_arithmeticOne] using htag)
  simpa [compactNumericVerifierStateStatusTagOneAtEnvironmentFormula,
    compactNumericVerifierStateStatusTagOneRawFormula,
    compactNumericVerifierStateEnvironmentTerms] using direct

noncomputable def
    compactNumericVerifierStateStatusFinishEqExplicitHybridCertificate
    (values : Fin 24 -> Nat) (hfinish : values 4 = values 16) :
    HybridCertificate
      (compactNumericVerifierStateStatusFinishEqAtEnvironmentFormula
        values) := by
  let direct := valuationEqCertificate
    (shortBinaryNumeralTerm (values 4))
    (shortBinaryNumeralTerm (values 16)) (by
      simpa [termValue_shortBinaryNumeralTerm] using hfinish)
  simpa [compactNumericVerifierStateStatusFinishEqAtEnvironmentFormula,
    compactNumericVerifierStateStatusFinishEqRawFormula,
    compactNumericVerifierStateEnvironmentTerms] using direct

theorem compactNumericVerifierStateOptionLayoutAtEnvironmentFormula_eq_closed
    (values : Fin 24 -> Nat) :
    compactNumericVerifierStateOptionLayoutAtEnvironmentFormula values =
      compactAdditiveOptionLayoutClosedFormula
        (values 0) (values 1) (values 2) (values 12)
        (values 15) (values 16) (values 4) := by
  unfold compactNumericVerifierStateOptionLayoutAtEnvironmentFormula
  unfold compactAdditiveOptionLayoutClosedFormula
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar,
        compactNumericVerifierStateEnvironmentTerms]
  · intro coordinate
    exact Empty.elim coordinate

noncomputable def
    compactNumericVerifierStateOptionLayoutNoneExplicitHybridCertificate
    (values : Fin 24 -> Nat)
    (hcell : CompactAdditiveTokenCell
      (values 0) (values 1) (values 2) (values 12)
      (values 15) (values 16))
    (htag : values 15 = 0)
    (hfinish : values 4 = values 16) :
    HybridCertificate
      (compactNumericVerifierStateOptionLayoutAtEnvironmentFormula values) := by
  rw [compactNumericVerifierStateOptionLayoutAtEnvironmentFormula_eq_closed]
  exact compactAdditiveOptionLayoutNoneExplicitHybridCertificate
    (values 0) (values 1) (values 2) (values 12)
    (values 15) (values 16) (values 4)
    hcell htag hfinish

noncomputable def
    compactNumericVerifierStateOptionLayoutSomeExplicitHybridCertificate
    (values : Fin 24 -> Nat)
    (hcell : CompactAdditiveTokenCell
      (values 0) (values 1) (values 2) (values 12)
      (values 15) (values 16))
    (htag : values 15 = 1)
    (hpayload : values 16 < values 4)
    (hfinish : values 4 ≤ values 2) :
    HybridCertificate
      (compactNumericVerifierStateOptionLayoutAtEnvironmentFormula values) := by
  rw [compactNumericVerifierStateOptionLayoutAtEnvironmentFormula_eq_closed]
  exact compactAdditiveOptionLayoutSomeExplicitHybridCertificate
    (values 0) (values 1) (values 2) (values 12)
    (values 15) (values 16) (values 4)
    hcell htag hpayload hfinish

theorem
    compactNumericVerifierStateStatusBoolSliceAtEnvironmentFormula_eq_closed
    (values : Fin 24 -> Nat) :
    compactNumericVerifierStateStatusBoolSliceAtEnvironmentFormula values =
      compactAdditiveBoolSliceClosedFormula
        (values 0) (values 1) (values 2) (values 16)
        (values 17) (values 4) := by
  unfold compactNumericVerifierStateStatusBoolSliceAtEnvironmentFormula
  unfold compactAdditiveBoolSliceClosedFormula
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar,
        compactNumericVerifierStateEnvironmentTerms]
  · intro coordinate
    exact Empty.elim coordinate

noncomputable def
    compactNumericVerifierStateStatusBoolSliceExplicitHybridCertificate
    (values : Fin 24 -> Nat) (decoded : Bool)
    (hcell : CompactAdditiveTokenCell
      (values 0) (values 1) (values 2) (values 16)
      (values 17) (values 4))
    (hvalue : values 17 = if decoded then 1 else 0) :
    HybridCertificate
      (compactNumericVerifierStateStatusBoolSliceAtEnvironmentFormula
        values) := by
  rw [
    compactNumericVerifierStateStatusBoolSliceAtEnvironmentFormula_eq_closed]
  exact compactAdditiveBoolSliceExplicitHybridCertificate
    (values 0) (values 1) (values 2) (values 16)
    (values 17) (values 4) decoded hcell hvalue

private noncomputable def
    compactNumericVerifierStateCoreImmediateCertificatesOfLeafData
    (values : Fin 24 -> Nat)
    (proofBodyStart certificateBodyStart : Nat)
    (hproofBodyBound : proofBodyStart ≤ values 2)
    (hproofHeader : CompactAdditiveListHeader
      (values 0) (values 1) (values 2) (values 3)
      (values 6) proofBodyStart)
    (hproofFinish : values 5 = proofBodyStart + values 6)
    (hcertificateBodyBound : certificateBodyStart ≤ values 2)
    (hcertificateHeader : CompactAdditiveListHeader
      (values 0) (values 1) (values 2) (values 5)
      (values 8) certificateBodyStart)
    (hcertificateFinish : values 7 = certificateBodyStart + values 8)
    (taskLayout : HybridCertificate
      (compactNumericVerifierStateTaskLayoutAtEnvironmentFormula values))
    (taskRows : HybridCertificate
      (compactNumericVerifierStateTaskRowsAtEnvironmentFormula values))
    (htaskBoundarySize : values 18 = Nat.size (values 11))
    (htaskBoundaryBound : values 18 ≤ (values 10 + 1) * values 2)
    (valueLayout : HybridCertificate
      (compactNumericVerifierStateValueLayoutAtEnvironmentFormula values))
    (valueRows : HybridCertificate
      (compactNumericVerifierStateValueRowsAtEnvironmentFormula values))
    (hvalueBoundarySize : values 19 = Nat.size (values 14))
    (hvalueBoundaryBound : values 19 ≤ (values 13 + 1) * values 2)
    (optionLayout : HybridCertificate
      (compactNumericVerifierStateOptionLayoutAtEnvironmentFormula values)) :
    CompactNumericVerifierStateCoreImmediateCertificates
      zeroValuation values where
  proofSlice :=
    compactNumericVerifierStateProofSliceExplicitHybridCertificate
      values proofBodyStart hproofBodyBound hproofHeader hproofFinish
  certificateSlice :=
    compactNumericVerifierStateCertificateSliceExplicitHybridCertificate
      values certificateBodyStart hcertificateBodyBound
      hcertificateHeader hcertificateFinish
  taskLayout := taskLayout
  taskRows := taskRows
  taskBoundarySize :=
    compactNumericVerifierStateTaskBoundarySizeExplicitHybridCertificate
      values htaskBoundarySize
  taskBoundaryBound :=
    compactNumericVerifierStateTaskBoundaryBoundExplicitHybridCertificate
      values htaskBoundaryBound
  valueLayout := valueLayout
  valueRows := valueRows
  valueBoundarySize :=
    compactNumericVerifierStateValueBoundarySizeExplicitHybridCertificate
      values hvalueBoundarySize
  valueBoundaryBound :=
    compactNumericVerifierStateValueBoundaryBoundExplicitHybridCertificate
      values hvalueBoundaryBound
  optionLayout := optionLayout

noncomputable def
    compactNumericVerifierStateCoreExplicitHybridCertificateOfNoneFromLeafData
    (values : Fin 24 -> Nat)
    (proofBodyStart certificateBodyStart : Nat)
    (hproofBodyBound : proofBodyStart ≤ values 2)
    (hproofHeader : CompactAdditiveListHeader
      (values 0) (values 1) (values 2) (values 3)
      (values 6) proofBodyStart)
    (hproofFinish : values 5 = proofBodyStart + values 6)
    (hcertificateBodyBound : certificateBodyStart ≤ values 2)
    (hcertificateHeader : CompactAdditiveListHeader
      (values 0) (values 1) (values 2) (values 5)
      (values 8) certificateBodyStart)
    (hcertificateFinish : values 7 = certificateBodyStart + values 8)
    (taskLayout : HybridCertificate
      (compactNumericVerifierStateTaskLayoutAtEnvironmentFormula values))
    (taskRows : HybridCertificate
      (compactNumericVerifierStateTaskRowsAtEnvironmentFormula values))
    (htaskBoundarySize : values 18 = Nat.size (values 11))
    (htaskBoundaryBound : values 18 ≤ (values 10 + 1) * values 2)
    (valueLayout : HybridCertificate
      (compactNumericVerifierStateValueLayoutAtEnvironmentFormula values))
    (valueRows : HybridCertificate
      (compactNumericVerifierStateValueRowsAtEnvironmentFormula values))
    (hvalueBoundarySize : values 19 = Nat.size (values 14))
    (hvalueBoundaryBound : values 19 ≤ (values 13 + 1) * values 2)
    (hoptionCell : CompactAdditiveTokenCell
      (values 0) (values 1) (values 2) (values 12)
      (values 15) (values 16))
    (htag : values 15 = 0)
    (hfinish : values 4 = values 16) :
    HybridCertificate
      (compactNumericVerifierStateCoreAtEnvironmentFormula values) := by
  let optionLayout :=
    compactNumericVerifierStateOptionLayoutNoneExplicitHybridCertificate
      values hoptionCell htag hfinish
  let parts := compactNumericVerifierStateCoreImmediateCertificatesOfLeafData
    values proofBodyStart certificateBodyStart hproofBodyBound hproofHeader
    hproofFinish hcertificateBodyBound hcertificateHeader
    hcertificateFinish taskLayout taskRows htaskBoundarySize
    htaskBoundaryBound valueLayout valueRows hvalueBoundarySize
    hvalueBoundaryBound optionLayout
  exact compactNumericVerifierStateCoreExplicitHybridCertificateOfNone parts
    (compactNumericVerifierStateStatusTagZeroExplicitHybridCertificate
      values htag)
    (compactNumericVerifierStateStatusFinishEqExplicitHybridCertificate
      values hfinish)

noncomputable def
    compactNumericVerifierStateCoreExplicitHybridCertificateOfSomeFromLeafData
    (values : Fin 24 -> Nat)
    (proofBodyStart certificateBodyStart : Nat)
    (hproofBodyBound : proofBodyStart ≤ values 2)
    (hproofHeader : CompactAdditiveListHeader
      (values 0) (values 1) (values 2) (values 3)
      (values 6) proofBodyStart)
    (hproofFinish : values 5 = proofBodyStart + values 6)
    (hcertificateBodyBound : certificateBodyStart ≤ values 2)
    (hcertificateHeader : CompactAdditiveListHeader
      (values 0) (values 1) (values 2) (values 5)
      (values 8) certificateBodyStart)
    (hcertificateFinish : values 7 = certificateBodyStart + values 8)
    (taskLayout : HybridCertificate
      (compactNumericVerifierStateTaskLayoutAtEnvironmentFormula values))
    (taskRows : HybridCertificate
      (compactNumericVerifierStateTaskRowsAtEnvironmentFormula values))
    (htaskBoundarySize : values 18 = Nat.size (values 11))
    (htaskBoundaryBound : values 18 ≤ (values 10 + 1) * values 2)
    (valueLayout : HybridCertificate
      (compactNumericVerifierStateValueLayoutAtEnvironmentFormula values))
    (valueRows : HybridCertificate
      (compactNumericVerifierStateValueRowsAtEnvironmentFormula values))
    (hvalueBoundarySize : values 19 = Nat.size (values 14))
    (hvalueBoundaryBound : values 19 ≤ (values 13 + 1) * values 2)
    (hoptionCell : CompactAdditiveTokenCell
      (values 0) (values 1) (values 2) (values 12)
      (values 15) (values 16))
    (htag : values 15 = 1)
    (hoptionPayload : values 16 < values 4)
    (hoptionFinish : values 4 ≤ values 2)
    (decoded : Bool)
    (hboolCell : CompactAdditiveTokenCell
      (values 0) (values 1) (values 2) (values 16)
      (values 17) (values 4))
    (hboolValue : values 17 = if decoded then 1 else 0) :
    HybridCertificate
      (compactNumericVerifierStateCoreAtEnvironmentFormula values) := by
  let optionLayout :=
    compactNumericVerifierStateOptionLayoutSomeExplicitHybridCertificate
      values hoptionCell htag hoptionPayload hoptionFinish
  let parts := compactNumericVerifierStateCoreImmediateCertificatesOfLeafData
    values proofBodyStart certificateBodyStart hproofBodyBound hproofHeader
    hproofFinish hcertificateBodyBound hcertificateHeader
    hcertificateFinish taskLayout taskRows htaskBoundarySize
    htaskBoundaryBound valueLayout valueRows hvalueBoundarySize
    hvalueBoundaryBound optionLayout
  exact compactNumericVerifierStateCoreExplicitHybridCertificateOfSome parts
    (compactNumericVerifierStateStatusTagOneExplicitHybridCertificate
      values htag)
    (compactNumericVerifierStateStatusBoolSliceExplicitHybridCertificate
      values decoded hboolCell hboolValue)

#print axioms
  compactNumericVerifierStateProofSliceExplicitHybridCertificate
#print axioms
  compactNumericVerifierStateCertificateSliceExplicitHybridCertificate
#print axioms
  compactNumericVerifierStateTaskBoundarySizeExplicitHybridCertificate
#print axioms
  compactNumericVerifierStateValueBoundarySizeExplicitHybridCertificate
#print axioms
  compactNumericVerifierStateTaskBoundaryBoundExplicitHybridCertificate
#print axioms
  compactNumericVerifierStateValueBoundaryBoundExplicitHybridCertificate
#print axioms
  compactNumericVerifierStateStatusTagZeroExplicitHybridCertificate
#print axioms
  compactNumericVerifierStateStatusTagOneExplicitHybridCertificate
#print axioms
  compactNumericVerifierStateStatusFinishEqExplicitHybridCertificate
#print axioms
  compactNumericVerifierStateOptionLayoutAtEnvironmentFormula_eq_closed
#print axioms
  compactNumericVerifierStateOptionLayoutNoneExplicitHybridCertificate
#print axioms
  compactNumericVerifierStateOptionLayoutSomeExplicitHybridCertificate
#print axioms
  compactNumericVerifierStateStatusBoolSliceAtEnvironmentFormula_eq_closed
#print axioms
  compactNumericVerifierStateStatusBoolSliceExplicitHybridCertificate
#print axioms
  compactNumericVerifierStateCoreExplicitHybridCertificateOfNoneFromLeafData
#print axioms
  compactNumericVerifierStateCoreExplicitHybridCertificateOfSomeFromLeafData

end FoundationCompactNumericListedDirectVerifierStateCoreLeafExplicitHybridCertificate
