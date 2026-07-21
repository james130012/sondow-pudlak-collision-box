import integration.FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

/-!
# Explicit hybrid certificates for additive `Bool` and `Option` layouts

The closed formulas retain the exact substituted syntax of the public layout
definitions.  Their certificates choose each finite disjunction branch
directly and reuse the public token-cell certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectAdditiveOptionBoolExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAValuationTermCompiler

private abbrev HybridCertificate :=
  CheckedHybridValuationBoundedFormulaCertificate

private def unaryNumeralTerm (value : Nat) : ValuationTerm :=
  Semiterm.Operator.operator
    (Semiterm.Operator.numeral ℒₒᵣ value) ![]

private theorem termValue_unaryNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (unaryNumeralTerm value) = value := by
  unfold termValue unaryNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘
      (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) = (![] : Fin 0 -> Nat) by
        funext index
        exact Fin.elim0 index]
  simp

private noncomputable def closedEqCertificate
    (left right : Nat) (heq : left = right) :
    HybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm left) =
        !!(shortBinaryNumeralTerm right)” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
      change termValue zeroValuation (shortBinaryNumeralTerm left) =
        termValue zeroValuation (shortBinaryNumeralTerm right)
      simpa [termValue_shortBinaryNumeralTerm] using heq)
  exact .cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

private noncomputable def closedFixedNumeralEqCertificate
    (left right : Nat) (heq : left = right) :
    HybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm left) = !!(unaryNumeralTerm right)” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm left, unaryNumeralTerm right] (by
      change termValue zeroValuation (shortBinaryNumeralTerm left) =
        termValue zeroValuation (unaryNumeralTerm right)
      simpa only [termValue_shortBinaryNumeralTerm,
        termValue_unaryNumeralTerm] using heq)
  exact .cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

private noncomputable def closedLtCertificate
    (left right : Nat) (hlt : left < right) :
    HybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm left) <
        !!(shortBinaryNumeralTerm right)” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
      change termValue zeroValuation (shortBinaryNumeralTerm left) <
        termValue zeroValuation (shortBinaryNumeralTerm right)
      simpa [termValue_shortBinaryNumeralTerm] using hlt)
  exact .cast (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct

private noncomputable def closedLeCertificate
    (left right : Nat) (hle : left ≤ right) :
    HybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm left) ≤
        !!(shortBinaryNumeralTerm right)” := by
  if heq : left = right then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq
      ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
        change termValue zeroValuation (shortBinaryNumeralTerm left) =
          termValue zeroValuation (shortBinaryNumeralTerm right)
        simpa [termValue_shortBinaryNumeralTerm] using heq)
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : left < right := Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
        change termValue zeroValuation (shortBinaryNumeralTerm left) <
          termValue zeroValuation (shortBinaryNumeralTerm right)
        simpa [termValue_shortBinaryNumeralTerm] using hlt)
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

def compactAdditiveBoolSliceClosedFormula
    (tokenTable width tokenCount start value finish : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveBoolSliceDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm start,
      shortBinaryNumeralTerm value,
      shortBinaryNumeralTerm finish]

theorem compactAdditiveBoolSliceClosedFormula_alignment
    (tokenTable width tokenCount start value finish : Nat) :
    compactAdditiveBoolSliceClosedFormula
        tokenTable width tokenCount start value finish =
      (compactAdditiveTokenCellClosedFormula
          tokenTable width tokenCount start value finish ⋏
        (“!!(shortBinaryNumeralTerm value) = 0” ⋎
          “!!(shortBinaryNumeralTerm value) = 1”)) := by
  unfold compactAdditiveBoolSliceClosedFormula
  unfold compactAdditiveTokenCellClosedFormula
  unfold compactAdditiveBoolSliceDef
  unfold compactAdditiveTokenCellDef
  simp [← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar]
  · intro coordinate
    exact Empty.elim coordinate

noncomputable def compactAdditiveBoolSliceZeroExplicitHybridCertificate
    (tokenTable width tokenCount start value finish : Nat)
    (hcell : CompactAdditiveTokenCell
      tokenTable width tokenCount start value finish)
    (hvalue : value = 0) :
    HybridCertificate zeroValuation
      (compactAdditiveBoolSliceClosedFormula
        tokenTable width tokenCount start value finish) := by
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveTokenCellExplicitHybridCertificate
      tokenTable width tokenCount start value finish hcell)
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := “!!(shortBinaryNumeralTerm value) = 1”)
      (closedFixedNumeralEqCertificate value 0 hvalue))
  exact .cast
    (compactAdditiveBoolSliceClosedFormula_alignment
      tokenTable width tokenCount start value finish).symm parts

noncomputable def compactAdditiveBoolSliceOneExplicitHybridCertificate
    (tokenTable width tokenCount start value finish : Nat)
    (hcell : CompactAdditiveTokenCell
      tokenTable width tokenCount start value finish)
    (hvalue : value = 1) :
    HybridCertificate zeroValuation
      (compactAdditiveBoolSliceClosedFormula
        tokenTable width tokenCount start value finish) := by
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveTokenCellExplicitHybridCertificate
      tokenTable width tokenCount start value finish hcell)
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := “!!(shortBinaryNumeralTerm value) = 0”)
      (closedFixedNumeralEqCertificate value 1 hvalue))
  exact .cast
    (compactAdditiveBoolSliceClosedFormula_alignment
      tokenTable width tokenCount start value finish).symm parts

noncomputable def compactAdditiveBoolSliceExplicitHybridCertificate
    (tokenTable width tokenCount start value finish : Nat)
    (decoded : Bool)
    (hcell : CompactAdditiveTokenCell
      tokenTable width tokenCount start value finish)
    (hvalue : value = if decoded then 1 else 0) :
    HybridCertificate zeroValuation
      (compactAdditiveBoolSliceClosedFormula
        tokenTable width tokenCount start value finish) := by
  cases decoded with
  | false =>
      exact compactAdditiveBoolSliceZeroExplicitHybridCertificate
        tokenTable width tokenCount start value finish hcell (by
          simpa using hvalue)
  | true =>
      exact compactAdditiveBoolSliceOneExplicitHybridCertificate
        tokenTable width tokenCount start value finish hcell (by
          simpa using hvalue)

def compactAdditiveOptionLayoutClosedFormula
    (tokenTable width tokenCount start tag payloadStart finish : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveOptionLayoutDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm start,
      shortBinaryNumeralTerm tag,
      shortBinaryNumeralTerm payloadStart,
      shortBinaryNumeralTerm finish]

theorem compactAdditiveOptionLayoutClosedFormula_alignment
    (tokenTable width tokenCount start tag payloadStart finish : Nat) :
    compactAdditiveOptionLayoutClosedFormula
        tokenTable width tokenCount start tag payloadStart finish =
      (compactAdditiveTokenCellClosedFormula
          tokenTable width tokenCount start tag payloadStart ⋏
        ((“!!(shortBinaryNumeralTerm tag) = 0” ⋏
            “!!(shortBinaryNumeralTerm finish) =
              !!(shortBinaryNumeralTerm payloadStart)”) ⋎
          (“!!(shortBinaryNumeralTerm tag) = 1” ⋏
            (“!!(shortBinaryNumeralTerm payloadStart) <
                !!(shortBinaryNumeralTerm finish)” ⋏
              “!!(shortBinaryNumeralTerm finish) ≤
                !!(shortBinaryNumeralTerm tokenCount)”)))) := by
  unfold compactAdditiveOptionLayoutClosedFormula
  unfold compactAdditiveTokenCellClosedFormula
  unfold compactAdditiveOptionLayoutDef
  unfold compactAdditiveTokenCellDef
  simp [← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar]
  · intro coordinate
    exact Empty.elim coordinate

noncomputable def compactAdditiveOptionLayoutNoneExplicitHybridCertificate
    (tokenTable width tokenCount start tag payloadStart finish : Nat)
    (hcell : CompactAdditiveTokenCell
      tokenTable width tokenCount start tag payloadStart)
    (htag : tag = 0)
    (hfinish : finish = payloadStart) :
    HybridCertificate zeroValuation
      (compactAdditiveOptionLayoutClosedFormula
        tokenTable width tokenCount start tag payloadStart finish) := by
  let noneBranch := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (closedFixedNumeralEqCertificate tag 0 htag)
    (closedEqCertificate finish payloadStart hfinish)
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveTokenCellExplicitHybridCertificate
      tokenTable width tokenCount start tag payloadStart hcell)
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right :=
        (“!!(shortBinaryNumeralTerm tag) = 1” ⋏
          (“!!(shortBinaryNumeralTerm payloadStart) <
              !!(shortBinaryNumeralTerm finish)” ⋏
            “!!(shortBinaryNumeralTerm finish) ≤
              !!(shortBinaryNumeralTerm tokenCount)”)))
      noneBranch)
  exact .cast
    (compactAdditiveOptionLayoutClosedFormula_alignment
      tokenTable width tokenCount start tag payloadStart finish).symm parts

noncomputable def compactAdditiveOptionLayoutSomeExplicitHybridCertificate
    (tokenTable width tokenCount start tag payloadStart finish : Nat)
    (hcell : CompactAdditiveTokenCell
      tokenTable width tokenCount start tag payloadStart)
    (htag : tag = 1)
    (hpayload : payloadStart < finish)
    (hfinish : finish ≤ tokenCount) :
    HybridCertificate zeroValuation
      (compactAdditiveOptionLayoutClosedFormula
        tokenTable width tokenCount start tag payloadStart finish) := by
  let someBranch := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (closedFixedNumeralEqCertificate tag 1 htag)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (closedLtCertificate payloadStart finish hpayload)
      (closedLeCertificate finish tokenCount hfinish))
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveTokenCellExplicitHybridCertificate
      tokenTable width tokenCount start tag payloadStart hcell)
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left :=
        (“!!(shortBinaryNumeralTerm tag) = 0” ⋏
          “!!(shortBinaryNumeralTerm finish) =
            !!(shortBinaryNumeralTerm payloadStart)”))
      someBranch)
  exact .cast
    (compactAdditiveOptionLayoutClosedFormula_alignment
      tokenTable width tokenCount start tag payloadStart finish).symm parts

/-- Derive the Boolean certificate by selecting its checked zero/one branch. -/
noncomputable def compactAdditiveBoolSliceExplicitHybridCertificateOfSlice
    (tokenTable width tokenCount start value finish : Nat)
    (hslice : CompactAdditiveBoolSlice
      tokenTable width tokenCount start value finish) :
    HybridCertificate zeroValuation
      (compactAdditiveBoolSliceClosedFormula
        tokenTable width tokenCount start value finish) := by
  if hzero : value = 0 then
    exact compactAdditiveBoolSliceZeroExplicitHybridCertificate
      tokenTable width tokenCount start value finish hslice.1 hzero
  else
    have hone : value = 1 := by
      rcases hslice.2 with hvalue | hvalue
      · exact False.elim (hzero hvalue)
      · exact hvalue
    exact compactAdditiveBoolSliceOneExplicitHybridCertificate
      tokenTable width tokenCount start value finish hslice.1 hone

/-- Derive the option certificate by selecting its checked tag branch. -/
noncomputable def compactAdditiveOptionLayoutExplicitHybridCertificateOfLayout
    (tokenTable width tokenCount start tag payloadStart finish : Nat)
    (hlayout : CompactAdditiveOptionLayout
      tokenTable width tokenCount start tag payloadStart finish) :
    HybridCertificate zeroValuation
      (compactAdditiveOptionLayoutClosedFormula
        tokenTable width tokenCount start tag payloadStart finish) := by
  if hzero : tag = 0 then
    have hfinish : finish = payloadStart := by
      rcases hlayout.2 with hnone | hsome
      · exact hnone.2
      · exact False.elim (by omega)
    exact compactAdditiveOptionLayoutNoneExplicitHybridCertificate
      tokenTable width tokenCount start tag payloadStart finish
      hlayout.1 hzero hfinish
  else
    have hsome : tag = 1 ∧ payloadStart < finish ∧ finish ≤ tokenCount := by
      rcases hlayout.2 with hnone | hsome
      · exact False.elim (hzero hnone.1)
      · exact hsome
    exact compactAdditiveOptionLayoutSomeExplicitHybridCertificate
      tokenTable width tokenCount start tag payloadStart finish
      hlayout.1 hsome.1 hsome.2.1 hsome.2.2

#print axioms compactAdditiveBoolSliceClosedFormula_alignment
#print axioms compactAdditiveOptionLayoutClosedFormula_alignment
#print axioms compactAdditiveBoolSliceZeroExplicitHybridCertificate
#print axioms compactAdditiveBoolSliceOneExplicitHybridCertificate
#print axioms compactAdditiveBoolSliceExplicitHybridCertificate
#print axioms compactAdditiveOptionLayoutNoneExplicitHybridCertificate
#print axioms compactAdditiveOptionLayoutSomeExplicitHybridCertificate
#print axioms compactAdditiveBoolSliceExplicitHybridCertificateOfSlice
#print axioms compactAdditiveOptionLayoutExplicitHybridCertificateOfLayout

end FoundationCompactNumericListedDirectAdditiveOptionBoolExplicitHybridCertificate
