import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for syntax-task list uncons rows

The original eleven-coordinate relation is assembled from independently
checked positivity, drop, triple-boundary, cons, binary-size, and area-bound
certificates.  No Sigma-zero truth conversion is used.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate

private abbrev HybridCertificate :=
  CheckedHybridValuationBoundedFormulaCertificate

def zeroValuation : Nat -> Nat := fun _ => 0

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left : ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
      ArithmeticSemiformula targetVariables targetArity) = Rewriting.app right := by
  cases h
  rfl

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left * !!right’ : ValuationTerm) =
      Semiterm.func Language.Mul.mul ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Mul.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

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

private theorem termValue_arithmeticZero (valuation : Nat -> Nat) :
    termValue valuation (‘0’ : ValuationTerm) = 0 := by
  exact termValue_zero valuation ![]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

def compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm sourceBoundary,
      shortBinaryNumeralTerm sourceCount, shortBinaryNumeralTerm tailBoundary,
      shortBinaryNumeralTerm tailCount, shortBinaryNumeralTerm tailBoundarySize,
      headKindTerm, headBinderArityTerm, headRepeatCountTerm]

def compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headBinderArity headRepeatCount : Nat)
    (headKindTerm : ValuationTerm) :
    ValuationFormula :=
  compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula tokenTable width
    tokenCount sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKindTerm
      (shortBinaryNumeralTerm headBinderArity) (shortBinaryNumeralTerm headRepeatCount)

def compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedFormula
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headKind headBinderArity headRepeatCount : Nat) :
    ValuationFormula :=
  compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula tokenTable width
    tokenCount sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headBinderArity
      headRepeatCount (shortBinaryNumeralTerm headKind)

def compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitFormula
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm) :
    ValuationFormula :=
  “0 < !!(shortBinaryNumeralTerm sourceCount)” ⋏
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula tokenTable width tokenCount
        sourceBoundary sourceCount tailBoundary tailCount 1 ⋏
      (compactAdditiveTripleBoundaryRowsClosedFormula tokenCount tailCount tailBoundary ⋏
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula tokenTable width tokenCount
            tailBoundary tailCount sourceBoundary sourceCount headKindTerm
              headBinderArityTerm headRepeatCountTerm ⋏
          (compactNatSizeClosedFormula tailBoundarySize tailBoundary ⋏
            “!!(shortBinaryNumeralTerm tailBoundarySize) ≤
              (!!(shortBinaryNumeralTerm tailCount) + 1) *
                !!(shortBinaryNumeralTerm tokenCount)”))))

def compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindExplicitFormula
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headBinderArity headRepeatCount : Nat)
    (headKindTerm : ValuationTerm) :
    ValuationFormula :=
  compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitFormula tokenTable width
    tokenCount sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKindTerm
      (shortBinaryNumeralTerm headBinderArity) (shortBinaryNumeralTerm headRepeatCount)

def compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitFormula
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headKind headBinderArity headRepeatCount : Nat) :
    ValuationFormula :=
  compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindExplicitFormula tokenTable width
    tokenCount sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headBinderArity
      headRepeatCount (shortBinaryNumeralTerm headKind)

theorem compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula_alignment
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm) :
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula tokenTable width
        tokenCount sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKindTerm
          headBinderArityTerm headRepeatCountTerm =
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitFormula tokenTable
        width tokenCount sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
          headKindTerm headBinderArityTerm headRepeatCountTerm := by
  unfold compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
  unfold compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitFormula
  unfold compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef
  unfold compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
  unfold compactAdditiveTripleBoundaryRowsClosedFormula
  unfold compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula
  unfold compactNatSizeClosedFormula
  simp [fixedNumeralTerm, ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

theorem compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula_alignment
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headBinderArity headRepeatCount : Nat)
    (headKindTerm : ValuationTerm) :
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula tokenTable width
        tokenCount sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
          headBinderArity headRepeatCount headKindTerm =
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindExplicitFormula tokenTable
        width tokenCount sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
          headBinderArity headRepeatCount headKindTerm := by
  simpa [compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula,
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindExplicitFormula] using
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula_alignment tokenTable
        width tokenCount sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
          headKindTerm (shortBinaryNumeralTerm headBinderArity)
            (shortBinaryNumeralTerm headRepeatCount)

theorem compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedFormula_alignment
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headKind headBinderArity headRepeatCount : Nat) :
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedFormula tokenTable width tokenCount
        sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKind
        headBinderArity headRepeatCount =
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitFormula tokenTable width tokenCount
        sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKind
        headBinderArity headRepeatCount := by
  simpa [compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedFormula,
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitFormula] using
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula_alignment
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary tailCount
          tailBoundarySize headBinderArity headRepeatCount (shortBinaryNumeralTerm headKind)

noncomputable def closedPositiveCertificate
    (value : Nat) (hpositive : 0 < value) :
    HybridCertificate zeroValuation
      “0 < !!(shortBinaryNumeralTerm value)” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
    ![(‘0’ : ValuationTerm), shortBinaryNumeralTerm value] (by
      change termValue zeroValuation (‘0’ : ValuationTerm) <
        termValue zeroValuation (shortBinaryNumeralTerm value)
      simpa [termValue_arithmeticZero, termValue_shortBinaryNumeralTerm]
        using hpositive)
  exact .cast (Semiformula.Operator.lt_def _ _).symm direct

def tailAreaTerm (tailCount tokenCount : Nat) : ValuationTerm :=
  ‘(!!(shortBinaryNumeralTerm tailCount) + 1) *
    !!(shortBinaryNumeralTerm tokenCount)’

noncomputable def closedTailAreaLeCertificate
    (tailBoundarySize tailCount tokenCount : Nat)
    (hbound : tailBoundarySize ≤ (tailCount + 1) * tokenCount) :
    HybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm tailBoundarySize) ≤
        (!!(shortBinaryNumeralTerm tailCount) + 1) *
          !!(shortBinaryNumeralTerm tokenCount)” := by
  let leftTerm := shortBinaryNumeralTerm tailBoundarySize
  let rightTerm := tailAreaTerm tailCount tokenCount
  have hvalue : termValue zeroValuation rightTerm =
      (tailCount + 1) * tokenCount := by
    simp [rightTerm, tailAreaTerm, termValue_arithmeticMul,
      termValue_arithmeticAdd, termValue_arithmeticOne,
      termValue_shortBinaryNumeralTerm]
  if heq : tailBoundarySize = (tailCount + 1) * tokenCount then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq ![leftTerm, rightTerm] (by
        change termValue zeroValuation leftTerm = termValue zeroValuation rightTerm
        simpa [leftTerm, termValue_shortBinaryNumeralTerm, hvalue] using heq)
    exact .cast (Semiformula.Operator.le_def _ _).symm (.disjunctionLeft equality)
  else
    have hlt : tailBoundarySize < (tailCount + 1) * tokenCount :=
      Nat.lt_of_le_of_ne hbound heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt ![leftTerm, rightTerm] (by
        change termValue zeroValuation leftTerm < termValue zeroValuation rightTerm
        simpa [leftTerm, termValue_shortBinaryNumeralTerm, hvalue] using hlt)
    exact .cast (Semiformula.Operator.le_def _ _).symm (.disjunctionRight strict)

noncomputable def
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm)
    (hheadKindValue : ∀ valuation, termValue valuation headKindTerm = headKind)
    (hheadBinderArityValue : ∀ valuation,
      termValue valuation headBinderArityTerm = headBinderArity)
    (hheadRepeatCountValue : ∀ valuation,
      termValue valuation headRepeatCountTerm = headRepeatCount)
    (hgraph : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKind
      headBinderArity headRepeatCount) :
    HybridCertificate zeroValuation
      (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula tokenTable width
        tokenCount sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKindTerm
          headBinderArityTerm headRepeatCountTerm) := by
  rcases hgraph with ⟨hpositive, hdrop, htriple, hcons, hsize, harea⟩
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (closedPositiveCertificate sourceCount hpositive)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph tokenTable
        width tokenCount sourceBoundary sourceCount tailBoundary tailCount 1 hdrop)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph tokenCount tailCount
          tailBoundary htriple)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph
            tokenTable width tokenCount tailBoundary tailCount sourceBoundary sourceCount headKind
              headBinderArity headRepeatCount headKindTerm headBinderArityTerm headRepeatCountTerm
                hheadKindValue hheadBinderArityValue hheadRepeatCountValue hcons)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactNatSizeExplicitHybridCertificateOfEq tailBoundarySize tailBoundary hsize)
            (closedTailAreaLeCertificate tailBoundarySize tailCount tokenCount harea)))))
  exact .cast
    (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula_alignment tokenTable
      width tokenCount sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
        headKindTerm headBinderArityTerm headRepeatCountTerm).symm parts

noncomputable def
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm : ValuationTerm)
    (hheadKindValue : ∀ valuation, termValue valuation headKindTerm = headKind)
    (hgraph : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKind
      headBinderArity headRepeatCount) :
    HybridCertificate zeroValuation
      (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula tokenTable width
        tokenCount sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
          headBinderArity headRepeatCount headKindTerm) := by
  simpa [compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula] using
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
        headKind headBinderArity headRepeatCount headKindTerm
          (shortBinaryNumeralTerm headBinderArity) (shortBinaryNumeralTerm headRepeatCount)
        hheadKindValue (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
          (fun valuation => by simp [termValue_shortBinaryNumeralTerm]) hgraph

noncomputable def
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headKind headBinderArity headRepeatCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKind
      headBinderArity headRepeatCount) :
    HybridCertificate zeroValuation
      (compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedFormula tokenTable width tokenCount
        sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKind
        headBinderArity headRepeatCount) := by
  simpa [compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedFormula] using
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
        headKind headBinderArity headRepeatCount (shortBinaryNumeralTerm headKind)
          (fun valuation => by simp [termValue_shortBinaryNumeralTerm]) hgraph

noncomputable def compileCompactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridContext
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headKind headBinderArity headRepeatCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKind
      headBinderArity headRepeatCount) :
    CertifiedPAContextProof
      (valuationContext
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedFormula tokenTable width tokenCount
          sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKind
          headBinderArity headRepeatCount).freeVariables zeroValuation)
      (compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedFormula tokenTable width tokenCount
        sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKind
        headBinderArity headRepeatCount) :=
  (compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridCertificateOfGraph tokenTable width
    tokenCount sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKind
    headBinderArity headRepeatCount hgraph).compile

noncomputable def compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitStructuralResource
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headKind headBinderArity headRepeatCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKind
      headBinderArity headRepeatCount) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridCertificateOfGraph tokenTable width
      tokenCount sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKind
      headBinderArity headRepeatCount hgraph)

theorem
    compileCompactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headKind headBinderArity headRepeatCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKind
      headBinderArity headRepeatCount) :
    (compileCompactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridContext tokenTable width
      tokenCount sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKind
      headBinderArity headRepeatCount hgraph).payloadLength ≤
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitStructuralResource tokenTable width
        tokenCount sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKind
        headBinderArity headRepeatCount hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridCertificateOfGraph tokenTable width
      tokenCount sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize headKind
      headBinderArity headRepeatCount hgraph)

#print axioms compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedFormula_alignment
#print axioms
  compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula_alignment
#print axioms
  compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula_alignment
#print axioms
  compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph
#print axioms
  compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindExplicitHybridCertificateOfGraph
#print axioms compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridCertificateOfGraph
#print axioms
  compileCompactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
