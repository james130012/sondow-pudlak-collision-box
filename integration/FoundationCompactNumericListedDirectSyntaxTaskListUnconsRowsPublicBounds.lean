import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicFiniteUniversalBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicFiniteUniversalBounds
import integration.FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsPublicBounds
import integration.FoundationCompactNumericListedDirectNatSizePublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds

/-!
# Public structural resources for syntax-task-list uncons

The uncons certificate is charged as six independent checked components:
positivity, one-row drop, triple-boundary validity, reconstruction by cons,
binary size, and the tail-boundary area inequality.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsPublicBounds
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizePublicBounds

private abbrev unconsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation

private abbrev dropZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation

private abbrev tripleZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate.zeroValuation

private abbrev consZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.zeroValuation

private abbrev natSizeZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate.zeroValuation

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

private theorem binaryFunctionTerm_freeVariables
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiterm.func functionSymbol
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem arithmeticZeroTerm_freeVariables_eq_empty :
    (‘0’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

def compactAdditiveSyntaxTaskListUnconsRowsPositivePayloadPolynomial
    (sourceCount : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial unconsZeroValuation
    Language.ORing.Rel.lt
    ![(‘0’ : ValuationTerm), shortBinaryNumeralTerm sourceCount]

theorem closedPositiveCertificate_structuralPayloadBound_le_public
    (sourceCount : Nat) (hpositive : 0 < sourceCount) :
    hybridFormulaStructuralPayloadBound
        (closedPositiveCertificate sourceCount hpositive) ≤
      compactAdditiveSyntaxTaskListUnconsRowsPositivePayloadPolynomial
        sourceCount := by
  have hfirst : (‘0’ : ValuationTerm).freeVariables ⊆ {0} := by
    rw [arithmeticZeroTerm_freeVariables_eq_empty]
    simp
  have hsecond :
      (shortBinaryNumeralTerm sourceCount).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    unconsZeroValuation Language.ORing.Rel.lt
    ![(‘0’ : ValuationTerm), shortBinaryNumeralTerm sourceCount]
    hfirst hsecond
  simpa only [closedPositiveCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveSyntaxTaskListUnconsRowsPositivePayloadPolynomial] using
    hpublic

def compactAdditiveSyntaxTaskListUnconsRowsTailAreaPayloadPolynomial
    (tailBoundarySize tailCount tokenCount : Nat) : Nat :=
  let leftTerm := shortBinaryNumeralTerm tailBoundarySize
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm tailCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula := LO.FirstOrder.Semiformula.rel Language.LT.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables unconsZeroValuation
  compilePositiveRelationPayloadPolynomial
      unconsZeroValuation Language.Eq.eq args +
    compilePositiveRelationPayloadPolynomial
      unconsZeroValuation Language.ORing.Rel.lt args +
    weakeningFullAssemblyCost (insert equalityFormula Gamma) +
    weakeningFullAssemblyCost (insert strictFormula Gamma) +
    disjunctionFullAssemblyCost Gamma equalityFormula strictFormula

theorem closedTailAreaLeCertificate_structuralPayloadBound_le_public
    (tailBoundarySize tailCount tokenCount : Nat)
    (hbound : tailBoundarySize ≤ (tailCount + 1) * tokenCount) :
    hybridFormulaStructuralPayloadBound
        (closedTailAreaLeCertificate tailBoundarySize tailCount tokenCount
          hbound) ≤
      compactAdditiveSyntaxTaskListUnconsRowsTailAreaPayloadPolynomial
        tailBoundarySize tailCount tokenCount := by
  let leftTerm := shortBinaryNumeralTerm tailBoundarySize
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm tailCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  have hleft : leftTerm.freeVariables ⊆ {0} := by
    dsimp only [leftTerm]
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hrightClosed : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    rw [arithmeticMulTerm_eq_func, binaryFunctionTerm_freeVariables,
      arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticOneTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hright : rightTerm.freeVariables ⊆ {0} := by
    rw [hrightClosed]
    simp
  have hequality :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      unconsZeroValuation Language.Eq.eq args hleft hright
  have hstrict :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      unconsZeroValuation Language.ORing.Rel.lt args hleft hright
  by_cases heq : tailBoundarySize = (tailCount + 1) * tokenCount
  · simp only [closedTailAreaLeCertificate, tailAreaTerm]
    rw [dif_pos heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold compactAdditiveSyntaxTaskListUnconsRowsTailAreaPayloadPolynomial
    dsimp only [leftTerm, rightTerm, args] at hequality hstrict ⊢
    simp only [unconsZeroValuation] at hequality hstrict ⊢
    omega
  · simp only [closedTailAreaLeCertificate, tailAreaTerm]
    rw [dif_neg heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold compactAdditiveSyntaxTaskListUnconsRowsTailAreaPayloadPolynomial
    dsimp only [leftTerm, rightTerm, args] at hequality hstrict ⊢
    simp only [unconsZeroValuation] at hequality hstrict ⊢
    omega

noncomputable def
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsGraphPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm)
    (hgraph : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headKind headBinderArity headRepeatCount) : Nat :=
  let positiveFormula : ValuationFormula :=
    “0 < !!(shortBinaryNumeralTerm sourceCount)”
  let dropFormula :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula tokenTable
      width tokenCount sourceBoundary sourceCount tailBoundary tailCount 1
  let tripleFormula := compactAdditiveTripleBoundaryRowsClosedFormula tokenCount
    tailCount tailBoundary
  let consFormula :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula tokenTable
      width tokenCount tailBoundary tailCount sourceBoundary sourceCount
      headKindTerm headBinderArityTerm headRepeatCountTerm
  let sizeFormula := compactNatSizeClosedFormula tailBoundarySize tailBoundary
  let areaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm tailBoundarySize) ≤
      (!!(shortBinaryNumeralTerm tailCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let sizeAreaResource := transparentHybridConjunctionPayloadEnvelope
    natSizeZeroValuation sizeFormula areaFormula
    (compactNatSizeStructuralPayloadPolynomial tailBoundarySize tailBoundary)
    (compactAdditiveSyntaxTaskListUnconsRowsTailAreaPayloadPolynomial
      tailBoundarySize tailCount tokenCount)
  let consTailResource := transparentHybridConjunctionPayloadEnvelope
    consZeroValuation consFormula (sizeFormula ⋏ areaFormula)
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsGraphPayloadEnvelope
      tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount headKind headBinderArity headRepeatCount headKindTerm
      headBinderArityTerm headRepeatCountTerm hgraph.2.2.2.1)
    sizeAreaResource
  let tripleTailResource := transparentHybridConjunctionPayloadEnvelope
    tripleZeroValuation tripleFormula
    (consFormula ⋏ (sizeFormula ⋏ areaFormula))
    (compactAdditiveTripleBoundaryRowsGraphStructuralPayloadEnvelope tokenCount
      tailCount tailBoundary hgraph.2.2.1)
    consTailResource
  let dropTailResource := transparentHybridConjunctionPayloadEnvelope
    dropZeroValuation dropFormula
    (tripleFormula ⋏ (consFormula ⋏ (sizeFormula ⋏ areaFormula)))
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsGraphPayloadEnvelope
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount 1 hgraph.2.1)
    tripleTailResource
  transparentHybridConjunctionPayloadEnvelope unconsZeroValuation
    positiveFormula
    (dropFormula ⋏
      (tripleFormula ⋏ (consFormula ⋏ (sizeFormula ⋏ areaFormula))))
    (compactAdditiveSyntaxTaskListUnconsRowsPositivePayloadPolynomial
      sourceCount)
    dropTailResource

def
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsPublicFinitePayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm) : Nat :=
  let positiveFormula : ValuationFormula :=
    “0 < !!(shortBinaryNumeralTerm sourceCount)”
  let dropFormula :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula tokenTable
      width tokenCount sourceBoundary sourceCount tailBoundary tailCount 1
  let tripleFormula := compactAdditiveTripleBoundaryRowsClosedFormula tokenCount
    tailCount tailBoundary
  let consFormula :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula tokenTable
      width tokenCount tailBoundary tailCount sourceBoundary sourceCount
      headKindTerm headBinderArityTerm headRepeatCountTerm
  let sizeFormula := compactNatSizeClosedFormula tailBoundarySize tailBoundary
  let areaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm tailBoundarySize) ≤
      (!!(shortBinaryNumeralTerm tailCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let sizeAreaResource := transparentHybridConjunctionPayloadEnvelope
    natSizeZeroValuation sizeFormula areaFormula
    (compactNatSizeStructuralPayloadPolynomial tailBoundarySize tailBoundary)
    (compactAdditiveSyntaxTaskListUnconsRowsTailAreaPayloadPolynomial
      tailBoundarySize tailCount tokenCount)
  let consTailResource := transparentHybridConjunctionPayloadEnvelope
    consZeroValuation consFormula (sizeFormula ⋏ areaFormula)
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsPublicFinitePayloadEnvelope
      tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount headKind headBinderArity headRepeatCount headKindTerm
      headBinderArityTerm headRepeatCountTerm)
    sizeAreaResource
  let tripleTailResource := transparentHybridConjunctionPayloadEnvelope
    tripleZeroValuation tripleFormula
    (consFormula ⋏ (sizeFormula ⋏ areaFormula))
    (compactAdditiveTripleBoundaryRowsPublicFiniteStructuralPayloadEnvelope
      tokenCount tailCount tailBoundary)
    consTailResource
  let dropTailResource := transparentHybridConjunctionPayloadEnvelope
    dropZeroValuation dropFormula
    (tripleFormula ⋏ (consFormula ⋏ (sizeFormula ⋏ areaFormula)))
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsPublicFinitePayloadEnvelope
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount 1)
    tripleTailResource
  transparentHybridConjunctionPayloadEnvelope unconsZeroValuation
    positiveFormula
    (dropFormula ⋏
      (tripleFormula ⋏ (consFormula ⋏ (sizeFormula ⋏ areaFormula))))
    (compactAdditiveSyntaxTaskListUnconsRowsPositivePayloadPolynomial
      sourceCount)
    dropTailResource

theorem
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsGraphPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm)
    (hgraph : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headKind headBinderArity headRepeatCount) :
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsGraphPayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount tailBoundarySize headKind headBinderArity headRepeatCount
        headKindTerm headBinderArityTerm headRepeatCountTerm hgraph <=
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsPublicFinitePayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount tailBoundarySize headKind headBinderArity headRepeatCount
        headKindTerm headBinderArityTerm headRepeatCountTerm := by
  unfold
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsGraphPayloadEnvelope
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsPublicFinitePayloadEnvelope
  exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsGraphPayloadEnvelope_le_publicFinite
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount 1 hgraph.2.1)
      (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
        (compactAdditiveTripleBoundaryRowsGraphStructuralPayloadEnvelope_le_publicFinite
          tokenCount tailCount tailBoundary hgraph.2.2.1)
        (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
          (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsGraphPayloadEnvelope_le_publicFinite
            tokenTable width tokenCount tailBoundary tailCount sourceBoundary
            sourceCount headKind headBinderArity headRepeatCount headKindTerm
            headBinderArityTerm headRepeatCountTerm hgraph.2.2.2.1)
          (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
            le_rfl))))

theorem
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm)
    (hheadKindClosed : headKindTerm.freeVariables = ∅)
    (hheadBinderArityClosed : headBinderArityTerm.freeVariables = ∅)
    (hheadRepeatCountClosed : headRepeatCountTerm.freeVariables = ∅)
    (hheadKindValue : ∀ valuation, termValue valuation headKindTerm = headKind)
    (hheadBinderArityValue : ∀ valuation,
      termValue valuation headBinderArityTerm = headBinderArity)
    (hheadRepeatCountValue : ∀ valuation,
      termValue valuation headRepeatCountTerm = headRepeatCount)
    (hgraph : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headKind headBinderArity headRepeatCount) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
          tailCount tailBoundarySize headKind headBinderArity headRepeatCount
          headKindTerm headBinderArityTerm headRepeatCountTerm hheadKindValue
          hheadBinderArityValue hheadRepeatCountValue hgraph) ≤
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsGraphPayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount tailBoundarySize headKind headBinderArity headRepeatCount
        headKindTerm headBinderArityTerm headRepeatCountTerm hgraph := by
  rcases hgraph with ⟨hpositive, hdrop, htriple, hcons, hsize, harea⟩
  let positiveCertificate := closedPositiveCertificate sourceCount hpositive
  let dropCertificate :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount 1 hdrop
  let tripleCertificate :=
    compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph tokenCount
      tailCount tailBoundary htriple
  let consCertificate :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount headKind headBinderArity headRepeatCount headKindTerm
      headBinderArityTerm headRepeatCountTerm hheadKindValue
      hheadBinderArityValue hheadRepeatCountValue hcons
  let sizeCertificate := compactNatSizeExplicitHybridCertificateOfEq
    tailBoundarySize tailBoundary hsize
  let areaCertificate := closedTailAreaLeCertificate tailBoundarySize
    tailCount tokenCount harea
  let sizeAreaCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      sizeCertificate areaCertificate
  let consTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      consCertificate sizeAreaCertificate
  let tripleTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      tripleCertificate consTailCertificate
  let dropTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      dropCertificate tripleTailCertificate
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    positiveCertificate dropTailCertificate
  have hpositiveResource :=
    closedPositiveCertificate_structuralPayloadBound_le_public sourceCount
      hpositive
  have hdropResource :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount 1 hdrop
  have htripleResource :=
    compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenCount tailCount tailBoundary htriple
  have hconsResource :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount headKind headBinderArity headRepeatCount headKindTerm
      headBinderArityTerm headRepeatCountTerm hheadKindClosed
      hheadBinderArityClosed hheadRepeatCountClosed hheadKindValue
      hheadBinderArityValue hheadRepeatCountValue hcons
  have hsizeResource :=
    compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
      tailBoundarySize tailBoundary hsize
  have hareaResource :=
    closedTailAreaLeCertificate_structuralPayloadBound_le_public
      tailBoundarySize tailCount tokenCount harea
  have hsizeAreaResource := transparentHybridConjunctionPayloadBound_le
    sizeCertificate areaCertificate _ _ hsizeResource hareaResource
  have hconsTailResource := transparentHybridConjunctionPayloadBound_le
    consCertificate sizeAreaCertificate _ _ hconsResource hsizeAreaResource
  have htripleTailResource := transparentHybridConjunctionPayloadBound_le
    tripleCertificate consTailCertificate _ _ htripleResource hconsTailResource
  have hdropTailResource := transparentHybridConjunctionPayloadBound_le
    dropCertificate tripleTailCertificate _ _ hdropResource htripleTailResource
  have hparts := transparentHybridConjunctionPayloadBound_le
    positiveCertificate dropTailCertificate _ _ hpositiveResource
    hdropTailResource
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula_alignment
          tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
          tailCount tailBoundarySize headKindTerm headBinderArityTerm
          headRepeatCountTerm).symm parts) ≤ _
  simpa [
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsGraphPayloadEnvelope,
    hybridFormulaStructuralPayloadBound, positiveCertificate,
    dropCertificate, tripleCertificate, consCertificate, sizeCertificate,
    areaCertificate, sizeAreaCertificate, consTailCertificate,
    tripleTailCertificate, dropTailCertificate, parts] using hparts

theorem
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm)
    (hheadKindClosed : headKindTerm.freeVariables = ∅)
    (hheadBinderArityClosed : headBinderArityTerm.freeVariables = ∅)
    (hheadRepeatCountClosed : headRepeatCountTerm.freeVariables = ∅)
    (hheadKindValue : ∀ valuation, termValue valuation headKindTerm = headKind)
    (hheadBinderArityValue : ∀ valuation,
      termValue valuation headBinderArityTerm = headBinderArity)
    (hheadRepeatCountValue : ∀ valuation,
      termValue valuation headRepeatCountTerm = headRepeatCount)
    (hgraph : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headKind headBinderArity headRepeatCount) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
          tailCount tailBoundarySize headKind headBinderArity headRepeatCount
          headKindTerm headBinderArityTerm headRepeatCountTerm hheadKindValue
          hheadBinderArityValue hheadRepeatCountValue hgraph) <=
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsPublicFinitePayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount tailBoundarySize headKind headBinderArity headRepeatCount
        headKindTerm headBinderArityTerm headRepeatCountTerm := by
  exact
    (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount
      headKindTerm headBinderArityTerm headRepeatCountTerm hheadKindClosed
      hheadBinderArityClosed hheadRepeatCountClosed hheadKindValue
      hheadBinderArityValue hheadRepeatCountValue hgraph).trans
    (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsGraphPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount
      headKindTerm headBinderArityTerm headRepeatCountTerm hgraph)

noncomputable def
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedGraphPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headKind headBinderArity headRepeatCount) : Nat :=
  compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsGraphPayloadEnvelope
    tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
    tailCount tailBoundarySize headKind headBinderArity headRepeatCount
    (shortBinaryNumeralTerm headKind)
    (shortBinaryNumeralTerm headBinderArity)
    (shortBinaryNumeralTerm headRepeatCount) hgraph

def
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedPublicFinitePayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount : Nat) :
    Nat :=
  compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsPublicFinitePayloadEnvelope
    tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
    tailCount tailBoundarySize headKind headBinderArity headRepeatCount
    (shortBinaryNumeralTerm headKind)
    (shortBinaryNumeralTerm headBinderArity)
    (shortBinaryNumeralTerm headRepeatCount)

theorem
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedGraphPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headKind headBinderArity headRepeatCount) :
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedGraphPayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount tailBoundarySize headKind headBinderArity headRepeatCount
        hgraph <=
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedPublicFinitePayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount tailBoundarySize headKind headBinderArity headRepeatCount := by
  simpa only [
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedGraphPayloadEnvelope,
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedPublicFinitePayloadEnvelope] using
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsGraphPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount
      (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount) hgraph

theorem
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headKind headBinderArity headRepeatCount) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
          tailCount tailBoundarySize headKind headBinderArity headRepeatCount
          hgraph) ≤
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedGraphPayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount tailBoundarySize headKind headBinderArity headRepeatCount
        hgraph := by
  simpa only [
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridCertificateOfGraph,
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedGraphPayloadEnvelope,
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedFormula,
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindExplicitHybridCertificateOfGraph,
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula,
    id_eq] using
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount
      (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)
      (shortBinaryNumeralTerm_freeVariables_eq_empty headKind)
      (shortBinaryNumeralTerm_freeVariables_eq_empty headBinderArity)
      (shortBinaryNumeralTerm_freeVariables_eq_empty headRepeatCount)
      (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
      (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
      (fun valuation => by simp [termValue_shortBinaryNumeralTerm]) hgraph

theorem
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize headKind headBinderArity headRepeatCount) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
          tailCount tailBoundarySize headKind headBinderArity headRepeatCount
          hgraph) <=
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedPublicFinitePayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount tailBoundarySize headKind headBinderArity headRepeatCount := by
  simpa only [
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridCertificateOfGraph,
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedPublicFinitePayloadEnvelope,
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedFormula,
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindExplicitHybridCertificateOfGraph,
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula,
    id_eq] using
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount
      (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)
      (shortBinaryNumeralTerm_freeVariables_eq_empty headKind)
      (shortBinaryNumeralTerm_freeVariables_eq_empty headBinderArity)
      (shortBinaryNumeralTerm_freeVariables_eq_empty headRepeatCount)
      (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
      (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
      (fun valuation => by simp [termValue_shortBinaryNumeralTerm]) hgraph

#print axioms closedPositiveCertificate_structuralPayloadBound_le_public
#print axioms closedTailAreaLeCertificate_structuralPayloadBound_le_public
#print axioms
  compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
#print axioms
  compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite

end FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsPublicBounds
