import integration.FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
import integration.FoundationCompactNumericListedDirectNatSizePublicBounds
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resource for equal completed parser statuses

The two completed prefixes, two output layouts, common output rows, two exact
binary sizes, and two area inequalities are charged by one transparent
nine-leaf conjunction envelope.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectCompletedStatusSameRowsPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectCompletedStatusSameRows
open FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizePublicBounds

private abbrev completedZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate.zeroValuation

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

private theorem arithmeticAddTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables
  exact binaryFunctionTerm_freeVariables Language.Add.add left right

private theorem arithmeticMulTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left * !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Mul.mul ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables
  exact binaryFunctionTerm_freeVariables Language.Mul.mul left right

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left * !!right’ : ValuationTerm) =
      Semiterm.func Language.Mul.mul ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Mul.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (left right : ValuationTerm) :
    termValue completedZeroValuation ‘!!left + !!right’ =
      termValue completedZeroValuation left +
        termValue completedZeroValuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add completedZeroValuation ![left, right]

private theorem termValue_arithmeticMul
    (left right : ValuationTerm) :
    termValue completedZeroValuation ‘!!left * !!right’ =
      termValue completedZeroValuation left *
        termValue completedZeroValuation right := by
  rw [arithmeticMulTerm_eq_func]
  exact termValue_mul completedZeroValuation ![left, right]

private theorem termValue_arithmeticOne :
    termValue completedZeroValuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one completedZeroValuation ![]

def completedStatusValuationLePayloadPolynomial
    (leftTerm rightTerm : ValuationTerm) : Nat :=
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula := LO.FirstOrder.Semiformula.rel Language.LT.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables completedZeroValuation
  compilePositiveRelationPayloadPolynomial
      completedZeroValuation Language.Eq.eq args +
    compilePositiveRelationPayloadPolynomial
      completedZeroValuation Language.ORing.Rel.lt args +
    weakeningFullAssemblyCost (insert equalityFormula Gamma) +
    weakeningFullAssemblyCost (insert strictFormula Gamma) +
    disjunctionFullAssemblyCost Gamma equalityFormula strictFormula

theorem valuationLeCertificate_structuralPayloadBound_le_public
    (leftTerm rightTerm : ValuationTerm)
    (hleft : leftTerm.freeVariables = ∅)
    (hright : rightTerm.freeVariables = ∅)
    (hle : termValue completedZeroValuation leftTerm ≤
      termValue completedZeroValuation rightTerm) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate.valuationLeCertificate
          leftTerm rightTerm hle) ≤
      completedStatusValuationLePayloadPolynomial leftTerm rightTerm := by
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  have hfirst : (args 0).freeVariables ⊆ {0} := by
    change leftTerm.freeVariables ⊆ {0}
    rw [hleft]
    simp
  have hsecond : (args 1).freeVariables ⊆ {0} := by
    change rightTerm.freeVariables ⊆ {0}
    rw [hright]
    simp
  have hequality :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      completedZeroValuation Language.Eq.eq args hfirst hsecond
  have hstrict :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      completedZeroValuation Language.ORing.Rel.lt args hfirst hsecond
  by_cases heq : termValue completedZeroValuation leftTerm =
      termValue completedZeroValuation rightTerm
  · simp only [
      FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate.valuationLeCertificate]
    rw [dif_pos heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold completedStatusValuationLePayloadPolynomial
    dsimp only [args] at hequality hstrict ⊢
    simp only [completedZeroValuation] at hequality hstrict ⊢
    omega
  · simp only [
      FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate.valuationLeCertificate]
    rw [dif_neg heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold completedStatusValuationLePayloadPolynomial
    dsimp only [args] at hequality hstrict ⊢
    simp only [completedZeroValuation] at hequality hstrict ⊢
    omega

def completedStatusBoundaryAreaPayloadPolynomial
    (tokenCount outputCount boundarySize : Nat) : Nat :=
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm outputCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  completedStatusValuationLePayloadPolynomial
    (shortBinaryNumeralTerm boundarySize) rightTerm

theorem boundaryAreaCertificate_structuralPayloadBound_le_public
    (tokenCount outputCount boundarySize : Nat)
    (hbound : boundarySize ≤ (outputCount + 1) * tokenCount) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate.boundaryAreaCertificate
          tokenCount outputCount boundarySize hbound) ≤
      completedStatusBoundaryAreaPayloadPolynomial tokenCount outputCount
        boundarySize := by
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm outputCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  have hleft :
      (shortBinaryNumeralTerm boundarySize).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty boundarySize
  have hright : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    rw [arithmeticMulTerm_freeVariables, arithmeticAddTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticOneTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hle : termValue completedZeroValuation
      (shortBinaryNumeralTerm boundarySize) ≤
      termValue completedZeroValuation rightTerm := by
    simpa [rightTerm, termValue_shortBinaryNumeralTerm,
      termValue_arithmeticAdd, termValue_arithmeticMul,
      termValue_arithmeticOne] using hbound
  have hpublic := valuationLeCertificate_structuralPayloadBound_le_public
    (shortBinaryNumeralTerm boundarySize) rightTerm hleft hright hle
  change hybridFormulaStructuralPayloadBound
      (FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate.valuationLeCertificate
        (shortBinaryNumeralTerm boundarySize) rightTerm hle) ≤ _
  unfold completedStatusBoundaryAreaPayloadPolynomial
  dsimp only [rightTerm] at hpublic ⊢
  exact hpublic

def compactBinaryNatCompletedStatusSameRowsWithSizePublicFinitePayloadEnvelope
    (tokenTable width tokenCount
      sourceStatusStart sourceStatusFinish
      targetStatusStart targetStatusFinish
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) : Nat := by
  let sourcePrefixFormula := compactBinaryNatCompletedStatusPrefixClosedFormula
    tokenTable width tokenCount sourceStatusStart sourceOutputStart
  let sourceLayoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount sourceOutputStart outputCount
    sourceStatusFinish sourceOutputBoundary
  let targetPrefixFormula := compactBinaryNatCompletedStatusPrefixClosedFormula
    tokenTable width tokenCount targetStatusStart targetOutputStart
  let targetLayoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount targetOutputStart outputCount
    targetStatusFinish targetOutputBoundary
  let sameFormula := compactAdditiveNatListSameRowsClosedFormula tokenTable
    width tokenCount sourceOutputBoundary outputCount targetOutputBoundary
    outputCount
  let sourceSizeFormula := compactNatSizeClosedFormula sourceOutputBoundarySize
    sourceOutputBoundary
  let sourceAreaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sourceOutputBoundarySize) ≤
      (!!(shortBinaryNumeralTerm outputCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let targetSizeFormula := compactNatSizeClosedFormula targetOutputBoundarySize
    targetOutputBoundary
  let targetAreaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetOutputBoundarySize) ≤
      (!!(shortBinaryNumeralTerm outputCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let sourcePrefixResource :=
    compactBinaryNatCompletedStatusPrefixStructuralPayloadPolynomial tokenTable
      width tokenCount sourceStatusStart sourceOutputStart
  let sourceLayoutResource :=
    compactAdditiveStructuredListLayoutPublicFiniteStructuralPayloadEnvelope
      tokenTable width tokenCount sourceOutputStart outputCount
      sourceStatusFinish sourceOutputBoundary
  let targetPrefixResource :=
    compactBinaryNatCompletedStatusPrefixStructuralPayloadPolynomial tokenTable
      width tokenCount targetStatusStart targetOutputStart
  let targetLayoutResource :=
    compactAdditiveStructuredListLayoutPublicFiniteStructuralPayloadEnvelope
      tokenTable width tokenCount targetOutputStart outputCount
      targetStatusFinish targetOutputBoundary
  let sameResource := compactAdditiveNatListSameRowsPublicFinitePayloadEnvelope
    tokenTable width tokenCount sourceOutputBoundary outputCount
    targetOutputBoundary outputCount
  let sourceSizeResource := compactNatSizeStructuralPayloadPolynomial
    sourceOutputBoundarySize sourceOutputBoundary
  let sourceAreaResource := completedStatusBoundaryAreaPayloadPolynomial
    tokenCount outputCount sourceOutputBoundarySize
  let targetSizeResource := compactNatSizeStructuralPayloadPolynomial
    targetOutputBoundarySize targetOutputBoundary
  let targetAreaResource := completedStatusBoundaryAreaPayloadPolynomial
    tokenCount outputCount targetOutputBoundarySize
  let targetSizeAreaResource := transparentHybridConjunctionPayloadEnvelope
    completedZeroValuation targetSizeFormula targetAreaFormula
    targetSizeResource targetAreaResource
  let sourceAreaTailResource := transparentHybridConjunctionPayloadEnvelope
    completedZeroValuation sourceAreaFormula
    (targetSizeFormula ⋏ targetAreaFormula) sourceAreaResource
    targetSizeAreaResource
  let sourceSizeTailResource := transparentHybridConjunctionPayloadEnvelope
    completedZeroValuation sourceSizeFormula
    (sourceAreaFormula ⋏ (targetSizeFormula ⋏ targetAreaFormula))
    sourceSizeResource sourceAreaTailResource
  let sameTailResource := transparentHybridConjunctionPayloadEnvelope
    completedZeroValuation sameFormula
    (sourceSizeFormula ⋏
      (sourceAreaFormula ⋏ (targetSizeFormula ⋏ targetAreaFormula)))
    sameResource sourceSizeTailResource
  let targetLayoutTailResource := transparentHybridConjunctionPayloadEnvelope
    completedZeroValuation targetLayoutFormula
    (sameFormula ⋏
      (sourceSizeFormula ⋏
        (sourceAreaFormula ⋏ (targetSizeFormula ⋏ targetAreaFormula))))
    targetLayoutResource sameTailResource
  let targetPrefixTailResource := transparentHybridConjunctionPayloadEnvelope
    completedZeroValuation targetPrefixFormula
    (targetLayoutFormula ⋏
      (sameFormula ⋏
        (sourceSizeFormula ⋏
          (sourceAreaFormula ⋏ (targetSizeFormula ⋏ targetAreaFormula)))))
    targetPrefixResource targetLayoutTailResource
  let sourceLayoutTailResource := transparentHybridConjunctionPayloadEnvelope
    completedZeroValuation sourceLayoutFormula
    (targetPrefixFormula ⋏
      (targetLayoutFormula ⋏
        (sameFormula ⋏
          (sourceSizeFormula ⋏
            (sourceAreaFormula ⋏ (targetSizeFormula ⋏ targetAreaFormula))))))
    sourceLayoutResource targetPrefixTailResource
  exact transparentHybridConjunctionPayloadEnvelope completedZeroValuation
    sourcePrefixFormula
    (sourceLayoutFormula ⋏
      (targetPrefixFormula ⋏
        (targetLayoutFormula ⋏
          (sameFormula ⋏
            (sourceSizeFormula ⋏
              (sourceAreaFormula ⋏
                (targetSizeFormula ⋏ targetAreaFormula)))))))
    sourcePrefixResource sourceLayoutTailResource

theorem
    compactBinaryNatCompletedStatusSameRowsWithSizeExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount
      sourceStatusStart sourceStatusFinish
      targetStatusStart targetStatusFinish
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat)
    (hgraph : CompactBinaryNatCompletedStatusSameRowsWithSize
      tokenTable width tokenCount sourceStatusStart sourceStatusFinish
      targetStatusStart targetStatusFinish sourceOutputStart
      sourceOutputBoundary sourceOutputBoundarySize targetOutputStart
      targetOutputBoundary targetOutputBoundarySize outputCount) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatCompletedStatusSameRowsWithSizeExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceStatusStart sourceStatusFinish
          targetStatusStart targetStatusFinish sourceOutputStart
          sourceOutputBoundary sourceOutputBoundarySize targetOutputStart
          targetOutputBoundary targetOutputBoundarySize outputCount hgraph) ≤
      compactBinaryNatCompletedStatusSameRowsWithSizePublicFinitePayloadEnvelope
        tokenTable width tokenCount sourceStatusStart sourceStatusFinish
        targetStatusStart targetStatusFinish sourceOutputStart
        sourceOutputBoundary sourceOutputBoundarySize targetOutputStart
        targetOutputBoundary targetOutputBoundarySize outputCount := by
  rcases hgraph with
    ⟨hbase, hsourceSize, hsourceArea, htargetSize, htargetArea⟩
  rcases hbase with
    ⟨hsourcePrefix, hsourceLayout, htargetPrefix,
      htargetLayout, hsame⟩
  let sourcePrefixCertificate :
      CheckedHybridValuationBoundedFormulaCertificate completedZeroValuation
        (compactBinaryNatCompletedStatusPrefixClosedFormula tokenTable width
          tokenCount sourceStatusStart sourceOutputStart) :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceStatusStart sourceOutputStart
      hsourcePrefix
  let sourceLayoutCertificate :
      CheckedHybridValuationBoundedFormulaCertificate completedZeroValuation
        (compactAdditiveStructuredListLayoutClosedFormula tokenTable width
          tokenCount sourceOutputStart outputCount sourceStatusFinish
          sourceOutputBoundary) :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
      tokenTable width tokenCount sourceOutputStart outputCount
      sourceStatusFinish sourceOutputBoundary hsourceLayout
  let targetPrefixCertificate :
      CheckedHybridValuationBoundedFormulaCertificate completedZeroValuation
        (compactBinaryNatCompletedStatusPrefixClosedFormula tokenTable width
          tokenCount targetStatusStart targetOutputStart) :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount targetStatusStart targetOutputStart
      htargetPrefix
  let targetLayoutCertificate :
      CheckedHybridValuationBoundedFormulaCertificate completedZeroValuation
        (compactAdditiveStructuredListLayoutClosedFormula tokenTable width
          tokenCount targetOutputStart outputCount targetStatusFinish
          targetOutputBoundary) :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
      tokenTable width tokenCount targetOutputStart outputCount
      targetStatusFinish targetOutputBoundary htargetLayout
  let sameCertificate :
      CheckedHybridValuationBoundedFormulaCertificate completedZeroValuation
        (compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
          sourceOutputBoundary outputCount targetOutputBoundary outputCount) :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount sourceOutputBoundary outputCount targetOutputBoundary
      outputCount hsame
  let sourceSizeCertificate :
      CheckedHybridValuationBoundedFormulaCertificate completedZeroValuation
        (compactNatSizeClosedFormula sourceOutputBoundarySize
          sourceOutputBoundary) :=
    compactNatSizeExplicitHybridCertificateOfEq sourceOutputBoundarySize
      sourceOutputBoundary hsourceSize
  let sourceAreaCertificate :
      CheckedHybridValuationBoundedFormulaCertificate completedZeroValuation
        “!!(shortBinaryNumeralTerm sourceOutputBoundarySize) ≤
          (!!(shortBinaryNumeralTerm outputCount) + 1) *
            !!(shortBinaryNumeralTerm tokenCount)” :=
    FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate.boundaryAreaCertificate
      tokenCount outputCount sourceOutputBoundarySize hsourceArea
  let targetSizeCertificate :
      CheckedHybridValuationBoundedFormulaCertificate completedZeroValuation
        (compactNatSizeClosedFormula targetOutputBoundarySize
          targetOutputBoundary) :=
    compactNatSizeExplicitHybridCertificateOfEq targetOutputBoundarySize
      targetOutputBoundary htargetSize
  let targetAreaCertificate :
      CheckedHybridValuationBoundedFormulaCertificate completedZeroValuation
        “!!(shortBinaryNumeralTerm targetOutputBoundarySize) ≤
          (!!(shortBinaryNumeralTerm outputCount) + 1) *
            !!(shortBinaryNumeralTerm tokenCount)” :=
    FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate.boundaryAreaCertificate
      tokenCount outputCount targetOutputBoundarySize htargetArea
  have hsourcePrefixResource :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount sourceStatusStart sourceOutputStart
      hsourcePrefix
  have hsourceLayoutResource :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout_structuralPayloadBound_le_publicFinite
      tokenTable width tokenCount sourceOutputStart outputCount
      sourceStatusFinish sourceOutputBoundary hsourceLayout
  have htargetPrefixResource :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount targetStatusStart targetOutputStart
      htargetPrefix
  have htargetLayoutResource :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout_structuralPayloadBound_le_publicFinite
      tokenTable width tokenCount targetOutputStart outputCount
      targetStatusFinish targetOutputBoundary htargetLayout
  have hsameResource :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
      tokenTable width tokenCount sourceOutputBoundary outputCount
      targetOutputBoundary outputCount hsame
  have hsourceSizeResource :=
    compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
      sourceOutputBoundarySize sourceOutputBoundary hsourceSize
  have hsourceAreaResource :=
    boundaryAreaCertificate_structuralPayloadBound_le_public tokenCount
      outputCount sourceOutputBoundarySize hsourceArea
  have htargetSizeResource :=
    compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
      targetOutputBoundarySize targetOutputBoundary htargetSize
  have htargetAreaResource :=
    boundaryAreaCertificate_structuralPayloadBound_le_public tokenCount
      outputCount targetOutputBoundarySize htargetArea
  let targetSizeArea :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      targetSizeCertificate targetAreaCertificate
  have htargetSizeArea := transparentHybridConjunctionPayloadBound_le
    targetSizeCertificate targetAreaCertificate _ _ htargetSizeResource
    htargetAreaResource
  let sourceAreaTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      sourceAreaCertificate targetSizeArea
  have hsourceAreaTail := transparentHybridConjunctionPayloadBound_le
    sourceAreaCertificate targetSizeArea _ _ hsourceAreaResource
    htargetSizeArea
  let sourceSizeTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      sourceSizeCertificate sourceAreaTail
  have hsourceSizeTail := transparentHybridConjunctionPayloadBound_le
    sourceSizeCertificate sourceAreaTail _ _ hsourceSizeResource
    hsourceAreaTail
  let sameTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    sameCertificate sourceSizeTail
  have hsameTail := transparentHybridConjunctionPayloadBound_le
    sameCertificate sourceSizeTail _ _ hsameResource hsourceSizeTail
  let targetLayoutTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      targetLayoutCertificate sameTail
  have htargetLayoutTail := transparentHybridConjunctionPayloadBound_le
    targetLayoutCertificate sameTail _ _ htargetLayoutResource hsameTail
  let targetPrefixTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      targetPrefixCertificate targetLayoutTail
  have htargetPrefixTail := transparentHybridConjunctionPayloadBound_le
    targetPrefixCertificate targetLayoutTail _ _ htargetPrefixResource
    htargetLayoutTail
  let sourceLayoutTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      sourceLayoutCertificate targetPrefixTail
  have hsourceLayoutTail := transparentHybridConjunctionPayloadBound_le
    sourceLayoutCertificate targetPrefixTail _ _ hsourceLayoutResource
    htargetPrefixTail
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    sourcePrefixCertificate sourceLayoutTail
  have hparts := transparentHybridConjunctionPayloadBound_le
    sourcePrefixCertificate sourceLayoutTail _ _ hsourcePrefixResource
    hsourceLayoutTail
  unfold compactBinaryNatCompletedStatusSameRowsWithSizePublicFinitePayloadEnvelope
  simpa only [
    compactBinaryNatCompletedStatusSameRowsWithSizeExplicitHybridCertificateOfGraph,
    hybridFormulaStructuralPayloadBound, sourcePrefixCertificate,
    sourceLayoutCertificate, targetPrefixCertificate,
    targetLayoutCertificate, sameCertificate, sourceSizeCertificate,
    sourceAreaCertificate, targetSizeCertificate, targetAreaCertificate,
    targetSizeArea, sourceAreaTail, sourceSizeTail, sameTail,
    targetLayoutTail, targetPrefixTail, sourceLayoutTail, parts] using hparts

#print axioms valuationLeCertificate_structuralPayloadBound_le_public
#print axioms boundaryAreaCertificate_structuralPayloadBound_le_public
#print axioms
  compactBinaryNatCompletedStatusSameRowsWithSizeExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite

end FoundationCompactNumericListedDirectCompletedStatusSameRowsPublicBounds
