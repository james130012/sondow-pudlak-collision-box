import integration.FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveProductSplitPublicBounds
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
import integration.FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsPublicBounds
import integration.FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsPublicBounds
import integration.FoundationCompactNumericListedDirectNatSizePublicBounds
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resource for the numeric parser-state core

The ten checked conjuncts are bounded separately and then reassembled with
transparent conjunction costs.  No generated proof object occurs in the
resource expression.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserStateCorePublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveProductSplitPublicBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsPublicBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsPublicBounds
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizePublicBounds

private abbrev parserZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate.zeroValuation

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
    termValue parserZeroValuation ‘!!left + !!right’ =
      termValue parserZeroValuation left +
        termValue parserZeroValuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add parserZeroValuation ![left, right]

private theorem termValue_arithmeticMul
    (left right : ValuationTerm) :
    termValue parserZeroValuation ‘!!left * !!right’ =
      termValue parserZeroValuation left *
        termValue parserZeroValuation right := by
  rw [arithmeticMulTerm_eq_func]
  exact termValue_mul parserZeroValuation ![left, right]

private theorem termValue_arithmeticOne :
    termValue parserZeroValuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one parserZeroValuation ![]

def parserValuationLeStructuralPayloadPolynomial
    (leftTerm rightTerm : ValuationTerm) : Nat :=
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula := LO.FirstOrder.Semiformula.rel Language.LT.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables parserZeroValuation
  compilePositiveRelationPayloadPolynomial
      parserZeroValuation Language.Eq.eq args +
    compilePositiveRelationPayloadPolynomial
      parserZeroValuation Language.ORing.Rel.lt args +
    weakeningFullAssemblyCost (insert equalityFormula Gamma) +
    weakeningFullAssemblyCost (insert strictFormula Gamma) +
    disjunctionFullAssemblyCost Gamma equalityFormula strictFormula

theorem valuationLeCertificate_structuralPayloadBound_le_public
    (leftTerm rightTerm : ValuationTerm)
    (hleft : leftTerm.freeVariables = ∅)
    (hright : rightTerm.freeVariables = ∅)
    (hle : termValue parserZeroValuation leftTerm ≤
      termValue parserZeroValuation rightTerm) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate.valuationLeCertificate
          leftTerm rightTerm hle) ≤
      parserValuationLeStructuralPayloadPolynomial leftTerm rightTerm := by
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
      parserZeroValuation Language.Eq.eq args hfirst hsecond
  have hstrict :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      parserZeroValuation Language.ORing.Rel.lt args hfirst hsecond
  by_cases heq : termValue parserZeroValuation leftTerm =
      termValue parserZeroValuation rightTerm
  · simp only [
      FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate.valuationLeCertificate]
    rw [dif_pos heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold parserValuationLeStructuralPayloadPolynomial
    dsimp only [args] at hequality hstrict ⊢
    simp only [parserZeroValuation] at hequality hstrict ⊢
    omega
  · simp only [
      FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate.valuationLeCertificate]
    rw [dif_neg heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold parserValuationLeStructuralPayloadPolynomial
    dsimp only [args] at hequality hstrict ⊢
    simp only [parserZeroValuation] at hequality hstrict ⊢
    omega

def boundaryAreaStructuralPayloadPolynomial
    (boundarySize count tokenCount : Nat) : Nat :=
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm count) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  parserValuationLeStructuralPayloadPolynomial
    (shortBinaryNumeralTerm boundarySize) rightTerm

theorem boundaryAreaCertificate_structuralPayloadBound_le_public
    (boundarySize count tokenCount : Nat)
    (hbound : boundarySize ≤ (count + 1) * tokenCount) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate.boundaryAreaCertificate
          boundarySize count tokenCount hbound) ≤
      boundaryAreaStructuralPayloadPolynomial
        boundarySize count tokenCount := by
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm count) + 1) *
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
  have hle : termValue parserZeroValuation
      (shortBinaryNumeralTerm boundarySize) ≤
      termValue parserZeroValuation rightTerm := by
    simpa [rightTerm, termValue_shortBinaryNumeralTerm,
      termValue_arithmeticAdd, termValue_arithmeticMul,
      termValue_arithmeticOne] using hbound
  have hpublic := valuationLeCertificate_structuralPayloadBound_le_public
    (shortBinaryNumeralTerm boundarySize) rightTerm hleft hright hle
  change hybridFormulaStructuralPayloadBound
      (FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate.valuationLeCertificate
        (shortBinaryNumeralTerm boundarySize) rightTerm hle) ≤ _
  unfold boundaryAreaStructuralPayloadPolynomial
  dsimp only [rightTerm] at hpublic ⊢
  exact hpublic

noncomputable def compactUnifiedParserStateCoreGraphStructuralPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (hgraph : CompactUnifiedParserStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) : Nat := by
  rcases hgraph with
    ⟨houter, htokensLayout, htokensRows,
      hinner, htasksLayout, htasksRows,
      htokensSize, htokensArea, htasksSize, htasksArea⟩
  let outerFormula := compactAdditiveProductSplitClosedFormula
    tokenCount coordinates.start coordinates.tokensFinish coordinates.finish
  let tokensLayoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount coordinates.start coordinates.tokensCount
      coordinates.tokensFinish coordinates.tokensBoundary
  let tokensRowsFormula := compactAdditiveUnitBoundaryRowsClosedFormula
    tokenCount coordinates.tokensCount coordinates.tokensBoundary
  let innerFormula := compactAdditiveProductSplitClosedFormula
    tokenCount coordinates.tokensFinish coordinates.tasksFinish
      coordinates.finish
  let tasksLayoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount coordinates.tokensFinish
      coordinates.tasksCount coordinates.tasksFinish coordinates.tasksBoundary
  let tasksRowsFormula := compactAdditiveTripleBoundaryRowsClosedFormula
    tokenCount coordinates.tasksCount coordinates.tasksBoundary
  let tokensSizeFormula := compactNatSizeClosedFormula
    sizeWitness.tokensBoundarySize coordinates.tokensBoundary
  let tokensAreaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sizeWitness.tokensBoundarySize) ≤
      (!!(shortBinaryNumeralTerm coordinates.tokensCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let tasksSizeFormula := compactNatSizeClosedFormula
    sizeWitness.tasksBoundarySize coordinates.tasksBoundary
  let tasksAreaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sizeWitness.tasksBoundarySize) ≤
      (!!(shortBinaryNumeralTerm coordinates.tasksCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let outerResource :=
    compactAdditiveProductSplitStructuralPayloadPolynomial
      tokenCount coordinates.start coordinates.tokensFinish coordinates.finish
  let tokensLayoutResource :=
    compactAdditiveStructuredListLayoutDataStructuralPayloadEnvelope
      tokenTable width tokenCount coordinates.start coordinates.tokensCount
      coordinates.tokensFinish coordinates.tokensBoundary
      (compactAdditiveStructuredListLayoutDataOfLayout
        tokenTable width tokenCount coordinates.start coordinates.tokensCount
        coordinates.tokensFinish coordinates.tokensBoundary htokensLayout)
  let tokensRowsResource :=
    compactAdditiveUnitBoundaryRowsGraphStructuralPayloadEnvelope
      tokenCount coordinates.tokensCount coordinates.tokensBoundary
      htokensRows
  let innerResource :=
    compactAdditiveProductSplitStructuralPayloadPolynomial
      tokenCount coordinates.tokensFinish coordinates.tasksFinish
      coordinates.finish
  let tasksLayoutResource :=
    compactAdditiveStructuredListLayoutDataStructuralPayloadEnvelope
      tokenTable width tokenCount coordinates.tokensFinish
      coordinates.tasksCount coordinates.tasksFinish coordinates.tasksBoundary
      (compactAdditiveStructuredListLayoutDataOfLayout
        tokenTable width tokenCount coordinates.tokensFinish
        coordinates.tasksCount coordinates.tasksFinish
        coordinates.tasksBoundary htasksLayout)
  let tasksRowsResource :=
    compactAdditiveTripleBoundaryRowsGraphStructuralPayloadEnvelope
      tokenCount coordinates.tasksCount coordinates.tasksBoundary htasksRows
  let tokensSizeResource := compactNatSizeStructuralPayloadPolynomial
    sizeWitness.tokensBoundarySize coordinates.tokensBoundary
  let tokensAreaResource := boundaryAreaStructuralPayloadPolynomial
    sizeWitness.tokensBoundarySize coordinates.tokensCount tokenCount
  let tasksSizeResource := compactNatSizeStructuralPayloadPolynomial
    sizeWitness.tasksBoundarySize coordinates.tasksBoundary
  let tasksAreaResource := boundaryAreaStructuralPayloadPolynomial
    sizeWitness.tasksBoundarySize coordinates.tasksCount tokenCount
  let tasksSizeAreaResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate.zeroValuation
    tasksSizeFormula tasksAreaFormula
    tasksSizeResource tasksAreaResource
  let tokensAreaTailResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate.zeroValuation
    tokensAreaFormula
    (tasksSizeFormula ⋏ tasksAreaFormula)
    tokensAreaResource tasksSizeAreaResource
  let tokensSizeTailResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate.zeroValuation
    tokensSizeFormula
    (tokensAreaFormula ⋏ (tasksSizeFormula ⋏ tasksAreaFormula))
    tokensSizeResource tokensAreaTailResource
  let tasksRowsTailResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate.zeroValuation
    tasksRowsFormula
    (tokensSizeFormula ⋏
      (tokensAreaFormula ⋏ (tasksSizeFormula ⋏ tasksAreaFormula)))
    tasksRowsResource tokensSizeTailResource
  let tasksLayoutTailResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation
    tasksLayoutFormula
    (tasksRowsFormula ⋏
      (tokensSizeFormula ⋏
        (tokensAreaFormula ⋏ (tasksSizeFormula ⋏ tasksAreaFormula))))
    tasksLayoutResource tasksRowsTailResource
  let innerTailResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate.zeroValuation
    innerFormula
    (tasksLayoutFormula ⋏
      (tasksRowsFormula ⋏
        (tokensSizeFormula ⋏
          (tokensAreaFormula ⋏
            (tasksSizeFormula ⋏ tasksAreaFormula)))))
    innerResource tasksLayoutTailResource
  let tokensRowsTailResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.zeroValuation
    tokensRowsFormula
    (innerFormula ⋏
      (tasksLayoutFormula ⋏
        (tasksRowsFormula ⋏
          (tokensSizeFormula ⋏
            (tokensAreaFormula ⋏
              (tasksSizeFormula ⋏ tasksAreaFormula))))))
    tokensRowsResource innerTailResource
  let tokensLayoutTailResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation
    tokensLayoutFormula
    (tokensRowsFormula ⋏
      (innerFormula ⋏
        (tasksLayoutFormula ⋏
          (tasksRowsFormula ⋏
            (tokensSizeFormula ⋏
              (tokensAreaFormula ⋏
                (tasksSizeFormula ⋏ tasksAreaFormula)))))))
    tokensLayoutResource tokensRowsTailResource
  exact transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate.zeroValuation
    outerFormula
    (tokensLayoutFormula ⋏
      (tokensRowsFormula ⋏
        (innerFormula ⋏
          (tasksLayoutFormula ⋏
            (tasksRowsFormula ⋏
              (tokensSizeFormula ⋏
                (tokensAreaFormula ⋏
                  (tasksSizeFormula ⋏ tasksAreaFormula))))))))
    outerResource tokensLayoutTailResource

theorem
    compactUnifiedParserStateCoreExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (hgraph : CompactUnifiedParserStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserStateCoreExplicitHybridCertificateOfGraph
          tokenTable width tokenCount coordinates sizeWitness hgraph) ≤
      compactUnifiedParserStateCoreGraphStructuralPayloadEnvelope
        tokenTable width tokenCount coordinates sizeWitness hgraph := by
  rcases hgraph with
    ⟨houter, htokensLayout, htokensRows,
      hinner, htasksLayout, htasksRows,
      htokensSize, htokensArea, htasksSize, htasksArea⟩
  let outerCertificate :=
    compactAdditiveProductSplitExplicitHybridCertificateOfGraph
      tokenCount coordinates.start coordinates.tokensFinish
      coordinates.finish houter
  let tokensLayoutCertificate :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
      tokenTable width tokenCount coordinates.start coordinates.tokensCount
      coordinates.tokensFinish coordinates.tokensBoundary htokensLayout
  let tokensRowsCertificate :=
    compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph
      tokenCount coordinates.tokensCount coordinates.tokensBoundary
      htokensRows
  let innerCertificate :=
    compactAdditiveProductSplitExplicitHybridCertificateOfGraph
      tokenCount coordinates.tokensFinish coordinates.tasksFinish
      coordinates.finish hinner
  let tasksLayoutCertificate :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
      tokenTable width tokenCount coordinates.tokensFinish
      coordinates.tasksCount coordinates.tasksFinish coordinates.tasksBoundary
      htasksLayout
  let tasksRowsCertificate :=
    compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph
      tokenCount coordinates.tasksCount coordinates.tasksBoundary htasksRows
  let tokensSizeCertificate := compactNatSizeExplicitHybridCertificateOfEq
    sizeWitness.tokensBoundarySize coordinates.tokensBoundary htokensSize
  let tokensAreaCertificate :=
    FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate.boundaryAreaCertificate
      sizeWitness.tokensBoundarySize coordinates.tokensCount tokenCount
      htokensArea
  let tasksSizeCertificate := compactNatSizeExplicitHybridCertificateOfEq
    sizeWitness.tasksBoundarySize coordinates.tasksBoundary htasksSize
  let tasksAreaCertificate :=
    FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate.boundaryAreaCertificate
      sizeWitness.tasksBoundarySize coordinates.tasksCount tokenCount
      htasksArea
  have houterResource :=
    compactAdditiveProductSplitExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenCount coordinates.start coordinates.tokensFinish
      coordinates.finish houter
  have htokensLayoutResource :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout_structuralPayloadBound_le_transparent
      tokenTable width tokenCount coordinates.start coordinates.tokensCount
      coordinates.tokensFinish coordinates.tokensBoundary htokensLayout
  have htokensRowsResource :=
    compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenCount coordinates.tokensCount coordinates.tokensBoundary
      htokensRows
  have hinnerResource :=
    compactAdditiveProductSplitExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenCount coordinates.tokensFinish coordinates.tasksFinish
      coordinates.finish hinner
  have htasksLayoutResource :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout_structuralPayloadBound_le_transparent
      tokenTable width tokenCount coordinates.tokensFinish
      coordinates.tasksCount coordinates.tasksFinish coordinates.tasksBoundary
      htasksLayout
  have htasksRowsResource :=
    compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenCount coordinates.tasksCount coordinates.tasksBoundary htasksRows
  have htokensSizeResource :=
    compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
      sizeWitness.tokensBoundarySize coordinates.tokensBoundary htokensSize
  have htokensAreaResource :=
    boundaryAreaCertificate_structuralPayloadBound_le_public
      sizeWitness.tokensBoundarySize coordinates.tokensCount tokenCount
      htokensArea
  have htasksSizeResource :=
    compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
      sizeWitness.tasksBoundarySize coordinates.tasksBoundary htasksSize
  have htasksAreaResource :=
    boundaryAreaCertificate_structuralPayloadBound_le_public
      sizeWitness.tasksBoundarySize coordinates.tasksCount tokenCount
      htasksArea
  let tasksSizeArea :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      tasksSizeCertificate tasksAreaCertificate
  have htasksSizeArea := transparentHybridConjunctionPayloadBound_le
    tasksSizeCertificate tasksAreaCertificate _ _
    htasksSizeResource htasksAreaResource
  let tokensAreaTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      tokensAreaCertificate tasksSizeArea
  have htokensAreaTail := transparentHybridConjunctionPayloadBound_le
    tokensAreaCertificate tasksSizeArea _ _
    htokensAreaResource htasksSizeArea
  let tokensSizeTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      tokensSizeCertificate tokensAreaTail
  have htokensSizeTail := transparentHybridConjunctionPayloadBound_le
    tokensSizeCertificate tokensAreaTail _ _
    htokensSizeResource htokensAreaTail
  let tasksRowsTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      tasksRowsCertificate tokensSizeTail
  have htasksRowsTail := transparentHybridConjunctionPayloadBound_le
    tasksRowsCertificate tokensSizeTail _ _
    htasksRowsResource htokensSizeTail
  let tasksLayoutTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      tasksLayoutCertificate tasksRowsTail
  have htasksLayoutTail := transparentHybridConjunctionPayloadBound_le
    tasksLayoutCertificate tasksRowsTail _ _
    htasksLayoutResource htasksRowsTail
  let innerTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      innerCertificate tasksLayoutTail
  have hinnerTail := transparentHybridConjunctionPayloadBound_le
    innerCertificate tasksLayoutTail _ _ hinnerResource htasksLayoutTail
  let tokensRowsTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      tokensRowsCertificate innerTail
  have htokensRowsTail := transparentHybridConjunctionPayloadBound_le
    tokensRowsCertificate innerTail _ _
    htokensRowsResource hinnerTail
  let tokensLayoutTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      tokensLayoutCertificate tokensRowsTail
  have htokensLayoutTail := transparentHybridConjunctionPayloadBound_le
    tokensLayoutCertificate tokensRowsTail _ _
    htokensLayoutResource htokensRowsTail
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    outerCertificate tokensLayoutTail
  have hparts := transparentHybridConjunctionPayloadBound_le
    outerCertificate tokensLayoutTail _ _
    houterResource htokensLayoutTail
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactUnifiedParserStateCoreClosedFormula_alignment
          tokenTable width tokenCount
          coordinates.start coordinates.finish
          coordinates.tokensFinish coordinates.tasksFinish
          coordinates.tokensBoundary coordinates.tokensCount
          coordinates.tasksBoundary coordinates.tasksCount
          sizeWitness.tokensBoundarySize
          sizeWitness.tasksBoundarySize).symm parts) ≤ _
  unfold compactUnifiedParserStateCoreGraphStructuralPayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound,
    outerCertificate, tokensLayoutCertificate, tokensRowsCertificate,
    innerCertificate, tasksLayoutCertificate, tasksRowsCertificate,
    tokensSizeCertificate, tokensAreaCertificate,
    tasksSizeCertificate, tasksAreaCertificate,
    tasksSizeArea, tokensAreaTail, tokensSizeTail, tasksRowsTail,
    tasksLayoutTail, innerTail, tokensRowsTail, tokensLayoutTail, parts]
    using hparts

#print axioms valuationLeCertificate_structuralPayloadBound_le_public
#print axioms boundaryAreaCertificate_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserStateCoreExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectParserStateCorePublicBounds
