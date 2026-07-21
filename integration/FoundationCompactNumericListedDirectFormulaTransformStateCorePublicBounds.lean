import integration.FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserStateCorePublicBounds
import integration.FoundationCompactNumericListedDirectAdditiveProductSplitPublicBounds
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
import integration.FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsPublicBounds
import integration.FoundationCompactNumericListedDirectNatSizePublicBounds
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resource for formula-transform state cores

The six state-core conjuncts are bounded independently and reassembled with
explicit conjunction costs.  The resource contains no generated proof object.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformStateCorePublicBounds

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
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCorePublicBounds
open FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveProductSplitPublicBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsPublicBounds
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizePublicBounds

private abbrev stateZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate.zeroValuation

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
    termValue stateZeroValuation ‘!!left + !!right’ =
      termValue stateZeroValuation left +
        termValue stateZeroValuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add stateZeroValuation ![left, right]

private theorem termValue_arithmeticMul
    (left right : ValuationTerm) :
    termValue stateZeroValuation ‘!!left * !!right’ =
      termValue stateZeroValuation left *
        termValue stateZeroValuation right := by
  rw [arithmeticMulTerm_eq_func]
  exact termValue_mul stateZeroValuation ![left, right]

private theorem termValue_arithmeticOne :
    termValue stateZeroValuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one stateZeroValuation ![]

def stateValuationLeStructuralPayloadPolynomial
    (leftTerm rightTerm : ValuationTerm) : Nat :=
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula := LO.FirstOrder.Semiformula.rel Language.LT.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables stateZeroValuation
  compilePositiveRelationPayloadPolynomial stateZeroValuation
      Language.Eq.eq args +
    compilePositiveRelationPayloadPolynomial stateZeroValuation
      Language.ORing.Rel.lt args +
    weakeningFullAssemblyCost (insert equalityFormula Gamma) +
    weakeningFullAssemblyCost (insert strictFormula Gamma) +
    disjunctionFullAssemblyCost Gamma equalityFormula strictFormula

theorem valuationLeCertificate_structuralPayloadBound_le_public
    (leftTerm rightTerm : ValuationTerm)
    (hleft : leftTerm.freeVariables = ∅)
    (hright : rightTerm.freeVariables = ∅)
    (hle : termValue stateZeroValuation leftTerm ≤
      termValue stateZeroValuation rightTerm) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate.valuationLeCertificate
          leftTerm rightTerm hle) ≤
      stateValuationLeStructuralPayloadPolynomial leftTerm rightTerm := by
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
      stateZeroValuation Language.Eq.eq args hfirst hsecond
  have hstrict :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      stateZeroValuation Language.ORing.Rel.lt args hfirst hsecond
  by_cases heq : termValue stateZeroValuation leftTerm =
      termValue stateZeroValuation rightTerm
  · simp only [
      FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate.valuationLeCertificate]
    rw [dif_pos heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold stateValuationLeStructuralPayloadPolynomial
    dsimp only [args] at hequality hstrict ⊢
    simp only [stateZeroValuation] at hequality hstrict ⊢
    omega
  · simp only [
      FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate.valuationLeCertificate]
    rw [dif_neg heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold stateValuationLeStructuralPayloadPolynomial
    dsimp only [args] at hequality hstrict ⊢
    simp only [stateZeroValuation] at hequality hstrict ⊢
    omega

def outputBoundaryAreaStructuralPayloadPolynomial
    (tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) : Nat :=
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm coordinates.outputCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  stateValuationLeStructuralPayloadPolynomial
    (shortBinaryNumeralTerm sizeWitness.outputBoundarySize) rightTerm

theorem outputBoundaryAreaCertificate_structuralPayloadBound_le_public
    (tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hbound : sizeWitness.outputBoundarySize ≤
      (coordinates.outputCount + 1) * tokenCount) :
    hybridFormulaStructuralPayloadBound
        (outputBoundaryAreaCertificate tokenCount coordinates sizeWitness
          hbound) ≤
      outputBoundaryAreaStructuralPayloadPolynomial
        tokenCount coordinates sizeWitness := by
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm coordinates.outputCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  have hleft :
      (shortBinaryNumeralTerm sizeWitness.outputBoundarySize).freeVariables =
        ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty
      sizeWitness.outputBoundarySize
  have hright : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    rw [arithmeticMulTerm_freeVariables, arithmeticAddTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticOneTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hle : termValue stateZeroValuation
      (shortBinaryNumeralTerm sizeWitness.outputBoundarySize) ≤
      termValue stateZeroValuation rightTerm := by
    simpa [rightTerm, termValue_shortBinaryNumeralTerm,
      termValue_arithmeticAdd, termValue_arithmeticMul,
      termValue_arithmeticOne] using hbound
  have hpublic := valuationLeCertificate_structuralPayloadBound_le_public
    (shortBinaryNumeralTerm sizeWitness.outputBoundarySize)
    rightTerm hleft hright hle
  change hybridFormulaStructuralPayloadBound
      (FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate.valuationLeCertificate
        (shortBinaryNumeralTerm sizeWitness.outputBoundarySize)
        rightTerm hle) ≤ _
  unfold outputBoundaryAreaStructuralPayloadPolynomial
  dsimp only [rightTerm] at hpublic ⊢
  exact hpublic

noncomputable def
    compactFormulaTransformStateCorePublicFiniteStructuralPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) : Nat :=
  let outerFormula := compactAdditiveProductSplitClosedFormula
    tokenCount coordinates.start coordinates.parserFinish coordinates.finish
  let parserFormula := compactUnifiedParserStateCoreClosedFormula
    tokenTable width tokenCount
    coordinates.parser.start coordinates.parser.finish
    coordinates.parser.tokensFinish coordinates.parser.tasksFinish
    coordinates.parser.tokensBoundary coordinates.parser.tokensCount
    coordinates.parser.tasksBoundary coordinates.parser.tasksCount
    sizeWitness.parser.tokensBoundarySize sizeWitness.parser.tasksBoundarySize
  let outputLayoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount coordinates.parserFinish
    coordinates.outputCount coordinates.finish coordinates.outputBoundary
  let outputRowsFormula := compactAdditiveUnitBoundaryRowsClosedFormula
    tokenCount coordinates.outputCount coordinates.outputBoundary
  let outputSizeFormula := compactNatSizeClosedFormula
    sizeWitness.outputBoundarySize coordinates.outputBoundary
  let outputAreaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sizeWitness.outputBoundarySize) ≤
      (!!(shortBinaryNumeralTerm coordinates.outputCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let outerResource :=
    compactAdditiveProductSplitStructuralPayloadPolynomial
      tokenCount coordinates.start coordinates.parserFinish coordinates.finish
  let parserResource :=
    compactUnifiedParserStateCorePublicFiniteStructuralPayloadEnvelope
      tokenTable width tokenCount coordinates.parser sizeWitness.parser
  let outputLayoutResource :=
    compactAdditiveStructuredListLayoutPublicFiniteStructuralPayloadEnvelope
      tokenTable width tokenCount coordinates.parserFinish
      coordinates.outputCount coordinates.finish coordinates.outputBoundary
  let outputRowsResource :=
    compactAdditiveUnitBoundaryRowsPublicFiniteStructuralPayloadEnvelope
      tokenCount coordinates.outputCount coordinates.outputBoundary
  let outputSizeResource := compactNatSizeStructuralPayloadPolynomial
    sizeWitness.outputBoundarySize coordinates.outputBoundary
  let outputAreaResource := outputBoundaryAreaStructuralPayloadPolynomial
    tokenCount coordinates sizeWitness
  let outputSizeAreaResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate.zeroValuation
    outputSizeFormula outputAreaFormula outputSizeResource outputAreaResource
  let outputRowsTailResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.zeroValuation
    outputRowsFormula (outputSizeFormula ⋏ outputAreaFormula)
    outputRowsResource outputSizeAreaResource
  let outputLayoutTailResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation
    outputLayoutFormula
    (outputRowsFormula ⋏ (outputSizeFormula ⋏ outputAreaFormula))
    outputLayoutResource outputRowsTailResource
  let parserTailResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate.zeroValuation
    parserFormula
    (outputLayoutFormula ⋏
      (outputRowsFormula ⋏ (outputSizeFormula ⋏ outputAreaFormula)))
    parserResource outputLayoutTailResource
  transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate.zeroValuation
    outerFormula
    (parserFormula ⋏
      (outputLayoutFormula ⋏
        (outputRowsFormula ⋏ (outputSizeFormula ⋏ outputAreaFormula))))
    outerResource parserTailResource

theorem
    compactFormulaTransformStateCoreExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hgraph : CompactFormulaTransformStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformStateCoreExplicitHybridCertificateOfGraph
          tokenTable width tokenCount coordinates sizeWitness hgraph) ≤
      compactFormulaTransformStateCorePublicFiniteStructuralPayloadEnvelope
        tokenTable width tokenCount coordinates sizeWitness := by
  rcases hgraph with
    ⟨houter, hparser, houtputLayout, houtputRows,
      houtputSize, houtputArea⟩
  let outerCertificate :=
    compactAdditiveProductSplitExplicitHybridCertificateOfGraph
      tokenCount coordinates.start coordinates.parserFinish
      coordinates.finish houter
  let parserCertificate :=
    compactUnifiedParserStateCoreExplicitHybridCertificateOfGraph
      tokenTable width tokenCount coordinates.parser sizeWitness.parser
      hparser
  let outputLayoutCertificate :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
      tokenTable width tokenCount coordinates.parserFinish
      coordinates.outputCount coordinates.finish coordinates.outputBoundary
      houtputLayout
  let outputRowsCertificate :=
    compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph
      tokenCount coordinates.outputCount coordinates.outputBoundary
      houtputRows
  let outputSizeCertificate := compactNatSizeExplicitHybridCertificateOfEq
    sizeWitness.outputBoundarySize coordinates.outputBoundary houtputSize
  let outputAreaCertificate :=
    FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate.outputBoundaryAreaCertificate
      tokenCount coordinates sizeWitness houtputArea
  have houterResource :=
    compactAdditiveProductSplitExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenCount coordinates.start coordinates.parserFinish
      coordinates.finish houter
  have hparserResource :=
    compactUnifiedParserStateCoreExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount coordinates.parser sizeWitness.parser hparser
  have houtputLayoutResource :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout_structuralPayloadBound_le_publicFinite
      tokenTable width tokenCount coordinates.parserFinish
      coordinates.outputCount coordinates.finish coordinates.outputBoundary
      houtputLayout
  have houtputRowsTransparent :=
    compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenCount coordinates.outputCount coordinates.outputBoundary
      houtputRows
  have houtputRowsPublic :=
    compactAdditiveUnitBoundaryRowsGraphStructuralPayloadEnvelope_le_publicFinite
      tokenCount coordinates.outputCount coordinates.outputBoundary houtputRows
  have houtputRowsResource := houtputRowsTransparent.trans houtputRowsPublic
  have houtputSizeResource :=
    compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
      sizeWitness.outputBoundarySize coordinates.outputBoundary houtputSize
  have houtputAreaResource :=
    outputBoundaryAreaCertificate_structuralPayloadBound_le_public
      tokenCount coordinates sizeWitness houtputArea
  let outputSizeArea :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      outputSizeCertificate outputAreaCertificate
  have houtputSizeArea := transparentHybridConjunctionPayloadBound_le
    outputSizeCertificate outputAreaCertificate _ _
    houtputSizeResource houtputAreaResource
  let outputRowsTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      outputRowsCertificate outputSizeArea
  have houtputRowsTail := transparentHybridConjunctionPayloadBound_le
    outputRowsCertificate outputSizeArea _ _
    houtputRowsResource houtputSizeArea
  let outputLayoutTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      outputLayoutCertificate outputRowsTail
  have houtputLayoutTail := transparentHybridConjunctionPayloadBound_le
    outputLayoutCertificate outputRowsTail _ _
    houtputLayoutResource houtputRowsTail
  let parserTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      parserCertificate outputLayoutTail
  have hparserTail := transparentHybridConjunctionPayloadBound_le
    parserCertificate outputLayoutTail _ _
    hparserResource houtputLayoutTail
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    outerCertificate parserTail
  have hparts := transparentHybridConjunctionPayloadBound_le
    outerCertificate parserTail _ _ houterResource hparserTail
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactFormulaTransformStateCoreClosedFormula_alignment
          tokenTable width tokenCount coordinates sizeWitness).symm parts) ≤ _
  unfold compactFormulaTransformStateCorePublicFiniteStructuralPayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound,
    outerCertificate, parserCertificate, outputLayoutCertificate,
    outputRowsCertificate, outputSizeCertificate, outputAreaCertificate,
    outputSizeArea, outputRowsTail, outputLayoutTail, parserTail, parts]
    using hparts

#print axioms valuationLeCertificate_structuralPayloadBound_le_public
#print axioms outputBoundaryAreaCertificate_structuralPayloadBound_le_public
#print axioms
  compactFormulaTransformStateCoreExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectFormulaTransformStateCorePublicBounds
