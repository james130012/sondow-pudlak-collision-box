import integration.FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
import integration.FoundationCompactNumericListedDirectNatSizePublicBounds
import integration.FoundationCompactNumericListedDirectParserStateCorePublicBounds
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resource for the empty parser branch

The nine checked conjuncts are charged separately: two zero counts, running
status, two equal-row tables, completed prefix, output layout, exact binary
size, and the output-area inequality.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserEmptyPublicBounds

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
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserEmptyFormula
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizePublicBounds
open FoundationCompactNumericListedDirectParserStateCorePublicBounds

private abbrev emptyZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate.zeroValuation

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

private theorem arithmeticZeroTerm_freeVariables_eq_empty :
    (‘0’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_zero,
    LO.FirstOrder.Semiterm.Operator.Zero.term_eq]

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
    termValue emptyZeroValuation ‘!!left + !!right’ =
      termValue emptyZeroValuation left +
        termValue emptyZeroValuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add emptyZeroValuation ![left, right]

private theorem termValue_arithmeticMul
    (left right : ValuationTerm) :
    termValue emptyZeroValuation ‘!!left * !!right’ =
      termValue emptyZeroValuation left *
        termValue emptyZeroValuation right := by
  rw [arithmeticMulTerm_eq_func]
  exact termValue_mul emptyZeroValuation ![left, right]

private theorem termValue_arithmeticOne :
    termValue emptyZeroValuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one emptyZeroValuation ![]

def parserEmptyClosedEqZeroPayloadPolynomial (value : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial emptyZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, (‘0’ : ValuationTerm)]

theorem closedEqZeroCertificate_structuralPayloadBound_le_public
    (value : Nat) (heq : value = 0) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate.closedEqZeroCertificate
          value heq) <=
      parserEmptyClosedEqZeroPayloadPolynomial value := by
  have hleft : (shortBinaryNumeralTerm value).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hright : (‘0’ : ValuationTerm).freeVariables ⊆ {0} := by
    rw [arithmeticZeroTerm_freeVariables_eq_empty]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    emptyZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, (‘0’ : ValuationTerm)] hleft hright
  simpa only [
    FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate.closedEqZeroCertificate,
    hybridFormulaStructuralPayloadBound,
    parserEmptyClosedEqZeroPayloadPolynomial] using hpublic

def parserEmptyValuationLePayloadPolynomial
    (leftTerm rightTerm : ValuationTerm) : Nat :=
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula := LO.FirstOrder.Semiformula.rel Language.LT.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables emptyZeroValuation
  compilePositiveRelationPayloadPolynomial
      emptyZeroValuation Language.Eq.eq args +
    compilePositiveRelationPayloadPolynomial
      emptyZeroValuation Language.ORing.Rel.lt args +
    weakeningFullAssemblyCost (insert equalityFormula Gamma) +
    weakeningFullAssemblyCost (insert strictFormula Gamma) +
    disjunctionFullAssemblyCost Gamma equalityFormula strictFormula

theorem valuationLeCertificate_structuralPayloadBound_le_public
    (leftTerm rightTerm : ValuationTerm)
    (hleft : leftTerm.freeVariables = ∅)
    (hright : rightTerm.freeVariables = ∅)
    (hle : termValue emptyZeroValuation leftTerm <=
      termValue emptyZeroValuation rightTerm) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate.valuationLeCertificate
          leftTerm rightTerm hle) <=
      parserEmptyValuationLePayloadPolynomial leftTerm rightTerm := by
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
      emptyZeroValuation Language.Eq.eq args hfirst hsecond
  have hstrict :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      emptyZeroValuation Language.ORing.Rel.lt args hfirst hsecond
  by_cases heq : termValue emptyZeroValuation leftTerm =
      termValue emptyZeroValuation rightTerm
  · simp only [
      FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate.valuationLeCertificate]
    rw [dif_pos heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold parserEmptyValuationLePayloadPolynomial
    dsimp only [args] at hequality hstrict ⊢
    simp only [emptyZeroValuation] at hequality hstrict ⊢
    omega
  · simp only [
      FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate.valuationLeCertificate]
    rw [dif_neg heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold parserEmptyValuationLePayloadPolynomial
    dsimp only [args] at hequality hstrict ⊢
    simp only [emptyZeroValuation] at hequality hstrict ⊢
    omega

def parserEmptyOutputBoundaryAreaPayloadPolynomial
    (tokenCount sourceCount outputBoundarySize : Nat) : Nat :=
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm sourceCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  parserEmptyValuationLePayloadPolynomial
    (shortBinaryNumeralTerm outputBoundarySize) rightTerm

theorem outputBoundaryAreaCertificate_structuralPayloadBound_le_public
    (tokenCount sourceCount outputBoundarySize : Nat)
    (hbound : outputBoundarySize <= (sourceCount + 1) * tokenCount) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate.outputBoundaryAreaCertificate
          tokenCount sourceCount outputBoundarySize hbound) <=
      parserEmptyOutputBoundaryAreaPayloadPolynomial tokenCount sourceCount
        outputBoundarySize := by
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm sourceCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  have hleft :
      (shortBinaryNumeralTerm outputBoundarySize).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty outputBoundarySize
  have hright : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    rw [arithmeticMulTerm_freeVariables, arithmeticAddTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticOneTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hle : termValue emptyZeroValuation
      (shortBinaryNumeralTerm outputBoundarySize) <=
      termValue emptyZeroValuation rightTerm := by
    simpa [rightTerm, termValue_shortBinaryNumeralTerm,
      termValue_arithmeticAdd, termValue_arithmeticMul,
      termValue_arithmeticOne] using hbound
  have hpublic := valuationLeCertificate_structuralPayloadBound_le_public
    (shortBinaryNumeralTerm outputBoundarySize) rightTerm hleft hright hle
  change hybridFormulaStructuralPayloadBound
      (FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate.valuationLeCertificate
        (shortBinaryNumeralTerm outputBoundarySize) rightTerm hle) <= _
  unfold parserEmptyOutputBoundaryAreaPayloadPolynomial
  dsimp only [rightTerm] at hpublic ⊢
  exact hpublic

def compactUnifiedParserEmptyPublicFinitePayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserEmptyWitnessCoordinates) : Nat := by
  let currentCountFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm current.tasksCount) = 0”
  let nextCountFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm next.tasksCount) = 0”
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount current.tasksFinish current.finish
  let tokenRowsFormula := compactAdditiveNatListSameRowsClosedFormula
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount
  let completedFormula := compactBinaryNatCompletedStatusPrefixClosedFormula
    tokenTable width tokenCount next.tasksFinish witness.targetOutputStart
  let layoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount witness.targetOutputStart current.tokensCount
    next.finish witness.targetOutputBoundary
  let outputRowsFormula := compactAdditiveNatListSameRowsClosedFormula
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
    witness.targetOutputBoundary current.tokensCount
  let sizeFormula := compactNatSizeClosedFormula
    witness.targetOutputBoundarySize witness.targetOutputBoundary
  let areaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm witness.targetOutputBoundarySize) ≤
      (!!(shortBinaryNumeralTerm current.tokensCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let currentCountResource := parserEmptyClosedEqZeroPayloadPolynomial
    current.tasksCount
  let nextCountResource := parserEmptyClosedEqZeroPayloadPolynomial
    next.tasksCount
  let runningResource :=
    compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial tokenTable
      width tokenCount current.tasksFinish current.finish
  let tokenRowsResource := compactAdditiveNatListSameRowsPublicFinitePayloadEnvelope
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount
  let completedResource :=
    compactBinaryNatCompletedStatusPrefixStructuralPayloadPolynomial tokenTable
      width tokenCount next.tasksFinish witness.targetOutputStart
  let layoutResource :=
    compactAdditiveStructuredListLayoutPublicFiniteStructuralPayloadEnvelope tokenTable
      width tokenCount witness.targetOutputStart current.tokensCount
      next.finish witness.targetOutputBoundary
  let outputRowsResource := compactAdditiveNatListSameRowsPublicFinitePayloadEnvelope
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
    witness.targetOutputBoundary current.tokensCount
  let sizeResource := compactNatSizeStructuralPayloadPolynomial
    witness.targetOutputBoundarySize witness.targetOutputBoundary
  let areaResource := parserEmptyOutputBoundaryAreaPayloadPolynomial tokenCount
    current.tokensCount witness.targetOutputBoundarySize
  let sizeAreaResource := transparentHybridConjunctionPayloadEnvelope
    emptyZeroValuation sizeFormula areaFormula sizeResource areaResource
  let outputRowsTailResource := transparentHybridConjunctionPayloadEnvelope
    emptyZeroValuation outputRowsFormula (sizeFormula ⋏ areaFormula)
    outputRowsResource sizeAreaResource
  let layoutTailResource := transparentHybridConjunctionPayloadEnvelope
    emptyZeroValuation layoutFormula
    (outputRowsFormula ⋏ (sizeFormula ⋏ areaFormula))
    layoutResource outputRowsTailResource
  let completedTailResource := transparentHybridConjunctionPayloadEnvelope
    emptyZeroValuation
    completedFormula
      (layoutFormula ⋏ (outputRowsFormula ⋏ (sizeFormula ⋏ areaFormula)))
    completedResource layoutTailResource
  let tokenRowsTailResource := transparentHybridConjunctionPayloadEnvelope
    emptyZeroValuation tokenRowsFormula
      (completedFormula ⋏
        (layoutFormula ⋏ (outputRowsFormula ⋏ (sizeFormula ⋏ areaFormula))))
    tokenRowsResource completedTailResource
  let runningTailResource := transparentHybridConjunctionPayloadEnvelope
    emptyZeroValuation
    runningFormula
      (tokenRowsFormula ⋏
        (completedFormula ⋏
          (layoutFormula ⋏
            (outputRowsFormula ⋏ (sizeFormula ⋏ areaFormula)))))
    runningResource tokenRowsTailResource
  let nextCountTailResource := transparentHybridConjunctionPayloadEnvelope
    emptyZeroValuation nextCountFormula
      (runningFormula ⋏
        (tokenRowsFormula ⋏
          (completedFormula ⋏
            (layoutFormula ⋏
              (outputRowsFormula ⋏ (sizeFormula ⋏ areaFormula))))))
    nextCountResource runningTailResource
  exact transparentHybridConjunctionPayloadEnvelope emptyZeroValuation
    currentCountFormula
    (nextCountFormula ⋏
      (runningFormula ⋏
        (tokenRowsFormula ⋏
          (completedFormula ⋏
            (layoutFormula ⋏
              (outputRowsFormula ⋏ (sizeFormula ⋏ areaFormula)))))))
    currentCountResource nextCountTailResource

theorem
    compactUnifiedParserEmptyExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserEmptyWitnessCoordinates)
    (hgraph : CompactUnifiedParserEmptyGraphRows tokenTable width tokenCount
      current next witness) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserEmptyExplicitHybridCertificateOfGraph tokenTable
          width tokenCount current next witness hgraph) <=
      compactUnifiedParserEmptyPublicFinitePayloadEnvelope tokenTable width
        tokenCount current next witness := by
  rcases hgraph with
    ⟨hcurrentCount, hnextCount, hrunning, htokenRows, hcompleted⟩
  rcases hcompleted with
    ⟨⟨hprefix, hlayout, houtputRows⟩, hsize, harea⟩
  let currentCountCertificate :
      CheckedHybridValuationBoundedFormulaCertificate emptyZeroValuation
        “!!(shortBinaryNumeralTerm current.tasksCount) = 0” :=
    FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate.closedEqZeroCertificate
      current.tasksCount hcurrentCount
  let nextCountCertificate :
      CheckedHybridValuationBoundedFormulaCertificate emptyZeroValuation
        “!!(shortBinaryNumeralTerm next.tasksCount) = 0” :=
    FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate.closedEqZeroCertificate
      next.tasksCount hnextCount
  let runningCertificate :
      CheckedHybridValuationBoundedFormulaCertificate emptyZeroValuation
        (compactBinaryNatRunningStatusSliceClosedFormula tokenTable width
          tokenCount current.tasksFinish current.finish) :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tasksFinish current.finish hrunning
  let tokenRowsCertificate :
      CheckedHybridValuationBoundedFormulaCertificate emptyZeroValuation
        (compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
          current.tokensBoundary current.tokensCount next.tokensBoundary
          next.tokensCount) :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount htokenRows
  let completedCertificate :
      CheckedHybridValuationBoundedFormulaCertificate emptyZeroValuation
        (compactBinaryNatCompletedStatusPrefixClosedFormula tokenTable width
          tokenCount next.tasksFinish witness.targetOutputStart) :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksFinish witness.targetOutputStart
      hprefix
  let layoutCertificate :
      CheckedHybridValuationBoundedFormulaCertificate emptyZeroValuation
        (compactAdditiveStructuredListLayoutClosedFormula tokenTable width
          tokenCount witness.targetOutputStart current.tokensCount next.finish
          witness.targetOutputBoundary) :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
      tokenTable width tokenCount witness.targetOutputStart
      current.tokensCount next.finish witness.targetOutputBoundary hlayout
  let outputRowsCertificate :
      CheckedHybridValuationBoundedFormulaCertificate emptyZeroValuation
        (compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
          current.tokensBoundary current.tokensCount
          witness.targetOutputBoundary current.tokensCount) :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.tokensBoundary current.tokensCount
      witness.targetOutputBoundary current.tokensCount houtputRows
  let sizeCertificate :
      CheckedHybridValuationBoundedFormulaCertificate emptyZeroValuation
        (compactNatSizeClosedFormula witness.targetOutputBoundarySize
          witness.targetOutputBoundary) :=
    compactNatSizeExplicitHybridCertificateOfEq
      witness.targetOutputBoundarySize witness.targetOutputBoundary hsize
  let areaCertificate :
      CheckedHybridValuationBoundedFormulaCertificate emptyZeroValuation
        “!!(shortBinaryNumeralTerm witness.targetOutputBoundarySize) ≤
          (!!(shortBinaryNumeralTerm current.tokensCount) + 1) *
            !!(shortBinaryNumeralTerm tokenCount)” :=
    FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate.outputBoundaryAreaCertificate
      tokenCount current.tokensCount witness.targetOutputBoundarySize harea
  have hcurrentCountResource :=
    closedEqZeroCertificate_structuralPayloadBound_le_public
      current.tasksCount hcurrentCount
  have hnextCountResource :=
    closedEqZeroCertificate_structuralPayloadBound_le_public
      next.tasksCount hnextCount
  have hrunningResource :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount current.tasksFinish current.finish hrunning
  have htokenRowsResource :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount htokenRows
  have hcompletedResource :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount next.tasksFinish witness.targetOutputStart
      hprefix
  have hlayoutResource :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout_structuralPayloadBound_le_publicFinite
      tokenTable width tokenCount witness.targetOutputStart
      current.tokensCount next.finish witness.targetOutputBoundary hlayout
  have houtputRowsResource :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      witness.targetOutputBoundary current.tokensCount houtputRows
  have hsizeResource :=
    compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
      witness.targetOutputBoundarySize witness.targetOutputBoundary hsize
  have hareaResource :=
    outputBoundaryAreaCertificate_structuralPayloadBound_le_public tokenCount
      current.tokensCount witness.targetOutputBoundarySize harea
  let sizeArea := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    sizeCertificate areaCertificate
  have hsizeArea := transparentHybridConjunctionPayloadBound_le
    sizeCertificate areaCertificate _ _ hsizeResource hareaResource
  let outputRowsTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      outputRowsCertificate sizeArea
  have houtputRowsTail := transparentHybridConjunctionPayloadBound_le
    outputRowsCertificate sizeArea _ _ houtputRowsResource hsizeArea
  let layoutTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    layoutCertificate outputRowsTail
  have hlayoutTail := transparentHybridConjunctionPayloadBound_le
    layoutCertificate outputRowsTail _ _ hlayoutResource houtputRowsTail
  let completedTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      completedCertificate layoutTail
  have hcompletedTail := transparentHybridConjunctionPayloadBound_le
    completedCertificate layoutTail _ _ hcompletedResource hlayoutTail
  let tokenRowsTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      tokenRowsCertificate completedTail
  have htokenRowsTail := transparentHybridConjunctionPayloadBound_le
    tokenRowsCertificate completedTail _ _ htokenRowsResource hcompletedTail
  let runningTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    runningCertificate tokenRowsTail
  have hrunningTail := transparentHybridConjunctionPayloadBound_le
    runningCertificate tokenRowsTail _ _ hrunningResource htokenRowsTail
  let nextCountTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      nextCountCertificate runningTail
  have hnextCountTail := transparentHybridConjunctionPayloadBound_le
    nextCountCertificate runningTail _ _ hnextCountResource hrunningTail
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    currentCountCertificate nextCountTail
  have hparts := transparentHybridConjunctionPayloadBound_le
    currentCountCertificate nextCountTail _ _
    hcurrentCountResource hnextCountTail
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactUnifiedParserEmptyClosedFormula_alignment tokenTable width
          tokenCount current next witness).symm parts) <= _
  unfold compactUnifiedParserEmptyPublicFinitePayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound,
    currentCountCertificate, nextCountCertificate, runningCertificate,
    tokenRowsCertificate, completedCertificate, layoutCertificate,
    outputRowsCertificate, sizeCertificate, areaCertificate, sizeArea,
    outputRowsTail, layoutTail, completedTail, tokenRowsTail, runningTail,
    nextCountTail, parts] using hparts

#print axioms closedEqZeroCertificate_structuralPayloadBound_le_public
#print axioms outputBoundaryAreaCertificate_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserEmptyExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite

end FoundationCompactNumericListedDirectParserEmptyPublicBounds
