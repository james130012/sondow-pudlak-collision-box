import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAtomicRowEqualityPublicBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutPublicBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds

/-!
# Public structural resources for cons syntax-task-list rows

The new head row and every shifted tail row expose their fixed-width entries.
The head layout, tail row equalities, bounded witnesses, and outer universal
are charged by proof-free transparent envelopes.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds

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
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectAtomicRowEqualityExplicitHybridCertificate
open FoundationCompactNumericListedDirectAtomicRowEqualityPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayoutPublicBounds

private abbrev sameRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.zeroValuation

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

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

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem arithmeticTwoTerm_freeVariables_eq_empty :
    (‘2’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem termValue_arithmeticTwo (valuation : Nat -> Nat) :
    termValue valuation (‘2’ : ValuationTerm) = 2 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

private theorem unaryNumeralTerm_freeVariables_eq_empty (value : Nat) :
    (unaryNumeralTerm value).freeVariables = ∅ := by
  unfold unaryNumeralTerm Semiterm.Operator.operator
  simp

def compactAdditiveSyntaxTaskListConsRowsCountEqualityPayloadPolynomial
    (sourceCount targetCount : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial sameRowsZeroValuation
    Language.Eq.eq
    ![shortBinaryNumeralTerm targetCount,
      ‘!!(shortBinaryNumeralTerm sourceCount) + 1’]

theorem consCountEqualityCertificate_structuralPayloadBound_le_public
    (sourceCount targetCount : Nat)
    (hcount : targetCount = sourceCount + 1) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.countEqualityCertificate
          sourceCount targetCount hcount) <=
      compactAdditiveSyntaxTaskListConsRowsCountEqualityPayloadPolynomial
        sourceCount targetCount := by
  have hfirst :
      (shortBinaryNumeralTerm targetCount).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hsecond :
      (‘!!(shortBinaryNumeralTerm sourceCount) + 1’ : ValuationTerm).freeVariables ⊆ {0} := by
    rw [arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticOneTerm_freeVariables_eq_empty]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    sameRowsZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm targetCount,
      ‘!!(shortBinaryNumeralTerm sourceCount) + 1’]
    hfirst hsecond
  simpa only [
    FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.countEqualityCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveSyntaxTaskListConsRowsCountEqualityPayloadPolynomial] using hpublic

def compactAdditiveSyntaxTaskRowEqStructuralPayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount sourceLeft sourceRight targetLeft
      targetRight : Nat) : Nat :=
  let tokenTableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let tokenCountTerm := shortBinaryNumeralTerm tokenCount
  let sourceLeftTerm := shortBinaryNumeralTerm sourceLeft
  let sourceRightTerm := shortBinaryNumeralTerm sourceRight
  let targetLeftTerm := shortBinaryNumeralTerm targetLeft
  let targetRightTerm := shortBinaryNumeralTerm targetRight
  let sourceSuccTerm : ValuationTerm := ‘!!sourceLeftTerm + 1’
  let sourceSuccSuccTerm : ValuationTerm := ‘!!sourceLeftTerm + 2’
  let targetSuccTerm : ValuationTerm := ‘!!targetLeftTerm + 1’
  let targetSuccSuccTerm : ValuationTerm := ‘!!targetLeftTerm + 2’
  let firstFormula := compactAdditiveAtomicRowEqAtValuationFormula
    tokenTableTerm widthTerm tokenCountTerm sourceLeftTerm sourceSuccTerm
    targetLeftTerm targetSuccTerm
  let secondFormula := compactAdditiveAtomicRowEqAtValuationFormula
    tokenTableTerm widthTerm tokenCountTerm sourceSuccTerm sourceSuccSuccTerm
    targetSuccTerm targetSuccSuccTerm
  let thirdFormula := compactAdditiveAtomicRowEqAtValuationFormula
    tokenTableTerm widthTerm tokenCountTerm sourceSuccSuccTerm sourceRightTerm
    targetSuccSuccTerm targetRightTerm
  let firstResource :=
    compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
      tokenTableTerm widthTerm tokenCountTerm sourceLeftTerm sourceSuccTerm
      targetLeftTerm targetSuccTerm
  let secondResource :=
    compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
      tokenTableTerm widthTerm tokenCountTerm sourceSuccTerm sourceSuccSuccTerm
      targetSuccTerm targetSuccSuccTerm
  let thirdResource :=
    compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
      tokenTableTerm widthTerm tokenCountTerm sourceSuccSuccTerm sourceRightTerm
      targetSuccSuccTerm targetRightTerm
  let secondThirdResource := transparentHybridConjunctionPayloadEnvelope
    valuation secondFormula thirdFormula secondResource thirdResource
  transparentHybridConjunctionPayloadEnvelope valuation firstFormula
    (secondFormula ⋏ thirdFormula) firstResource secondThirdResource

theorem
    compactAdditiveSyntaxTaskRowEqExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount sourceLeft sourceRight targetLeft
      targetRight : Nat)
    (hrow : CompactAdditiveSyntaxTaskRowEq tokenTable width tokenCount
      sourceLeft sourceRight targetLeft targetRight) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskRowEqExplicitHybridCertificateOfGraph
          valuation tokenTable width tokenCount sourceLeft sourceRight
          targetLeft targetRight hrow) <=
      compactAdditiveSyntaxTaskRowEqStructuralPayloadEnvelope valuation
        tokenTable width tokenCount sourceLeft sourceRight targetLeft
        targetRight := by
  let tokenTableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let tokenCountTerm := shortBinaryNumeralTerm tokenCount
  let sourceLeftTerm := shortBinaryNumeralTerm sourceLeft
  let sourceRightTerm := shortBinaryNumeralTerm sourceRight
  let targetLeftTerm := shortBinaryNumeralTerm targetLeft
  let targetRightTerm := shortBinaryNumeralTerm targetRight
  let sourceSuccTerm : ValuationTerm := ‘!!sourceLeftTerm + 1’
  let sourceSuccSuccTerm : ValuationTerm := ‘!!sourceLeftTerm + 2’
  let targetSuccTerm : ValuationTerm := ‘!!targetLeftTerm + 1’
  let targetSuccSuccTerm : ValuationTerm := ‘!!targetLeftTerm + 2’
  have hfirst : CompactAdditiveAtomicRowEq
      (termValue valuation tokenTableTerm) (termValue valuation widthTerm)
      (termValue valuation tokenCountTerm) (termValue valuation sourceLeftTerm)
      (termValue valuation sourceSuccTerm) (termValue valuation targetLeftTerm)
      (termValue valuation targetSuccTerm) := by
    simpa [tokenTableTerm, widthTerm, tokenCountTerm, sourceLeftTerm,
      targetLeftTerm, sourceSuccTerm, targetSuccTerm,
      termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne] using hrow.1
  have hsecond : CompactAdditiveAtomicRowEq
      (termValue valuation tokenTableTerm) (termValue valuation widthTerm)
      (termValue valuation tokenCountTerm) (termValue valuation sourceSuccTerm)
      (termValue valuation sourceSuccSuccTerm)
      (termValue valuation targetSuccTerm)
      (termValue valuation targetSuccSuccTerm) := by
    simpa [tokenTableTerm, widthTerm, tokenCountTerm, sourceLeftTerm,
      targetLeftTerm, sourceSuccTerm, sourceSuccSuccTerm, targetSuccTerm,
      targetSuccSuccTerm, termValue_shortBinaryNumeralTerm,
      termValue_arithmeticAdd, termValue_arithmeticOne,
      termValue_arithmeticTwo] using hrow.2.1
  have hthird : CompactAdditiveAtomicRowEq
      (termValue valuation tokenTableTerm) (termValue valuation widthTerm)
      (termValue valuation tokenCountTerm)
      (termValue valuation sourceSuccSuccTerm)
      (termValue valuation sourceRightTerm)
      (termValue valuation targetSuccSuccTerm)
      (termValue valuation targetRightTerm) := by
    simpa [tokenTableTerm, widthTerm, tokenCountTerm, sourceLeftTerm,
      sourceRightTerm, targetLeftTerm, targetRightTerm, sourceSuccSuccTerm,
      targetSuccSuccTerm, termValue_shortBinaryNumeralTerm,
      termValue_arithmeticAdd, termValue_arithmeticTwo] using hrow.2.2
  let firstCertificate :=
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate valuation
      tokenTableTerm widthTerm tokenCountTerm sourceLeftTerm sourceSuccTerm
      targetLeftTerm targetSuccTerm hfirst
  let secondCertificate :=
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate valuation
      tokenTableTerm widthTerm tokenCountTerm sourceSuccTerm sourceSuccSuccTerm
      targetSuccTerm targetSuccSuccTerm hsecond
  let thirdCertificate :=
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate valuation
      tokenTableTerm widthTerm tokenCountTerm sourceSuccSuccTerm sourceRightTerm
      targetSuccSuccTerm targetRightTerm hthird
  have htokenTable : tokenTableTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  have hwidth : widthTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty width
  have hsourceLeft : sourceLeftTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty sourceLeft
  have htargetLeft : targetLeftTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty targetLeft
  have hsourceSucc : sourceSuccTerm.freeVariables = ∅ := by
    dsimp only [sourceSuccTerm]
    rw [arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticOneTerm_freeVariables_eq_empty]
    simp
  have htargetSucc : targetSuccTerm.freeVariables = ∅ := by
    dsimp only [targetSuccTerm]
    rw [arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticOneTerm_freeVariables_eq_empty]
    simp
  have hsourceSuccSucc : sourceSuccSuccTerm.freeVariables = ∅ := by
    dsimp only [sourceSuccSuccTerm]
    rw [arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticTwoTerm_freeVariables_eq_empty]
    simp
  have htargetSuccSucc : targetSuccSuccTerm.freeVariables = ∅ := by
    dsimp only [targetSuccSuccTerm]
    rw [arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticTwoTerm_freeVariables_eq_empty]
    simp
  have hfirstResource :=
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_of_closed
      valuation tokenTableTerm widthTerm tokenCountTerm sourceLeftTerm
      sourceSuccTerm targetLeftTerm targetSuccTerm htokenTable hwidth
      hsourceLeft htargetLeft hfirst
  have hsecondResource :=
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_of_closed
      valuation tokenTableTerm widthTerm tokenCountTerm sourceSuccTerm
      sourceSuccSuccTerm targetSuccTerm targetSuccSuccTerm htokenTable hwidth
      hsourceSucc htargetSucc hsecond
  have hthirdResource :=
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_of_closed
      valuation tokenTableTerm widthTerm tokenCountTerm sourceSuccSuccTerm
      sourceRightTerm targetSuccSuccTerm targetRightTerm htokenTable hwidth
      hsourceSuccSucc htargetSuccSucc hthird
  let secondThird :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      secondCertificate thirdCertificate
  have hsecondThird := transparentHybridConjunctionPayloadBound_le
    secondCertificate thirdCertificate _ _ hsecondResource hthirdResource
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    firstCertificate secondThird
  have hparts := transparentHybridConjunctionPayloadBound_le
    firstCertificate secondThird _ _ hfirstResource hsecondThird
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactAdditiveSyntaxTaskRowEqClosedFormula_alignment tokenTable width
          tokenCount sourceLeft sourceRight targetLeft targetRight).symm
        parts) <= _
  unfold compactAdditiveSyntaxTaskRowEqStructuralPayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound, tokenTableTerm, widthTerm,
    tokenCountTerm, sourceLeftTerm, sourceRightTerm, targetLeftTerm,
    targetRightTerm, sourceSuccTerm, sourceSuccSuccTerm, targetSuccTerm,
    targetSuccSuccTerm, firstCertificate, secondCertificate,
    thirdCertificate, secondThird, parts] using hparts

noncomputable def
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadPayloadEnvelope
    (tokenTable width tokenCount targetBoundary
      headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm)
    (data : CompactAdditiveSyntaxTaskListConsHeadData tokenTable width tokenCount
      targetBoundary headKind headBinderArity headRepeatCount) : Nat :=
  let valuation := sameRowsZeroValuation
  let boundaryTerm := shortBinaryNumeralTerm targetBoundary
  let countTerm := shortBinaryNumeralTerm tokenCount
  let zeroTerm := unaryNumeralTerm 0
  let oneTerm := unaryNumeralTerm 1
  let leftTerm := shortBinaryNumeralTerm data.targetLeft
  let rightTerm := shortBinaryNumeralTerm data.targetRight
  let leftFormula := compactFixedWidthEntryAtValuationFormula boundaryTerm
    countTerm zeroTerm leftTerm
  let rightFormula := compactFixedWidthEntryAtValuationFormula boundaryTerm
    countTerm oneTerm rightTerm
  let layoutFormula := compactSyntaxTaskDirectLayoutAtValuationTermsFormula
    tokenTable width tokenCount data.targetLeft data.targetRight headKindTerm
    headBinderArityTerm headRepeatCountTerm
  let leftResource :=
    compactFixedWidthEntryAtValuationStructuralPayloadPolynomial valuation
      boundaryTerm countTerm zeroTerm leftTerm
  let rightResource :=
    compactFixedWidthEntryAtValuationStructuralPayloadPolynomial valuation
      boundaryTerm countTerm oneTerm rightTerm
  let layoutResource :=
    compactSyntaxTaskDirectLayoutAtValuationTermsPayloadEnvelope tokenTable width
      tokenCount data.targetLeft data.targetRight headKind headBinderArity
      headRepeatCount headKindTerm headBinderArityTerm headRepeatCountTerm
      data.layout
  let rightLayoutResource := transparentHybridConjunctionPayloadEnvelope
    valuation rightFormula layoutFormula rightResource layoutResource
  let terminalResource := transparentHybridConjunctionPayloadEnvelope valuation
    leftFormula (rightFormula ⋏ layoutFormula) leftResource rightLayoutResource
  let values : Fin 2 -> Nat := ![data.targetRight, data.targetLeft]
  explicitBoundedWitnessHybridStructuralPayloadEnvelope valuation tokenCount
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal
      tokenTable width tokenCount targetBoundary headKindTerm
      headBinderArityTerm headRepeatCountTerm) values terminalResource

theorem
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadCertificate_structuralPayloadBound_le_public
    (tokenTable width tokenCount targetBoundary
      headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm)
    (hheadKindClosed : headKindTerm.freeVariables = ∅)
    (hheadBinderArityClosed : headBinderArityTerm.freeVariables = ∅)
    (hheadRepeatCountClosed : headRepeatCountTerm.freeVariables = ∅)
    (hheadKindValue : ∀ valuation, termValue valuation headKindTerm = headKind)
    (hheadBinderArityValue : ∀ valuation,
      termValue valuation headBinderArityTerm = headBinderArity)
    (hheadRepeatCountValue : ∀ valuation,
      termValue valuation headRepeatCountTerm = headRepeatCount)
    (data : CompactAdditiveSyntaxTaskListConsHeadData tokenTable width tokenCount
      targetBoundary headKind headBinderArity headRepeatCount) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadCertificate
          tokenTable width tokenCount targetBoundary headKind headBinderArity
          headRepeatCount headKindTerm headBinderArityTerm headRepeatCountTerm
          hheadKindValue hheadBinderArityValue hheadRepeatCountValue data) ≤
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadPayloadEnvelope
        tokenTable width tokenCount targetBoundary headKind headBinderArity
        headRepeatCount headKindTerm headBinderArityTerm headRepeatCountTerm
        data := by
  let valuation := sameRowsZeroValuation
  let boundaryTerm := shortBinaryNumeralTerm targetBoundary
  let countTerm := shortBinaryNumeralTerm tokenCount
  let zeroTerm := unaryNumeralTerm 0
  let oneTerm := unaryNumeralTerm 1
  let leftTerm := shortBinaryNumeralTerm data.targetLeft
  let rightTerm := shortBinaryNumeralTerm data.targetRight
  let leftCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      boundaryTerm countTerm zeroTerm leftTerm (by
        simpa [valuation, boundaryTerm, countTerm, zeroTerm, leftTerm,
          sameRowsZeroValuation, termValue_shortBinaryNumeralTerm,
          termValue_unaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.targetLeft_entry)
  let rightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      boundaryTerm countTerm oneTerm rightTerm (by
        simpa [valuation, boundaryTerm, countTerm, oneTerm, rightTerm,
          sameRowsZeroValuation, termValue_shortBinaryNumeralTerm,
          termValue_unaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.targetRight_entry)
  let layoutCertificate :=
    compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
      tokenTable width tokenCount data.targetLeft data.targetRight headKind
      headBinderArity headRepeatCount headKindTerm headBinderArityTerm
      headRepeatCountTerm hheadKindValue hheadBinderArityValue
      hheadRepeatCountValue data.layout
  have hboundary : boundaryTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty targetBoundary
  have hcount : countTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hzero : zeroTerm.freeVariables = ∅ :=
    unaryNumeralTerm_freeVariables_eq_empty 0
  have hone : oneTerm.freeVariables = ∅ :=
    unaryNumeralTerm_freeVariables_eq_empty 1
  have hleftTerm : leftTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty data.targetLeft
  have hrightTerm : rightTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty data.targetRight
  have hleftResource :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public
      valuation boundaryTerm countTerm zeroTerm leftTerm hboundary hcount hzero
      hleftTerm (by
        simpa [valuation, boundaryTerm, countTerm, zeroTerm, leftTerm,
          sameRowsZeroValuation, termValue_shortBinaryNumeralTerm,
          termValue_unaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.targetLeft_entry)
  have hrightResource :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public
      valuation boundaryTerm countTerm oneTerm rightTerm hboundary hcount hone
      hrightTerm (by
        simpa [valuation, boundaryTerm, countTerm, oneTerm, rightTerm,
          sameRowsZeroValuation, termValue_shortBinaryNumeralTerm,
          termValue_unaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.targetRight_entry)
  have hlayoutResource :=
    compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout_structuralPayloadBound_le_public
      tokenTable width tokenCount data.targetLeft data.targetRight headKind
      headBinderArity headRepeatCount headKindTerm headBinderArityTerm
      headRepeatCountTerm hheadKindClosed hheadBinderArityClosed
      hheadRepeatCountClosed hheadKindValue hheadBinderArityValue
      hheadRepeatCountValue data.layout
  let rightLayout :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      rightCertificate layoutCertificate
  have hrightLayout := transparentHybridConjunctionPayloadBound_le
    rightCertificate layoutCertificate _ _ hrightResource hlayoutResource
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      leftCertificate rightLayout
  have hterminalParts := transparentHybridConjunctionPayloadBound_le
    leftCertificate rightLayout _ _ hleftResource hrightLayout
  let values : Fin 2 -> Nat := ![data.targetRight, data.targetLeft]
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![rightTerm, leftTerm] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminal : CheckedHybridValuationBoundedFormulaCertificate valuation
      ((compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal
        tokenTable width tokenCount targetBoundary headKindTerm
        headBinderArityTerm headRepeatCountTerm) ⇜
          fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal_substitution_alignment
          tokenTable width tokenCount targetBoundary data.targetLeft
          data.targetRight headKindTerm headBinderArityTerm
          headRepeatCountTerm).symm) terminalParts
  have hterminal : hybridFormulaStructuralPayloadBound terminal ≤
      transparentHybridConjunctionPayloadEnvelope valuation
        (compactFixedWidthEntryAtValuationFormula boundaryTerm countTerm
          zeroTerm leftTerm)
        (compactFixedWidthEntryAtValuationFormula boundaryTerm countTerm
            oneTerm rightTerm ⋏
          compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width
            tokenCount data.targetLeft data.targetRight headKindTerm
            headBinderArityTerm headRepeatCountTerm)
        (compactFixedWidthEntryAtValuationStructuralPayloadPolynomial valuation
          boundaryTerm countTerm zeroTerm leftTerm)
        (transparentHybridConjunctionPayloadEnvelope valuation
          (compactFixedWidthEntryAtValuationFormula boundaryTerm countTerm
            oneTerm rightTerm)
          (compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width
            tokenCount data.targetLeft data.targetRight headKindTerm
            headBinderArityTerm headRepeatCountTerm)
          (compactFixedWidthEntryAtValuationStructuralPayloadPolynomial valuation
            boundaryTerm countTerm oneTerm rightTerm)
          (compactSyntaxTaskDirectLayoutAtValuationTermsPayloadEnvelope tokenTable
            width tokenCount data.targetLeft data.targetRight headKind
            headBinderArity headRepeatCount headKindTerm headBinderArityTerm
            headRepeatCountTerm data.layout)) := by
    simpa only [terminal, hybridFormulaStructuralPayloadBound, valuation,
      boundaryTerm, countTerm, zeroTerm, oneTerm, leftTerm, rightTerm,
      leftCertificate, rightCertificate, layoutCertificate, rightLayout,
      terminalParts] using hterminalParts
  have hinstalled :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount
      (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal
        tokenTable width tokenCount targetBoundary headKindTerm
        headBinderArityTerm headRepeatCountTerm)
      values (by
        intro coordinate
        fin_cases coordinate
        · exact data.targetRight_le
        · exact data.targetLeft_le)
      terminal _ hterminal
  change hybridFormulaStructuralPayloadBound
      (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadCertificate
        tokenTable width tokenCount targetBoundary headKind headBinderArity
        headRepeatCount headKindTerm headBinderArityTerm headRepeatCountTerm
        hheadKindValue hheadBinderArityValue hheadRepeatCountValue data) ≤ _
  unfold compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadPayloadEnvelope
  simpa only [
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadCertificate,
    hybridFormulaStructuralPayloadBound, valuation, boundaryTerm, countTerm,
    zeroTerm, oneTerm, leftTerm, rightTerm, leftCertificate,
    rightCertificate, layoutCertificate, rightLayout, terminalParts, values,
    terminal] using hinstalled

def compactAdditiveSyntaxTaskListConsRowsTailTerminalStructuralPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveSyntaxTaskListConsTailRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) : Nat :=
  let valuation := extendValuation index sameRowsZeroValuation
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let sourceIndexTerm : ValuationTerm := &0
  let nextIndexTerm : ValuationTerm := ‘&0 + 1’
  let targetRightIndexTerm : ValuationTerm := ‘&0 + 2’
  let sourceLeftTerm := shortBinaryNumeralTerm data.sourceLeft
  let sourceRightTerm := shortBinaryNumeralTerm data.sourceRight
  let targetLeftTerm := shortBinaryNumeralTerm data.targetLeft
  let targetRightTerm := shortBinaryNumeralTerm data.targetRight
  let sourceLeftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm sourceBoundary) widthTerm sourceIndexTerm
    sourceLeftTerm
  let sourceRightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm sourceBoundary) widthTerm nextIndexTerm
    sourceRightTerm
  let targetLeftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary) widthTerm nextIndexTerm
    targetLeftTerm
  let targetRightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary) widthTerm targetRightIndexTerm
    targetRightTerm
  let rowFormula :=
    (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
      ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
        widthTerm, sourceLeftTerm, sourceRightTerm, targetLeftTerm,
        targetRightTerm]
  let sourceLeftResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation (shortBinaryNumeralTerm sourceBoundary) widthTerm
      sourceIndexTerm sourceLeftTerm
  let sourceRightResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation (shortBinaryNumeralTerm sourceBoundary) widthTerm
      nextIndexTerm sourceRightTerm
  let targetLeftResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation (shortBinaryNumeralTerm targetBoundary) widthTerm
      nextIndexTerm targetLeftTerm
  let targetRightResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation (shortBinaryNumeralTerm targetBoundary) widthTerm
      targetRightIndexTerm targetRightTerm
  let rowResource :=
    compactAdditiveSyntaxTaskRowEqStructuralPayloadEnvelope valuation tokenTable
      width tokenCount data.sourceLeft data.sourceRight data.targetLeft
      data.targetRight
  let targetRightRowResource := transparentHybridConjunctionPayloadEnvelope
    valuation targetRightFormula rowFormula targetRightResource rowResource
  let targetLeftTailResource := transparentHybridConjunctionPayloadEnvelope
    valuation targetLeftFormula (targetRightFormula ⋏ rowFormula)
    targetLeftResource targetRightRowResource
  let sourceRightTailResource := transparentHybridConjunctionPayloadEnvelope
    valuation sourceRightFormula
      (targetLeftFormula ⋏ (targetRightFormula ⋏ rowFormula))
    sourceRightResource targetLeftTailResource
  transparentHybridConjunctionPayloadEnvelope valuation sourceLeftFormula
    (sourceRightFormula ⋏
      (targetLeftFormula ⋏ (targetRightFormula ⋏ rowFormula)))
    sourceLeftResource sourceRightTailResource

def compactAdditiveSyntaxTaskListConsRowsTailBranchStructuralPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveSyntaxTaskListConsTailRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) : Nat :=
  let valuation := extendValuation index sameRowsZeroValuation
  let values : Fin 4 -> Nat :=
    ![data.targetRight, data.targetLeft,
      data.sourceRight, data.sourceLeft]
  explicitBoundedWitnessHybridStructuralPayloadEnvelope valuation tokenCount
    (compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary)
    values
    (compactAdditiveSyntaxTaskListConsRowsTailTerminalStructuralPayloadEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary index data)

theorem
    compactAdditiveSyntaxTaskListConsRowsTailBranchCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveSyntaxTaskListConsTailRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListConsRowsTailBranchCertificate tokenTable width
          tokenCount sourceBoundary targetBoundary index data) <=
      compactAdditiveSyntaxTaskListConsRowsTailBranchStructuralPayloadEnvelope tokenTable
        width tokenCount sourceBoundary targetBoundary index data := by
  let valuation := extendValuation index sameRowsZeroValuation
  let values : Fin 4 -> Nat :=
    ![data.targetRight, data.targetLeft,
      data.sourceRight, data.sourceLeft]
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let sourceIndexTerm : ValuationTerm := &0
  let nextIndexTerm : ValuationTerm := ‘&0 + 1’
  let targetRightIndexTerm : ValuationTerm := ‘&0 + 2’
  let sourceLeftTerm := shortBinaryNumeralTerm data.sourceLeft
  let sourceRightTerm := shortBinaryNumeralTerm data.sourceRight
  let targetLeftTerm := shortBinaryNumeralTerm data.targetLeft
  let targetRightTerm := shortBinaryNumeralTerm data.targetRight
  let sourceLeftCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm sourceBoundary) widthTerm sourceIndexTerm
      sourceLeftTerm (by
        simpa [valuation, widthTerm, sourceIndexTerm, sourceLeftTerm,
          sameRowsZeroValuation,
          termValue_shortBinaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.sourceLeft_entry)
  let sourceRightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm sourceBoundary) widthTerm nextIndexTerm
      sourceRightTerm (by
        simpa [valuation, widthTerm, nextIndexTerm, sourceRightTerm,
          sameRowsZeroValuation,
          termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.sourceRight_entry)
  let targetLeftCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm targetBoundary) widthTerm nextIndexTerm
      targetLeftTerm (by
        simpa [valuation, widthTerm, nextIndexTerm, targetLeftTerm,
          sameRowsZeroValuation,
          termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.targetLeft_entry)
  let targetRightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm targetBoundary) widthTerm targetRightIndexTerm
      targetRightTerm (by
        simpa [valuation, widthTerm, targetRightIndexTerm, targetRightTerm,
          sameRowsZeroValuation,
          termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
          termValue_arithmeticTwo,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.targetRight_entry)
  let rowCertificate :=
    compactAdditiveSyntaxTaskRowEqExplicitHybridCertificateOfGraph valuation
      tokenTable width tokenCount data.sourceLeft data.sourceRight
      data.targetLeft data.targetRight data.row_eq
  have hsourceIndex : sourceIndexTerm.freeVariables ⊆ {0} := by
    simp [sourceIndexTerm]
  have hnextIndex : nextIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [nextIndexTerm]
    rw [arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
      arithmeticOneTerm_freeVariables_eq_empty]
    simp
  have htargetRightIndex : targetRightIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [targetRightIndexTerm]
    rw [arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
      arithmeticTwoTerm_freeVariables_eq_empty]
    simp
  have hsourceBoundary :
      (shortBinaryNumeralTerm sourceBoundary).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty sourceBoundary
  have htargetBoundary :
      (shortBinaryNumeralTerm targetBoundary).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty targetBoundary
  have hwidthTerm : widthTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hsourceLeftTerm : sourceLeftTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty data.sourceLeft
  have hsourceRightTerm : sourceRightTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty data.sourceRight
  have htargetLeftTerm : targetLeftTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty data.targetLeft
  have htargetRightTerm : targetRightTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty data.targetRight
  have hsourceLeft :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation (shortBinaryNumeralTerm sourceBoundary) widthTerm
      sourceIndexTerm sourceLeftTerm hsourceBoundary hwidthTerm
      hsourceIndex hsourceLeftTerm (by
        simpa [valuation, widthTerm, sourceIndexTerm, sourceLeftTerm,
          sameRowsZeroValuation,
          termValue_shortBinaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.sourceLeft_entry)
  have hsourceRight :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation (shortBinaryNumeralTerm sourceBoundary) widthTerm
      nextIndexTerm sourceRightTerm hsourceBoundary hwidthTerm
      hnextIndex hsourceRightTerm (by
        simpa [valuation, widthTerm, nextIndexTerm, sourceRightTerm,
          sameRowsZeroValuation,
          termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.sourceRight_entry)
  have htargetLeft :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation (shortBinaryNumeralTerm targetBoundary) widthTerm
      nextIndexTerm targetLeftTerm htargetBoundary hwidthTerm
      hnextIndex htargetLeftTerm (by
        simpa [valuation, widthTerm, nextIndexTerm, targetLeftTerm,
          sameRowsZeroValuation,
          termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.targetLeft_entry)
  have htargetRight :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation (shortBinaryNumeralTerm targetBoundary) widthTerm
      targetRightIndexTerm targetRightTerm htargetBoundary hwidthTerm
      htargetRightIndex htargetRightTerm (by
        simpa [valuation, widthTerm, targetRightIndexTerm, targetRightTerm,
          sameRowsZeroValuation,
          termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
          termValue_arithmeticTwo,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.targetRight_entry)
  have hrow :=
    compactAdditiveSyntaxTaskRowEqExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      valuation tokenTable width tokenCount data.sourceLeft data.sourceRight
      data.targetLeft data.targetRight data.row_eq
  let targetRightRow :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      targetRightCertificate rowCertificate
  have htargetRightRow := transparentHybridConjunctionPayloadBound_le
    targetRightCertificate rowCertificate _ _ htargetRight hrow
  let targetLeftTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      targetLeftCertificate targetRightRow
  have htargetLeftTail := transparentHybridConjunctionPayloadBound_le
    targetLeftCertificate targetRightRow _ _ htargetLeft htargetRightRow
  let sourceRightTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      sourceRightCertificate targetLeftTail
  have hsourceRightTail := transparentHybridConjunctionPayloadBound_le
    sourceRightCertificate targetLeftTail _ _ hsourceRight htargetLeftTail
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      sourceLeftCertificate sourceRightTail
  have hterminalParts := transparentHybridConjunctionPayloadBound_le
    sourceLeftCertificate sourceRightTail _ _ hsourceLeft hsourceRightTail
  have hvalueTerms :
      (fun coordinate : Fin 4 => shortBinaryNumeralTerm (values coordinate)) =
        ![targetRightTerm, targetLeftTerm, sourceRightTerm,
          sourceLeftTerm] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminal : CheckedHybridValuationBoundedFormulaCertificate valuation
      ((compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary) ⇜
          fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal_substitution_alignment
          tokenTable width tokenCount sourceBoundary targetBoundary
          data.sourceLeft data.sourceRight data.targetLeft
          data.targetRight).symm) terminalParts
  have hterminal : hybridFormulaStructuralPayloadBound terminal <=
      compactAdditiveSyntaxTaskListConsRowsTailTerminalStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary index
        data := by
    simpa only [terminal, hybridFormulaStructuralPayloadBound,
      compactAdditiveSyntaxTaskListConsRowsTailTerminalStructuralPayloadEnvelope,
      valuation, widthTerm, sourceIndexTerm, nextIndexTerm,
      targetRightIndexTerm,
      sourceLeftTerm, sourceRightTerm, targetLeftTerm, targetRightTerm,
      sourceLeftCertificate, sourceRightCertificate, targetLeftCertificate,
      targetRightCertificate, rowCertificate, targetRightRow,
      targetLeftTail, sourceRightTail, terminalParts] using hterminalParts
  have hinstalled :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount
      (compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary)
      values (by
        intro coordinate
        fin_cases coordinate
        · exact data.targetRight_le
        · exact data.targetLeft_le
        · exact data.sourceRight_le
        · exact data.sourceLeft_le)
      terminal
      (compactAdditiveSyntaxTaskListConsRowsTailTerminalStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary index data)
      hterminal
  simpa only [compactAdditiveSyntaxTaskListConsRowsTailBranchCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveSyntaxTaskListConsRowsTailBranchStructuralPayloadEnvelope,
    valuation, values, terminal, terminalParts, targetRightRow,
    targetLeftTail, sourceRightTail, sourceLeftCertificate,
    sourceRightCertificate, targetLeftCertificate, targetRightCertificate,
    rowCertificate] using hinstalled

noncomputable def compactAdditiveSyntaxTaskListConsRowsTailBranchPayloadResourceSum
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListConsTailRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) : Nat :=
  ∑ index : Fin sourceCount,
    compactAdditiveSyntaxTaskListConsRowsTailBranchStructuralPayloadEnvelope tokenTable
      width tokenCount sourceBoundary targetBoundary index (rows index)

theorem
    compactAdditiveSyntaxTaskListConsRowsTailDirectHybridBranchesAtCount_leafPayloadBound
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListConsTailRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    HybridBranchesLeafPayloadBound
      (compactAdditiveSyntaxTaskListConsRowsTailBranchPayloadResourceSum tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows)
      (compactAdditiveSyntaxTaskListConsRowsTailDirectHybridBranchesAtCount tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary rows) := by
  unfold compactAdditiveSyntaxTaskListConsRowsTailDirectHybridBranchesAtCount
  apply buildExplicitHybridUniversalBranches_leafPayloadBound
  intro index hindex
  let finiteIndex : Fin sourceCount := ⟨index, hindex⟩
  have hbranch :=
    compactAdditiveSyntaxTaskListConsRowsTailBranchCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary targetBoundary finiteIndex
      (rows finiteIndex)
  have hsum :
      compactAdditiveSyntaxTaskListConsRowsTailBranchStructuralPayloadEnvelope tokenTable
          width tokenCount sourceBoundary targetBoundary finiteIndex
          (rows finiteIndex) <=
        compactAdditiveSyntaxTaskListConsRowsTailBranchPayloadResourceSum tokenTable width
          tokenCount sourceBoundary sourceCount targetBoundary rows := by
    unfold compactAdditiveSyntaxTaskListConsRowsTailBranchPayloadResourceSum
    exact Finset.single_le_sum
      (fun (candidate : Fin sourceCount) _ => Nat.zero_le
        (compactAdditiveSyntaxTaskListConsRowsTailBranchStructuralPayloadEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary candidate
          (rows candidate)))
      (Finset.mem_univ finiteIndex)
  dsimp only [finiteIndex] at hbranch hsum ⊢
  exact hbranch.trans hsum

private theorem hybridBranchesLeafPayloadBound_transport
    {valuation : Nat -> Nat}
    {body : ArithmeticSemiformula Nat 1}
    {sourceBound targetBound leafBound : Nat}
    (hbound : sourceBound = targetBound)
    (branches : CheckedHybridValuationUniversalBranches
      valuation body sourceBound)
    (hleaves : HybridBranchesLeafPayloadBound leafBound branches) :
    HybridBranchesLeafPayloadBound leafBound (hbound ▸ branches) := by
  cases hbound
  exact hleaves

theorem compactAdditiveSyntaxTaskListConsRowsTailDirectHybridBranches_leafPayloadBound
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListConsTailRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    HybridBranchesLeafPayloadBound
      (compactAdditiveSyntaxTaskListConsRowsTailBranchPayloadResourceSum tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows)
      (compactAdditiveSyntaxTaskListConsRowsTailDirectHybridBranches tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows) := by
  unfold compactAdditiveSyntaxTaskListConsRowsTailDirectHybridBranches
  exact hybridBranchesLeafPayloadBound_transport
    (compactAdditiveSyntaxTaskListConsRowsShortNumeralBound_eq_sourceCount
      sourceCount).symm
    (compactAdditiveSyntaxTaskListConsRowsTailDirectHybridBranchesAtCount tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary rows)
    (compactAdditiveSyntaxTaskListConsRowsTailDirectHybridBranchesAtCount_leafPayloadBound
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows)

noncomputable def compactAdditiveSyntaxTaskListConsRowsTailBranchesTransparentEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListConsTailRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) : Nat :=
  let body := compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue sameRowsZeroValuation
    (shortBinaryNumeralTerm sourceCount)
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
    sameRowsZeroValuation body
    (compactAdditiveSyntaxTaskListConsRowsTailBranchPayloadResourceSum tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary rows)
    bound

theorem
    compactAdditiveSyntaxTaskListConsRowsTailBranchesStructuralPayloadEnvelope_le_transparent
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListConsTailRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    let body := compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
      sourceBoundary targetBoundary
    let outerFormula := ∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body
    hybridBranchesStructuralPayloadEnvelope
        (termValue sameRowsZeroValuation (shortBinaryNumeralTerm sourceCount))
        outerFormula.freeVariables
        (compactAdditiveSyntaxTaskListConsRowsTailDirectHybridBranches tokenTable width
          tokenCount sourceBoundary sourceCount targetBoundary rows) <=
      compactAdditiveSyntaxTaskListConsRowsTailBranchesTransparentEnvelope tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary rows := by
  let body := compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue sameRowsZeroValuation
    (shortBinaryNumeralTerm sourceCount)
  let branches := compactAdditiveSyntaxTaskListConsRowsTailDirectHybridBranches
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows
  have hleaves :=
    compactAdditiveSyntaxTaskListConsRowsTailDirectHybridBranches_leafPayloadBound
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows
  have hbound := hybridBranchesStructuralPayloadEnvelope_le_uniformEnvelope
    bound outerVariables
    (compactAdditiveSyntaxTaskListConsRowsTailBranchPayloadResourceSum tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary rows)
    branches hleaves
  simpa only [compactAdditiveSyntaxTaskListConsRowsTailBranchesTransparentEnvelope,
    body, outerFormula, outerVariables, bound, branches] using hbound

noncomputable def compactAdditiveSyntaxTaskListConsRowsTailUniversalPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListConsTailRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) : Nat :=
  let body := compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let boundTerm := shortBinaryNumeralTerm sourceCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables sameRowsZeroValuation
  let bound := termValue sameRowsZeroValuation boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (compactAdditiveSyntaxTaskListConsRowsTailBranchesTransparentEnvelope tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary rows)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift boundTerm) body
    (compileShiftedBoundEqualityPayloadResource sameRowsZeroValuation
      outerVariables boundTerm)
    branchResource

theorem
    compactAdditiveSyntaxTaskListConsRowsTailUniversalCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListConsTailRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListConsRowsTailUniversalCertificate tokenTable width
          tokenCount sourceBoundary sourceCount targetBoundary rows) <=
      compactAdditiveSyntaxTaskListConsRowsTailUniversalPayloadEnvelope tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows := by
  let body := compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let boundTerm := shortBinaryNumeralTerm sourceCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables sameRowsZeroValuation
  let bound := termValue sameRowsZeroValuation boundTerm
  let branches := compactAdditiveSyntaxTaskListConsRowsTailDirectHybridBranches
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows
  let oldBranchCore := hybridBranchesStructuralPayloadEnvelope
    bound outerVariables branches
  let newBranchCore := compactAdditiveSyntaxTaskListConsRowsTailBranchesTransparentEnvelope
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldBranchCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newBranchCore
  let boundResource := compileShiftedBoundEqualityPayloadResource
    sameRowsZeroValuation outerVariables boundTerm
  have hbranchCore : oldBranchCore <= newBranchCore := by
    dsimp only [oldBranchCore, newBranchCore, bound, branches,
      outerVariables, outerFormula, body, boundTerm]
    exact
      compactAdditiveSyntaxTaskListConsRowsTailBranchesStructuralPayloadEnvelope_le_transparent
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        rows
  have hbranchResource : oldBranchResource <= newBranchResource :=
    contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldBranchCore newBranchCore hbranchCore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift boundTerm) body
    boundResource oldBranchResource boundResource newBranchResource
    le_rfl hbranchResource
  simpa only [compactAdditiveSyntaxTaskListConsRowsTailUniversalCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveSyntaxTaskListConsRowsTailUniversalPayloadEnvelope,
    body, boundTerm, outerFormula, outerVariables, Gamma, bound, branches,
    oldBranchCore, newBranchCore, oldBranchResource, newBranchResource,
    boundResource] using htotal

noncomputable def
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFromDataPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm)
    (headData : CompactAdditiveSyntaxTaskListConsHeadData tokenTable width
      tokenCount targetBoundary headKind headBinderArity headRepeatCount)
    (tailRows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index) : Nat :=
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm sourceCount) + 1”
  let headFormula :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsBody tokenTable
      width tokenCount targetBoundary headKindTerm headBinderArityTerm
      headRepeatCountTerm
  let tailFormula : ValuationFormula :=
    (compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
      sourceBoundary targetBoundary).ballLT
        (shortBinaryNumeralTerm sourceCount)
  let headTailResource := transparentHybridConjunctionPayloadEnvelope
    sameRowsZeroValuation headFormula tailFormula
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadPayloadEnvelope
      tokenTable width tokenCount targetBoundary headKind headBinderArity
      headRepeatCount headKindTerm headBinderArityTerm headRepeatCountTerm
      headData)
    (compactAdditiveSyntaxTaskListConsRowsTailUniversalPayloadEnvelope tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary tailRows)
  transparentHybridConjunctionPayloadEnvelope sameRowsZeroValuation countFormula
    (headFormula ⋏ tailFormula)
    (compactAdditiveSyntaxTaskListConsRowsCountEqualityPayloadPolynomial
      sourceCount targetCount)
    headTailResource

theorem
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFromDataExplicitHybridCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm)
    (hheadKindClosed : headKindTerm.freeVariables = ∅)
    (hheadBinderArityClosed : headBinderArityTerm.freeVariables = ∅)
    (hheadRepeatCountClosed : headRepeatCountTerm.freeVariables = ∅)
    (hheadKindValue : ∀ valuation, termValue valuation headKindTerm = headKind)
    (hheadBinderArityValue : ∀ valuation,
      termValue valuation headBinderArityTerm = headBinderArity)
    (hheadRepeatCountValue : ∀ valuation,
      termValue valuation headRepeatCountTerm = headRepeatCount)
    (hcount : targetCount = sourceCount + 1)
    (headData : CompactAdditiveSyntaxTaskListConsHeadData tokenTable width
      tokenCount targetBoundary headKind headBinderArity headRepeatCount)
    (tailRows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFromDataExplicitHybridCertificate
          tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
          targetCount headKind headBinderArity headRepeatCount headKindTerm
          headBinderArityTerm headRepeatCountTerm hheadKindValue
          hheadBinderArityValue hheadRepeatCountValue hcount headData tailRows) ≤
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFromDataPayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount headKind headBinderArity headRepeatCount headKindTerm
        headBinderArityTerm headRepeatCountTerm headData tailRows := by
  let countCertificate :=
    FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.countEqualityCertificate
      sourceCount targetCount hcount
  let headCertificate :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadCertificate
      tokenTable width tokenCount targetBoundary headKind headBinderArity
      headRepeatCount headKindTerm headBinderArityTerm headRepeatCountTerm
      hheadKindValue hheadBinderArityValue hheadRepeatCountValue headData
  let tailCertificate :=
    compactAdditiveSyntaxTaskListConsRowsTailUniversalCertificate tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary tailRows
  let headTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      headCertificate tailCertificate
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    countCertificate headTailCertificate
  have hcountResource := consCountEqualityCertificate_structuralPayloadBound_le_public
    sourceCount targetCount hcount
  have hheadResource :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount targetBoundary headKind headBinderArity
      headRepeatCount headKindTerm headBinderArityTerm headRepeatCountTerm
      hheadKindClosed hheadBinderArityClosed hheadRepeatCountClosed
      hheadKindValue hheadBinderArityValue hheadRepeatCountValue headData
  have htailResource :=
    compactAdditiveSyntaxTaskListConsRowsTailUniversalCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary tailRows
  have hheadTailResource := transparentHybridConjunctionPayloadBound_le
    headCertificate tailCertificate _ _ hheadResource htailResource
  have hparts := transparentHybridConjunctionPayloadBound_le
    countCertificate headTailCertificate _ _ hcountResource hheadTailResource
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula_alignment
          tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
          targetCount headKindTerm headBinderArityTerm
          headRepeatCountTerm).symm parts) ≤ _
  unfold
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFromDataPayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound, countCertificate,
    headCertificate, tailCertificate, headTailCertificate, parts] using hparts

noncomputable def
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsGraphPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm)
    (hgraph : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount headKind
      headBinderArity headRepeatCount) : Nat :=
  compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFromDataPayloadEnvelope
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
    targetCount headKind headBinderArity headRepeatCount headKindTerm
    headBinderArityTerm headRepeatCountTerm
    (compactAdditiveSyntaxTaskListConsRowsHeadDataOfGraph tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary targetCount headKind
      headBinderArity headRepeatCount hgraph)
    (compactAdditiveSyntaxTaskListConsRowsTailRowDataOfGraph tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary targetCount headKind
      headBinderArity headRepeatCount hgraph)

theorem
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm)
    (hheadKindClosed : headKindTerm.freeVariables = ∅)
    (hheadBinderArityClosed : headBinderArityTerm.freeVariables = ∅)
    (hheadRepeatCountClosed : headRepeatCountTerm.freeVariables = ∅)
    (hheadKindValue : ∀ valuation, termValue valuation headKindTerm = headKind)
    (hheadBinderArityValue : ∀ valuation,
      termValue valuation headBinderArityTerm = headBinderArity)
    (hheadRepeatCountValue : ∀ valuation,
      termValue valuation headRepeatCountTerm = headRepeatCount)
    (hgraph : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount headKind
      headBinderArity headRepeatCount) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
          targetCount headKind headBinderArity headRepeatCount headKindTerm
          headBinderArityTerm headRepeatCountTerm hheadKindValue
          hheadBinderArityValue hheadRepeatCountValue hgraph) ≤
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsGraphPayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount headKind headBinderArity headRepeatCount headKindTerm
        headBinderArityTerm headRepeatCountTerm hgraph := by
  simpa only [
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph,
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsGraphPayloadEnvelope] using
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFromDataExplicitHybridCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount headKind headBinderArity headRepeatCount headKindTerm
      headBinderArityTerm headRepeatCountTerm hheadKindClosed
      hheadBinderArityClosed hheadRepeatCountClosed hheadKindValue
      hheadBinderArityValue hheadRepeatCountValue hgraph.1
      (compactAdditiveSyntaxTaskListConsRowsHeadDataOfGraph tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount headKind
        headBinderArity headRepeatCount hgraph)
      (compactAdditiveSyntaxTaskListConsRowsTailRowDataOfGraph tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount headKind
        headBinderArity headRepeatCount hgraph)

noncomputable def compactAdditiveSyntaxTaskListConsRowsGraphPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount headKind headBinderArity headRepeatCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount headKind
      headBinderArity headRepeatCount) : Nat :=
  compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsGraphPayloadEnvelope
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
    targetCount headKind headBinderArity headRepeatCount
    (shortBinaryNumeralTerm headKind)
    (shortBinaryNumeralTerm headBinderArity)
    (shortBinaryNumeralTerm headRepeatCount) hgraph

theorem
    compactAdditiveSyntaxTaskListConsRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount headKind headBinderArity headRepeatCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount headKind
      headBinderArity headRepeatCount) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListConsRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
          targetCount headKind headBinderArity headRepeatCount hgraph) ≤
      compactAdditiveSyntaxTaskListConsRowsGraphPayloadEnvelope tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount headKind
        headBinderArity headRepeatCount hgraph := by
  let hheadKindValue : ∀ valuation,
      termValue valuation (shortBinaryNumeralTerm headKind) = headKind :=
    fun valuation => termValue_shortBinaryNumeralTerm valuation headKind
  let hheadBinderArityValue : ∀ valuation,
      termValue valuation (shortBinaryNumeralTerm headBinderArity) =
        headBinderArity :=
    fun valuation => termValue_shortBinaryNumeralTerm valuation headBinderArity
  let hheadRepeatCountValue : ∀ valuation,
      termValue valuation (shortBinaryNumeralTerm headRepeatCount) =
        headRepeatCount :=
    fun valuation => termValue_shortBinaryNumeralTerm valuation headRepeatCount
  change hybridFormulaStructuralPayloadBound
      (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount headKind headBinderArity headRepeatCount
        (shortBinaryNumeralTerm headKind)
        (shortBinaryNumeralTerm headBinderArity)
        (shortBinaryNumeralTerm headRepeatCount) hheadKindValue
        hheadBinderArityValue hheadRepeatCountValue hgraph) ≤ _
  unfold compactAdditiveSyntaxTaskListConsRowsGraphPayloadEnvelope
  exact
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount headKind headBinderArity headRepeatCount
      (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)
      (shortBinaryNumeralTerm_freeVariables_eq_empty headKind)
      (shortBinaryNumeralTerm_freeVariables_eq_empty headBinderArity)
      (shortBinaryNumeralTerm_freeVariables_eq_empty headRepeatCount)
      hheadKindValue hheadBinderArityValue hheadRepeatCountValue hgraph

#print axioms consCountEqualityCertificate_structuralPayloadBound_le_public
#print axioms
  compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadCertificate_structuralPayloadBound_le_public
#print axioms
  compactAdditiveSyntaxTaskListConsRowsTailBranchCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveSyntaxTaskListConsRowsTailUniversalCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveSyntaxTaskListConsRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds
