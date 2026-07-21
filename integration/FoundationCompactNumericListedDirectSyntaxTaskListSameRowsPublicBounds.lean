import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAtomicRowEqualityPublicBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds

/-!
# Public structural resources for equal syntax-task-list rows

Each row exposes four fixed-width table entries and three consecutive atomic-row equalities.
The four bounded witnesses and the outer row universal are then charged by
proof-free transparent envelopes.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds

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
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate

private abbrev sameRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate.zeroValuation

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

def compactAdditiveSyntaxTaskListSameRowsCountEqualityPayloadPolynomial
    (sourceCount targetCount : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial sameRowsZeroValuation
    Language.Eq.eq
    ![shortBinaryNumeralTerm targetCount,
      shortBinaryNumeralTerm sourceCount]

theorem countEqualityCertificate_structuralPayloadBound_le_public
    (sourceCount targetCount : Nat)
    (hcount : targetCount = sourceCount) :
    hybridFormulaStructuralPayloadBound
        (countEqualityCertificate sourceCount targetCount hcount) <=
      compactAdditiveSyntaxTaskListSameRowsCountEqualityPayloadPolynomial
        sourceCount targetCount := by
  have hfirst :
      (shortBinaryNumeralTerm targetCount).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hsecond :
      (shortBinaryNumeralTerm sourceCount).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    sameRowsZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm targetCount,
      shortBinaryNumeralTerm sourceCount]
    hfirst hsecond
  simpa only [countEqualityCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveSyntaxTaskListSameRowsCountEqualityPayloadPolynomial] using hpublic

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

def compactAdditiveSyntaxTaskListSameRowsTerminalStructuralPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveSyntaxTaskListSameRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) : Nat :=
  let valuation := extendValuation index sameRowsZeroValuation
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let sourceIndexTerm : ValuationTerm := &0
  let nextIndexTerm : ValuationTerm := ‘&0 + 1’
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
    (shortBinaryNumeralTerm targetBoundary) widthTerm sourceIndexTerm
    targetLeftTerm
  let targetRightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary) widthTerm nextIndexTerm
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
      sourceIndexTerm targetLeftTerm
  let targetRightResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation (shortBinaryNumeralTerm targetBoundary) widthTerm
      nextIndexTerm targetRightTerm
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

def compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveSyntaxTaskListSameRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) : Nat :=
  let valuation := extendValuation index sameRowsZeroValuation
  let values : Fin 4 -> Nat :=
    ![data.targetRight, data.targetLeft,
      data.sourceRight, data.sourceLeft]
  explicitBoundedWitnessHybridStructuralPayloadEnvelope valuation tokenCount
    (compactAdditiveSyntaxTaskListSameRowsBranchTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary)
    values
    (compactAdditiveSyntaxTaskListSameRowsTerminalStructuralPayloadEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary index data)

theorem
    compactAdditiveSyntaxTaskListSameRowsBranchCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveSyntaxTaskListSameRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListSameRowsBranchCertificate tokenTable width
          tokenCount sourceBoundary targetBoundary index data) <=
      compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope tokenTable
        width tokenCount sourceBoundary targetBoundary index data := by
  let valuation := extendValuation index sameRowsZeroValuation
  let values : Fin 4 -> Nat :=
    ![data.targetRight, data.targetLeft,
      data.sourceRight, data.sourceLeft]
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let sourceIndexTerm : ValuationTerm := &0
  let nextIndexTerm : ValuationTerm := ‘&0 + 1’
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
      (shortBinaryNumeralTerm targetBoundary) widthTerm sourceIndexTerm
      targetLeftTerm (by
        simpa [valuation, widthTerm, sourceIndexTerm, targetLeftTerm,
          sameRowsZeroValuation,
          termValue_shortBinaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.targetLeft_entry)
  let targetRightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm targetBoundary) widthTerm nextIndexTerm
      targetRightTerm (by
        simpa [valuation, widthTerm, nextIndexTerm, targetRightTerm,
          sameRowsZeroValuation,
          termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne,
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
      sourceIndexTerm targetLeftTerm htargetBoundary hwidthTerm
      hsourceIndex htargetLeftTerm (by
        simpa [valuation, widthTerm, sourceIndexTerm, targetLeftTerm,
          sameRowsZeroValuation,
          termValue_shortBinaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.targetLeft_entry)
  have htargetRight :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation (shortBinaryNumeralTerm targetBoundary) widthTerm
      nextIndexTerm targetRightTerm htargetBoundary hwidthTerm
      hnextIndex htargetRightTerm (by
        simpa [valuation, widthTerm, nextIndexTerm, targetRightTerm,
          sameRowsZeroValuation,
          termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne,
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
      ((compactAdditiveSyntaxTaskListSameRowsBranchTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary) ⇜
          fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveSyntaxTaskListSameRowsBranchTerminal_substitution_alignment
          tokenTable width tokenCount sourceBoundary targetBoundary
          data.sourceLeft data.sourceRight data.targetLeft
          data.targetRight).symm) terminalParts
  have hterminal : hybridFormulaStructuralPayloadBound terminal <=
      compactAdditiveSyntaxTaskListSameRowsTerminalStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary index
        data := by
    simpa only [terminal, hybridFormulaStructuralPayloadBound,
      compactAdditiveSyntaxTaskListSameRowsTerminalStructuralPayloadEnvelope,
      valuation, widthTerm, sourceIndexTerm, nextIndexTerm,
      sourceLeftTerm, sourceRightTerm, targetLeftTerm, targetRightTerm,
      sourceLeftCertificate, sourceRightCertificate, targetLeftCertificate,
      targetRightCertificate, rowCertificate, targetRightRow,
      targetLeftTail, sourceRightTail, terminalParts] using hterminalParts
  have hinstalled :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount
      (compactAdditiveSyntaxTaskListSameRowsBranchTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary)
      values (by
        intro coordinate
        fin_cases coordinate
        · exact data.targetRight_le
        · exact data.targetLeft_le
        · exact data.sourceRight_le
        · exact data.sourceLeft_le)
      terminal
      (compactAdditiveSyntaxTaskListSameRowsTerminalStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary index data)
      hterminal
  simpa only [compactAdditiveSyntaxTaskListSameRowsBranchCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope,
    valuation, values, terminal, terminalParts, targetRightRow,
    targetLeftTail, sourceRightTail, sourceLeftCertificate,
    sourceRightCertificate, targetLeftCertificate, targetRightCertificate,
    rowCertificate] using hinstalled

noncomputable def compactAdditiveSyntaxTaskListSameRowsBranchPayloadResourceSum
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) : Nat :=
  ∑ index : Fin sourceCount,
    compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope tokenTable
      width tokenCount sourceBoundary targetBoundary index (rows index)

theorem
    compactAdditiveSyntaxTaskListSameRowsDirectHybridBranchesAtCount_leafPayloadBound
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    HybridBranchesLeafPayloadBound
      (compactAdditiveSyntaxTaskListSameRowsBranchPayloadResourceSum tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows)
      (compactAdditiveSyntaxTaskListSameRowsDirectHybridBranchesAtCount tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary rows) := by
  unfold compactAdditiveSyntaxTaskListSameRowsDirectHybridBranchesAtCount
  apply buildExplicitHybridUniversalBranches_leafPayloadBound
  intro index hindex
  let finiteIndex : Fin sourceCount := ⟨index, hindex⟩
  have hbranch :=
    compactAdditiveSyntaxTaskListSameRowsBranchCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary targetBoundary finiteIndex
      (rows finiteIndex)
  have hsum :
      compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope tokenTable
          width tokenCount sourceBoundary targetBoundary finiteIndex
          (rows finiteIndex) <=
        compactAdditiveSyntaxTaskListSameRowsBranchPayloadResourceSum tokenTable width
          tokenCount sourceBoundary sourceCount targetBoundary rows := by
    unfold compactAdditiveSyntaxTaskListSameRowsBranchPayloadResourceSum
    exact Finset.single_le_sum
      (fun (candidate : Fin sourceCount) _ => Nat.zero_le
        (compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope
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

theorem compactAdditiveSyntaxTaskListSameRowsDirectHybridBranches_leafPayloadBound
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    HybridBranchesLeafPayloadBound
      (compactAdditiveSyntaxTaskListSameRowsBranchPayloadResourceSum tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows)
      (compactAdditiveSyntaxTaskListSameRowsDirectHybridBranches tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows) := by
  unfold compactAdditiveSyntaxTaskListSameRowsDirectHybridBranches
  exact hybridBranchesLeafPayloadBound_transport
    (compactAdditiveSyntaxTaskListSameRowsShortNumeralBound_eq_sourceCount
      sourceCount).symm
    (compactAdditiveSyntaxTaskListSameRowsDirectHybridBranchesAtCount tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary rows)
    (compactAdditiveSyntaxTaskListSameRowsDirectHybridBranchesAtCount_leafPayloadBound
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows)

noncomputable def compactAdditiveSyntaxTaskListSameRowsBranchesTransparentEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) : Nat :=
  let body := compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue sameRowsZeroValuation
    (shortBinaryNumeralTerm sourceCount)
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
    sameRowsZeroValuation body
    (compactAdditiveSyntaxTaskListSameRowsBranchPayloadResourceSum tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary rows)
    bound

theorem
    compactAdditiveSyntaxTaskListSameRowsBranchesStructuralPayloadEnvelope_le_transparent
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    let body := compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
      sourceBoundary targetBoundary
    let outerFormula := ∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body
    hybridBranchesStructuralPayloadEnvelope
        (termValue sameRowsZeroValuation (shortBinaryNumeralTerm sourceCount))
        outerFormula.freeVariables
        (compactAdditiveSyntaxTaskListSameRowsDirectHybridBranches tokenTable width
          tokenCount sourceBoundary sourceCount targetBoundary rows) <=
      compactAdditiveSyntaxTaskListSameRowsBranchesTransparentEnvelope tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary rows := by
  let body := compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue sameRowsZeroValuation
    (shortBinaryNumeralTerm sourceCount)
  let branches := compactAdditiveSyntaxTaskListSameRowsDirectHybridBranches
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows
  have hleaves :=
    compactAdditiveSyntaxTaskListSameRowsDirectHybridBranches_leafPayloadBound
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows
  have hbound := hybridBranchesStructuralPayloadEnvelope_le_uniformEnvelope
    bound outerVariables
    (compactAdditiveSyntaxTaskListSameRowsBranchPayloadResourceSum tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary rows)
    branches hleaves
  simpa only [compactAdditiveSyntaxTaskListSameRowsBranchesTransparentEnvelope,
    body, outerFormula, outerVariables, bound, branches] using hbound

noncomputable def compactAdditiveSyntaxTaskListSameRowsUniversalPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) : Nat :=
  let body := compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let boundTerm := shortBinaryNumeralTerm sourceCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables sameRowsZeroValuation
  let bound := termValue sameRowsZeroValuation boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (compactAdditiveSyntaxTaskListSameRowsBranchesTransparentEnvelope tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary rows)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift boundTerm) body
    (compileShiftedBoundEqualityPayloadResource sameRowsZeroValuation
      outerVariables boundTerm)
    branchResource

theorem
    compactAdditiveSyntaxTaskListSameRowsUniversalCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListSameRowsUniversalCertificate tokenTable width
          tokenCount sourceBoundary sourceCount targetBoundary rows) <=
      compactAdditiveSyntaxTaskListSameRowsUniversalPayloadEnvelope tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows := by
  let body := compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let boundTerm := shortBinaryNumeralTerm sourceCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables sameRowsZeroValuation
  let bound := termValue sameRowsZeroValuation boundTerm
  let branches := compactAdditiveSyntaxTaskListSameRowsDirectHybridBranches
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows
  let oldBranchCore := hybridBranchesStructuralPayloadEnvelope
    bound outerVariables branches
  let newBranchCore := compactAdditiveSyntaxTaskListSameRowsBranchesTransparentEnvelope
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
      compactAdditiveSyntaxTaskListSameRowsBranchesStructuralPayloadEnvelope_le_transparent
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
  simpa only [compactAdditiveSyntaxTaskListSameRowsUniversalCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveSyntaxTaskListSameRowsUniversalPayloadEnvelope,
    body, boundTerm, outerFormula, outerVariables, Gamma, bound, branches,
    oldBranchCore, newBranchCore, oldBranchResource, newBranchResource,
    boundResource] using htotal

noncomputable def compactAdditiveSyntaxTaskListSameRowsFromRowDataPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) : Nat :=
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm sourceCount)”
  let universalFormula : ValuationFormula :=
    (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
      sourceBoundary targetBoundary).ballLT
        (shortBinaryNumeralTerm sourceCount)
  transparentHybridConjunctionPayloadEnvelope sameRowsZeroValuation
    countFormula universalFormula
    (compactAdditiveSyntaxTaskListSameRowsCountEqualityPayloadPolynomial
      sourceCount targetCount)
    (compactAdditiveSyntaxTaskListSameRowsUniversalPayloadEnvelope tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary rows)

theorem
    compactAdditiveSyntaxTaskListSameRowsFromRowDataExplicitHybridCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (hcount : targetCount = sourceCount)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListSameRowsFromRowDataExplicitHybridCertificate
          tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount hcount rows) <=
      compactAdditiveSyntaxTaskListSameRowsFromRowDataPayloadEnvelope tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
        rows := by
  let countCertificate := countEqualityCertificate sourceCount targetCount hcount
  let universalCertificate := compactAdditiveSyntaxTaskListSameRowsUniversalCertificate
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    countCertificate universalCertificate
  have hcountResource := countEqualityCertificate_structuralPayloadBound_le_public
    sourceCount targetCount hcount
  have huniversalResource :=
    compactAdditiveSyntaxTaskListSameRowsUniversalCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows
  have hparts := transparentHybridConjunctionPayloadBound_le
    countCertificate universalCertificate _ _
    hcountResource huniversalResource
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactAdditiveSyntaxTaskListSameRowsClosedFormula_alignment tokenTable width
          tokenCount sourceBoundary sourceCount targetBoundary
          targetCount).symm parts) <= _
  unfold compactAdditiveSyntaxTaskListSameRowsFromRowDataPayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound, countCertificate,
    universalCertificate, parts,
    compactAdditiveSyntaxTaskListSameRowsCountEqualityPayloadPolynomial] using hparts

noncomputable def compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount) : Nat :=
  compactAdditiveSyntaxTaskListSameRowsFromRowDataPayloadEnvelope tokenTable width
    tokenCount sourceBoundary sourceCount targetBoundary targetCount
    (compactAdditiveSyntaxTaskListSameRowDataOfGraph tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount hgraph)

theorem
    compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount hgraph) <=
      compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
        hgraph := by
  simpa only [compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph,
    compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope] using
    compactAdditiveSyntaxTaskListSameRowsFromRowDataExplicitHybridCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount hgraph.1
      (compactAdditiveSyntaxTaskListSameRowDataOfGraph tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount hgraph)

/-! ## Removing row-data dependence by a finite public envelope -/

def
    compactAdditiveSyntaxTaskListSameRowsTerminalStructuralPayloadEnvelopeOfValues
    (tokenTable width tokenCount sourceBoundary targetBoundary index
      sourceLeft sourceRight targetLeft targetRight : Nat) : Nat :=
  let valuation := extendValuation index sameRowsZeroValuation
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let sourceIndexTerm : ValuationTerm := &0
  let nextIndexTerm : ValuationTerm := ‘&0 + 1’
  let sourceLeftTerm := shortBinaryNumeralTerm sourceLeft
  let sourceRightTerm := shortBinaryNumeralTerm sourceRight
  let targetLeftTerm := shortBinaryNumeralTerm targetLeft
  let targetRightTerm := shortBinaryNumeralTerm targetRight
  let sourceLeftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm sourceBoundary) widthTerm sourceIndexTerm
    sourceLeftTerm
  let sourceRightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm sourceBoundary) widthTerm nextIndexTerm
    sourceRightTerm
  let targetLeftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary) widthTerm sourceIndexTerm
    targetLeftTerm
  let targetRightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary) widthTerm nextIndexTerm
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
      sourceIndexTerm targetLeftTerm
  let targetRightResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation (shortBinaryNumeralTerm targetBoundary) widthTerm
      nextIndexTerm targetRightTerm
  let rowResource :=
    compactAdditiveSyntaxTaskRowEqStructuralPayloadEnvelope valuation tokenTable
      width tokenCount sourceLeft sourceRight targetLeft targetRight
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

def
    compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelopeOfValues
    (tokenTable width tokenCount sourceBoundary targetBoundary index
      sourceLeft sourceRight targetLeft targetRight : Nat) : Nat :=
  let valuation := extendValuation index sameRowsZeroValuation
  let values : Fin 4 -> Nat :=
    ![targetRight, targetLeft, sourceRight, sourceLeft]
  explicitBoundedWitnessHybridStructuralPayloadEnvelope valuation tokenCount
    (compactAdditiveSyntaxTaskListSameRowsBranchTerminal tokenTable width
      tokenCount sourceBoundary targetBoundary)
    values
    (compactAdditiveSyntaxTaskListSameRowsTerminalStructuralPayloadEnvelopeOfValues
      tokenTable width tokenCount sourceBoundary targetBoundary index
      sourceLeft sourceRight targetLeft targetRight)

theorem
    compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope_eq_values
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveSyntaxTaskListSameRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) :
    compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary index data =
      compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelopeOfValues
        tokenTable width tokenCount sourceBoundary targetBoundary index
        data.sourceLeft data.sourceRight data.targetLeft data.targetRight := by
  rfl

private theorem member_le_sum_range
    (bound value : Nat) (f : Nat -> Nat) (hvalue : value <= bound) :
    f value <= (Finset.range (bound + 1)).sum f := by
  exact Finset.single_le_sum
    (fun candidate _ => Nat.zero_le (f candidate))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hvalue))

def compactAdditiveSyntaxTaskListSameRowsPublicFiniteBranchEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat) :
    Nat :=
  (Finset.range (tokenCount + 1)).sum fun sourceLeft =>
    (Finset.range (tokenCount + 1)).sum fun sourceRight =>
      (Finset.range (tokenCount + 1)).sum fun targetLeft =>
        (Finset.range (tokenCount + 1)).sum fun targetRight =>
          compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelopeOfValues
            tokenTable width tokenCount sourceBoundary targetBoundary index
            sourceLeft sourceRight targetLeft targetRight

theorem
    compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveSyntaxTaskListSameRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) :
    compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary index data <=
      compactAdditiveSyntaxTaskListSameRowsPublicFiniteBranchEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary index := by
  rw [
    compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope_eq_values]
  let resource :=
    compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelopeOfValues
      tokenTable width tokenCount sourceBoundary targetBoundary index
  have htargetRight := member_le_sum_range tokenCount data.targetRight
    (fun targetRight => resource data.sourceLeft data.sourceRight
      data.targetLeft targetRight) data.targetRight_le
  have htargetLeft := member_le_sum_range tokenCount data.targetLeft
    (fun targetLeft =>
      (Finset.range (tokenCount + 1)).sum fun targetRight =>
        resource data.sourceLeft data.sourceRight targetLeft targetRight)
    data.targetLeft_le
  have hsourceRight := member_le_sum_range tokenCount data.sourceRight
    (fun sourceRight =>
      (Finset.range (tokenCount + 1)).sum fun targetLeft =>
        (Finset.range (tokenCount + 1)).sum fun targetRight =>
          resource data.sourceLeft sourceRight targetLeft targetRight)
    data.sourceRight_le
  have hsourceLeft := member_le_sum_range tokenCount data.sourceLeft
    (fun sourceLeft =>
      (Finset.range (tokenCount + 1)).sum fun sourceRight =>
        (Finset.range (tokenCount + 1)).sum fun targetLeft =>
          (Finset.range (tokenCount + 1)).sum fun targetRight =>
            resource sourceLeft sourceRight targetLeft targetRight)
    data.sourceLeft_le
  unfold compactAdditiveSyntaxTaskListSameRowsPublicFiniteBranchEnvelope
  exact htargetRight.trans
    (htargetLeft.trans (hsourceRight.trans hsourceLeft))

def compactAdditiveSyntaxTaskListSameRowsPublicFiniteLeafPayloadResourceSum
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary :
      Nat) : Nat :=
  ∑ index : Fin sourceCount,
    compactAdditiveSyntaxTaskListSameRowsPublicFiniteBranchEnvelope tokenTable
      width tokenCount sourceBoundary targetBoundary index

theorem
    compactAdditiveSyntaxTaskListSameRowsBranchPayloadResourceSum_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    compactAdditiveSyntaxTaskListSameRowsBranchPayloadResourceSum tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary rows <=
      compactAdditiveSyntaxTaskListSameRowsPublicFiniteLeafPayloadResourceSum
        tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary := by
  unfold compactAdditiveSyntaxTaskListSameRowsBranchPayloadResourceSum
    compactAdditiveSyntaxTaskListSameRowsPublicFiniteLeafPayloadResourceSum
  exact Finset.sum_le_sum fun index _ =>
    compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount sourceBoundary targetBoundary index
      (rows index)

private theorem hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf
    (totalBound : Nat) (outerVariables : Finset Nat)
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    {small large : Nat} (hresource : small <= large) :
    forall bound,
      hybridBranchesUniformStructuralPayloadEnvelope totalBound outerVariables
          valuation body small bound <=
        hybridBranchesUniformStructuralPayloadEnvelope totalBound
          outerVariables valuation body large bound
  | 0 => by rfl
  | bound + 1 => by
      simp only [hybridBranchesUniformStructuralPayloadEnvelope]
      have hinduction :=
        hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf totalBound
          outerVariables valuation body hresource bound
      omega

def compactAdditiveSyntaxTaskListSameRowsBranchesPublicFiniteEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary :
      Nat) : Nat :=
  let body := compactAdditiveSyntaxTaskListSameRowsBody tokenTable width
    tokenCount sourceBoundary targetBoundary
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue sameRowsZeroValuation
    (shortBinaryNumeralTerm sourceCount)
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
    sameRowsZeroValuation body
    (compactAdditiveSyntaxTaskListSameRowsPublicFiniteLeafPayloadResourceSum
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary)
    bound

theorem
    compactAdditiveSyntaxTaskListSameRowsBranchesTransparentEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    compactAdditiveSyntaxTaskListSameRowsBranchesTransparentEnvelope tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary rows <=
      compactAdditiveSyntaxTaskListSameRowsBranchesPublicFiniteEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary := by
  unfold compactAdditiveSyntaxTaskListSameRowsBranchesTransparentEnvelope
    compactAdditiveSyntaxTaskListSameRowsBranchesPublicFiniteEnvelope
  exact hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf
    (termValue sameRowsZeroValuation (shortBinaryNumeralTerm sourceCount))
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm sourceCount))
      (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary)).freeVariables
    sameRowsZeroValuation
    (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
      sourceBoundary targetBoundary)
    (compactAdditiveSyntaxTaskListSameRowsBranchPayloadResourceSum_le_publicFinite
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows)
    (termValue sameRowsZeroValuation (shortBinaryNumeralTerm sourceCount))

def
    compactAdditiveSyntaxTaskListSameRowsPublicFiniteUniversalPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary :
      Nat) : Nat :=
  let body := compactAdditiveSyntaxTaskListSameRowsBody tokenTable width
    tokenCount sourceBoundary targetBoundary
  let boundTerm := shortBinaryNumeralTerm sourceCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables sameRowsZeroValuation
  let bound := termValue sameRowsZeroValuation boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (compactAdditiveSyntaxTaskListSameRowsBranchesPublicFiniteEnvelope
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift boundTerm) body
    (compileShiftedBoundEqualityPayloadResource sameRowsZeroValuation
      outerVariables boundTerm)
    branchResource

theorem
    compactAdditiveSyntaxTaskListSameRowsUniversalPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    compactAdditiveSyntaxTaskListSameRowsUniversalPayloadEnvelope tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary rows <=
      compactAdditiveSyntaxTaskListSameRowsPublicFiniteUniversalPayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary := by
  let body := compactAdditiveSyntaxTaskListSameRowsBody tokenTable width
    tokenCount sourceBoundary targetBoundary
  let boundTerm := shortBinaryNumeralTerm sourceCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables sameRowsZeroValuation
  let bound := termValue sameRowsZeroValuation boundTerm
  let oldCore :=
    compactAdditiveSyntaxTaskListSameRowsBranchesTransparentEnvelope tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary rows
  let newCore :=
    compactAdditiveSyntaxTaskListSameRowsBranchesPublicFiniteEnvelope
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newCore
  let boundResource := compileShiftedBoundEqualityPayloadResource
    sameRowsZeroValuation outerVariables boundTerm
  have hcore : oldCore <= newCore := by
    exact
      compactAdditiveSyntaxTaskListSameRowsBranchesTransparentEnvelope_le_publicFinite
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows
  have hbranch : oldBranchResource <= newBranchResource :=
    contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldCore newCore hcore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift boundTerm) body
    boundResource oldBranchResource boundResource newBranchResource
    le_rfl hbranch
  simpa only [compactAdditiveSyntaxTaskListSameRowsUniversalPayloadEnvelope,
    compactAdditiveSyntaxTaskListSameRowsPublicFiniteUniversalPayloadEnvelope,
    body, boundTerm, outerFormula, outerVariables, Gamma, bound, oldCore,
    newCore, oldBranchResource, newBranchResource, boundResource] using htotal

def compactAdditiveSyntaxTaskListSameRowsPublicFinitePayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat) : Nat :=
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm sourceCount)”
  let universalFormula : ValuationFormula :=
    (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
      sourceBoundary targetBoundary).ballLT
        (shortBinaryNumeralTerm sourceCount)
  transparentHybridConjunctionPayloadEnvelope sameRowsZeroValuation
    countFormula universalFormula
    (compactAdditiveSyntaxTaskListSameRowsCountEqualityPayloadPolynomial
      sourceCount targetCount)
    (compactAdditiveSyntaxTaskListSameRowsPublicFiniteUniversalPayloadEnvelope
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary)

private theorem transparentHybridConjunctionPayloadEnvelope_mono_right
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    (leftResource : Nat) {small large : Nat} (hresource : small <= large) :
    transparentHybridConjunctionPayloadEnvelope valuation left right
        leftResource small <=
      transparentHybridConjunctionPayloadEnvelope valuation left right
        leftResource large := by
  unfold transparentHybridConjunctionPayloadEnvelope
  dsimp only
  omega

theorem
    compactAdditiveSyntaxTaskListSameRowsFromRowDataPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    compactAdditiveSyntaxTaskListSameRowsFromRowDataPayloadEnvelope tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary targetCount
        rows <=
      compactAdditiveSyntaxTaskListSameRowsPublicFinitePayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount := by
  unfold compactAdditiveSyntaxTaskListSameRowsFromRowDataPayloadEnvelope
    compactAdditiveSyntaxTaskListSameRowsPublicFinitePayloadEnvelope
  exact transparentHybridConjunctionPayloadEnvelope_mono_right _ _ _ _
    (compactAdditiveSyntaxTaskListSameRowsUniversalPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows)

theorem
    compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount) :
    compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
        hgraph <=
      compactAdditiveSyntaxTaskListSameRowsPublicFinitePayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount := by
  unfold compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope
  exact
    compactAdditiveSyntaxTaskListSameRowsFromRowDataPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount
      (compactAdditiveSyntaxTaskListSameRowDataOfGraph tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount hgraph)

#print axioms countEqualityCertificate_structuralPayloadBound_le_public
#print axioms
  compactAdditiveSyntaxTaskListSameRowsBranchCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveSyntaxTaskListSameRowsUniversalCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope_le_publicFinite
#print axioms
  compactAdditiveSyntaxTaskListSameRowsUniversalPayloadEnvelope_le_publicFinite
#print axioms
  compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope_le_publicFinite

end FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds
