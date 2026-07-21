import integration.FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAtomicRowEqualityPublicBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds

/-!
# Public structural resources for dropping fixed natural-list rows

Each retained row exposes four fixed-width table entries and one atomic-row
equality. The four bounded witnesses and the outer row universal are charged
by proof-free transparent envelopes.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds

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
open FoundationCompactNumericListedDirectNatListDropRows
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate

private abbrev dropRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation

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

@[simp] private theorem fixedNumeralTerm_freeVariables_eq_empty
    (value : Nat) :
    (fixedNumeralTerm value).freeVariables = ∅ := by
  unfold fixedNumeralTerm Semiterm.Operator.operator
  simp

def compactAdditiveNatListDropFixedNumeralRowsCountBoundPayloadPolynomial
    (consumed sourceCount : Nat) : Nat :=
  let args : Fin 2 -> ValuationTerm :=
    ![fixedNumeralTerm consumed, shortBinaryNumeralTerm sourceCount]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula := LO.FirstOrder.Semiformula.rel Language.LT.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables dropRowsZeroValuation
  compilePositiveRelationPayloadPolynomial
      dropRowsZeroValuation Language.Eq.eq args +
    compilePositiveRelationPayloadPolynomial
      dropRowsZeroValuation Language.ORing.Rel.lt args +
    weakeningFullAssemblyCost (insert equalityFormula Gamma) +
    weakeningFullAssemblyCost (insert strictFormula Gamma) +
    disjunctionFullAssemblyCost Gamma equalityFormula strictFormula

theorem closedFixedNumeralLeCertificate_structuralPayloadBound_le_public
    (consumed sourceCount : Nat) (hle : consumed ≤ sourceCount) :
    hybridFormulaStructuralPayloadBound
        (closedFixedNumeralLeCertificate consumed sourceCount hle) ≤
      compactAdditiveNatListDropFixedNumeralRowsCountBoundPayloadPolynomial
        consumed sourceCount := by
  let args : Fin 2 -> ValuationTerm :=
    ![fixedNumeralTerm consumed, shortBinaryNumeralTerm sourceCount]
  have hfirst : (args 0).freeVariables ⊆ {0} := by
    change (fixedNumeralTerm consumed).freeVariables ⊆ {0}
    rw [fixedNumeralTerm_freeVariables_eq_empty]
    simp
  have hsecond : (args 1).freeVariables ⊆ {0} := by
    change (shortBinaryNumeralTerm sourceCount).freeVariables ⊆ {0}
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hequality :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      dropRowsZeroValuation Language.Eq.eq args hfirst hsecond
  have hstrict :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      dropRowsZeroValuation Language.ORing.Rel.lt args hfirst hsecond
  by_cases heq : consumed = sourceCount
  · simp only [closedFixedNumeralLeCertificate]
    rw [dif_pos heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold compactAdditiveNatListDropFixedNumeralRowsCountBoundPayloadPolynomial
    dsimp only [args] at hequality hstrict ⊢
    simp only [dropRowsZeroValuation] at hequality hstrict ⊢
    omega
  · simp only [closedFixedNumeralLeCertificate]
    rw [dif_neg heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold compactAdditiveNatListDropFixedNumeralRowsCountBoundPayloadPolynomial
    dsimp only [args] at hequality hstrict ⊢
    simp only [dropRowsZeroValuation] at hequality hstrict ⊢
    omega

def compactAdditiveNatListDropFixedNumeralRowsCountEqualityPayloadPolynomial
    (sourceCount consumed targetCount : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial dropRowsZeroValuation
    Language.Eq.eq
    ![shortBinaryNumeralTerm sourceCount,
      ‘!!(fixedNumeralTerm consumed) + !!(shortBinaryNumeralTerm targetCount)’]

theorem closedFixedNumeralAddEqCertificate_structuralPayloadBound_le_public
    (sourceCount consumed targetCount : Nat)
    (heq : sourceCount = consumed + targetCount) :
    hybridFormulaStructuralPayloadBound
        (closedFixedNumeralAddEqCertificate sourceCount consumed targetCount heq) ≤
      compactAdditiveNatListDropFixedNumeralRowsCountEqualityPayloadPolynomial
        sourceCount consumed targetCount := by
  have hfirst :
      (shortBinaryNumeralTerm sourceCount).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hsecond :
      (‘!!(fixedNumeralTerm consumed) +
        !!(shortBinaryNumeralTerm targetCount)’ : ValuationTerm).freeVariables ⊆ {0} := by
    rw [arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
      fixedNumeralTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    dropRowsZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm sourceCount,
      ‘!!(fixedNumeralTerm consumed) + !!(shortBinaryNumeralTerm targetCount)’]
    hfirst hsecond
  simpa only [closedFixedNumeralAddEqCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveNatListDropFixedNumeralRowsCountEqualityPayloadPolynomial] using hpublic

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

@[simp] private theorem termValue_fixedNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (fixedNumeralTerm value) = value := by
  unfold termValue fixedNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘ (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) =
        (![] : Fin 0 -> Nat) by
      funext index
      exact Fin.elim0 index]
  simp

def compactAdditiveNatListDropFixedNumeralRowsTerminalStructuralPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed index : Nat)
    (data : CompactAdditiveNatListDropRowData tokenTable width tokenCount
      sourceBoundary targetBoundary consumed index) : Nat :=
  let valuation := extendValuation index dropRowsZeroValuation
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let sourceIndexTerm : ValuationTerm := ‘!!(fixedNumeralTerm consumed) + &0’
  let sourceNextTerm : ValuationTerm :=
    ‘(!!(fixedNumeralTerm consumed) + &0) + 1’
  let targetIndexTerm : ValuationTerm := &0
  let targetNextTerm : ValuationTerm := ‘&0 + 1’
  let sourceLeftTerm := shortBinaryNumeralTerm data.sourceLeft
  let sourceRightTerm := shortBinaryNumeralTerm data.sourceRight
  let targetLeftTerm := shortBinaryNumeralTerm data.targetLeft
  let targetRightTerm := shortBinaryNumeralTerm data.targetRight
  let sourceLeftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm sourceBoundary) widthTerm sourceIndexTerm
    sourceLeftTerm
  let sourceRightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm sourceBoundary) widthTerm sourceNextTerm
    sourceRightTerm
  let targetLeftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary) widthTerm targetIndexTerm
    targetLeftTerm
  let targetRightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary) widthTerm targetNextTerm
    targetRightTerm
  let rowFormula := compactAdditiveAtomicRowEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    widthTerm sourceLeftTerm sourceRightTerm targetLeftTerm targetRightTerm
  let sourceLeftResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation (shortBinaryNumeralTerm sourceBoundary) widthTerm
      sourceIndexTerm sourceLeftTerm
  let sourceRightResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation (shortBinaryNumeralTerm sourceBoundary) widthTerm
      sourceNextTerm sourceRightTerm
  let targetLeftResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation (shortBinaryNumeralTerm targetBoundary) widthTerm
      targetIndexTerm targetLeftTerm
  let targetRightResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation (shortBinaryNumeralTerm targetBoundary) widthTerm
      targetNextTerm targetRightTerm
  let rowResource :=
    compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      widthTerm sourceLeftTerm sourceRightTerm targetLeftTerm targetRightTerm
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

def compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed index : Nat)
    (data : CompactAdditiveNatListDropRowData tokenTable width tokenCount
      sourceBoundary targetBoundary consumed index) : Nat :=
  let valuation := extendValuation index dropRowsZeroValuation
  let values : Fin 4 -> Nat :=
    ![data.targetRight, data.targetLeft, data.sourceRight, data.sourceLeft]
  explicitBoundedWitnessHybridStructuralPayloadEnvelope valuation tokenCount
    (compactAdditiveNatListDropFixedNumeralRowsBranchTerminal tokenTable width
      tokenCount sourceBoundary targetBoundary consumed)
    values
    (compactAdditiveNatListDropFixedNumeralRowsTerminalStructuralPayloadEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index data)

theorem
    compactAdditiveNatListDropFixedNumeralRowsBranchCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed index : Nat)
    (data : CompactAdditiveNatListDropRowData tokenTable width tokenCount
      sourceBoundary targetBoundary consumed index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListDropFixedNumeralRowsBranchCertificate tokenTable width
          tokenCount sourceBoundary targetBoundary consumed index data) ≤
      compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelope tokenTable
        width tokenCount sourceBoundary targetBoundary consumed index data := by
  let valuation := extendValuation index dropRowsZeroValuation
  let values : Fin 4 -> Nat :=
    ![data.targetRight, data.targetLeft, data.sourceRight, data.sourceLeft]
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let sourceIndexTerm : ValuationTerm := ‘!!(fixedNumeralTerm consumed) + &0’
  let sourceNextTerm : ValuationTerm :=
    ‘(!!(fixedNumeralTerm consumed) + &0) + 1’
  let targetIndexTerm : ValuationTerm := &0
  let targetNextTerm : ValuationTerm := ‘&0 + 1’
  let sourceLeftTerm := shortBinaryNumeralTerm data.sourceLeft
  let sourceRightTerm := shortBinaryNumeralTerm data.sourceRight
  let targetLeftTerm := shortBinaryNumeralTerm data.targetLeft
  let targetRightTerm := shortBinaryNumeralTerm data.targetRight
  let sourceLeftCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm sourceBoundary) widthTerm sourceIndexTerm
      sourceLeftTerm (by
        simpa [valuation, widthTerm, sourceIndexTerm, sourceLeftTerm,
          dropRowsZeroValuation, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_fixedNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.sourceLeft_entry)
  let sourceRightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm sourceBoundary) widthTerm sourceNextTerm
      sourceRightTerm (by
        simpa [valuation, widthTerm, sourceNextTerm, sourceRightTerm,
          dropRowsZeroValuation, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne,
          termValue_fixedNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.sourceRight_entry)
  let targetLeftCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm targetBoundary) widthTerm targetIndexTerm
      targetLeftTerm (by
        simpa [valuation, widthTerm, targetIndexTerm, targetLeftTerm,
          dropRowsZeroValuation, termValue_shortBinaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.targetLeft_entry)
  let targetRightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm targetBoundary) widthTerm targetNextTerm
      targetRightTerm (by
        simpa [valuation, widthTerm, targetNextTerm, targetRightTerm,
          dropRowsZeroValuation, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.targetRight_entry)
  let rowCertificate :=
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      widthTerm sourceLeftTerm sourceRightTerm targetLeftTerm targetRightTerm
      (by
        simpa only [widthTerm, sourceLeftTerm, sourceRightTerm,
          targetLeftTerm, targetRightTerm, termValue_shortBinaryNumeralTerm]
          using data.row_eq)
  have hsourceIndex : sourceIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [sourceIndexTerm]
    rw [arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
      fixedNumeralTerm_freeVariables_eq_empty]
    simp
  have hsourceNext : sourceNextTerm.freeVariables ⊆ {0} := by
    dsimp only [sourceNextTerm]
    rw [arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
      arithmeticOneTerm_freeVariables_eq_empty, arithmeticAddTerm_eq_func,
      binaryFunctionTerm_freeVariables, fixedNumeralTerm_freeVariables_eq_empty]
    simp
  have htargetIndex : targetIndexTerm.freeVariables ⊆ {0} := by
    simp [targetIndexTerm]
  have htargetNext : targetNextTerm.freeVariables ⊆ {0} := by
    dsimp only [targetNextTerm]
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
          dropRowsZeroValuation, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_fixedNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.sourceLeft_entry)
  have hsourceRight :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation (shortBinaryNumeralTerm sourceBoundary) widthTerm
      sourceNextTerm sourceRightTerm hsourceBoundary hwidthTerm
      hsourceNext hsourceRightTerm (by
        simpa [valuation, widthTerm, sourceNextTerm, sourceRightTerm,
          dropRowsZeroValuation, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne,
          termValue_fixedNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.sourceRight_entry)
  have htargetLeft :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation (shortBinaryNumeralTerm targetBoundary) widthTerm
      targetIndexTerm targetLeftTerm htargetBoundary hwidthTerm
      htargetIndex htargetLeftTerm (by
        simpa [valuation, widthTerm, targetIndexTerm, targetLeftTerm,
          dropRowsZeroValuation, termValue_shortBinaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.targetLeft_entry)
  have htargetRight :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation (shortBinaryNumeralTerm targetBoundary) widthTerm
      targetNextTerm targetRightTerm htargetBoundary hwidthTerm
      htargetNext htargetRightTerm (by
        simpa [valuation, widthTerm, targetNextTerm, targetRightTerm,
          dropRowsZeroValuation, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.targetRight_entry)
  have hrow :=
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_of_closed
      valuation (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width) widthTerm sourceLeftTerm sourceRightTerm
      targetLeftTerm targetRightTerm
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable)
      (shortBinaryNumeralTerm_freeVariables_eq_empty width)
      hsourceLeftTerm htargetLeftTerm
      (by
        simpa only [widthTerm, sourceLeftTerm, sourceRightTerm,
          targetLeftTerm, targetRightTerm, termValue_shortBinaryNumeralTerm]
          using data.row_eq)
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
        ![targetRightTerm, targetLeftTerm, sourceRightTerm, sourceLeftTerm] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminal : CheckedHybridValuationBoundedFormulaCertificate valuation
      ((compactAdditiveNatListDropFixedNumeralRowsBranchTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary consumed) ⇜
          fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveNatListDropFixedNumeralRowsBranchTerminal_substitution_alignment
          tokenTable width tokenCount sourceBoundary targetBoundary
          data.sourceLeft data.sourceRight data.targetLeft data.targetRight
          consumed).symm) terminalParts
  have hterminal : hybridFormulaStructuralPayloadBound terminal ≤
      compactAdditiveNatListDropFixedNumeralRowsTerminalStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary consumed index data := by
    simpa only [terminal, hybridFormulaStructuralPayloadBound,
      compactAdditiveNatListDropFixedNumeralRowsTerminalStructuralPayloadEnvelope,
      valuation, widthTerm, sourceIndexTerm, sourceNextTerm,
      targetIndexTerm, targetNextTerm, sourceLeftTerm, sourceRightTerm,
      targetLeftTerm, targetRightTerm, sourceLeftCertificate,
      sourceRightCertificate, targetLeftCertificate, targetRightCertificate,
      rowCertificate, targetRightRow, targetLeftTail, sourceRightTail,
      terminalParts] using hterminalParts
  have hinstalled :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount
      (compactAdditiveNatListDropFixedNumeralRowsBranchTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary consumed)
      values (by
        intro coordinate
        fin_cases coordinate
        · exact data.targetRight_le
        · exact data.targetLeft_le
        · exact data.sourceRight_le
        · exact data.sourceLeft_le)
      terminal
      (compactAdditiveNatListDropFixedNumeralRowsTerminalStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary consumed index data)
      hterminal
  simpa only [compactAdditiveNatListDropFixedNumeralRowsBranchCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelope,
    valuation, values, terminal, terminalParts, targetRightRow,
    targetLeftTail, sourceRightTail, sourceLeftCertificate,
    sourceRightCertificate, targetLeftCertificate, targetRightCertificate,
    rowCertificate] using hinstalled

noncomputable def compactAdditiveNatListDropFixedNumeralRowsBranchPayloadResourceSum
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed : Nat)
    (rows : (index : Fin targetCount) -> CompactAdditiveNatListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index) : Nat :=
  ∑ index : Fin targetCount,
    compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index
      (rows index)

theorem
    compactAdditiveNatListDropFixedNumeralRowsDirectHybridBranchesAtCount_leafPayloadBound
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed : Nat)
    (rows : (index : Fin targetCount) -> CompactAdditiveNatListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index) :
    HybridBranchesLeafPayloadBound
      (compactAdditiveNatListDropFixedNumeralRowsBranchPayloadResourceSum
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed rows)
      (compactAdditiveNatListDropFixedNumeralRowsDirectHybridBranchesAtCount
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed rows) := by
  unfold compactAdditiveNatListDropFixedNumeralRowsDirectHybridBranchesAtCount
  apply buildExplicitHybridUniversalBranches_leafPayloadBound
  intro index hindex
  let finiteIndex : Fin targetCount := ⟨index, hindex⟩
  have hbranch :=
    compactAdditiveNatListDropFixedNumeralRowsBranchCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary targetBoundary consumed
      finiteIndex (rows finiteIndex)
  have hsum :
      compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary consumed
          finiteIndex (rows finiteIndex) ≤
        compactAdditiveNatListDropFixedNumeralRowsBranchPayloadResourceSum
          tokenTable width tokenCount sourceBoundary targetBoundary targetCount
          consumed rows := by
    unfold compactAdditiveNatListDropFixedNumeralRowsBranchPayloadResourceSum
    exact Finset.single_le_sum
      (fun (candidate : Fin targetCount) _ => Nat.zero_le
        (compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary consumed
          candidate (rows candidate)))
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

theorem compactAdditiveNatListDropFixedNumeralRowsDirectHybridBranches_leafPayloadBound
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed : Nat)
    (rows : (index : Fin targetCount) -> CompactAdditiveNatListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index) :
    HybridBranchesLeafPayloadBound
      (compactAdditiveNatListDropFixedNumeralRowsBranchPayloadResourceSum
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed rows)
      (compactAdditiveNatListDropFixedNumeralRowsDirectHybridBranches tokenTable
        width tokenCount sourceBoundary targetBoundary targetCount consumed rows) := by
  unfold compactAdditiveNatListDropFixedNumeralRowsDirectHybridBranches
  exact hybridBranchesLeafPayloadBound_transport
    (compactAdditiveNatListDropFixedNumeralRowsShortNumeralBound_eq_targetCount
      targetCount).symm
    (compactAdditiveNatListDropFixedNumeralRowsDirectHybridBranchesAtCount
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed rows)
    (compactAdditiveNatListDropFixedNumeralRowsDirectHybridBranchesAtCount_leafPayloadBound
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed rows)

noncomputable def compactAdditiveNatListDropFixedNumeralRowsBranchesTransparentEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed : Nat)
    (rows : (index : Fin targetCount) -> CompactAdditiveNatListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index) : Nat :=
  let body := compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
    tokenCount sourceBoundary targetBoundary consumed
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm targetCount)) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue dropRowsZeroValuation
    (shortBinaryNumeralTerm targetCount)
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
    dropRowsZeroValuation body
    (compactAdditiveNatListDropFixedNumeralRowsBranchPayloadResourceSum
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed rows)
    bound

theorem
    compactAdditiveNatListDropFixedNumeralRowsBranchesStructuralPayloadEnvelope_le_transparent
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed : Nat)
    (rows : (index : Fin targetCount) -> CompactAdditiveNatListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index) :
    let body := compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary consumed
    let outerFormula := ∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm targetCount)) body
    hybridBranchesStructuralPayloadEnvelope
        (termValue dropRowsZeroValuation
          (shortBinaryNumeralTerm targetCount))
        outerFormula.freeVariables
        (compactAdditiveNatListDropFixedNumeralRowsDirectHybridBranches
          tokenTable width tokenCount sourceBoundary targetBoundary targetCount
          consumed rows) ≤
      compactAdditiveNatListDropFixedNumeralRowsBranchesTransparentEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed rows := by
  let body := compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
    tokenCount sourceBoundary targetBoundary consumed
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm targetCount)) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue dropRowsZeroValuation
    (shortBinaryNumeralTerm targetCount)
  let branches := compactAdditiveNatListDropFixedNumeralRowsDirectHybridBranches
    tokenTable width tokenCount sourceBoundary targetBoundary targetCount
    consumed rows
  have hleaves :=
    compactAdditiveNatListDropFixedNumeralRowsDirectHybridBranches_leafPayloadBound
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed rows
  have hbound := hybridBranchesStructuralPayloadEnvelope_le_uniformEnvelope
    bound outerVariables
    (compactAdditiveNatListDropFixedNumeralRowsBranchPayloadResourceSum
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed rows)
    branches hleaves
  simpa only [
    compactAdditiveNatListDropFixedNumeralRowsBranchesTransparentEnvelope,
    body, outerFormula, outerVariables, bound, branches] using hbound

noncomputable def compactAdditiveNatListDropFixedNumeralRowsUniversalPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed : Nat)
    (rows : (index : Fin targetCount) -> CompactAdditiveNatListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index) : Nat :=
  let body := compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
    tokenCount sourceBoundary targetBoundary consumed
  let boundTerm := shortBinaryNumeralTerm targetCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables dropRowsZeroValuation
  let bound := termValue dropRowsZeroValuation boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (compactAdditiveNatListDropFixedNumeralRowsBranchesTransparentEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed rows)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift boundTerm) body
    (compileShiftedBoundEqualityPayloadResource dropRowsZeroValuation
      outerVariables boundTerm)
    branchResource

theorem
    compactAdditiveNatListDropFixedNumeralRowsUniversalCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed : Nat)
    (rows : (index : Fin targetCount) -> CompactAdditiveNatListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListDropFixedNumeralRowsUniversalCertificate
          tokenTable width tokenCount sourceBoundary targetBoundary targetCount
          consumed rows) ≤
      compactAdditiveNatListDropFixedNumeralRowsUniversalPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed rows := by
  let body := compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
    tokenCount sourceBoundary targetBoundary consumed
  let boundTerm := shortBinaryNumeralTerm targetCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables dropRowsZeroValuation
  let bound := termValue dropRowsZeroValuation boundTerm
  let branches := compactAdditiveNatListDropFixedNumeralRowsDirectHybridBranches
    tokenTable width tokenCount sourceBoundary targetBoundary targetCount
    consumed rows
  let oldBranchCore := hybridBranchesStructuralPayloadEnvelope
    bound outerVariables branches
  let newBranchCore :=
    compactAdditiveNatListDropFixedNumeralRowsBranchesTransparentEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed rows
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldBranchCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newBranchCore
  let boundResource := compileShiftedBoundEqualityPayloadResource
    dropRowsZeroValuation outerVariables boundTerm
  have hbranchCore : oldBranchCore ≤ newBranchCore := by
    dsimp only [oldBranchCore, newBranchCore, bound, branches,
      outerVariables, outerFormula, body, boundTerm]
    exact
      compactAdditiveNatListDropFixedNumeralRowsBranchesStructuralPayloadEnvelope_le_transparent
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed rows
  have hbranchResource : oldBranchResource ≤ newBranchResource :=
    contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldBranchCore newBranchCore hbranchCore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift boundTerm) body
    boundResource oldBranchResource boundResource newBranchResource
    le_rfl hbranchResource
  simpa only [compactAdditiveNatListDropFixedNumeralRowsUniversalCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveNatListDropFixedNumeralRowsUniversalPayloadEnvelope,
    body, boundTerm, outerFormula, outerVariables, Gamma, bound, branches,
    oldBranchCore, newBranchCore, oldBranchResource, newBranchResource,
    boundResource] using htotal

noncomputable def compactAdditiveNatListDropFixedNumeralRowsFromRowDataPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed : Nat)
    (rows : (index : Fin targetCount) -> CompactAdditiveNatListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index) : Nat :=
  let countBoundFormula : ValuationFormula :=
    “!!(fixedNumeralTerm consumed) ≤
      !!(shortBinaryNumeralTerm sourceCount)”
  let countEqualityFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sourceCount) =
      !!(fixedNumeralTerm consumed) +
        !!(shortBinaryNumeralTerm targetCount)”
  let universalFormula : ValuationFormula :=
    (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary consumed).ballLT
        (shortBinaryNumeralTerm targetCount)
  let equalityUniversalResource := transparentHybridConjunctionPayloadEnvelope
    dropRowsZeroValuation countEqualityFormula universalFormula
    (compactAdditiveNatListDropFixedNumeralRowsCountEqualityPayloadPolynomial
      sourceCount consumed targetCount)
    (compactAdditiveNatListDropFixedNumeralRowsUniversalPayloadEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed rows)
  transparentHybridConjunctionPayloadEnvelope dropRowsZeroValuation
    countBoundFormula (countEqualityFormula ⋏ universalFormula)
    (compactAdditiveNatListDropFixedNumeralRowsCountBoundPayloadPolynomial
      consumed sourceCount)
    equalityUniversalResource

theorem
    compactAdditiveNatListDropFixedNumeralRowsFromRowDataExplicitHybridCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed : Nat)
    (hbound : consumed ≤ sourceCount)
    (heq : sourceCount = consumed + targetCount)
    (rows : (index : Fin targetCount) -> CompactAdditiveNatListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListDropFixedNumeralRowsFromRowDataExplicitHybridCertificate
          tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
          targetCount consumed hbound heq rows) ≤
      compactAdditiveNatListDropFixedNumeralRowsFromRowDataPayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount consumed rows := by
  let countBoundCertificate :=
    closedFixedNumeralLeCertificate consumed sourceCount hbound
  let countEqualityCertificate :=
    closedFixedNumeralAddEqCertificate sourceCount consumed targetCount heq
  let universalCertificate :=
    compactAdditiveNatListDropFixedNumeralRowsUniversalCertificate tokenTable
      width tokenCount sourceBoundary targetBoundary targetCount consumed rows
  let equalityUniversalCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      countEqualityCertificate universalCertificate
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    countBoundCertificate equalityUniversalCertificate
  have hboundResource :=
    closedFixedNumeralLeCertificate_structuralPayloadBound_le_public
      consumed sourceCount hbound
  have hequalityResource :=
    closedFixedNumeralAddEqCertificate_structuralPayloadBound_le_public
      sourceCount consumed targetCount heq
  have huniversalResource :=
    compactAdditiveNatListDropFixedNumeralRowsUniversalCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed rows
  have hequalityUniversalResource := transparentHybridConjunctionPayloadBound_le
    countEqualityCertificate universalCertificate _ _
    hequalityResource huniversalResource
  have hparts := transparentHybridConjunctionPayloadBound_le
    countBoundCertificate equalityUniversalCertificate _ _
    hboundResource hequalityUniversalResource
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactAdditiveNatListDropFixedNumeralRowsClosedFormula_alignment
          tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
          targetCount consumed).symm parts) ≤ _
  unfold compactAdditiveNatListDropFixedNumeralRowsFromRowDataPayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound, countBoundCertificate,
    countEqualityCertificate, universalCertificate,
    equalityUniversalCertificate, parts] using hparts

noncomputable def compactAdditiveNatListDropFixedNumeralRowsGraphPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount consumed) : Nat :=
  compactAdditiveNatListDropFixedNumeralRowsFromRowDataPayloadEnvelope
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
    targetCount consumed
    (compactAdditiveNatListDropFixedNumeralRowDataOfGraph tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary targetCount consumed
      hgraph)

theorem
    compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount consumed) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
          targetCount consumed hgraph) ≤
      compactAdditiveNatListDropFixedNumeralRowsGraphPayloadEnvelope tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary targetCount
        consumed hgraph := by
  simpa only [
    compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph,
    compactAdditiveNatListDropFixedNumeralRowsGraphPayloadEnvelope] using
    compactAdditiveNatListDropFixedNumeralRowsFromRowDataExplicitHybridCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed hgraph.1 hgraph.2.1
      (compactAdditiveNatListDropFixedNumeralRowDataOfGraph tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
        consumed hgraph)

#print axioms closedFixedNumeralLeCertificate_structuralPayloadBound_le_public
#print axioms closedFixedNumeralAddEqCertificate_structuralPayloadBound_le_public
#print axioms
  compactAdditiveNatListDropFixedNumeralRowsBranchCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveNatListDropFixedNumeralRowsUniversalCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent

end FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
