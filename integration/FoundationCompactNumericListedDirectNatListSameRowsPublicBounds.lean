import integration.FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAtomicRowEqualityPublicBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds

/-!
# Public structural resources for equal natural-list rows

Each row exposes four fixed-width table entries and one atomic-row equality.
The four bounded witnesses and the outer row universal are then charged by
proof-free transparent envelopes.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListSameRowsPublicBounds

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
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate

private abbrev sameRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate.zeroValuation

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

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

def compactAdditiveNatListSameRowsCountEqualityPayloadPolynomial
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
      compactAdditiveNatListSameRowsCountEqualityPayloadPolynomial
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
    compactAdditiveNatListSameRowsCountEqualityPayloadPolynomial] using hpublic

def compactAdditiveNatListSameRowsTerminalStructuralPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListSameRowData
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

def compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListSameRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) : Nat :=
  let valuation := extendValuation index sameRowsZeroValuation
  let values : Fin 4 -> Nat :=
    ![data.targetRight, data.targetLeft,
      data.sourceRight, data.sourceLeft]
  explicitBoundedWitnessHybridStructuralPayloadEnvelope valuation tokenCount
    (compactAdditiveNatListSameRowsBranchTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary)
    values
    (compactAdditiveNatListSameRowsTerminalStructuralPayloadEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary index data)

theorem
    compactAdditiveNatListSameRowsBranchCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListSameRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListSameRowsBranchCertificate tokenTable width
          tokenCount sourceBoundary targetBoundary index data) <=
      compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope tokenTable
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
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      widthTerm sourceLeftTerm sourceRightTerm targetLeftTerm targetRightTerm
      (by
        simpa only [widthTerm, sourceLeftTerm, sourceRightTerm,
          targetLeftTerm, targetRightTerm,
          termValue_shortBinaryNumeralTerm] using data.row_eq)
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
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_of_closed
      valuation (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width) widthTerm sourceLeftTerm sourceRightTerm
      targetLeftTerm targetRightTerm
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable)
      (shortBinaryNumeralTerm_freeVariables_eq_empty width)
      hsourceLeftTerm htargetLeftTerm
      (by
        simpa only [widthTerm, sourceLeftTerm, sourceRightTerm,
          targetLeftTerm, targetRightTerm,
          termValue_shortBinaryNumeralTerm] using data.row_eq)
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
      ((compactAdditiveNatListSameRowsBranchTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary) ⇜
          fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveNatListSameRowsBranchTerminal_substitution_alignment
          tokenTable width tokenCount sourceBoundary targetBoundary
          data.sourceLeft data.sourceRight data.targetLeft
          data.targetRight).symm) terminalParts
  have hterminal : hybridFormulaStructuralPayloadBound terminal <=
      compactAdditiveNatListSameRowsTerminalStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary index
        data := by
    simpa only [terminal, hybridFormulaStructuralPayloadBound,
      compactAdditiveNatListSameRowsTerminalStructuralPayloadEnvelope,
      valuation, widthTerm, sourceIndexTerm, nextIndexTerm,
      sourceLeftTerm, sourceRightTerm, targetLeftTerm, targetRightTerm,
      sourceLeftCertificate, sourceRightCertificate, targetLeftCertificate,
      targetRightCertificate, rowCertificate, targetRightRow,
      targetLeftTail, sourceRightTail, terminalParts] using hterminalParts
  have hinstalled :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount
      (compactAdditiveNatListSameRowsBranchTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary)
      values (by
        intro coordinate
        fin_cases coordinate
        · exact data.targetRight_le
        · exact data.targetLeft_le
        · exact data.sourceRight_le
        · exact data.sourceLeft_le)
      terminal
      (compactAdditiveNatListSameRowsTerminalStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary index data)
      hterminal
  simpa only [compactAdditiveNatListSameRowsBranchCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope,
    valuation, values, terminal, terminalParts, targetRightRow,
    targetLeftTail, sourceRightTail, sourceLeftCertificate,
    sourceRightCertificate, targetLeftCertificate, targetRightCertificate,
    rowCertificate] using hinstalled

noncomputable def compactAdditiveNatListSameRowsBranchPayloadResourceSum
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) : Nat :=
  ∑ index : Fin sourceCount,
    compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope tokenTable
      width tokenCount sourceBoundary targetBoundary index (rows index)

theorem
    compactAdditiveNatListSameRowsDirectHybridBranchesAtCount_leafPayloadBound
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    HybridBranchesLeafPayloadBound
      (compactAdditiveNatListSameRowsBranchPayloadResourceSum tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows)
      (compactAdditiveNatListSameRowsDirectHybridBranchesAtCount tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary rows) := by
  unfold compactAdditiveNatListSameRowsDirectHybridBranchesAtCount
  apply buildExplicitHybridUniversalBranches_leafPayloadBound
  intro index hindex
  let finiteIndex : Fin sourceCount := ⟨index, hindex⟩
  have hbranch :=
    compactAdditiveNatListSameRowsBranchCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary targetBoundary finiteIndex
      (rows finiteIndex)
  have hsum :
      compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope tokenTable
          width tokenCount sourceBoundary targetBoundary finiteIndex
          (rows finiteIndex) <=
        compactAdditiveNatListSameRowsBranchPayloadResourceSum tokenTable width
          tokenCount sourceBoundary sourceCount targetBoundary rows := by
    unfold compactAdditiveNatListSameRowsBranchPayloadResourceSum
    exact Finset.single_le_sum
      (fun (candidate : Fin sourceCount) _ => Nat.zero_le
        (compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope
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

theorem compactAdditiveNatListSameRowsDirectHybridBranches_leafPayloadBound
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    HybridBranchesLeafPayloadBound
      (compactAdditiveNatListSameRowsBranchPayloadResourceSum tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows)
      (compactAdditiveNatListSameRowsDirectHybridBranches tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows) := by
  unfold compactAdditiveNatListSameRowsDirectHybridBranches
  exact hybridBranchesLeafPayloadBound_transport
    (compactAdditiveNatListSameRowsShortNumeralBound_eq_sourceCount
      sourceCount).symm
    (compactAdditiveNatListSameRowsDirectHybridBranchesAtCount tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary rows)
    (compactAdditiveNatListSameRowsDirectHybridBranchesAtCount_leafPayloadBound
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows)

noncomputable def compactAdditiveNatListSameRowsBranchesTransparentEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) : Nat :=
  let body := compactAdditiveNatListSameRowsBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue sameRowsZeroValuation
    (shortBinaryNumeralTerm sourceCount)
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
    sameRowsZeroValuation body
    (compactAdditiveNatListSameRowsBranchPayloadResourceSum tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary rows)
    bound

theorem
    compactAdditiveNatListSameRowsBranchesStructuralPayloadEnvelope_le_transparent
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    let body := compactAdditiveNatListSameRowsBody tokenTable width tokenCount
      sourceBoundary targetBoundary
    let outerFormula := ∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body
    hybridBranchesStructuralPayloadEnvelope
        (termValue sameRowsZeroValuation (shortBinaryNumeralTerm sourceCount))
        outerFormula.freeVariables
        (compactAdditiveNatListSameRowsDirectHybridBranches tokenTable width
          tokenCount sourceBoundary sourceCount targetBoundary rows) <=
      compactAdditiveNatListSameRowsBranchesTransparentEnvelope tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary rows := by
  let body := compactAdditiveNatListSameRowsBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue sameRowsZeroValuation
    (shortBinaryNumeralTerm sourceCount)
  let branches := compactAdditiveNatListSameRowsDirectHybridBranches
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows
  have hleaves :=
    compactAdditiveNatListSameRowsDirectHybridBranches_leafPayloadBound
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows
  have hbound := hybridBranchesStructuralPayloadEnvelope_le_uniformEnvelope
    bound outerVariables
    (compactAdditiveNatListSameRowsBranchPayloadResourceSum tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary rows)
    branches hleaves
  simpa only [compactAdditiveNatListSameRowsBranchesTransparentEnvelope,
    body, outerFormula, outerVariables, bound, branches] using hbound

noncomputable def compactAdditiveNatListSameRowsUniversalPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) : Nat :=
  let body := compactAdditiveNatListSameRowsBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let boundTerm := shortBinaryNumeralTerm sourceCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables sameRowsZeroValuation
  let bound := termValue sameRowsZeroValuation boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (compactAdditiveNatListSameRowsBranchesTransparentEnvelope tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary rows)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift boundTerm) body
    (compileShiftedBoundEqualityPayloadResource sameRowsZeroValuation
      outerVariables boundTerm)
    branchResource

theorem
    compactAdditiveNatListSameRowsUniversalCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListSameRowsUniversalCertificate tokenTable width
          tokenCount sourceBoundary sourceCount targetBoundary rows) <=
      compactAdditiveNatListSameRowsUniversalPayloadEnvelope tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows := by
  let body := compactAdditiveNatListSameRowsBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let boundTerm := shortBinaryNumeralTerm sourceCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables sameRowsZeroValuation
  let bound := termValue sameRowsZeroValuation boundTerm
  let branches := compactAdditiveNatListSameRowsDirectHybridBranches
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows
  let oldBranchCore := hybridBranchesStructuralPayloadEnvelope
    bound outerVariables branches
  let newBranchCore := compactAdditiveNatListSameRowsBranchesTransparentEnvelope
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
      compactAdditiveNatListSameRowsBranchesStructuralPayloadEnvelope_le_transparent
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
  simpa only [compactAdditiveNatListSameRowsUniversalCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveNatListSameRowsUniversalPayloadEnvelope,
    body, boundTerm, outerFormula, outerVariables, Gamma, bound, branches,
    oldBranchCore, newBranchCore, oldBranchResource, newBranchResource,
    boundResource] using htotal

noncomputable def compactAdditiveNatListSameRowsFromRowDataPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) : Nat :=
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm sourceCount)”
  let universalFormula : ValuationFormula :=
    (compactAdditiveNatListSameRowsBody tokenTable width tokenCount
      sourceBoundary targetBoundary).ballLT
        (shortBinaryNumeralTerm sourceCount)
  transparentHybridConjunctionPayloadEnvelope sameRowsZeroValuation
    countFormula universalFormula
    (compactAdditiveNatListSameRowsCountEqualityPayloadPolynomial
      sourceCount targetCount)
    (compactAdditiveNatListSameRowsUniversalPayloadEnvelope tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary rows)

theorem
    compactAdditiveNatListSameRowsFromRowDataExplicitHybridCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (hcount : targetCount = sourceCount)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListSameRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListSameRowsFromRowDataExplicitHybridCertificate
          tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount hcount rows) <=
      compactAdditiveNatListSameRowsFromRowDataPayloadEnvelope tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
        rows := by
  let countCertificate := countEqualityCertificate sourceCount targetCount hcount
  let universalCertificate := compactAdditiveNatListSameRowsUniversalCertificate
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    countCertificate universalCertificate
  have hcountResource := countEqualityCertificate_structuralPayloadBound_le_public
    sourceCount targetCount hcount
  have huniversalResource :=
    compactAdditiveNatListSameRowsUniversalCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows
  have hparts := transparentHybridConjunctionPayloadBound_le
    countCertificate universalCertificate _ _
    hcountResource huniversalResource
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactAdditiveNatListSameRowsClosedFormula_alignment tokenTable width
          tokenCount sourceBoundary sourceCount targetBoundary
          targetCount).symm parts) <= _
  unfold compactAdditiveNatListSameRowsFromRowDataPayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound, countCertificate,
    universalCertificate, parts,
    compactAdditiveNatListSameRowsCountEqualityPayloadPolynomial] using hparts

noncomputable def compactAdditiveNatListSameRowsGraphPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (hgraph : CompactAdditiveNatListSameRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount) : Nat :=
  compactAdditiveNatListSameRowsFromRowDataPayloadEnvelope tokenTable width
    tokenCount sourceBoundary sourceCount targetBoundary targetCount
    (compactAdditiveNatListSameRowDataOfGraph tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount hgraph)

theorem
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (hgraph : CompactAdditiveNatListSameRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount hgraph) <=
      compactAdditiveNatListSameRowsGraphPayloadEnvelope tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
        hgraph := by
  simpa only [compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph,
    compactAdditiveNatListSameRowsGraphPayloadEnvelope] using
    compactAdditiveNatListSameRowsFromRowDataExplicitHybridCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount hgraph.1
      (compactAdditiveNatListSameRowDataOfGraph tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount hgraph)

#print axioms countEqualityCertificate_structuralPayloadBound_le_public
#print axioms
  compactAdditiveNatListSameRowsBranchCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveNatListSameRowsUniversalCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent

end FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
