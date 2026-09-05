import integration.FoundationCompactNumericListedDirectAdditiveTokenCellClosedValueTermFullyFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueTerminalSyntaxFixedBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTermCodeBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-!
# Fully fixed row terminal with exact index and value terms

The two boundary-table entries use term-code-bounded open-index compilers.
The token cell uses the exact closed value term.  The final ceiling depends
only on the common numeric and bit-width coordinates.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 120000

namespace FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueTerminalFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTermCodeBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds
open FoundationCompactNumericListedDirectAdditiveTokenCellClosedValueTermFullyFixedBounds
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsTerminalSyntaxFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueTerminalSyntaxFixedBounds
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

private abbrev atRowsValueZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation

private theorem binaryFunctionTerm_freeVariables_terminalValue
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiterm.func functionSymbol ![left, right]).freeVariables =
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

private theorem arithmeticAddTerm_freeVariables_terminalValue
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables
  exact binaryFunctionTerm_freeVariables_terminalValue Language.Add.add left
    right

private theorem arithmeticOneTerm_freeVariables_eq_empty_terminalValue :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem arithmeticAddTerm_eq_func_terminalValue
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd_terminalValue
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func_terminalValue]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne_terminalValue
    (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem fixedWidthEntryFormula_closed_terminalValue
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables = ∅)
    (hvalue : valueTerm.freeVariables = ∅) :
    (compactFixedWidthEntryAtValuationFormula tableTerm widthTerm indexTerm
      valueTerm).freeVariables = ∅ := by
  unfold compactFixedWidthEntryAtValuationFormula
  exact embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    compactFixedWidthEntryDef.val ![tableTerm, widthTerm, indexTerm, valueTerm]
      (by
        intro coordinate
        fin_cases coordinate
        · exact htable
        · exact hwidth
        · exact hindex
        · exact hvalue)

private theorem binaryFormulaCode_left_length_le_and_terminalValue
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_right_length_le_and_terminalValue
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

def natListAtRowsExactIndexCodeEnvelope (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitBound

def natListAtRowsExactSuccessorIndexCodeEnvelope (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (‘1’ : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add

def natListAtRowsExactIndexEntryPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexShortNumeralAtTermCodeBoundScale
      (natListAtRowsExactIndexCodeEnvelope bitBound) numericBound bitBound)

def natListAtRowsExactSuccessorEntryPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexShortNumeralAtTermCodeBoundScale
      (natListAtRowsExactSuccessorIndexCodeEnvelope bitBound) numericBound
      bitBound)

def natListAtRowsExactValueTerminalSyntaxResource (bitBound : Nat) : Nat :=
  natListAtRowsInstalledTerminalCodePolynomial bitBound + 1

def compactAdditiveNatListAtRowsExactValueTerminalFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource := natListAtRowsExactValueTerminalSyntaxResource bitBound
  let leftResource :=
    natListAtRowsExactIndexEntryPayloadPolynomial numericBound bitBound
  let rightResource :=
    natListAtRowsExactSuccessorEntryPayloadPolynomial numericBound bitBound
  let cellResource :=
    additiveTokenCellFullyUniformPayloadPolynomial numericBound bitBound
  hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
    (hybridConjunctionGeneralPayloadEnvelope syntaxResource rightResource
      cellResource)

theorem
    compactAdditiveNatListAtRowsExactValueTerminalCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount boundaryTable count index value numericBound
      bitBound : Nat)
    (indexTerm valueTerm : ValuationTerm)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable index value)
    (hindexValue : termValue atRowsValueZeroValuation indexTerm = index)
    (hvalueValue : termValue atRowsValueZeroValuation valueTerm = value)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hvalueClosed : valueTerm.freeVariables = ∅)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcountValue : count <= numericBound)
    (hindex : index < count)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hindexSize : Nat.size index <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <=
      natListAtRowsExactIndexCodeEnvelope bitBound)
    (hvalueCode : (binaryTermCode valueTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound) :
    let values : Fin 2 -> Nat := ![data.right, data.left]
    let terminalParts :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          atRowsValueZeroValuation (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount) indexTerm
          (shortBinaryNumeralTerm data.left) (by
            simpa [termValue_shortBinaryNumeralTerm, hindexValue] using
              data.left_entry))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryAtValuationExplicitHybridCertificate
            atRowsValueZeroValuation (shortBinaryNumeralTerm boundaryTable)
            (shortBinaryNumeralTerm tokenCount)
            (natListAtSuccessorTermAtValuationIndex indexTerm)
            (shortBinaryNumeralTerm data.right) (by
              simpa [natListAtSuccessorTermAtValuationIndex,
                termValue_shortBinaryNumeralTerm,
                termValue_arithmeticAdd_terminalValue,
                termValue_arithmeticOne_terminalValue, hindexValue] using
                  data.right_entry))
          (compactAdditiveTokenCellAtValuationExplicitHybridCertificateLocal
            atRowsValueZeroValuation
            (shortBinaryNumeralTerm tokenTable)
            (shortBinaryNumeralTerm width)
            (shortBinaryNumeralTerm tokenCount)
            (shortBinaryNumeralTerm data.left) valueTerm
            (shortBinaryNumeralTerm data.right) (by
              simpa [termValue_shortBinaryNumeralTerm, hvalueValue] using
                data.cell)))
    let terminal : CheckedHybridValuationBoundedFormulaCertificate
        atRowsValueZeroValuation
        ((compactAdditiveNatListAtRowsTerminalAtValuationIndexValue tokenTable
          width tokenCount boundaryTable indexTerm valueTerm) ⇜
          fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
      .cast (by
        have hvalueTerms :
            (fun coordinate : Fin 2 =>
              shortBinaryNumeralTerm (values coordinate)) =
              ![shortBinaryNumeralTerm data.right,
                shortBinaryNumeralTerm data.left] := by
          funext coordinate
          fin_cases coordinate <;> rfl
        rw [hvalueTerms]
        exact
          (compactAdditiveNatListAtRowsTerminalAtValuationIndexValue_substitution_alignment
            tokenTable width tokenCount boundaryTable data.left data.right
            indexTerm valueTerm).symm) terminalParts
    hybridFormulaStructuralPayloadBound terminal <=
      compactAdditiveNatListAtRowsExactValueTerminalFullyFixedPayloadPolynomial
        numericBound bitBound := by
  dsimp only
  let values : Fin 2 -> Nat := ![data.right, data.left]
  let successorTerm := natListAtSuccessorTermAtValuationIndex indexTerm
  let leftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount) indexTerm
    (shortBinaryNumeralTerm data.left)
  let rightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount) successorTerm
    (shortBinaryNumeralTerm data.right)
  let cellFormula := compactAdditiveTokenCellAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm data.left)
    valueTerm (shortBinaryNumeralTerm data.right)
  let leftCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      atRowsValueZeroValuation (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) indexTerm
      (shortBinaryNumeralTerm data.left) (by
        simpa [termValue_shortBinaryNumeralTerm, hindexValue] using
          data.left_entry)
  let rightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      atRowsValueZeroValuation (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) successorTerm
      (shortBinaryNumeralTerm data.right) (by
        simpa [successorTerm, natListAtSuccessorTermAtValuationIndex,
          termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd_terminalValue,
          termValue_arithmeticOne_terminalValue, hindexValue] using
            data.right_entry)
  have hcellTerms : CompactAdditiveTokenCell
      (termValue atRowsValueZeroValuation
        (shortBinaryNumeralTerm tokenTable))
      (termValue atRowsValueZeroValuation (shortBinaryNumeralTerm width))
      (termValue atRowsValueZeroValuation
        (shortBinaryNumeralTerm tokenCount))
      (termValue atRowsValueZeroValuation
        (shortBinaryNumeralTerm data.left))
      (termValue atRowsValueZeroValuation valueTerm)
      (termValue atRowsValueZeroValuation
        (shortBinaryNumeralTerm data.right)) := by
    simpa [termValue_shortBinaryNumeralTerm, hvalueValue] using data.cell
  let cellCertificate :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificateLocal
      atRowsValueZeroValuation (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm data.left) valueTerm
      (shortBinaryNumeralTerm data.right) hcellTerms
  let syntaxResource := natListAtRowsExactValueTerminalSyntaxResource bitBound
  let leftResource :=
    natListAtRowsExactIndexEntryPayloadPolynomial numericBound bitBound
  let rightResource :=
    natListAtRowsExactSuccessorEntryPayloadPolynomial numericBound bitBound
  let cellResource :=
    additiveTokenCellFullyUniformPayloadPolynomial numericBound bitBound
  have hleftSize : Nat.size data.left <= bitBound :=
    (Nat.size_le_size data.left_le).trans htokenCountSize
  have hrightSize : Nat.size data.right <= bitBound :=
    (Nat.size_le_size data.right_le).trans htokenCountSize
  have hindexNumeric : index <= numericBound :=
    (Nat.le_of_lt hindex).trans hcountValue
  have hsuccessorNumeric : index + 1 <= numericBound :=
    (Nat.succ_le_iff.mpr hindex).trans hcountValue
  have hsuccessorSize : Nat.size (index + 1) <= bitBound :=
    (Nat.size_le_size (Nat.succ_le_iff.mpr hindex)).trans hcountSize
  have hindexSubset : indexTerm.freeVariables ⊆ {0} := by
    rw [hindexClosed]
    exact Finset.empty_subset _
  have hsuccessorClosed : successorTerm.freeVariables = ∅ := by
    dsimp only [successorTerm]
    unfold natListAtSuccessorTermAtValuationIndex
    rw [arithmeticAddTerm_freeVariables_terminalValue, hindexClosed,
      arithmeticOneTerm_freeVariables_eq_empty_terminalValue]
    simp
  have hsuccessorSubset : successorTerm.freeVariables ⊆ {0} := by
    rw [hsuccessorClosed]
    exact Finset.empty_subset _
  have hsuccessorCode : (binaryTermCode successorTerm).length <=
      natListAtRowsExactSuccessorIndexCodeEnvelope bitBound := by
    have hraw := paAddTerm_code_length_le indexTerm (‘1’ : ValuationTerm)
    dsimp only [successorTerm]
    unfold natListAtSuccessorTermAtValuationIndex
    exact hraw.trans (by
      unfold natListAtRowsExactIndexCodeEnvelope at hindexCode
      unfold natListAtRowsExactSuccessorIndexCodeEnvelope
      omega)
  have hleft : hybridFormulaStructuralPayloadBound leftCertificate <=
      leftResource := by
    simpa only [leftCertificate, leftResource,
      natListAtRowsExactIndexEntryPayloadPolynomial] using
      compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_termCodeBound
        atRowsValueZeroValuation boundaryTable tokenCount data.left indexTerm
        (natListAtRowsExactIndexCodeEnvelope bitBound) numericBound bitBound
        htokenCountValue (by simpa [hindexValue] using hindexNumeric)
        (by simp [atRowsValueZeroValuation]) hboundarySize htokenCountSize
        (by simpa [hindexValue] using hindexSize) hleftSize hindexCode
        hindexSubset (by simpa [hindexValue] using data.left_entry)
  have hright : hybridFormulaStructuralPayloadBound rightCertificate <=
      rightResource := by
    simpa only [rightCertificate, rightResource,
      natListAtRowsExactSuccessorEntryPayloadPolynomial] using
      compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_termCodeBound
        atRowsValueZeroValuation boundaryTable tokenCount data.right
        successorTerm (natListAtRowsExactSuccessorIndexCodeEnvelope bitBound)
        numericBound bitBound htokenCountValue (by
          simpa [successorTerm, natListAtSuccessorTermAtValuationIndex,
            termValue_arithmeticAdd_terminalValue,
            termValue_arithmeticOne_terminalValue, hindexValue] using
              hsuccessorNumeric)
        (by simp [atRowsValueZeroValuation]) hboundarySize htokenCountSize
        (by
          simpa [successorTerm, natListAtSuccessorTermAtValuationIndex,
            termValue_arithmeticAdd_terminalValue,
            termValue_arithmeticOne_terminalValue, hindexValue] using
              hsuccessorSize)
        hrightSize hsuccessorCode hsuccessorSubset (by
          simpa [successorTerm, natListAtSuccessorTermAtValuationIndex,
            termValue_arithmeticAdd_terminalValue,
            termValue_arithmeticOne_terminalValue, hindexValue] using
              data.right_entry)
  have hcell : hybridFormulaStructuralPayloadBound cellCertificate <=
      cellResource := by
    simpa only [cellCertificate, cellResource] using
      compactAdditiveNatListAtRowsValueTokenCellCertificate_structuralPayloadBound_le_closedValueFixed
        tokenTable width tokenCount data.left data.right numericBound bitBound
        valueTerm hwidthValue (data.left_le.trans htokenCountValue) htableSize
        hwidthSize htokenCountSize hleftSize (by
          simpa [hvalueValue] using hvalueSize) hrightSize hvalueCode
        hvalueClosed hcellTerms
  have hleftClosed : leftFormula.freeVariables = ∅ := by
    exact fixedWidthEntryFormula_closed_terminalValue
      (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) indexTerm
      (shortBinaryNumeralTerm data.left)
      (shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable)
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount) hindexClosed
      (shortBinaryNumeralTerm_freeVariables_eq_empty data.left)
  have hrightClosed : rightFormula.freeVariables = ∅ := by
    exact fixedWidthEntryFormula_closed_terminalValue
      (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) successorTerm
      (shortBinaryNumeralTerm data.right)
      (shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable)
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
      hsuccessorClosed
      (shortBinaryNumeralTerm_freeVariables_eq_empty data.right)
  have hcellClosed : cellFormula.freeVariables = ∅ := by
    simpa only [cellFormula] using
      compactAdditiveTokenCellAtClosedValueTermFormula_freeVariables_eq_empty
        tokenTable width tokenCount data.left data.right valueTerm hvalueClosed
  have hwholeCodeRaw :=
    compactAdditiveNatListAtRowsInstalledTerminalAtValuationIndexValue_code_length_le_fixed
      tokenTable width tokenCount boundaryTable count index value bitBound
      indexTerm valueTerm data htableSize hwidthSize htokenCountSize
      hboundarySize hcountSize (by
        simpa only [natListAtRowsExactIndexCodeEnvelope] using hindexCode)
      hvalueCode
  have hvalueTerms :
      (fun coordinate : Fin 2 =>
        shortBinaryNumeralTerm (![data.right, data.left] coordinate)) =
        ![shortBinaryNumeralTerm data.right,
          shortBinaryNumeralTerm data.left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have halignment :=
    compactAdditiveNatListAtRowsTerminalAtValuationIndexValue_substitution_alignment
      tokenTable width tokenCount boundaryTable data.left data.right indexTerm
      valueTerm
  rw [hvalueTerms, halignment] at hwholeCodeRaw
  have hwholeCode :
      (binaryFormulaCode
        (leftFormula ⋏ (rightFormula ⋏ cellFormula))).length <=
        natListAtRowsInstalledTerminalCodePolynomial bitBound := by
    simpa only [leftFormula, rightFormula, cellFormula, successorTerm] using
      hwholeCodeRaw
  have hrightTailCode :
      (binaryFormulaCode (rightFormula ⋏ cellFormula)).length <=
        syntaxResource :=
    (binaryFormulaCode_right_length_le_and_terminalValue leftFormula
      (rightFormula ⋏ cellFormula)).trans (hwholeCode.trans (by
        unfold syntaxResource natListAtRowsExactValueTerminalSyntaxResource
        omega))
  have hleftCode : (binaryFormulaCode leftFormula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_and_terminalValue leftFormula
      (rightFormula ⋏ cellFormula)).trans (hwholeCode.trans (by
        unfold syntaxResource natListAtRowsExactValueTerminalSyntaxResource
        omega))
  have hrightCode :
      (binaryFormulaCode rightFormula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_and_terminalValue rightFormula
      cellFormula).trans hrightTailCode
  have hcellCode :
      (binaryFormulaCode cellFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_and_terminalValue rightFormula
      cellFormula).trans hrightTailCode
  have hsyntaxPositive : 1 <= syntaxResource := by
    unfold syntaxResource natListAtRowsExactValueTerminalSyntaxResource
    omega
  let rightCell := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    rightCertificate cellCertificate
  have hrightCellTransparent := transparentHybridConjunctionPayloadBound_le
    rightCertificate cellCertificate _ _ hright hcell
  have hrightCellGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      atRowsValueZeroValuation rightFormula cellFormula rightResource
      cellResource syntaxResource hsyntaxPositive hrightClosed hcellClosed
      hrightCode hcellCode hrightTailCode
  have hrightCell : hybridFormulaStructuralPayloadBound rightCell <=
      hybridConjunctionGeneralPayloadEnvelope syntaxResource rightResource
        cellResource :=
    hrightCellTransparent.trans hrightCellGeneral
  have hrightTailClosed :
      (rightFormula ⋏ cellFormula).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hrightClosed, hcellClosed]
    simp
  let terminalParts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    leftCertificate rightCell
  have hterminalTransparent := transparentHybridConjunctionPayloadBound_le
    leftCertificate rightCell _ _ hleft hrightCell
  have hterminalGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      atRowsValueZeroValuation leftFormula (rightFormula ⋏ cellFormula)
      leftResource
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource rightResource
        cellResource)
      syntaxResource hsyntaxPositive hleftClosed hrightTailClosed hleftCode
      hrightTailCode (hwholeCode.trans (by
        unfold syntaxResource natListAtRowsExactValueTerminalSyntaxResource
        omega))
  have hterminalParts := hterminalTransparent.trans hterminalGeneral
  let terminal : CheckedHybridValuationBoundedFormulaCertificate
      atRowsValueZeroValuation
      ((compactAdditiveNatListAtRowsTerminalAtValuationIndexValue tokenTable
        width tokenCount boundaryTable indexTerm valueTerm) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [show (fun coordinate : Fin 2 =>
          shortBinaryNumeralTerm (values coordinate)) =
          ![shortBinaryNumeralTerm data.right,
            shortBinaryNumeralTerm data.left] by
        funext coordinate
        fin_cases coordinate <;> rfl]
      exact halignment.symm) terminalParts
  unfold
    compactAdditiveNatListAtRowsExactValueTerminalFullyFixedPayloadPolynomial
  simpa only [hybridFormulaStructuralPayloadBound, successorTerm, leftFormula,
    rightFormula, cellFormula, leftCertificate, rightCertificate,
    cellCertificate, syntaxResource, leftResource, rightResource,
    cellResource, rightCell, terminalParts, values, terminal] using
      hterminalParts

#print axioms
  compactAdditiveNatListAtRowsExactValueTerminalCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueTerminalFullyFixedBounds
