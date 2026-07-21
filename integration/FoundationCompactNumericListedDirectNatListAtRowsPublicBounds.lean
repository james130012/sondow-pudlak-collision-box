import integration.FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveListHeaderPublicBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resource for one natural-list lookup

The strict index guard, two boundary entries, token cell, and two bounded
cursor witnesses are charged by proof-free transparent envelopes.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListAtRowsPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTokenCellValuationPublicBounds
open FoundationCompactNumericListedDirectAdditiveListHeaderPublicBounds

private abbrev natListAtZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation

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

def compactAdditiveNatListAtRowsIndexGuardPayloadPolynomial
    (count : Nat) (indexTerm : ValuationTerm) : Nat :=
  compilePositiveRelationPayloadPolynomial natListAtZeroValuation
    Language.ORing.Rel.lt
    ![indexTerm, shortBinaryNumeralTerm count]

theorem strictCertificate_structuralPayloadBound_le_public
    (count : Nat) (indexTerm : ValuationTerm)
    (hindexClosed : indexTerm.freeVariables ⊆ {0})
    (hstrict : termValue natListAtZeroValuation indexTerm < count) :
    hybridFormulaStructuralPayloadBound
        (strictCertificate indexTerm (shortBinaryNumeralTerm count) (by
          simpa [termValue_shortBinaryNumeralTerm] using hstrict)) ≤
      compactAdditiveNatListAtRowsIndexGuardPayloadPolynomial count
        indexTerm := by
  have hcount : (shortBinaryNumeralTerm count).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    natListAtZeroValuation Language.ORing.Rel.lt
    ![indexTerm, shortBinaryNumeralTerm count] hindexClosed hcount
  change compilePositiveRelationPayloadResource natListAtZeroValuation
      Language.ORing.Rel.lt ![indexTerm, shortBinaryNumeralTerm count] ≤ _
  exact hpublic

def compactAdditiveNatListAtRowsAtValuationIndexTerminalPayloadEnvelope
    (tokenTable width tokenCount boundaryTable value : Nat)
    (indexTerm : ValuationTerm)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable (termValue natListAtZeroValuation indexTerm) value) : Nat :=
  let successorTerm := natListAtSuccessorTermAtValuationIndex indexTerm
  let leftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount) indexTerm
    (shortBinaryNumeralTerm data.left)
  let rightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount) successorTerm
    (shortBinaryNumeralTerm data.right)
  let cellFormula := compactAdditiveTokenCellClosedFormula tokenTable width
    tokenCount data.left value data.right
  let leftResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      natListAtZeroValuation (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) indexTerm
      (shortBinaryNumeralTerm data.left)
  let rightResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      natListAtZeroValuation (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) successorTerm
      (shortBinaryNumeralTerm data.right)
  let cellResource := compactAdditiveTokenCellClosedStructuralPayloadPolynomial
    tokenTable width tokenCount data.left value data.right
  let rightCellResource := transparentHybridConjunctionPayloadEnvelope
    natListAtZeroValuation rightFormula cellFormula rightResource cellResource
  transparentHybridConjunctionPayloadEnvelope natListAtZeroValuation
    leftFormula (rightFormula ⋏ cellFormula) leftResource rightCellResource

def compactAdditiveNatListAtRowsAtValuationIndexWitnessPayloadEnvelope
    (tokenTable width tokenCount boundaryTable value : Nat)
    (indexTerm : ValuationTerm)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable (termValue natListAtZeroValuation indexTerm) value) : Nat :=
  let values : Fin 2 -> Nat := ![data.right, data.left]
  explicitBoundedWitnessHybridStructuralPayloadEnvelope natListAtZeroValuation
    tokenCount
    (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
      tokenCount boundaryTable value indexTerm)
    values
    (compactAdditiveNatListAtRowsAtValuationIndexTerminalPayloadEnvelope
      tokenTable width tokenCount boundaryTable value indexTerm data)

theorem
    compactAdditiveNatListAtRowsAtValuationIndexWitnessCertificate_structuralPayloadBound_le_public
    (tokenTable width tokenCount boundaryTable value : Nat)
    (indexTerm : ValuationTerm)
    (hindexClosed : indexTerm.freeVariables ⊆ {0})
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable (termValue natListAtZeroValuation indexTerm) value) :
    let values : Fin 2 -> Nat := ![data.right, data.left]
    let terminalParts :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          natListAtZeroValuation (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount) indexTerm
          (shortBinaryNumeralTerm data.left) (by
            simpa [termValue_shortBinaryNumeralTerm] using data.left_entry))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryAtValuationExplicitHybridCertificate
            natListAtZeroValuation (shortBinaryNumeralTerm boundaryTable)
            (shortBinaryNumeralTerm tokenCount)
            (natListAtSuccessorTermAtValuationIndex indexTerm)
            (shortBinaryNumeralTerm data.right) (by
              simpa [natListAtSuccessorTermAtValuationIndex,
                termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
                termValue_arithmeticOne] using data.right_entry))
          (compactAdditiveTokenCellExplicitHybridCertificate tokenTable width
            tokenCount data.left value data.right data.cell))
    let terminal : CheckedHybridValuationBoundedFormulaCertificate
        natListAtZeroValuation
        ((compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
          tokenCount boundaryTable value indexTerm) ⇜
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
          (compactAdditiveNatListAtRowsTerminalAtValuationIndex_substitution_alignment
            tokenTable width tokenCount boundaryTable value data.left
            data.right indexTerm).symm) terminalParts
    hybridFormulaStructuralPayloadBound
        (buildExplicitBoundedWitnessHybridCertificate tokenCount
          (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
            tokenCount boundaryTable value indexTerm)
          values (by
            intro coordinate
            fin_cases coordinate
            · exact data.right_le
            · exact data.left_le)
          terminal) ≤
      compactAdditiveNatListAtRowsAtValuationIndexWitnessPayloadEnvelope
        tokenTable width tokenCount boundaryTable value indexTerm data := by
  dsimp only
  let values : Fin 2 -> Nat := ![data.right, data.left]
  let successorTerm := natListAtSuccessorTermAtValuationIndex indexTerm
  let leftCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      natListAtZeroValuation (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) indexTerm
      (shortBinaryNumeralTerm data.left) (by
        simpa [termValue_shortBinaryNumeralTerm] using data.left_entry)
  let rightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      natListAtZeroValuation (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) successorTerm
      (shortBinaryNumeralTerm data.right) (by
        simpa [successorTerm, natListAtSuccessorTermAtValuationIndex,
          termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne] using data.right_entry)
  let cellCertificate := compactAdditiveTokenCellExplicitHybridCertificate
    tokenTable width tokenCount data.left value data.right data.cell
  have hsuccessorClosed : successorTerm.freeVariables ⊆ {0} := by
    dsimp only [successorTerm, natListAtSuccessorTermAtValuationIndex]
    rw [arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
      arithmeticOneTerm_freeVariables_eq_empty]
    simpa using hindexClosed
  have hboundary :
      (shortBinaryNumeralTerm boundaryTable).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable
  have hcount : (shortBinaryNumeralTerm tokenCount).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hleftTerm : (shortBinaryNumeralTerm data.left).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty data.left
  have hrightTerm : (shortBinaryNumeralTerm data.right).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty data.right
  have hleftResource :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      natListAtZeroValuation (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) indexTerm
      (shortBinaryNumeralTerm data.left) hboundary hcount hindexClosed
      hleftTerm (by
        simpa [termValue_shortBinaryNumeralTerm] using data.left_entry)
  have hrightResource :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      natListAtZeroValuation (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) successorTerm
      (shortBinaryNumeralTerm data.right) hboundary hcount hsuccessorClosed
      hrightTerm (by
        simpa [successorTerm, natListAtSuccessorTermAtValuationIndex,
          termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne] using data.right_entry)
  have hcellResource :=
    compactAdditiveTokenCellExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount data.left value data.right data.cell
  let rightCell := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    rightCertificate cellCertificate
  have hrightCell := transparentHybridConjunctionPayloadBound_le
    rightCertificate cellCertificate _ _ hrightResource hcellResource
  let terminalParts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    leftCertificate rightCell
  have hterminalParts := transparentHybridConjunctionPayloadBound_le
    leftCertificate rightCell _ _ hleftResource hrightCell
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm data.right,
          shortBinaryNumeralTerm data.left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminal : CheckedHybridValuationBoundedFormulaCertificate
      natListAtZeroValuation
      ((compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
        tokenCount boundaryTable value indexTerm) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveNatListAtRowsTerminalAtValuationIndex_substitution_alignment
          tokenTable width tokenCount boundaryTable value data.left data.right
          indexTerm).symm) terminalParts
  have hterminal : hybridFormulaStructuralPayloadBound terminal ≤
      compactAdditiveNatListAtRowsAtValuationIndexTerminalPayloadEnvelope
        tokenTable width tokenCount boundaryTable value indexTerm data := by
    unfold compactAdditiveNatListAtRowsAtValuationIndexTerminalPayloadEnvelope
    simpa only [hybridFormulaStructuralPayloadBound, successorTerm,
      leftCertificate, rightCertificate, cellCertificate, rightCell,
      terminalParts, terminal] using hterminalParts
  have hinstalled :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount
      (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
        tokenCount boundaryTable value indexTerm)
      values (by
        intro coordinate
        fin_cases coordinate
        · exact data.right_le
        · exact data.left_le)
      terminal
      (compactAdditiveNatListAtRowsAtValuationIndexTerminalPayloadEnvelope
        tokenTable width tokenCount boundaryTable value indexTerm data)
      hterminal
  simpa only [compactAdditiveNatListAtRowsAtValuationIndexWitnessPayloadEnvelope,
    values, terminal] using hinstalled

def compactAdditiveNatListAtRowsAtValuationIndexPayloadEnvelope
    (tokenTable width tokenCount boundaryTable count value : Nat)
    (indexTerm : ValuationTerm)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable (termValue natListAtZeroValuation indexTerm) value) : Nat :=
  let guardFormula : ValuationFormula :=
    “!!indexTerm < !!(shortBinaryNumeralTerm count)”
  let witnessFormula :=
    compactAdditiveNatListAtRowsWitnessBodyAtValuationIndex tokenTable width
      tokenCount boundaryTable value indexTerm
  transparentHybridConjunctionPayloadEnvelope natListAtZeroValuation
    guardFormula witnessFormula
    (compactAdditiveNatListAtRowsIndexGuardPayloadPolynomial count indexTerm)
    (compactAdditiveNatListAtRowsAtValuationIndexWitnessPayloadEnvelope
      tokenTable width tokenCount boundaryTable value indexTerm data)

theorem
    compactAdditiveNatListAtRowsAtValuationIndexExplicitFormulaCertificateFromRowData_structuralPayloadBound_le_public
    (tokenTable width tokenCount boundaryTable count value : Nat)
    (indexTerm : ValuationTerm)
    (hindexClosed : indexTerm.freeVariables ⊆ {0})
    (hindex : termValue natListAtZeroValuation indexTerm < count)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable (termValue natListAtZeroValuation indexTerm) value) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAtRowsAtValuationIndexExplicitFormulaCertificateFromRowData
          tokenTable width tokenCount boundaryTable count
          (termValue natListAtZeroValuation indexTerm) value indexTerm rfl
          hindex data) ≤
      compactAdditiveNatListAtRowsAtValuationIndexPayloadEnvelope tokenTable
        width tokenCount boundaryTable count value indexTerm data := by
  let values : Fin 2 -> Nat := ![data.right, data.left]
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        natListAtZeroValuation (shortBinaryNumeralTerm boundaryTable)
        (shortBinaryNumeralTerm tokenCount) indexTerm
        (shortBinaryNumeralTerm data.left) (by
          simpa [termValue_shortBinaryNumeralTerm] using data.left_entry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          natListAtZeroValuation (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (natListAtSuccessorTermAtValuationIndex indexTerm)
          (shortBinaryNumeralTerm data.right) (by
            simpa [natListAtSuccessorTermAtValuationIndex,
              termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
              termValue_arithmeticOne] using data.right_entry))
        (compactAdditiveTokenCellExplicitHybridCertificate tokenTable width
          tokenCount data.left value data.right data.cell))
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm data.right,
          shortBinaryNumeralTerm data.left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminal : CheckedHybridValuationBoundedFormulaCertificate
      natListAtZeroValuation
      ((compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
        tokenCount boundaryTable value indexTerm) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveNatListAtRowsTerminalAtValuationIndex_substitution_alignment
          tokenTable width tokenCount boundaryTable value data.left data.right
          indexTerm).symm) terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate tokenCount
    (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
      tokenCount boundaryTable value indexTerm)
    values (by
      intro coordinate
      fin_cases coordinate
      · exact data.right_le
      · exact data.left_le) terminal
  let body : CheckedHybridValuationBoundedFormulaCertificate
      natListAtZeroValuation
      (compactAdditiveNatListAtRowsWitnessBodyAtValuationIndex tokenTable width
        tokenCount boundaryTable value indexTerm) :=
    .cast (by
      rw [explicitBoundedWitnessFormula_two_eq]
      rfl) installed
  let guard := strictCertificate indexTerm (shortBinaryNumeralTerm count) (by
    simpa [termValue_shortBinaryNumeralTerm] using hindex)
  have hguardResource :=
    strictCertificate_structuralPayloadBound_le_public count indexTerm
      hindexClosed hindex
  have hinstalledResource :=
    compactAdditiveNatListAtRowsAtValuationIndexWitnessCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount boundaryTable value indexTerm hindexClosed
      data
  have hbodyResource : hybridFormulaStructuralPayloadBound body ≤
      compactAdditiveNatListAtRowsAtValuationIndexWitnessPayloadEnvelope
        tokenTable width tokenCount boundaryTable value indexTerm data := by
    simpa only [body, hybridFormulaStructuralPayloadBound, installed,
      terminal, values, terminalParts] using hinstalledResource
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    guard body
  have hparts := transparentHybridConjunctionPayloadBound_le
    guard body _ _ hguardResource hbodyResource
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction guard body) ≤ _
  unfold compactAdditiveNatListAtRowsAtValuationIndexPayloadEnvelope
  simpa only [guard, body, parts] using hparts

theorem
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateFromRowData_structuralPayloadBound_le_public
    (tokenTable width tokenCount boundaryTable count value : Nat)
    (indexTerm : ValuationTerm)
    (hindexClosed : indexTerm.freeVariables ⊆ {0})
    (hindex : termValue natListAtZeroValuation indexTerm < count)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable (termValue natListAtZeroValuation indexTerm) value) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateFromRowData
          tokenTable width tokenCount boundaryTable count
          (termValue natListAtZeroValuation indexTerm) value indexTerm rfl
          hindex data) ≤
      compactAdditiveNatListAtRowsAtValuationIndexPayloadEnvelope tokenTable
        width tokenCount boundaryTable count value indexTerm data := by
  simpa only [
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateFromRowData,
    hybridFormulaStructuralPayloadBound] using
    compactAdditiveNatListAtRowsAtValuationIndexExplicitFormulaCertificateFromRowData_structuralPayloadBound_le_public
      tokenTable width tokenCount boundaryTable count value indexTerm
      hindexClosed hindex data

noncomputable def
    compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope
    (tokenTable width tokenCount boundaryTable count index value : Nat)
    (indexTerm : ValuationTerm)
    (hindexValue : termValue natListAtZeroValuation indexTerm = index)
    (hrows : CompactAdditiveNatListAtRows tokenTable width tokenCount
      boundaryTable count index value) : Nat :=
  let data := compactAdditiveNatListAtRowDataOfGraph tokenTable width
    tokenCount boundaryTable count index value hrows
  let normalizedData : CompactAdditiveNatListAtRowData tokenTable width
      tokenCount boundaryTable (termValue natListAtZeroValuation indexTerm)
      value := hindexValue.symm ▸ data
  compactAdditiveNatListAtRowsAtValuationIndexPayloadEnvelope tokenTable width
    tokenCount boundaryTable count value indexTerm normalizedData

theorem
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tokenTable width tokenCount boundaryTable count index value : Nat)
    (indexTerm : ValuationTerm)
    (hindexClosed : indexTerm.freeVariables ⊆ {0})
    (hindexValue : termValue natListAtZeroValuation indexTerm = index)
    (hrows : CompactAdditiveNatListAtRows tokenTable width tokenCount
      boundaryTable count index value) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
          tokenTable width tokenCount boundaryTable count index value indexTerm
          hindexValue hrows) ≤
      compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope tokenTable
        width tokenCount boundaryTable count index value indexTerm hindexValue
        hrows := by
  subst index
  simpa only [
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph,
    compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope] using
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateFromRowData_structuralPayloadBound_le_public
      tokenTable width tokenCount boundaryTable count value indexTerm
      hindexClosed hrows.1
      (compactAdditiveNatListAtRowDataOfGraph tokenTable width tokenCount
        boundaryTable count (termValue natListAtZeroValuation indexTerm) value
        hrows)

#print axioms
  compactAdditiveNatListAtRowsAtValuationIndexWitnessCertificate_structuralPayloadBound_le_public
#print axioms
  compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectNatListAtRowsPublicBounds
