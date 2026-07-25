import integration.FoundationCompactNumericListedDirectNatListAtRowsPublicBounds
import integration.FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds

/-!
# Fixed child resources for a natural-list row lookup terminal

The terminal certificate has two fixed-width boundary-table entries and one
closed additive token cell.  This file bounds those three actual certificate
leaves by fixed resources while preserving only the two conjunction shells.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListAtRowsTerminalFixedChildrenBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexAtomicGuardBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexScalarBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsPublicBounds
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation

private theorem arithmeticAddTerm_eq_func_terminal
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd_terminal
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func_terminal]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne_terminal (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

def compactAdditiveNatListAtRowsTerminalFixedWidthScale
    (boundaryTable tokenCount : Nat)
    (indexTerm : ValuationTerm)
    (left right : Nat) : Nat :=
  let successorTerm := natListAtSuccessorTermAtValuationIndex indexTerm
  fixedWidthOpenIndexAtomicCoordinateScale atRowsZeroValuation
      (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) indexTerm
      (shortBinaryNumeralTerm left) +
    fixedWidthOpenIndexAtomicCoordinateScale atRowsZeroValuation
      (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) successorTerm
      (shortBinaryNumeralTerm right)

def compactAdditiveNatListAtRowsTerminalFixedChildrenPayloadEnvelope
    (tokenTable width tokenCount boundaryTable value numericBound bitBound :
      Nat)
    (indexTerm : ValuationTerm)
    (left right : Nat) : Nat :=
  let successorTerm := natListAtSuccessorTermAtValuationIndex indexTerm
  let leftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount) indexTerm
    (shortBinaryNumeralTerm left)
  let rightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount) successorTerm
    (shortBinaryNumeralTerm right)
  let cellFormula := compactAdditiveTokenCellClosedFormula tokenTable width
    tokenCount left value right
  let entryScale := compactAdditiveNatListAtRowsTerminalFixedWidthScale
    boundaryTable tokenCount indexTerm left right
  let entryResource :=
    compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
      entryScale
  let cellResource :=
    additiveTokenCellFullyUniformPayloadPolynomial numericBound bitBound
  let rightCellResource := transparentHybridConjunctionPayloadEnvelope
    atRowsZeroValuation rightFormula cellFormula entryResource cellResource
  transparentHybridConjunctionPayloadEnvelope atRowsZeroValuation leftFormula
    (rightFormula ⋏ cellFormula) entryResource rightCellResource

theorem
    compactAdditiveNatListAtRowsTerminalCertificate_structuralPayloadBound_le_fixedChildren
    (tokenTable width tokenCount boundaryTable value numericBound bitBound :
      Nat)
    (indexTerm : ValuationTerm)
    (hindexClosed : indexTerm.freeVariables ⊆ {0})
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable (termValue atRowsZeroValuation indexTerm) value)
    (hwidthValue : width <= numericBound)
    (hleftValue : data.left <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hleftSize : Nat.size data.left <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hrightSize : Nat.size data.right <= bitBound) :
    let values : Fin 2 -> Nat := ![data.right, data.left]
    let terminalParts :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount) indexTerm
          (shortBinaryNumeralTerm data.left) (by
            simpa [termValue_shortBinaryNumeralTerm] using data.left_entry))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryAtValuationExplicitHybridCertificate
            atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
            (shortBinaryNumeralTerm tokenCount)
            (natListAtSuccessorTermAtValuationIndex indexTerm)
            (shortBinaryNumeralTerm data.right) (by
              simpa [natListAtSuccessorTermAtValuationIndex,
                termValue_shortBinaryNumeralTerm,
                termValue_arithmeticAdd_terminal,
                termValue_arithmeticOne_terminal] using data.right_entry))
          (compactAdditiveTokenCellExplicitHybridCertificate tokenTable width
            tokenCount data.left value data.right data.cell))
    let terminal : CheckedHybridValuationBoundedFormulaCertificate
        atRowsZeroValuation
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
    hybridFormulaStructuralPayloadBound terminal <=
      compactAdditiveNatListAtRowsTerminalFixedChildrenPayloadEnvelope
        tokenTable width tokenCount boundaryTable value numericBound bitBound
        indexTerm data.left data.right := by
  dsimp only
  let values : Fin 2 -> Nat := ![data.right, data.left]
  let successorTerm := natListAtSuccessorTermAtValuationIndex indexTerm
  let leftCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) indexTerm
      (shortBinaryNumeralTerm data.left) (by
        simpa [termValue_shortBinaryNumeralTerm] using data.left_entry)
  let rightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) successorTerm
      (shortBinaryNumeralTerm data.right) (by
        simpa [successorTerm, natListAtSuccessorTermAtValuationIndex,
          termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd_terminal,
          termValue_arithmeticOne_terminal] using data.right_entry)
  let cellCertificate := compactAdditiveTokenCellExplicitHybridCertificate
    tokenTable width tokenCount data.left value data.right data.cell
  let entryScale := compactAdditiveNatListAtRowsTerminalFixedWidthScale
    boundaryTable tokenCount indexTerm data.left data.right
  have hsuccessorClosed : successorTerm.freeVariables ⊆ {0} :=
    natListAtSuccessorTermAtValuationIndex_freeVariables_subset indexTerm
      hindexClosed
  have hboundary :=
    shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable
  have hcount := shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hleftTerm := shortBinaryNumeralTerm_freeVariables_eq_empty data.left
  have hrightTerm := shortBinaryNumeralTerm_freeVariables_eq_empty data.right
  have hleftScale :
      fixedWidthOpenIndexAtomicCoordinateScale atRowsZeroValuation
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount) indexTerm
          (shortBinaryNumeralTerm data.left) <= entryScale := by
    dsimp only [entryScale,
      compactAdditiveNatListAtRowsTerminalFixedWidthScale]
    omega
  have hrightScale :
      fixedWidthOpenIndexAtomicCoordinateScale atRowsZeroValuation
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount) successorTerm
          (shortBinaryNumeralTerm data.right) <= entryScale := by
    dsimp only [entryScale,
      compactAdditiveNatListAtRowsTerminalFixedWidthScale, successorTerm]
    omega
  have hleftOpen :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) indexTerm
      (shortBinaryNumeralTerm data.left) hboundary hcount hindexClosed
      hleftTerm (by
        simpa [termValue_shortBinaryNumeralTerm] using data.left_entry)
  have hrightOpen :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) successorTerm
      (shortBinaryNumeralTerm data.right) hboundary hcount hsuccessorClosed
      hrightTerm (by
        simpa [successorTerm, natListAtSuccessorTermAtValuationIndex,
          termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd_terminal,
          termValue_arithmeticOne_terminal] using data.right_entry)
  have hleftFixed :=
    hleftOpen.trans
      (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fullyFixed
        atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
        (shortBinaryNumeralTerm tokenCount) indexTerm
        (shortBinaryNumeralTerm data.left) entryScale hleftScale hboundary
        hcount hindexClosed hleftTerm)
  have hrightFixed :=
    hrightOpen.trans
      (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fullyFixed
        atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
        (shortBinaryNumeralTerm tokenCount) successorTerm
        (shortBinaryNumeralTerm data.right) entryScale hrightScale hboundary
        hcount hsuccessorClosed hrightTerm)
  have hcellTerms : CompactAdditiveTokenCell
      (termValue atRowsZeroValuation (shortBinaryNumeralTerm tokenTable))
      (termValue atRowsZeroValuation (shortBinaryNumeralTerm width))
      (termValue atRowsZeroValuation (shortBinaryNumeralTerm tokenCount))
      (termValue atRowsZeroValuation (shortBinaryNumeralTerm data.left))
      (termValue atRowsZeroValuation (shortBinaryNumeralTerm value))
      (termValue atRowsZeroValuation
        (shortBinaryNumeralTerm data.right)) := by
    simpa only [termValue_shortBinaryNumeralTerm] using data.cell
  have hcellFixed :
      hybridFormulaStructuralPayloadBound cellCertificate <=
        additiveTokenCellFullyUniformPayloadPolynomial numericBound bitBound := by
    change hybridFormulaStructuralPayloadBound
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm data.left)
          (shortBinaryNumeralTerm value)
          (shortBinaryNumeralTerm data.right) hcellTerms) <= _
    exact
      compactAdditiveTokenCellShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
        tokenTable width tokenCount data.left value data.right numericBound
        bitBound hwidthValue hleftValue htableSize hwidthSize htokenCountSize
        hleftSize hvalueSize hrightSize data.cell
  let rightCell := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    rightCertificate cellCertificate
  have hrightCell := transparentHybridConjunctionPayloadBound_le
    rightCertificate cellCertificate _ _ hrightFixed hcellFixed
  let terminalParts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    leftCertificate rightCell
  have hterminalParts := transparentHybridConjunctionPayloadBound_le
    leftCertificate rightCell _ _ hleftFixed hrightCell
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm data.right,
          shortBinaryNumeralTerm data.left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminal : CheckedHybridValuationBoundedFormulaCertificate
      atRowsZeroValuation
      ((compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
        tokenCount boundaryTable value indexTerm) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveNatListAtRowsTerminalAtValuationIndex_substitution_alignment
          tokenTable width tokenCount boundaryTable value data.left data.right
          indexTerm).symm) terminalParts
  unfold compactAdditiveNatListAtRowsTerminalFixedChildrenPayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound, successorTerm,
    leftCertificate, rightCertificate, cellCertificate, entryScale,
    rightCell, terminalParts, terminal] using hterminalParts

#print axioms
  compactAdditiveNatListAtRowsTerminalCertificate_structuralPayloadBound_le_fixedChildren

end FoundationCompactNumericListedDirectNatListAtRowsTerminalFixedChildrenBounds
