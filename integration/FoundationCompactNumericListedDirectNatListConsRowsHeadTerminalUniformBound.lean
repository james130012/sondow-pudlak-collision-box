import integration.FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectFixedBounds
import integration.FoundationCompactPAFixedWidthEntryOpenIndexTermUniformCeilingBounds
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

/-!
# Uniform three-leaf terminal for natural-list cons rows

The head terminal contains two genuine boundary-table entries and one genuine
additive token cell.  This file keeps the native unary indices `0` and `1` and
removes both hidden cursor witnesses from the public payload bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 320000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsHeadTerminalUniformBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactPAFixedWidthEntryOpenIndexTermUniformCeilingBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectFixedBounds
open FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

private abbrev consHeadZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation

def consHeadNumeralTerm (value : Nat) : ValuationTerm :=
  Semiterm.Operator.operator (Semiterm.Operator.numeral ℒₒᵣ value) ![]

@[simp] theorem termValue_consHeadNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (consHeadNumeralTerm value) = value := by
  unfold termValue consHeadNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘ (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) =
        (![] : Fin 0 -> Nat) by
      funext coordinate
      exact Fin.elim0 coordinate]
  simp

theorem consHeadNumeralTerm_freeVariables_eq_empty
    (value : Nat) :
    (consHeadNumeralTerm value).freeVariables = ∅ := by
  simp [consHeadNumeralTerm, LO.FirstOrder.Semiterm.Operator.operator]

def natListConsHeadEntryResource
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtTermCoordinate numericBound bitBound
        (binaryTermCode indexTerm).length))

def natListConsHeadTerminalFormulaCodeEnvelope
    (numericBound bitBound : Nat) : Nat :=
  natListConsHeadEntryResource (consHeadNumeralTerm 0) numericBound bitBound +
    natListConsHeadEntryResource (consHeadNumeralTerm 1) numericBound bitBound +
    structuredListHeaderCellFormulaCodePolynomial bitBound +
    2 * (binaryNatCode 4).length + 1

def natListConsHeadTerminalPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (natListConsHeadTerminalFormulaCodeEnvelope numericBound bitBound)
    (natListConsHeadEntryResource (consHeadNumeralTerm 0) numericBound bitBound)
    (natListConsHeadEntryResource (consHeadNumeralTerm 1) numericBound bitBound)
    (additiveTokenCellFullyUniformPayloadPolynomial numericBound bitBound)

noncomputable def compactAdditiveNatListConsRowsHeadTerminalCertificate
    (tokenTable width tokenCount targetBoundary head : Nat)
    (data : CompactAdditiveNatListConsHeadData tokenTable width tokenCount
      targetBoundary head) :
    CheckedHybridValuationBoundedFormulaCertificate consHeadZeroValuation
      ((compactAdditiveNatListConsRowsHeadTerminal tokenTable width tokenCount
          targetBoundary head) ⇜
        fun coordinate : Fin 2 =>
          shortBinaryNumeralTerm (![data.targetRight, data.targetLeft]
            coordinate)) := by
  let parts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        consHeadZeroValuation (shortBinaryNumeralTerm targetBoundary)
        (shortBinaryNumeralTerm tokenCount) (consHeadNumeralTerm 0)
        (shortBinaryNumeralTerm data.targetLeft) (by
          simpa only [termValue_shortBinaryNumeralTerm,
            termValue_consHeadNumeralTerm] using data.targetLeft_entry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          consHeadZeroValuation (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount) (consHeadNumeralTerm 1)
          (shortBinaryNumeralTerm data.targetRight) (by
            simpa only [termValue_shortBinaryNumeralTerm,
              termValue_consHeadNumeralTerm] using data.targetRight_entry))
        (compactAdditiveTokenCellExplicitHybridCertificate tokenTable width
          tokenCount data.targetLeft head data.targetRight data.token_cell))
  exact CheckedHybridValuationBoundedFormulaCertificate.cast (by
    rw [show
      (fun coordinate : Fin 2 =>
        shortBinaryNumeralTerm
          (![data.targetRight, data.targetLeft] coordinate)) =
        ![shortBinaryNumeralTerm data.targetRight,
          shortBinaryNumeralTerm data.targetLeft] by
        funext coordinate
        fin_cases coordinate <;> rfl]
    exact
      (compactAdditiveNatListConsRowsHeadTerminal_substitution_alignment
        tokenTable width tokenCount targetBoundary head data.targetLeft
          data.targetRight).symm) parts

private theorem entryFormula_freeVariables_eq_empty
    (table width value : Nat) (indexTerm : ValuationTerm)
    (hindex : indexTerm.freeVariables = ∅) :
    (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
      indexTerm (shortBinaryNumeralTerm value)).freeVariables = ∅ := by
  unfold compactFixedWidthEntryAtValuationFormula
  exact embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    compactFixedWidthEntryDef.val
    ![shortBinaryNumeralTerm table, shortBinaryNumeralTerm width,
      indexTerm, shortBinaryNumeralTerm value] (by
        intro coordinate
        fin_cases coordinate
        · exact shortBinaryNumeralTerm_freeVariables_eq_empty table
        · exact shortBinaryNumeralTerm_freeVariables_eq_empty width
        · exact hindex
        · exact shortBinaryNumeralTerm_freeVariables_eq_empty value)

private theorem tokenCellClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount cursor value next : Nat) :
    (compactAdditiveTokenCellClosedFormula tokenTable width tokenCount cursor
      value next).freeVariables = ∅ := by
  unfold compactAdditiveTokenCellClosedFormula
  exact embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    compactAdditiveTokenCellDef.val
    ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm cursor,
      shortBinaryNumeralTerm value, shortBinaryNumeralTerm next] (by
        intro coordinate
        fin_cases coordinate <;>
          apply shortBinaryNumeralTerm_freeVariables_eq_empty)

theorem
    compactAdditiveNatListConsRowsHeadTerminalCertificate_payloadLength_le_uniform
    (tokenTable width tokenCount targetBoundary head numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hheadSize : Nat.size head <= bitBound)
    (data : CompactAdditiveNatListConsHeadData tokenTable width tokenCount
      targetBoundary head) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListConsRowsHeadTerminalCertificate tokenTable width
          tokenCount targetBoundary head data) <=
      natListConsHeadTerminalPayloadEnvelope numericBound bitBound := by
  let zeroTerm := consHeadNumeralTerm 0
  let oneTerm := consHeadNumeralTerm 1
  let leftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary)
    (shortBinaryNumeralTerm tokenCount) zeroTerm
    (shortBinaryNumeralTerm data.targetLeft)
  let rightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary)
    (shortBinaryNumeralTerm tokenCount) oneTerm
    (shortBinaryNumeralTerm data.targetRight)
  let cellFormula := compactAdditiveTokenCellClosedFormula tokenTable width
    tokenCount data.targetLeft head data.targetRight
  let leftCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      consHeadZeroValuation (shortBinaryNumeralTerm targetBoundary)
      (shortBinaryNumeralTerm tokenCount) zeroTerm
      (shortBinaryNumeralTerm data.targetLeft) (by
        simpa only [zeroTerm, termValue_shortBinaryNumeralTerm,
          termValue_consHeadNumeralTerm] using data.targetLeft_entry)
  let rightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      consHeadZeroValuation (shortBinaryNumeralTerm targetBoundary)
      (shortBinaryNumeralTerm tokenCount) oneTerm
      (shortBinaryNumeralTerm data.targetRight) (by
        simpa only [oneTerm, termValue_shortBinaryNumeralTerm,
          termValue_consHeadNumeralTerm] using data.targetRight_entry)
  let cellCertificate := compactAdditiveTokenCellExplicitHybridCertificate
    tokenTable width tokenCount data.targetLeft head data.targetRight
      data.token_cell
  let leftResource := natListConsHeadEntryResource zeroTerm numericBound bitBound
  let rightResource := natListConsHeadEntryResource oneTerm numericBound bitBound
  let cellResource :=
    additiveTokenCellFullyUniformPayloadPolynomial numericBound bitBound
  have hpositive : 1 <= tokenCount :=
    Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt data.token_cell.1)
  have hnumericPositive : 1 <= numericBound :=
    hpositive.trans htokenCountValue
  have hbitPositive : 1 <= bitBound :=
    (Nat.succ_le_iff.mpr (Nat.size_pos.mpr hpositive)).trans htokenCountSize
  have hleftSize : Nat.size data.targetLeft <= bitBound :=
    (Nat.size_le_size data.targetLeft_le).trans htokenCountSize
  have hrightSize : Nat.size data.targetRight <= bitBound :=
    (Nat.size_le_size data.targetRight_le).trans htokenCountSize
  have hleft :=
    compactFixedWidthEntryAtValuationOpenIndexShortNumeralsAtTermPayloadAndCode_le_uniform
      consHeadZeroValuation targetBoundary tokenCount data.targetLeft zeroTerm
      numericBound bitBound (binaryTermCode zeroTerm).length htokenCountValue
      (by simpa only [zeroTerm, termValue_consHeadNumeralTerm] using
        (Nat.zero_le numericBound))
      (Nat.zero_le numericBound) htargetBoundarySize htokenCountSize
      (by
        dsimp only [zeroTerm]
        rw [termValue_consHeadNumeralTerm]
        simpa [Nat.size] using (Nat.zero_le bitBound))
      hleftSize le_rfl (by
        rw [show zeroTerm.freeVariables = ∅ by
          exact consHeadNumeralTerm_freeVariables_eq_empty 0]
        simp) data.targetLeft_entry
  have hright :=
    compactFixedWidthEntryAtValuationOpenIndexShortNumeralsAtTermPayloadAndCode_le_uniform
      consHeadZeroValuation targetBoundary tokenCount data.targetRight oneTerm
      numericBound bitBound (binaryTermCode oneTerm).length htokenCountValue
      (by simpa only [oneTerm, termValue_consHeadNumeralTerm] using
        hnumericPositive)
      (Nat.zero_le numericBound) htargetBoundarySize htokenCountSize
      (by
        dsimp only [oneTerm]
        rw [termValue_consHeadNumeralTerm]
        simpa [Nat.size] using hbitPositive)
      hrightSize le_rfl (by
        rw [show oneTerm.freeVariables = ∅ by
          exact consHeadNumeralTerm_freeVariables_eq_empty 1]
        simp) data.targetRight_entry
  have hleftCertificate :
      hybridFormulaStructuralPayloadBound leftCertificate <= leftResource := by
    have hopen :=
      compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
        consHeadZeroValuation (shortBinaryNumeralTerm targetBoundary)
        (shortBinaryNumeralTerm tokenCount) zeroTerm
        (shortBinaryNumeralTerm data.targetLeft)
        (shortBinaryNumeralTerm_freeVariables_eq_empty targetBoundary)
        (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount) (by
          rw [show zeroTerm.freeVariables = ∅ by
            exact consHeadNumeralTerm_freeVariables_eq_empty 0]
          simp)
        (shortBinaryNumeralTerm_freeVariables_eq_empty data.targetLeft) (by
          simpa only [zeroTerm, termValue_shortBinaryNumeralTerm,
            termValue_consHeadNumeralTerm] using data.targetLeft_entry)
    exact hopen.trans (by
      simpa only [leftResource, natListConsHeadEntryResource] using hleft.1)
  have hrightCertificate :
      hybridFormulaStructuralPayloadBound rightCertificate <= rightResource := by
    have hopen :=
      compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
        consHeadZeroValuation (shortBinaryNumeralTerm targetBoundary)
        (shortBinaryNumeralTerm tokenCount) oneTerm
        (shortBinaryNumeralTerm data.targetRight)
        (shortBinaryNumeralTerm_freeVariables_eq_empty targetBoundary)
        (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount) (by
          rw [show oneTerm.freeVariables = ∅ by
            exact consHeadNumeralTerm_freeVariables_eq_empty 1]
          simp)
        (shortBinaryNumeralTerm_freeVariables_eq_empty data.targetRight) (by
          simpa only [oneTerm, termValue_shortBinaryNumeralTerm,
            termValue_consHeadNumeralTerm] using data.targetRight_entry)
    exact hopen.trans (by
      simpa only [rightResource, natListConsHeadEntryResource] using hright.1)
  have hcellCertificate :
      hybridFormulaStructuralPayloadBound cellCertificate <= cellResource := by
    change hybridFormulaStructuralPayloadBound
      (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm data.targetLeft)
        (shortBinaryNumeralTerm head)
        (shortBinaryNumeralTerm data.targetRight) (by
          simpa only [termValue_shortBinaryNumeralTerm] using
            data.token_cell)) <= cellResource
    simpa only [cellResource] using
      compactAdditiveTokenCellShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
        tokenTable width tokenCount data.targetLeft head data.targetRight
        numericBound bitBound hwidthValue
        (data.targetLeft_le.trans htokenCountValue) htableSize hwidthSize
        htokenCountSize hleftSize hheadSize hrightSize data.token_cell
  have hcellCode :
      (binaryFormulaCode cellFormula).length <=
        structuredListHeaderCellFormulaCodePolynomial bitBound := by
    simpa only [cellFormula] using
      compactAdditiveTokenCellClosedFormula_code_length_le_fixed tokenTable
        width tokenCount data.targetLeft head data.targetRight bitBound
        htableSize hwidthSize htokenCountSize hleftSize hheadSize hrightSize
  have hleftCode :
      (binaryFormulaCode leftFormula).length <= leftResource := by
    simpa only [leftFormula, leftResource, natListConsHeadEntryResource,
      zeroTerm] using hleft.2
  have hrightCode :
      (binaryFormulaCode rightFormula).length <= rightResource := by
    simpa only [rightFormula, rightResource, natListConsHeadEntryResource,
      oneTerm] using hright.2
  have htotalCode :
      (binaryFormulaCode
        (leftFormula ⋏ (rightFormula ⋏ cellFormula))).length <=
        natListConsHeadTerminalFormulaCodeEnvelope numericBound bitBound := by
    simp only [binaryFormulaCode, List.length_append] at *
    unfold natListConsHeadTerminalFormulaCodeEnvelope
    dsimp only [leftResource, rightResource, zeroTerm, oneTerm] at *
    omega
  have htotalClosed :
      (leftFormula ⋏ (rightFormula ⋏ cellFormula)).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      LO.FirstOrder.Semiformula.freeVariables_and]
    rw [show leftFormula.freeVariables = ∅ by
      exact entryFormula_freeVariables_eq_empty targetBoundary tokenCount
        data.targetLeft zeroTerm
          (consHeadNumeralTerm_freeVariables_eq_empty 0)]
    rw [show rightFormula.freeVariables = ∅ by
      exact entryFormula_freeVariables_eq_empty targetBoundary tokenCount
        data.targetRight oneTerm
          (consHeadNumeralTerm_freeVariables_eq_empty 1)]
    rw [show cellFormula.freeVariables = ∅ by
      exact tokenCellClosedFormula_freeVariables_eq_empty tokenTable width
        tokenCount data.targetLeft head data.targetRight]
    simp
  have hsyntaxPositive :
      1 <= natListConsHeadTerminalFormulaCodeEnvelope numericBound bitBound := by
    unfold natListConsHeadTerminalFormulaCodeEnvelope
    omega
  have henvelope :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      consHeadZeroValuation leftFormula rightFormula cellFormula leftResource
      rightResource cellResource
      (natListConsHeadTerminalFormulaCodeEnvelope numericBound bitBound)
      hsyntaxPositive htotalClosed htotalCode
  let rightCell := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    rightCertificate cellCertificate
  have hrightCell := transparentHybridConjunctionPayloadBound_le
    rightCertificate cellCertificate _ _ hrightCertificate hcellCertificate
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    leftCertificate rightCell
  have hparts := transparentHybridConjunctionPayloadBound_le
    leftCertificate rightCell _ _ hleftCertificate hrightCell
  have hvalueTerms :
      (fun coordinate : Fin 2 =>
        shortBinaryNumeralTerm
          (![data.targetRight, data.targetLeft] coordinate)) =
        ![shortBinaryNumeralTerm data.targetRight,
          shortBinaryNumeralTerm data.targetLeft] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  change hybridFormulaStructuralPayloadBound
    (CheckedHybridValuationBoundedFormulaCertificate.cast _ parts) <= _
  exact hparts.trans (by
    simpa only [leftFormula, rightFormula, cellFormula, leftResource,
      rightResource, cellResource, natListConsHeadTerminalPayloadEnvelope,
      rightCell, parts, zeroTerm, oneTerm] using henvelope)

#print axioms compactAdditiveNatListConsRowsHeadTerminalCertificate
#print axioms
  compactAdditiveNatListConsRowsHeadTerminalCertificate_payloadLength_le_uniform

end FoundationCompactNumericListedDirectNatListConsRowsHeadTerminalUniformBound
