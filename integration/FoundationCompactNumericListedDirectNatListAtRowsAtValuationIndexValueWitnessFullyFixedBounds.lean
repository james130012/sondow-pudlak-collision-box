import integration.FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueTerminalFullyFixedBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-!
# Fully fixed two-witness body for exact row index and value terms

The terminal certificate is installed under the two bounded row witnesses.
Its formula is closed, so the valuation-context coordinate is zero.  The
result contains neither concrete row witness.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 120000

namespace FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueWitnessFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsTerminalSyntaxFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueTerminalSyntaxFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

private abbrev atRowsValueZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation

private theorem arithmeticAddTerm_eq_func_witnessValue
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd_witnessValue
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func_witnessValue]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne_witnessValue
    (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

def compactAdditiveNatListAtRowsExactValueWitnessFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02 0 numericBound
    (natListAtRowsFullFormulaCodePolynomial bitBound)
    (compactAdditiveNatListAtRowsExactValueTerminalFullyFixedPayloadPolynomial
      numericBound bitBound)

theorem
    compactAdditiveNatListAtRowsExactValueWitnessCertificate_structuralPayloadBound_le_fullyFixed
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
                termValue_arithmeticAdd_witnessValue,
                termValue_arithmeticOne_witnessValue, hindexValue] using
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
    hybridFormulaStructuralPayloadBound
        (buildExplicitBoundedWitnessHybridCertificate tokenCount
          (compactAdditiveNatListAtRowsTerminalAtValuationIndexValue tokenTable
            width tokenCount boundaryTable indexTerm valueTerm)
          values (by
            intro coordinate
            fin_cases coordinate
            · exact data.right_le
            · exact data.left_le)
          terminal) <=
      compactAdditiveNatListAtRowsExactValueWitnessFullyFixedPayloadPolynomial
        numericBound bitBound := by
  dsimp only
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
              termValue_arithmeticAdd_witnessValue,
              termValue_arithmeticOne_witnessValue, hindexValue] using
                data.right_entry))
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificateLocal
          atRowsValueZeroValuation (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm data.left) valueTerm
          (shortBinaryNumeralTerm data.right) (by
            simpa [termValue_shortBinaryNumeralTerm, hvalueValue] using
              data.cell)))
  have hvalueTerms :
      (fun coordinate : Fin 2 =>
        shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm data.right,
          shortBinaryNumeralTerm data.left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminal : CheckedHybridValuationBoundedFormulaCertificate
      atRowsValueZeroValuation
      ((compactAdditiveNatListAtRowsTerminalAtValuationIndexValue tokenTable
        width tokenCount boundaryTable indexTerm valueTerm) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveNatListAtRowsTerminalAtValuationIndexValue_substitution_alignment
          tokenTable width tokenCount boundaryTable data.left data.right
          indexTerm valueTerm).symm) terminalParts
  have hterminal : hybridFormulaStructuralPayloadBound terminal <=
      compactAdditiveNatListAtRowsExactValueTerminalFullyFixedPayloadPolynomial
        numericBound bitBound := by
    simpa only [terminal, terminalParts, values] using
      compactAdditiveNatListAtRowsExactValueTerminalCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount boundaryTable count index value numericBound
        bitBound indexTerm valueTerm data hindexValue hvalueValue hindexClosed
        hvalueClosed hwidthValue htokenCountValue hcountValue hindex htableSize
        hwidthSize htokenCountSize hboundarySize hcountSize hindexSize
        hvalueSize hindexCode hvalueCode
  have hbodyCode :=
    compactAdditiveNatListAtRowsTerminalAtValuationIndexValue_code_length_le_fixed
      tokenTable width tokenCount boundaryTable count bitBound indexTerm
      valueTerm htableSize hwidthSize htokenCountSize hboundarySize hcountSize
      (by simpa only [natListAtRowsExactIndexCodeEnvelope] using hindexCode)
      hvalueCode
  have hterminalClosed :=
    compactAdditiveNatListAtRowsTerminalAtValuationIndexValue_closed tokenTable
      width tokenCount boundaryTable indexTerm valueTerm hindexClosed
      hvalueClosed
  have hcontextCode :
      formulaCodeSum
        (valuationContext
          (compactAdditiveNatListAtRowsTerminalAtValuationIndexValue tokenTable
            width tokenCount boundaryTable indexTerm valueTerm).freeVariables
          atRowsValueZeroValuation) <= 0 := by
    rw [hterminalClosed]
    simp [valuationContext, formulaCodeSum]
  have htransparent :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount
      (compactAdditiveNatListAtRowsTerminalAtValuationIndexValue tokenTable
        width tokenCount boundaryTable indexTerm valueTerm)
      values (by
        intro coordinate
        fin_cases coordinate
        · exact data.right_le
        · exact data.left_le)
      terminal
      (compactAdditiveNatListAtRowsExactValueTerminalFullyFixedPayloadPolynomial
        numericBound bitBound)
      hterminal
  have harity :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity02
      atRowsValueZeroValuation 0 tokenCount numericBound
      (natListAtRowsFullFormulaCodePolynomial bitBound)
      (compactAdditiveNatListAtRowsTerminalAtValuationIndexValue tokenTable
        width tokenCount boundaryTable indexTerm valueTerm)
      values
      (terminalSmall :=
        compactAdditiveNatListAtRowsExactValueTerminalFullyFixedPayloadPolynomial
          numericBound bitBound)
      (terminalLarge :=
        compactAdditiveNatListAtRowsExactValueTerminalFullyFixedPayloadPolynomial
          numericBound bitBound)
      (by
        intro coordinate
        fin_cases coordinate
        · exact data.right_le
        · exact data.left_le)
      htokenCountValue hbodyCode hcontextCode le_rfl
  unfold
    compactAdditiveNatListAtRowsExactValueWitnessFullyFixedPayloadPolynomial
  simpa only [values, terminal] using htransparent.trans harity

#print axioms
  compactAdditiveNatListAtRowsExactValueWitnessCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueWitnessFullyFixedBounds
