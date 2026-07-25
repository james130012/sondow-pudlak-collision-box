import integration.FoundationCompactNumericListedDirectNatListAtRowsTerminalFullyUniformBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-!
# Uniform two-witness body bound for a row lookup

The terminal resource, source formula code and valuation context are all
discharged internally.  The resulting envelope contains no row witness value.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListAtRowsWitnessFullyUniformBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsTerminalFullyUniformBounds
open FoundationCompactNumericListedDirectNatListAtRowsTerminalSyntaxFixedBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation

private theorem arithmeticAddTerm_eq_func_uniformWitness
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd_uniformWitness
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func_uniformWitness]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne_uniformWitness
    (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

def compactAdditiveNatListAtRowsWitnessFullyUniformPayloadPolynomial
    (index numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02 0 numericBound
    (natListAtRowsFullFormulaCodePolynomial bitBound)
    (compactAdditiveNatListAtRowsTerminalFullyUniformPayloadPolynomial
      (shortBinaryNumeralTerm index) numericBound bitBound)

theorem
    compactAdditiveNatListAtRowsWitnessCertificate_structuralPayloadBound_le_fullyUniform
    (tokenTable width tokenCount boundaryTable count index value numericBound
      bitBound : Nat)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable index value)
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
    (hvalueSize : Nat.size value <= bitBound) :
    let values : Fin 2 -> Nat := ![data.right, data.left]
    let terminalParts :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm index)
          (shortBinaryNumeralTerm data.left) (by
            simpa [termValue_shortBinaryNumeralTerm] using data.left_entry))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryAtValuationExplicitHybridCertificate
            atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
            (shortBinaryNumeralTerm tokenCount)
            (natListAtSuccessorTermAtValuationIndex
              (shortBinaryNumeralTerm index))
            (shortBinaryNumeralTerm data.right) (by
              simpa [natListAtSuccessorTermAtValuationIndex,
                termValue_shortBinaryNumeralTerm,
                termValue_arithmeticAdd_uniformWitness,
                termValue_arithmeticOne_uniformWitness] using
                  data.right_entry))
          (compactAdditiveTokenCellExplicitHybridCertificate tokenTable width
            tokenCount data.left value data.right data.cell))
    let terminal : CheckedHybridValuationBoundedFormulaCertificate
        atRowsZeroValuation
        ((compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
          tokenCount boundaryTable value (shortBinaryNumeralTerm index)) ⇜
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
            data.right (shortBinaryNumeralTerm index)).symm) terminalParts
    hybridFormulaStructuralPayloadBound
        (buildExplicitBoundedWitnessHybridCertificate tokenCount
          (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
            tokenCount boundaryTable value (shortBinaryNumeralTerm index))
          values (by
            intro coordinate
            fin_cases coordinate
            · exact data.right_le
            · exact data.left_le)
          terminal) <=
      compactAdditiveNatListAtRowsWitnessFullyUniformPayloadPolynomial index
        numericBound bitBound := by
  dsimp only
  let indexTerm : ValuationTerm := shortBinaryNumeralTerm index
  let values : Fin 2 -> Nat := ![data.right, data.left]
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
        (shortBinaryNumeralTerm tokenCount) indexTerm
        (shortBinaryNumeralTerm data.left) (by
          simpa [indexTerm, termValue_shortBinaryNumeralTerm] using
            data.left_entry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (natListAtSuccessorTermAtValuationIndex indexTerm)
          (shortBinaryNumeralTerm data.right) (by
            simpa [indexTerm, natListAtSuccessorTermAtValuationIndex,
              termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd_uniformWitness,
              termValue_arithmeticOne_uniformWitness] using data.right_entry))
        (compactAdditiveTokenCellExplicitHybridCertificate tokenTable width
          tokenCount data.left value data.right data.cell))
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
  have hterminal :
      hybridFormulaStructuralPayloadBound terminal <=
        compactAdditiveNatListAtRowsTerminalFullyUniformPayloadPolynomial
          indexTerm numericBound bitBound := by
    simpa only [terminal, terminalParts, values, indexTerm] using
      compactAdditiveNatListAtRowsTerminalCertificate_structuralPayloadBound_le_fullyUniform
        tokenTable width tokenCount boundaryTable count index value numericBound
        bitBound data hwidthValue htokenCountValue hcountValue hindex htableSize
        hwidthSize htokenCountSize hboundarySize hcountSize hindexSize hvalueSize
  have hbodyCode :=
    compactAdditiveNatListAtRowsTerminalAtShortIndex_code_length_le_fixed
      tokenTable width tokenCount boundaryTable count index value bitBound
      htableSize hwidthSize htokenCountSize hboundarySize hcountSize hindexSize
      hvalueSize
  have hterminalClosed :=
    compactAdditiveNatListAtRowsTerminalAtShortIndex_closed tokenTable width
      tokenCount boundaryTable value index
  have hcontextCode :
      formulaCodeSum
        (valuationContext
          (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable
            width tokenCount boundaryTable value indexTerm).freeVariables
          atRowsZeroValuation) <= 0 := by
    dsimp only [indexTerm]
    rw [hterminalClosed]
    simp [valuationContext, formulaCodeSum]
  have htransparent :=
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
      (compactAdditiveNatListAtRowsTerminalFullyUniformPayloadPolynomial
        indexTerm numericBound bitBound)
      hterminal
  have harity :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity02
      atRowsZeroValuation 0 tokenCount numericBound
      (natListAtRowsFullFormulaCodePolynomial bitBound)
      (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
        tokenCount boundaryTable value indexTerm)
      values
      (terminalSmall :=
        compactAdditiveNatListAtRowsTerminalFullyUniformPayloadPolynomial
          indexTerm numericBound bitBound)
      (terminalLarge :=
        compactAdditiveNatListAtRowsTerminalFullyUniformPayloadPolynomial
          indexTerm numericBound bitBound)
      (by
        intro coordinate
        fin_cases coordinate
        · exact data.right_le
        · exact data.left_le)
      htokenCountValue (by simpa only [indexTerm] using hbodyCode)
      hcontextCode le_rfl
  unfold compactAdditiveNatListAtRowsWitnessFullyUniformPayloadPolynomial
  simpa only [values, terminal, indexTerm] using htransparent.trans harity

#print axioms
  compactAdditiveNatListAtRowsWitnessCertificate_structuralPayloadBound_le_fullyUniform

end FoundationCompactNumericListedDirectNatListAtRowsWitnessFullyUniformBounds
