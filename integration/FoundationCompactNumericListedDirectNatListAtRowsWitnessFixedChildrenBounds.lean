import integration.FoundationCompactNumericListedDirectNatListAtRowsTerminalFixedChildrenBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-!
# Fixed child resources for the two row-lookup witnesses

This layer feeds the actual fixed terminal certificate into the exact
two-witness compiler bound.  Formula-code and valuation-context ceilings are
explicit local arithmetic obligations for the next syntax layer.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListAtRowsWitnessFixedChildrenBounds

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
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsPublicBounds
open FoundationCompactNumericListedDirectNatListAtRowsTerminalFixedChildrenBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation

private theorem arithmeticAddTerm_eq_func_witness
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd_witness
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func_witness]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne_witness (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

def compactAdditiveNatListAtRowsWitnessFixedChildrenPayloadEnvelope
    (tokenTable width tokenCount boundaryTable value numericBound bitBound
      contextCodeBound bodyCodeBound : Nat)
    (indexTerm : ValuationTerm)
    (left right : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02
    contextCodeBound numericBound bodyCodeBound
    (compactAdditiveNatListAtRowsTerminalFixedChildrenPayloadEnvelope
      tokenTable width tokenCount boundaryTable value numericBound bitBound
      indexTerm left right)

theorem
    compactAdditiveNatListAtRowsWitnessCertificate_structuralPayloadBound_le_fixedChildren
    (tokenTable width tokenCount boundaryTable value numericBound bitBound
      contextCodeBound bodyCodeBound : Nat)
    (indexTerm : ValuationTerm)
    (hindexClosed : indexTerm.freeVariables ⊆ {0})
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable (termValue atRowsZeroValuation indexTerm) value)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hbodyCode :
      (binaryFormulaCode
        (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
          tokenCount boundaryTable value indexTerm)).length <= bodyCodeBound)
    (hcontextCode :
      formulaCodeSum
        (valuationContext
          (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable
            width tokenCount boundaryTable value indexTerm).freeVariables
          atRowsZeroValuation) <= contextCodeBound) :
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
                termValue_arithmeticAdd_witness,
                termValue_arithmeticOne_witness]
                using data.right_entry))
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
    hybridFormulaStructuralPayloadBound
        (buildExplicitBoundedWitnessHybridCertificate tokenCount
          (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
            tokenCount boundaryTable value indexTerm)
          values (by
            intro coordinate
            fin_cases coordinate
            · exact data.right_le
            · exact data.left_le)
          terminal) <=
      compactAdditiveNatListAtRowsWitnessFixedChildrenPayloadEnvelope
        tokenTable width tokenCount boundaryTable value numericBound bitBound
        contextCodeBound bodyCodeBound indexTerm data.left data.right := by
  dsimp only
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
              termValue_arithmeticAdd_witness,
              termValue_arithmeticOne_witness]
              using data.right_entry))
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
  have hleftSize : Nat.size data.left <= bitBound :=
    (Nat.size_le_size data.left_le).trans htokenCountSize
  have hrightSize : Nat.size data.right <= bitBound :=
    (Nat.size_le_size data.right_le).trans htokenCountSize
  have hterminal :
      hybridFormulaStructuralPayloadBound terminal <=
        compactAdditiveNatListAtRowsTerminalFixedChildrenPayloadEnvelope
          tokenTable width tokenCount boundaryTable value numericBound bitBound
          indexTerm data.left data.right := by
    simpa only [terminal, terminalParts, values] using
      compactAdditiveNatListAtRowsTerminalCertificate_structuralPayloadBound_le_fixedChildren
        tokenTable width tokenCount boundaryTable value numericBound bitBound
        indexTerm hindexClosed data hwidthValue
        (data.left_le.trans htokenCountValue) htableSize hwidthSize
        htokenCountSize hleftSize hvalueSize hrightSize
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
      (compactAdditiveNatListAtRowsTerminalFixedChildrenPayloadEnvelope
        tokenTable width tokenCount boundaryTable value numericBound bitBound
        indexTerm data.left data.right)
      hterminal
  have harity :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity02
      atRowsZeroValuation contextCodeBound tokenCount numericBound bodyCodeBound
      (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
        tokenCount boundaryTable value indexTerm)
      values
      (terminalSmall :=
        compactAdditiveNatListAtRowsTerminalFixedChildrenPayloadEnvelope
          tokenTable width tokenCount boundaryTable value numericBound bitBound
          indexTerm data.left data.right)
      (terminalLarge :=
        compactAdditiveNatListAtRowsTerminalFixedChildrenPayloadEnvelope
          tokenTable width tokenCount boundaryTable value numericBound bitBound
          indexTerm data.left data.right)
      (by
        intro coordinate
        fin_cases coordinate
        · exact data.right_le
        · exact data.left_le)
      htokenCountValue hbodyCode hcontextCode le_rfl
  unfold compactAdditiveNatListAtRowsWitnessFixedChildrenPayloadEnvelope
  simpa only [values, terminal] using htransparent.trans harity

#print axioms
  compactAdditiveNatListAtRowsWitnessCertificate_structuralPayloadBound_le_fixedChildren

end FoundationCompactNumericListedDirectNatListAtRowsWitnessFixedChildrenBounds
