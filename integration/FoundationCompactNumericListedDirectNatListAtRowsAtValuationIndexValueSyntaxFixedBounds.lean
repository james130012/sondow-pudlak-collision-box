import integration.FoundationCompactNumericListedDirectNatListAtRowsTerminalSyntaxFixedBounds

/-!
# Fixed syntax for a row lookup with exact index and value terms

The five scalar coordinates remain canonical short numerals.  The index and
value coordinates may be arbitrary closed terms whose binary codes fit the
same common term-code envelope.  The checked formula therefore preserves the
caller's arithmetic expressions without finite enumeration.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 60000

namespace FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsTerminalSyntaxFixedBounds

def natListAtRowsAtValuationIndexValueTerms
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm valueTerm : ValuationTerm) : Fin 7 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm boundaryTable,
    shortBinaryNumeralTerm count,
    indexTerm,
    valueTerm]

theorem
    compactAdditiveNatListAtRowsAtValuationIndexValueFormula_code_length_le_fixed
    (tokenTable width tokenCount boundaryTable count bitBound : Nat)
    (indexTerm valueTerm : ValuationTerm)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound)
    (hvalueCode : (binaryTermCode valueTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListAtRowsAtValuationIndexValueFormula tokenTable width
        tokenCount boundaryTable count indexTerm valueTerm)).length <=
      natListAtRowsFullFormulaCodePolynomial bitBound := by
  let terms := natListAtRowsAtValuationIndexValueTerms tokenTable width
    tokenCount boundaryTable count indexTerm valueTerm
  let termCode := binaryNumeralTermCodeEnvelope bitBound
  let source : ArithmeticSemiformula Nat 7 :=
    Rewriting.emb (ξ := Nat) compactAdditiveNatListAtRowsDef.val
  have hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact binaryNumeralTerm_code_length_le_envelope tokenTable bitBound
        htableSize
    · exact binaryNumeralTerm_code_length_le_envelope width bitBound
        hwidthSize
    · exact binaryNumeralTerm_code_length_le_envelope tokenCount bitBound
        htokenCountSize
    · exact binaryNumeralTerm_code_length_le_envelope boundaryTable bitBound
        hboundarySize
    · exact binaryNumeralTerm_code_length_le_envelope count bitBound
        hcountSize
    · exact hindexCode
    · exact hvalueCode
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 termCode (binaryFormulaCode source).length terms source hterms le_rfl
  rw [
    compactAdditiveNatListAtRowsAtValuationIndexValueFormula_eq_explicitSubstitution]
  unfold natListAtRowsFullFormulaCodePolynomial
  simpa only [sourceSubstitutionQpow, terms, termCode, source,
    natListAtRowsAtValuationIndexValueTerms] using hraw

theorem compactAdditiveNatListAtRowsAtValuationIndexValueFormula_closed
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm valueTerm : ValuationTerm)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hvalueClosed : valueTerm.freeVariables = ∅) :
    (compactAdditiveNatListAtRowsAtValuationIndexValueFormula tokenTable width
      tokenCount boundaryTable count indexTerm valueTerm).freeVariables = ∅ := by
  let terms := natListAtRowsAtValuationIndexValueTerms tokenTable width
    tokenCount boundaryTable count indexTerm valueTerm
  have hterms : forall coordinate, (terms coordinate).freeVariables = ∅ := by
    intro coordinate
    fin_cases coordinate
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty width
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty count
    · exact hindexClosed
    · exact hvalueClosed
  rw [
    compactAdditiveNatListAtRowsAtValuationIndexValueFormula_eq_explicitSubstitution]
  change
    ((Rewriting.emb (ξ := Nat) compactAdditiveNatListAtRowsDef.val) ⇜
      terms).freeVariables = ∅
  exact embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
    _ terms hterms

#print axioms
  compactAdditiveNatListAtRowsAtValuationIndexValueFormula_code_length_le_fixed
#print axioms compactAdditiveNatListAtRowsAtValuationIndexValueFormula_closed

end FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueSyntaxFixedBounds
