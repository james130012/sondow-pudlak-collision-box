import integration.FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixArithmeticFixedBounds
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-!
# Fixed syntax bound for mapped source-prefix append

The original fifteen-place bounded formula is instantiated once by closed
short binary numerals.  Its complete code and closedness are therefore bounded
without exposing a formula-size parameter.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixFormulaFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefix
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables

def appendMappedSourcePrefixClosedTerms
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetBoundary targetCount mappedHead : Nat) :
    Fin 15 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm leftStart,
    shortBinaryNumeralTerm leftFinish,
    shortBinaryNumeralTerm leftCount,
    shortBinaryNumeralTerm sourceStart,
    shortBinaryNumeralTerm sourceFinish,
    shortBinaryNumeralTerm sourceCount,
    shortBinaryNumeralTerm prefixCount,
    shortBinaryNumeralTerm targetStart,
    shortBinaryNumeralTerm targetFinish,
    shortBinaryNumeralTerm targetBoundary,
    shortBinaryNumeralTerm targetCount,
    shortBinaryNumeralTerm mappedHead]

def appendMappedSourcePrefixFullFormulaCodePolynomial (bitBound : Nat) : Nat :=
  let termCode := appendSourcePrefixCompositeTermCodePolynomial bitBound
  let source : LO.FirstOrder.ArithmeticSemiformula Nat 15 :=
    Rewriting.emb (ξ := Nat)
      compactAdditiveNatListAppendMappedSourcePrefixDef.val
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 0 termCode
    (binaryFormulaCode source).length

theorem
    compactAdditiveNatListAppendMappedSourcePrefixClosedFormula_code_length_le_fixed
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetBoundary targetCount mappedHead bitBound :
      Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hleftStartSize : Nat.size leftStart <= bitBound)
    (hleftFinishSize : Nat.size leftFinish <= bitBound)
    (hleftCountSize : Nat.size leftCount <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (hsourceFinishSize : Nat.size sourceFinish <= bitBound)
    (hsourceCountSize : Nat.size sourceCount <= bitBound)
    (hprefixCountSize : Nat.size prefixCount <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound)
    (htargetFinishSize : Nat.size targetFinish <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (htargetCountSize : Nat.size targetCount <= bitBound)
    (hmappedHeadSize : Nat.size mappedHead <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListAppendMappedSourcePrefixClosedFormula tokenTable
        width tokenCount leftStart leftFinish leftCount sourceStart
        sourceFinish sourceCount prefixCount targetStart targetFinish
        targetBoundary targetCount mappedHead)).length <=
      appendMappedSourcePrefixFullFormulaCodePolynomial bitBound := by
  let terms := appendMappedSourcePrefixClosedTerms tokenTable width tokenCount
    leftStart leftFinish leftCount sourceStart sourceFinish sourceCount
    prefixCount targetStart targetFinish targetBoundary targetCount mappedHead
  let termCode := appendSourcePrefixCompositeTermCodePolynomial bitBound
  let source : LO.FirstOrder.ArithmeticSemiformula Nat 15 :=
    Rewriting.emb (ξ := Nat)
      compactAdditiveNatListAppendMappedSourcePrefixDef.val
  have hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate <;>
      simp only [terms, appendMappedSourcePrefixClosedTerms] <;>
      apply appendSourcePrefixShortNumeral_code_le <;> assumption
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 termCode (binaryFormulaCode source).length terms source hterms le_rfl
  unfold compactAdditiveNatListAppendMappedSourcePrefixClosedFormula
    appendMappedSourcePrefixFullFormulaCodePolynomial
  simpa only [sourceSubstitutionQpow, terms, termCode, source,
    appendMappedSourcePrefixClosedTerms] using hraw

theorem compactAdditiveNatListAppendMappedSourcePrefixExplicitFormula_closed
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetBoundary targetCount mappedHead : Nat) :
    (compactAdditiveNatListAppendMappedSourcePrefixExplicitFormula tokenTable
      width tokenCount leftStart leftFinish leftCount sourceStart sourceFinish
      sourceCount prefixCount targetStart targetFinish targetBoundary
      targetCount mappedHead).freeVariables = ∅ := by
  rw [← compactAdditiveNatListAppendMappedSourcePrefixClosedFormula_alignment]
  unfold compactAdditiveNatListAppendMappedSourcePrefixClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

#print axioms
  compactAdditiveNatListAppendMappedSourcePrefixClosedFormula_code_length_le_fixed
#print axioms
  compactAdditiveNatListAppendMappedSourcePrefixExplicitFormula_closed

end FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixFormulaFixedBounds
