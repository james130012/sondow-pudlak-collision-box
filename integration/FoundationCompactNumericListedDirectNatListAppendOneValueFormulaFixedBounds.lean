import integration.FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Fixed code and closedness for the append-one formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 240000

namespace FoundationCompactNumericListedDirectNatListAppendOneValueFormulaFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectNatListAppendOneValue
open FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables

def appendOneClosedTerms
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value : Nat) :
    Fin 11 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm sourceStart,
    shortBinaryNumeralTerm sourceFinish,
    shortBinaryNumeralTerm sourceCount,
    shortBinaryNumeralTerm targetStart,
    shortBinaryNumeralTerm targetFinish,
    shortBinaryNumeralTerm targetBoundary,
    shortBinaryNumeralTerm targetCount,
    shortBinaryNumeralTerm value]

def appendOneFullFormulaCodePolynomial (bitBound : Nat) : Nat :=
  let termCode := appendSourcePrefixCompositeTermCodePolynomial bitBound
  let source : LO.FirstOrder.ArithmeticSemiformula Nat 11 :=
    Rewriting.emb (ξ := Nat) compactAdditiveNatListAppendOneValueDef.val
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 0 termCode
    (binaryFormulaCode source).length

theorem compactAdditiveNatListAppendOneValueClosedFormula_code_length_le_fixed
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (hsourceFinishSize : Nat.size sourceFinish <= bitBound)
    (hsourceCountSize : Nat.size sourceCount <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound)
    (htargetFinishSize : Nat.size targetFinish <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (htargetCountSize : Nat.size targetCount <= bitBound)
    (hvalueSize : Nat.size value <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListAppendOneValueClosedFormula tokenTable width
        tokenCount sourceStart sourceFinish sourceCount targetStart targetFinish
        targetBoundary targetCount value)).length <=
      appendOneFullFormulaCodePolynomial bitBound := by
  let terms := appendOneClosedTerms tokenTable width tokenCount sourceStart
    sourceFinish sourceCount targetStart targetFinish targetBoundary targetCount
    value
  let termCode := appendSourcePrefixCompositeTermCodePolynomial bitBound
  let source : LO.FirstOrder.ArithmeticSemiformula Nat 11 :=
    Rewriting.emb (ξ := Nat) compactAdditiveNatListAppendOneValueDef.val
  have hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate <;>
      simp only [terms, appendOneClosedTerms] <;>
      apply appendSourcePrefixShortNumeral_code_le <;> assumption
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 termCode (binaryFormulaCode source).length terms source hterms le_rfl
  unfold compactAdditiveNatListAppendOneValueClosedFormula
    appendOneFullFormulaCodePolynomial
  simpa only [sourceSubstitutionQpow, terms, termCode, source,
    appendOneClosedTerms] using hraw

theorem compactAdditiveNatListAppendOneValueExplicitFormula_closed
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value : Nat) :
    (compactAdditiveNatListAppendOneValueExplicitFormula tokenTable width
      tokenCount sourceStart sourceFinish sourceCount targetStart targetFinish
      targetBoundary targetCount value).freeVariables = ∅ := by
  rw [← compactAdditiveNatListAppendOneValueClosedFormula_alignment]
  unfold compactAdditiveNatListAppendOneValueClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

#print axioms
  compactAdditiveNatListAppendOneValueClosedFormula_code_length_le_fixed
#print axioms compactAdditiveNatListAppendOneValueExplicitFormula_closed

end FoundationCompactNumericListedDirectNatListAppendOneValueFormulaFixedBounds
