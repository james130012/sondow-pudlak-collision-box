import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-!
# Fixed code and closedness bounds for the full source-prefix append formula

The original thirteen-place bounded formula is instantiated in one step by
closed short binary numerals.  The resulting full formula code is controlled
by the uniform substitution theorem, not by an opaque formula-size parameter.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListAppendSourcePrefixFormulaFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefix
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables

def appendSourcePrefixClosedTerms
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount : Nat) :
    Fin 13 -> ValuationTerm :=
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
    shortBinaryNumeralTerm targetCount]

def appendSourcePrefixFullFormulaCodePolynomial (bitBound : Nat) : Nat :=
  let termCode := appendSourcePrefixCompositeTermCodePolynomial bitBound
  let source : LO.FirstOrder.ArithmeticSemiformula Nat 13 :=
    Rewriting.emb (ξ := Nat) compactAdditiveNatListAppendSourcePrefixDef.val
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 0 termCode
    (binaryFormulaCode source).length

theorem compactAdditiveNatListAppendSourcePrefixClosedFormula_code_length_le_fixed
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount bitBound : Nat)
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
    (htargetCountSize : Nat.size targetCount <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListAppendSourcePrefixClosedFormula tokenTable width
        tokenCount leftStart leftFinish leftCount sourceStart sourceFinish
        sourceCount prefixCount targetStart targetFinish targetCount)).length <=
      appendSourcePrefixFullFormulaCodePolynomial bitBound := by
  let terms := appendSourcePrefixClosedTerms tokenTable width tokenCount
    leftStart leftFinish leftCount sourceStart sourceFinish sourceCount
    prefixCount targetStart targetFinish targetCount
  let termCode := appendSourcePrefixCompositeTermCodePolynomial bitBound
  let source : LO.FirstOrder.ArithmeticSemiformula Nat 13 :=
    Rewriting.emb (ξ := Nat) compactAdditiveNatListAppendSourcePrefixDef.val
  have hterms : ∀ coordinate,
      (binaryTermCode (terms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate <;>
      simp only [terms, appendSourcePrefixClosedTerms] <;>
      apply appendSourcePrefixShortNumeral_code_le <;> assumption
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 termCode (binaryFormulaCode source).length terms source hterms le_rfl
  unfold compactAdditiveNatListAppendSourcePrefixClosedFormula
    appendSourcePrefixFullFormulaCodePolynomial
  simpa only [sourceSubstitutionQpow, terms, termCode, source,
    appendSourcePrefixClosedTerms] using hraw

theorem compactAdditiveNatListAppendSourcePrefixExplicitFormula_closed
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount : Nat) :
    (compactAdditiveNatListAppendSourcePrefixExplicitFormula tokenTable width
      tokenCount leftStart leftFinish leftCount sourceStart sourceFinish
      sourceCount prefixCount targetStart targetFinish
      targetCount).freeVariables = ∅ := by
  rw [← compactAdditiveNatListAppendSourcePrefixClosedFormula_alignment]
  unfold compactAdditiveNatListAppendSourcePrefixClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

#print axioms
  compactAdditiveNatListAppendSourcePrefixClosedFormula_code_length_le_fixed
#print axioms compactAdditiveNatListAppendSourcePrefixExplicitFormula_closed

end FoundationCompactNumericListedDirectNatListAppendSourcePrefixFormulaFixedBounds
