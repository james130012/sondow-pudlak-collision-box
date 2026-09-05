import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAtomicFixedBounds
import integration.FoundationCompactPAHybridDisjunctionGeneralContextBounds

/-!
# Fixed resources for term-output failure decisions

The double and triple failure selectors contain only closed arithmetic atoms.
Their public-finite envelopes are bounded here by one common polynomial in the
binary coordinate width.  No checked branch data or concrete coordinate value
occurs in the resulting resources.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 240000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAtomicFixedBounds

def termOutputFailureTermCodePolynomial (bitBound : Nat) : Nat :=
  outputRowsAtomicTermCodePolynomial bitBound

def termOutputFailureAtomicPayloadPolynomial (bitBound : Nat) : Nat :=
  compileNegativeRelationFixedPayloadPolynomial 0
    (termOutputFailureTermCodePolynomial bitBound)

def termOutputFailureAtomFormulaCodePolynomial (bitBound : Nat) : Nat :=
  2 * outputRowsAtomicLeafFormulaCodePolynomial bitBound + 128

def termOutputFailureInnerFormulaCodePolynomial (bitBound : Nat) : Nat :=
  2 * termOutputFailureAtomFormulaCodePolynomial bitBound +
    (binaryNatCode 5).length + 1

def termOutputFailureFormulaCodePolynomial (bitBound : Nat) : Nat :=
  termOutputFailureAtomFormulaCodePolynomial bitBound +
    termOutputFailureInnerFormulaCodePolynomial bitBound +
    (binaryNatCode 5).length + 1

def termOutputFailurePathPayloadPolynomial (bitBound : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (termOutputFailureFormulaCodePolynomial bitBound)
    (termOutputFailureAtomicPayloadPolynomial bitBound)

def termOutputDoubleFailureFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  2 * termOutputFailurePathPayloadPolynomial bitBound

def termOutputTripleFailureFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  let inner := termOutputFailurePathPayloadPolynomial bitBound
  let outer := hybridDisjunctionGeneralPayloadEnvelope
    (termOutputFailureFormulaCodePolynomial bitBound) inner
  3 * outer

theorem binaryFunctionTerm_freeVariables_failure
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiterm.func functionSymbol
      ![left, right]).freeVariables =
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

theorem nativeAddTerm_freeVariables_failure
    (left right : ValuationTerm) :
    (nativeAddTerm left right).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change (paAddTerm left right).freeVariables = _
  exact binaryFunctionTerm_freeVariables_failure Language.Add.add left right

theorem failureShortNumeralCode_le
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      termOutputFailureTermCodePolynomial bitBound := by
  unfold termOutputFailureTermCodePolynomial
  exact outputRowsShortNumeralCode_le value bitBound hvalue

theorem failureLiteralCode_le
    (literal : ValuationTerm) (bitBound : Nat)
    (hliteral :
      literal = (‘0’ : ValuationTerm) ∨
      literal = (‘1’ : ValuationTerm) ∨
      literal = (‘2’ : ValuationTerm)) :
    (binaryTermCode literal).length <=
      termOutputFailureTermCodePolynomial bitBound := by
  unfold termOutputFailureTermCodePolynomial
  rcases hliteral with rfl | rfl | rfl
  · exact outputRowsModeLiteralCode_le (‘0’ : ValuationTerm) bitBound
      (Or.inl rfl)
  · exact outputRowsModeLiteralCode_le (‘1’ : ValuationTerm) bitBound
      (Or.inr (Or.inl rfl))
  · exact outputRowsModeLiteralCode_le (‘2’ : ValuationTerm) bitBound
      (Or.inr (Or.inr (Or.inl rfl)))

theorem failureLiteral_closed
    (literal : ValuationTerm)
    (hliteral :
      literal = (‘0’ : ValuationTerm) ∨
      literal = (‘1’ : ValuationTerm) ∨
      literal = (‘2’ : ValuationTerm)) :
    literal.freeVariables = ∅ := by
  rcases hliteral with rfl | rfl | rfl
  · exact outputRowsModeLiteral_closed (‘0’ : ValuationTerm) (Or.inl rfl)
  · exact outputRowsModeLiteral_closed (‘1’ : ValuationTerm)
      (Or.inr (Or.inl rfl))
  · exact outputRowsModeLiteral_closed (‘2’ : ValuationTerm)
      (Or.inr (Or.inr (Or.inl rfl)))

theorem failureAddArgumentOneCode_le
    (argument bitBound : Nat)
    (hargument : Nat.size argument <= bitBound) :
    (binaryTermCode
      (nativeAddTerm (shortBinaryNumeralTerm argument)
        (‘1’ : ValuationTerm))).length <=
      termOutputFailureTermCodePolynomial bitBound := by
  have hargumentCode :=
    binaryNumeralTerm_code_length_le_envelope argument bitBound hargument
  have hadd := paAddTerm_code_length_le
    (shortBinaryNumeralTerm argument) (‘1’ : ValuationTerm)
  change (binaryTermCode
    (paAddTerm (shortBinaryNumeralTerm argument)
      (‘1’ : ValuationTerm))).length <= _
  unfold termOutputFailureTermCodePolynomial
    outputRowsAtomicTermCodePolynomial
  omega

theorem failureAddArgumentOne_closed (argument : Nat) :
    (nativeAddTerm (shortBinaryNumeralTerm argument)
      (‘1’ : ValuationTerm)).freeVariables = ∅ := by
  rw [nativeAddTerm_freeVariables_failure,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    failureLiteral_closed (‘1’ : ValuationTerm) (Or.inr (Or.inl rfl))]
  simp

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds

