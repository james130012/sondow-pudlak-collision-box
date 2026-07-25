import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatPublicBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
import integration.FoundationCompactPABinaryNumeralAdditionBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds

/-! # Fixed native equality resources for the Repeat parser branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatAtomicFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate

private abbrev repeatAtomicZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate.zeroValuation

def repeatAtomicTermCodePolynomial (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (fixedNumeralTerm 0)).length +
    (binaryTermCode (fixedNumeralTerm 1)).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

def repeatNativeEqFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (repeatAtomicTermCodePolynomial bitBound)

theorem repeatShortNumeralTerm_code_length_le
    (value bitBound : Nat)
    (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      repeatAtomicTermCodePolynomial bitBound := by
  have hraw :=
    binaryNumeralTerm_code_length_le_envelope value bitBound hvalue
  unfold repeatAtomicTermCodePolynomial
  omega

theorem repeatFixedZeroTerm_code_length_le (bitBound : Nat) :
    (binaryTermCode (fixedNumeralTerm 0)).length <=
      repeatAtomicTermCodePolynomial bitBound := by
  unfold repeatAtomicTermCodePolynomial
  omega

theorem repeatFixedOneTerm_code_length_le (bitBound : Nat) :
    (binaryTermCode (fixedNumeralTerm 1)).length <=
      repeatAtomicTermCodePolynomial bitBound := by
  unfold repeatAtomicTermCodePolynomial
  omega

theorem repeatSuccessorTerm_code_length_le
    (predecessor bitBound : Nat)
    (hpredecessor : Nat.size predecessor <= bitBound) :
    (binaryTermCode
      (‘!!(shortBinaryNumeralTerm predecessor) +
        !!(fixedNumeralTerm 1)’ : ValuationTerm)).length <=
      repeatAtomicTermCodePolynomial bitBound := by
  have hadd := arithmeticAddTerm_code_length_le
    (shortBinaryNumeralTerm predecessor) (fixedNumeralTerm 1)
  have hleft :=
    binaryNumeralTerm_code_length_le_envelope predecessor bitBound
      hpredecessor
  unfold repeatAtomicTermCodePolynomial
  omega

private theorem repeatFixedNumeralTerm_closed (value : Nat) :
    (fixedNumeralTerm value).freeVariables = ∅ := by
  simp [fixedNumeralTerm, LO.FirstOrder.Semiterm.Operator.operator]

private theorem repeatArithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem repeatBinaryFunctionTerm_freeVariables
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

private theorem repeatSuccessorTerm_closed (predecessor : Nat) :
    (‘!!(shortBinaryNumeralTerm predecessor) +
      !!(fixedNumeralTerm 1)’ : ValuationTerm).freeVariables = ∅ := by
  rw [repeatArithmeticAddTerm_eq_func,
    repeatBinaryFunctionTerm_freeVariables,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    repeatFixedNumeralTerm_closed]
  simp

theorem nativeEqCertificate_structuralPayloadBound_le_fixed
    (value bitBound : Nat)
    (heq : value = 0)
    (hvalueSize : Nat.size value <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (nativeEqCertificate value 0 heq) <=
      repeatNativeEqFixedPayloadPolynomial bitBound := by
  change compilePositiveRelationPayloadResource repeatAtomicZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm value, fixedNumeralTerm 0] <= _
  unfold repeatNativeEqFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed
    repeatAtomicZeroValuation Language.Eq.eq
    (shortBinaryNumeralTerm value) (fixedNumeralTerm 0)
    0 (repeatAtomicTermCodePolynomial bitBound)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    (repeatFixedNumeralTerm_closed 0)
    (repeatShortNumeralTerm_code_length_le value bitBound hvalueSize)
    (repeatFixedZeroTerm_code_length_le bitBound)

theorem nativeSuccessorEqCertificate_structuralPayloadBound_le_fixed
    (value predecessor bitBound : Nat)
    (heq : value = predecessor + 1)
    (hvalueSize : Nat.size value <= bitBound)
    (hpredecessorSize : Nat.size predecessor <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (nativeSuccessorEqCertificate value predecessor heq) <=
      repeatNativeEqFixedPayloadPolynomial bitBound := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm predecessor) + !!(fixedNumeralTerm 1)’
  change compilePositiveRelationPayloadResource repeatAtomicZeroValuation
      Language.Eq.eq ![shortBinaryNumeralTerm value, rightTerm] <= _
  unfold repeatNativeEqFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed
    repeatAtomicZeroValuation Language.Eq.eq
    (shortBinaryNumeralTerm value) rightTerm
    0 (repeatAtomicTermCodePolynomial bitBound)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    (by simpa only [rightTerm] using repeatSuccessorTerm_closed predecessor)
    (repeatShortNumeralTerm_code_length_le value bitBound hvalueSize)
    (by
      simpa only [rightTerm] using
        repeatSuccessorTerm_code_length_le predecessor bitBound
          hpredecessorSize)

end FoundationCompactNumericListedDirectParserSyntaxRepeatAtomicFixedBounds
