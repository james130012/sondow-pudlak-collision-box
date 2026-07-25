import integration.FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate

/-!
# Fixed token-cell bound for a binder-successor value term

The quantifier transition stores `binderArity + 1` through a genuine addition
term.  This module keeps that syntax and absorbs its code overhead into an
explicit enlarged bit coordinate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskLayoutSuccessorTokenCellFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate

def quantifierBinderSuccessorTokenCellBitBound (bitBound : Nat) : Nat :=
  bitBound + binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (‘1’ : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 2

private theorem binderSuccessor_size_add_one_le (value : Nat) :
    Nat.size (value + 1) <= Nat.size value + 1 := by
  rw [Nat.size_le]
  have hvalue : value + 1 <= 2 ^ Nat.size value :=
    Nat.succ_le_iff.mpr (Nat.lt_size_self value)
  exact hvalue.trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat))
      (Nat.lt_succ_self (Nat.size value)))

private theorem binderSuccessorArithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem binderSuccessorBinaryFunctionTerm_freeVariables
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

@[simp] private theorem binderSuccessorArithmeticOne_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

theorem binderSuccessorTerm_code_length_le_tokenCellEnvelope
    (binderArity bitBound : Nat)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    (binaryTermCode (binderSuccessorTerm binderArity)).length <=
      binaryNumeralTermCodeEnvelope
        (quantifierBinderSuccessorTokenCellBitBound bitBound) := by
  have hbinderCode :=
    binaryNumeralTerm_code_length_le_envelope binderArity bitBound
      hbinderSize
  have hraw := paAddTerm_code_length_le
    (shortBinaryNumeralTerm binderArity) (‘1’ : ValuationTerm)
  have hstep : 1 <= binaryNumeralStepBudget := by decide
  have hinput :
      binaryNumeralTermCodeEnvelope bitBound +
          (binaryTermCode (‘1’ : ValuationTerm)).length +
          binaryFunctionTermCodeOverhead Language.Add.add <=
        quantifierBinderSuccessorTokenCellBitBound bitBound := by
    unfold quantifierBinderSuccessorTokenCellBitBound
    omega
  have hexpanded :
      quantifierBinderSuccessorTokenCellBitBound bitBound <=
        binaryNumeralTermCodeEnvelope
          (quantifierBinderSuccessorTokenCellBitBound bitBound) := by
    have hmul := Nat.mul_le_mul_right
      (quantifierBinderSuccessorTokenCellBitBound bitBound) hstep
    unfold binaryNumeralTermCodeEnvelope
    omega
  unfold binderSuccessorTerm
  change
    (binaryTermCode
      (paAddTerm (shortBinaryNumeralTerm binderArity)
        (‘1’ : ValuationTerm))).length <= _
  exact hraw.trans (by omega)

@[simp] theorem binderSuccessorTerm_freeVariables_eq_empty_fixed
    (binderArity : Nat) :
    (binderSuccessorTerm binderArity).freeVariables = ∅ := by
  unfold binderSuccessorTerm
  rw [binderSuccessorArithmeticAddTerm_eq_func,
    binderSuccessorBinaryFunctionTerm_freeVariables,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    binderSuccessorArithmeticOne_freeVariables_eq_empty]
  simp

theorem
    compactAdditiveTokenCellBinderSuccessorExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount cursor next binderArity numericBound
      bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (hcursorValue : cursor <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcursorSize : Nat.size cursor <= bitBound)
    (hnextSize : Nat.size next <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hcell : CompactAdditiveTokenCell tokenTable width tokenCount cursor
      (binderArity + 1) next) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm cursor)
          (binderSuccessorTerm binderArity)
          (shortBinaryNumeralTerm next) (by
            simpa only [termValue_shortBinaryNumeralTerm,
              termValue_binderSuccessorTerm] using hcell)) <=
      additiveTokenCellFullyUniformPayloadPolynomial numericBound
        (quantifierBinderSuccessorTokenCellBitBound bitBound) := by
  let expandedBit :=
    quantifierBinderSuccessorTokenCellBitBound bitBound
  have hbit : bitBound <= expandedBit := by
    unfold expandedBit quantifierBinderSuccessorTokenCellBitBound
    omega
  have hvalueSize :
      Nat.size
          (termValue
            FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation
            (binderSuccessorTerm binderArity)) <= expandedBit := by
    rw [termValue_binderSuccessorTerm]
    exact (binderSuccessor_size_add_one_le binderArity).trans (by
      unfold expandedBit quantifierBinderSuccessorTokenCellBitBound
      omega)
  have hvalueCode :
      (binaryTermCode (binderSuccessorTerm binderArity)).length <=
        binaryNumeralTermCodeEnvelope expandedBit := by
    exact binderSuccessorTerm_code_length_le_tokenCellEnvelope binderArity
      bitBound hbinderSize
  have hclosed :=
    binderSuccessorTerm_freeVariables_eq_empty_fixed binderArity
  exact
    compactAdditiveTokenCellShortNumeralsAtClosedValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount cursor next numericBound expandedBit
      (binderSuccessorTerm binderArity) hwidthValue hcursorValue
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) (hcursorSize.trans hbit) hvalueSize
      (hnextSize.trans hbit) hvalueCode hclosed (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_binderSuccessorTerm] using hcell)

#print axioms binderSuccessorTerm_code_length_le_tokenCellEnvelope
#print axioms binderSuccessorTerm_freeVariables_eq_empty_fixed
#print axioms
  compactAdditiveTokenCellBinderSuccessorExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskLayoutSuccessorTokenCellFixedBounds
