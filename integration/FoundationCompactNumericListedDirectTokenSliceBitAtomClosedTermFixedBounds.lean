import integration.FoundationCompactNumericListedDirectTokenSliceBitAtomFixedBounds
import integration.FoundationCompactNumericListedDirectTokenSliceBitUniversalTermFixedBounds
import integration.FoundationCompactPABitAtomArityCodeBounds

/-!
# Fixed token-slice bit atoms over arbitrary closed terms

This is the syntax-preserving bridge needed by callers whose starts are
arithmetic composites rather than short numerals.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceBitAtomClosedTermFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABinaryBitValuationFixedPolynomialBounds
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABitMembershipValuationCompilerPublicBounds
open FoundationCompactPABitMembershipValuationContextCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceBitAtomFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitUniversalTermFixedBounds
open FoundationCompactPABitAtomArityCodeBounds

def tokenSliceClosedTermBitTermCodeCeiling (termCode : Nat) : Nat :=
  let shiftedCode := 4 * termCode
  let firstAddCode :=
    shiftedCode + (binaryTermCode (&1 : ValuationTerm)).length +
      binaryFunctionTermCodeOverhead Language.Add.add
  let productCode :=
    firstAddCode + shiftedCode +
      binaryFunctionTermCodeOverhead Language.Mul.mul
  productCode + (binaryTermCode (&0 : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

def tokenSliceClosedTermBitAtomCodePolynomial (termCode : Nat) : Nat :=
  bitAtomArityCodePolynomial
    (tokenSliceClosedTermBitTermCodeCeiling termCode)

def tokenSliceClosedTermBitAtomFixedPayloadPolynomial
    (numericBound termCode bitBound : Nat) : Nat :=
  binaryBitValuationFixedAtomPayloadPolynomial numericBound
    (tokenSliceClosedTermBitTermCodeCeiling termCode)
    (tokenSliceBitPositionTraceWidth numericBound) bitBound

private theorem binaryFunctionTerm_freeVariables_closedTokenSlice
    {arity : Nat}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
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

private theorem closedTokenSliceAdd_freeVariables
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (‘!!left + !!right’ :
      LO.FirstOrder.ArithmeticSemiterm Nat arity).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  rw [arithmeticAddTerm_eq_func_tokenSliceUniversalTerm]
  exact binaryFunctionTerm_freeVariables_closedTokenSlice Language.Add.add
    left right

private theorem closedTokenSliceMul_freeVariables
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (‘!!left * !!right’ :
      LO.FirstOrder.ArithmeticSemiterm Nat arity).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  rw [arithmeticMulTerm_eq_func_tokenSliceUniversalTerm]
  exact binaryFunctionTerm_freeVariables_closedTokenSlice Language.Mul.mul
    left right

private theorem termValue_closedTokenSliceAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (‘!!left + !!right’) =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func_tokenSliceUniversalTerm]
  exact termValue_add valuation ![left, right]

private theorem termValue_closedTokenSliceMul
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (‘!!left * !!right’) =
      termValue valuation left * termValue valuation right := by
  rw [arithmeticMulTerm_eq_func_tokenSliceUniversalTerm]
  exact termValue_mul valuation ![left, right]

theorem tokenSliceClosedTerms_freeVariables
    (tokenTableTerm widthTerm startTerm : ValuationTerm)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hwidthClosed : widthTerm.freeVariables = ∅)
    (hstartClosed : startTerm.freeVariables = ∅) :
    let indexTerm := tokenSliceAtValuationBitIndexTerm startTerm widthTerm
    let valueTerm := Rew.shift (Rew.shift tokenTableTerm)
    indexTerm.freeVariables ⊆ {0, 1} ∧
      valueTerm.freeVariables = ∅ := by
  have htableShift :=
    shiftedTerm_freeVariables_eq_empty_of_closed tokenTableTerm htableClosed
  have htableShift2 :=
    shiftedTerm_freeVariables_eq_empty_of_closed (Rew.shift tokenTableTerm)
      htableShift
  have hwidthShift :=
    shiftedTerm_freeVariables_eq_empty_of_closed widthTerm hwidthClosed
  have hwidthShift2 :=
    shiftedTerm_freeVariables_eq_empty_of_closed (Rew.shift widthTerm)
      hwidthShift
  have hstartShift :=
    shiftedTerm_freeVariables_eq_empty_of_closed startTerm hstartClosed
  have hstartShift2 :=
    shiftedTerm_freeVariables_eq_empty_of_closed (Rew.shift startTerm)
      hstartShift
  constructor
  · unfold tokenSliceAtValuationBitIndexTerm
    rw [closedTokenSliceAdd_freeVariables,
      closedTokenSliceMul_freeVariables,
      closedTokenSliceAdd_freeVariables,
      hstartShift2, hwidthShift2]
    simpa [Finset.subset_iff, or_comm]
  · exact htableShift2

theorem tokenSliceClosedTerms_code_le
    (tokenTableTerm widthTerm startTerm : ValuationTerm)
    (termCode : Nat)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termCode)
    (hwidthCode : (binaryTermCode widthTerm).length <= termCode)
    (hstartCode : (binaryTermCode startTerm).length <= termCode) :
    let indexTerm := tokenSliceAtValuationBitIndexTerm startTerm widthTerm
    let valueTerm := Rew.shift (Rew.shift tokenTableTerm)
    (binaryTermCode indexTerm).length <=
        tokenSliceClosedTermBitTermCodeCeiling termCode ∧
      (binaryTermCode valueTerm).length <=
        tokenSliceClosedTermBitTermCodeCeiling termCode := by
  let startShift := Rew.shift (Rew.shift startTerm)
  let widthShift := Rew.shift (Rew.shift widthTerm)
  let tableShift := Rew.shift (Rew.shift tokenTableTerm)
  let firstAdd :=
    paAddTerm startShift (&1 : ValuationTerm)
  let product := paMulTerm firstAdd widthShift
  let indexTerm := paAddTerm product (&0 : ValuationTerm)
  have htableShift1 := binaryTermCode_shift_length_le tokenTableTerm
  have htableShift2 := binaryTermCode_shift_length_le
    (Rew.shift tokenTableTerm)
  have hwidthShift1 := binaryTermCode_shift_length_le widthTerm
  have hwidthShift2 := binaryTermCode_shift_length_le (Rew.shift widthTerm)
  have hstartShift1 := binaryTermCode_shift_length_le startTerm
  have hstartShift2 := binaryTermCode_shift_length_le (Rew.shift startTerm)
  have hfirstAdd := paAddTerm_code_length_le startShift
    (&1 : ValuationTerm)
  have hproduct := paMulTerm_code_length_le firstAdd widthShift
  have hindex := paAddTerm_code_length_le product (&0 : ValuationTerm)
  constructor
  · unfold tokenSliceAtValuationBitIndexTerm
    change (binaryTermCode indexTerm).length <= _
    unfold tokenSliceClosedTermBitTermCodeCeiling
    dsimp only [startShift, widthShift, tableShift, firstAdd, product,
      indexTerm] at *
    omega
  · unfold tokenSliceClosedTermBitTermCodeCeiling
    dsimp only [startShift, widthShift, tableShift, firstAdd, product,
      indexTerm] at *
    omega

theorem tokenSliceClosedTermBitAtom_freeVariables_subset
    (tokenTableTerm widthTerm startTerm : ValuationTerm)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hwidthClosed : widthTerm.freeVariables = ∅)
    (hstartClosed : startTerm.freeVariables = ∅) :
    (tokenSliceAtValuationBitAtom tokenTableTerm startTerm
      widthTerm).freeVariables ⊆ {0, 1} := by
  let indexTerm := tokenSliceAtValuationBitIndexTerm startTerm widthTerm
  let valueTerm := Rew.shift (Rew.shift tokenTableTerm)
  have hterms := tokenSliceClosedTerms_freeVariables tokenTableTerm widthTerm
    startTerm htableClosed hwidthClosed hstartClosed
  have hunion :
      indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆ {0, 1} := by
    rw [hterms.2, Finset.union_empty]
    exact hterms.1
  have hraw :=
    binaryBitAtValuationFormula_freeVariables_subset true indexTerm valueTerm
  have hformula :
      tokenSliceAtValuationBitAtom tokenTableTerm startTerm widthTerm =
        binaryBitAtValuationFormula true indexTerm valueTerm := by
    simp [tokenSliceAtValuationBitAtom, indexTerm, valueTerm,
      binaryBitAtValuationFormula, binaryBitLiteralAtTerms]
  rw [hformula]
  exact hraw.trans hunion

theorem tokenSliceClosedTermBitAtom_code_le
    (tokenTableTerm widthTerm startTerm : ValuationTerm)
    (termCode : Nat)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termCode)
    (hwidthCode : (binaryTermCode widthTerm).length <= termCode)
    (hstartCode : (binaryTermCode startTerm).length <= termCode) :
    (binaryFormulaCode
      (tokenSliceAtValuationBitAtom tokenTableTerm startTerm
        widthTerm)).length <=
      tokenSliceClosedTermBitAtomCodePolynomial termCode := by
  let indexTerm := tokenSliceAtValuationBitIndexTerm startTerm widthTerm
  let valueTerm := Rew.shift (Rew.shift tokenTableTerm)
  have hcodes := tokenSliceClosedTerms_code_le tokenTableTerm widthTerm
    startTerm termCode htableCode hwidthCode hstartCode
  have hraw := binaryBitAtomAtTerms_code_length_le_arity indexTerm valueTerm
    (tokenSliceClosedTermBitTermCodeCeiling termCode) hcodes.1 hcodes.2
  simpa only [tokenSliceAtValuationBitAtom, indexTerm, valueTerm,
    tokenSliceClosedTermBitAtomCodePolynomial] using hraw

theorem tokenSliceAtValuationBitAtomStructuralEnvelope_le_closedFixed
    (expected : Bool) (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm startTerm : ValuationTerm)
    (offset bitIndex numericBound termCode bitBound : Nat)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hwidthClosed : widthTerm.freeVariables = ∅)
    (hstartClosed : startTerm.freeVariables = ∅)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termCode)
    (hwidthCode : (binaryTermCode widthTerm).length <= termCode)
    (hstartCode : (binaryTermCode startTerm).length <= termCode)
    (hwidth : termValue valuation widthTerm <= numericBound)
    (hstart : termValue valuation startTerm <= numericBound)
    (hoffset : offset <= numericBound)
    (hbitIndex : bitIndex < termValue valuation widthTerm)
    (htableSize : Nat.size (termValue valuation tokenTableTerm) <= bitBound) :
    tokenSliceAtValuationBitAtomStructuralEnvelope expected valuation
        tokenTableTerm startTerm widthTerm offset bitIndex <=
      tokenSliceClosedTermBitAtomFixedPayloadPolynomial numericBound termCode
        bitBound := by
  let branchValuation :=
    extendValuation bitIndex (extendValuation offset valuation)
  let indexTerm := tokenSliceAtValuationBitIndexTerm startTerm widthTerm
  let valueTerm := Rew.shift (Rew.shift tokenTableTerm)
  have hvariables := tokenSliceClosedTerms_freeVariables tokenTableTerm
    widthTerm startTerm htableClosed hwidthClosed hstartClosed
  have hcodes := tokenSliceClosedTerms_code_le tokenTableTerm widthTerm
    startTerm termCode htableCode hwidthCode hstartCode
  have hindexValue :
      termValue branchValuation indexTerm =
        (termValue valuation startTerm + offset) *
          termValue valuation widthTerm + bitIndex := by
    simp [branchValuation, indexTerm,
      tokenSliceAtValuationBitIndexTerm, termValue_closedTokenSliceAdd,
      termValue_closedTokenSliceMul, termValue_shift]
  have hvalueValue :
      termValue branchValuation valueTerm =
        termValue valuation tokenTableTerm := by
    simp [branchValuation, valueTerm, termValue_shift]
  have hunion :
      indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆ {0, 1} := by
    rw [hvariables.2, Finset.union_empty]
    exact hvariables.1
  have hcard :
      (indexTerm.freeVariables ∪ valueTerm.freeVariables).card <= 4 :=
    (Finset.card_le_card hunion).trans (by simp)
  have hvalues : forall coordinate,
      coordinate ∈ indexTerm.freeVariables ∪ valueTerm.freeVariables ->
        branchValuation coordinate <= numericBound := by
    intro coordinate hcoordinate
    have hsmall := hunion hcoordinate
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsmall
    rcases hsmall with rfl | rfl
    · simp only [branchValuation, extendValuation_zero]
      exact (Nat.le_of_lt hbitIndex).trans hwidth
    · simp only [branchValuation, extendValuation_succ,
        extendValuation_zero]
      exact hoffset
  have hindexTrace :
      termValue branchValuation indexTerm <
        tokenSliceBitPositionTraceWidth numericBound := by
    rw [hindexValue]
    exact tokenSliceBitPosition_lt_traceWidth
      (termValue valuation widthTerm) (termValue valuation startTerm)
      offset bitIndex numericBound hwidth hstart hoffset hbitIndex
  have hvalueSize :
      Nat.size (termValue branchValuation valueTerm) <= bitBound := by
    rw [hvalueValue]
    exact htableSize
  have hraw := binaryBitLiteralAtValuationStructuralEnvelope_le_fixed
    expected branchValuation indexTerm valueTerm numericBound
    (tokenSliceClosedTermBitTermCodeCeiling termCode)
    (tokenSliceBitPositionTraceWidth numericBound) bitBound hcard hvalues
    hcodes.1 hcodes.2 hindexTrace hvalueSize
  simpa only [tokenSliceAtValuationBitAtomStructuralEnvelope,
    tokenSliceClosedTermBitAtomFixedPayloadPolynomial, branchValuation,
    indexTerm, valueTerm] using hraw

#print axioms tokenSliceClosedTerms_freeVariables
#print axioms tokenSliceClosedTerms_code_le
#print axioms tokenSliceClosedTermBitAtom_freeVariables_subset
#print axioms tokenSliceClosedTermBitAtom_code_le
#print axioms
  tokenSliceAtValuationBitAtomStructuralEnvelope_le_closedFixed

end FoundationCompactNumericListedDirectTokenSliceBitAtomClosedTermFixedBounds
