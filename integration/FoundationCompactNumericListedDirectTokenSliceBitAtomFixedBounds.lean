import integration.FoundationCompactNumericListedDirectTokenSlicePublicBounds
import integration.FoundationCompactPABinaryBitValuationFixedPolynomialBounds
import integration.FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
import integration.FoundationCompactSyntaxTransformationCodeBounds
import integration.FoundationCompactPAHybridDisjunctionGeneralContextBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactListedLocalCostPrimitives

/-!
# Fixed bounds for token-slice bit atoms

This layer instantiates the open valuation bit compiler at the concrete
two-binder token-slice index.  The offset and bit-index valuation coordinates
are eliminated in favor of one numeric bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceBitAtomFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABinaryBitValuationFixedPolynomialBounds
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABitMembershipValuationCompilerPublicBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPABitMembershipValuationContextCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds

private theorem arithmeticAddTerm_eq_func_tokenSliceFixed
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      LO.FirstOrder.Semiterm.func Language.Add.add ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func_tokenSliceFixed
    (left right : ValuationTerm) :
    (‘!!left * !!right’ : ValuationTerm) =
      LO.FirstOrder.Semiterm.func Language.Mul.mul ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Mul.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd_tokenSliceFixed
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (‘!!left + !!right’) =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func_tokenSliceFixed]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticMul_tokenSliceFixed
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (‘!!left * !!right’) =
      termValue valuation left * termValue valuation right := by
  rw [arithmeticMulTerm_eq_func_tokenSliceFixed]
  exact termValue_mul valuation ![left, right]

def tokenSliceBitPositionTraceWidth (numericBound : Nat) : Nat :=
  (numericBound + numericBound) * numericBound + numericBound + 1

def tokenSliceBitTermCodeCeiling (bitBound : Nat) : Nat :=
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let shiftedCode := 4 * numeralCode
  let firstAddCode :=
    shiftedCode + (binaryTermCode (&1 : ValuationTerm)).length +
      binaryFunctionTermCodeOverhead Language.Add.add
  let productCode :=
    firstAddCode + shiftedCode +
      binaryFunctionTermCodeOverhead Language.Mul.mul
  productCode + (binaryTermCode (&0 : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

def tokenSliceBitAtomFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  binaryBitValuationFixedAtomPayloadPolynomial numericBound
    (tokenSliceBitTermCodeCeiling bitBound)
    (tokenSliceBitPositionTraceWidth numericBound) bitBound

def tokenSliceBitBranchVariableCodeCeiling : Nat :=
  (binaryTermCode (&0 : ValuationTerm)).length +
    (binaryTermCode (&1 : ValuationTerm)).length + 1

def tokenSliceBitBranchContextCodePolynomial (numericBound : Nat) : Nat :=
  valuationContextFormulaCodeSumEnvelope 2 numericBound
    tokenSliceBitBranchVariableCodeCeiling

def tokenSliceBitAtomCodePolynomial (bitBound : Nat) : Nat :=
  binaryBitAtomFormulaCodeEnvelope (tokenSliceBitTermCodeCeiling bitBound)

def tokenSliceBitBranchSyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  tokenSliceBitBranchContextCodePolynomial numericBound +
    8 * tokenSliceBitAtomCodePolynomial bitBound + 65

def tokenSliceBitSingleBranchFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let atomResource :=
    tokenSliceBitAtomFixedPayloadPolynomial numericBound bitBound
  let disjunctionResource :=
    hybridDisjunctionGeneralPayloadEnvelope
      (tokenSliceBitBranchSyntaxPolynomial numericBound bitBound)
      atomResource
  hybridConjunctionGeneralPayloadEnvelope
    (tokenSliceBitBranchSyntaxPolynomial numericBound bitBound)
    disjunctionResource disjunctionResource

def tokenSliceBitBranchesFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  2 * tokenSliceBitSingleBranchFixedPayloadPolynomial numericBound bitBound

private theorem binaryFunctionTerm_freeVariables_tokenSliceFixed
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiterm.func functionSymbol ![left, right]).freeVariables =
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

private theorem paAddTerm_freeVariables_tokenSliceFixed
    (left right : ValuationTerm) :
    (paAddTerm left right).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [← finiteCaseAddTerm_eq_paAddTerm]
  exact binaryFunctionTerm_freeVariables_tokenSliceFixed
    Language.Add.add left right

private theorem paMulTerm_freeVariables_tokenSliceFixed
    (left right : ValuationTerm) :
    (paMulTerm left right).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [← finiteCaseMulTerm_eq_paMulTerm]
  exact binaryFunctionTerm_freeVariables_tokenSliceFixed
    Language.Mul.mul left right

theorem tokenSliceBitTerms_freeVariables
    (tokenTable width start : Nat) :
    let tableTerm := shortBinaryNumeralTerm tokenTable
    let widthTerm := shortBinaryNumeralTerm width
    let startTerm := shortBinaryNumeralTerm start
    let indexTerm := tokenSliceAtValuationBitIndexTerm startTerm widthTerm
    let valueTerm := Rew.shift (Rew.shift tableTerm)
    indexTerm.freeVariables ⊆ {0, 1} ∧
      valueTerm.freeVariables = ∅ := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let startTerm := shortBinaryNumeralTerm start
  have htable := shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  have hwidth := shortBinaryNumeralTerm_freeVariables_eq_empty width
  have hstart := shortBinaryNumeralTerm_freeVariables_eq_empty start
  have htableShift :=
    shiftedTerm_freeVariables_eq_empty_of_closed tableTerm htable
  have htableShift2 :=
    shiftedTerm_freeVariables_eq_empty_of_closed (Rew.shift tableTerm)
      htableShift
  have hwidthShift :=
    shiftedTerm_freeVariables_eq_empty_of_closed widthTerm hwidth
  have hwidthShift2 :=
    shiftedTerm_freeVariables_eq_empty_of_closed (Rew.shift widthTerm)
      hwidthShift
  have hstartShift :=
    shiftedTerm_freeVariables_eq_empty_of_closed startTerm hstart
  have hstartShift2 :=
    shiftedTerm_freeVariables_eq_empty_of_closed (Rew.shift startTerm)
      hstartShift
  constructor
  · unfold tokenSliceAtValuationBitIndexTerm
    change
      (paAddTerm
        (paMulTerm
          (paAddTerm (Rew.shift (Rew.shift startTerm))
            (&1 : ValuationTerm))
          (Rew.shift (Rew.shift widthTerm)))
        (&0 : ValuationTerm)).freeVariables ⊆ {0, 1}
    rw [paAddTerm_freeVariables_tokenSliceFixed,
      paMulTerm_freeVariables_tokenSliceFixed,
      paAddTerm_freeVariables_tokenSliceFixed,
      hstartShift2, hwidthShift2]
    simpa [Finset.subset_iff, or_comm]
  · exact htableShift2

theorem tokenSliceBitTermCodes_le
    (tokenTable width start bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hstartSize : Nat.size start <= bitBound) :
    let tableTerm := shortBinaryNumeralTerm tokenTable
    let widthTerm := shortBinaryNumeralTerm width
    let startTerm := shortBinaryNumeralTerm start
    let indexTerm := tokenSliceAtValuationBitIndexTerm startTerm widthTerm
    let valueTerm := Rew.shift (Rew.shift tableTerm)
    (binaryTermCode indexTerm).length <=
        tokenSliceBitTermCodeCeiling bitBound ∧
      (binaryTermCode valueTerm).length <=
        tokenSliceBitTermCodeCeiling bitBound := by
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let startTerm := shortBinaryNumeralTerm start
  have htableCode :=
    binaryNumeralTerm_code_length_le_envelope tokenTable bitBound htableSize
  have hwidthCode :=
    binaryNumeralTerm_code_length_le_envelope width bitBound hwidthSize
  have hstartCode :=
    binaryNumeralTerm_code_length_le_envelope start bitBound hstartSize
  have htableShift := binaryTermCode_shift_length_le tableTerm
  have htableShift2 := binaryTermCode_shift_length_le (Rew.shift tableTerm)
  have hwidthShift := binaryTermCode_shift_length_le widthTerm
  have hwidthShift2 := binaryTermCode_shift_length_le (Rew.shift widthTerm)
  have hstartShift := binaryTermCode_shift_length_le startTerm
  have hstartShift2 := binaryTermCode_shift_length_le (Rew.shift startTerm)
  let firstAdd :=
    paAddTerm (Rew.shift (Rew.shift startTerm)) (&1 : ValuationTerm)
  let product :=
    paMulTerm firstAdd (Rew.shift (Rew.shift widthTerm))
  have hfirstAdd := paAddTerm_code_length_le
    (Rew.shift (Rew.shift startTerm)) (&1 : ValuationTerm)
  have hproduct := paMulTerm_code_length_le firstAdd
    (Rew.shift (Rew.shift widthTerm))
  have hindex := paAddTerm_code_length_le product (&0 : ValuationTerm)
  dsimp only [tableTerm] at htableShift htableShift2
  dsimp only [widthTerm] at hwidthShift hwidthShift2
  dsimp only [startTerm] at hstartShift hstartShift2
  constructor
  · unfold tokenSliceAtValuationBitIndexTerm
    change
      (binaryTermCode (paAddTerm product (&0 : ValuationTerm))).length <= _
    unfold tokenSliceBitTermCodeCeiling
    dsimp only [numeralCode, tableTerm, widthTerm, startTerm, firstAdd,
      product] at *
    omega
  · unfold tokenSliceBitTermCodeCeiling
    change
      (binaryTermCode
        (Rew.shift (Rew.shift tableTerm))).length <= _
    dsimp only [numeralCode, tableTerm, widthTerm, startTerm, firstAdd,
      product] at *
    omega

theorem tokenSliceBitBranchContext_formulaCodeSum_le
    (valuation : Nat -> Nat) (vars : Finset Nat)
    (offset bitIndex numericBound : Nat)
    (hvars : vars ⊆ {0, 1})
    (hoffset : offset <= numericBound)
    (hbitIndex : bitIndex <= numericBound) :
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
        (valuationContext vars
          (extendValuation bitIndex (extendValuation offset valuation))) <=
      tokenSliceBitBranchContextCodePolynomial numericBound := by
  let branchValuation :=
    extendValuation bitIndex (extendValuation offset valuation)
  have hcard : vars.card <= 2 :=
    (Finset.card_le_card hvars).trans (by simp)
  have hvalues : forall coordinate, coordinate ∈ vars ->
      branchValuation coordinate <= numericBound := by
    intro coordinate hcoordinate
    have hsmall := hvars hcoordinate
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsmall
    rcases hsmall with rfl | rfl
    · simp only [branchValuation, extendValuation_zero]
      exact hbitIndex
    · simp only [branchValuation, extendValuation_succ,
        extendValuation_zero]
      exact hoffset
  have hvariableCodes : forall coordinate, coordinate ∈ vars ->
      (binaryTermCode (&coordinate : ValuationTerm)).length <=
        tokenSliceBitBranchVariableCodeCeiling := by
    intro coordinate hcoordinate
    have hsmall := hvars hcoordinate
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsmall
    rcases hsmall with rfl | rfl <;>
      unfold tokenSliceBitBranchVariableCodeCeiling <;> omega
  have hraw := valuationContext_formulaCodeSum_le_uniform vars
    branchValuation 2 numericBound tokenSliceBitBranchVariableCodeCeiling
    hcard hvalues hvariableCodes
  simpa only [branchValuation, tokenSliceBitBranchContextCodePolynomial,
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum,
    FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum] using
      hraw

theorem tokenSliceBitAtom_freeVariables_subset
    (tokenTable width start : Nat) :
    (tokenSliceAtValuationBitAtom
      (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm start)
      (shortBinaryNumeralTerm width)).freeVariables ⊆ {0, 1} := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let startTerm := shortBinaryNumeralTerm start
  let indexTerm := tokenSliceAtValuationBitIndexTerm startTerm widthTerm
  let valueTerm := Rew.shift (Rew.shift tableTerm)
  have hterms := tokenSliceBitTerms_freeVariables tokenTable width start
  have hunion :
      indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆ {0, 1} := by
    have hindex : indexTerm.freeVariables ⊆ {0, 1} := by
      simpa only [indexTerm, widthTerm, startTerm] using hterms.1
    have hvalue : valueTerm.freeVariables = ∅ := by
      simpa only [valueTerm, tableTerm] using hterms.2
    rw [hvalue, Finset.union_empty]
    exact hindex
  have hraw :=
    binaryBitAtValuationFormula_freeVariables_subset true indexTerm valueTerm
  have hformula :
      tokenSliceAtValuationBitAtom tableTerm startTerm widthTerm =
        binaryBitAtValuationFormula true indexTerm valueTerm := by
    simp [tokenSliceAtValuationBitAtom, indexTerm, valueTerm,
      binaryBitAtValuationFormula, binaryBitLiteralAtTerms]
  rw [hformula]
  exact hraw.trans hunion

theorem tokenSliceBitAtom_code_le
    (tokenTable width start bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hstartSize : Nat.size start <= bitBound) :
    (binaryFormulaCode
      (tokenSliceAtValuationBitAtom
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm start)
        (shortBinaryNumeralTerm width))).length <=
      tokenSliceBitAtomCodePolynomial bitBound := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let startTerm := shortBinaryNumeralTerm start
  let indexTerm := tokenSliceAtValuationBitIndexTerm startTerm widthTerm
  let valueTerm := Rew.shift (Rew.shift tableTerm)
  have hcodes := tokenSliceBitTermCodes_le tokenTable width start bitBound
    htableSize hwidthSize hstartSize
  have hindex :
      (binaryTermCode indexTerm).length <=
        tokenSliceBitTermCodeCeiling bitBound := by
    simpa only [indexTerm, widthTerm, startTerm] using hcodes.1
  have hvalue :
      (binaryTermCode valueTerm).length <=
        tokenSliceBitTermCodeCeiling bitBound := by
    simpa only [valueTerm, tableTerm] using hcodes.2
  have hraw := binaryBitAtomAtTerms_code_length_le_uniform indexTerm
    valueTerm (tokenSliceBitTermCodeCeiling bitBound) hindex hvalue
  simpa only [tokenSliceAtValuationBitAtom, indexTerm, valueTerm, tableTerm,
    widthTerm, startTerm, tokenSliceBitAtomCodePolynomial] using hraw

private theorem tokenSliceBitIndex_value
    (valuation : Nat -> Nat) (width start offset bitIndex : Nat) :
    let branchValuation :=
      extendValuation bitIndex (extendValuation offset valuation)
    let widthTerm := shortBinaryNumeralTerm width
    let startTerm := shortBinaryNumeralTerm start
    termValue branchValuation
        (tokenSliceAtValuationBitIndexTerm startTerm widthTerm) =
      (start + offset) * width + bitIndex := by
  simp [tokenSliceAtValuationBitIndexTerm,
    termValue_arithmeticMul_tokenSliceFixed, termValue_shift,
    termValue_arithmeticAdd_tokenSliceFixed,
    termValue_shortBinaryNumeralTerm]

private theorem tokenSliceBitValue_value
    (valuation : Nat -> Nat) (tokenTable offset bitIndex : Nat) :
    let branchValuation :=
      extendValuation bitIndex (extendValuation offset valuation)
    termValue branchValuation
        (Rew.shift (Rew.shift (shortBinaryNumeralTerm tokenTable))) =
      tokenTable := by
  simp [termValue_shift, termValue_shortBinaryNumeralTerm]

theorem tokenSliceBitPosition_lt_traceWidth
    (width start offset bitIndex numericBound : Nat)
    (hwidth : width <= numericBound)
    (hstart : start <= numericBound)
    (hoffset : offset <= numericBound)
    (hbitIndex : bitIndex < width) :
    (start + offset) * width + bitIndex <
      tokenSliceBitPositionTraceWidth numericBound := by
  have hsum : start + offset <= numericBound + numericBound := by omega
  have hproduct :
      (start + offset) * width <=
        (numericBound + numericBound) * numericBound :=
    Nat.mul_le_mul hsum hwidth
  unfold tokenSliceBitPositionTraceWidth
  omega

theorem tokenSliceAtValuationBitAtomStructuralEnvelope_le_fixed
    (expected : Bool) (valuation : Nat -> Nat)
    (tokenTable width start offset bitIndex numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (hstart : start <= numericBound)
    (hoffset : offset <= numericBound)
    (hbitIndex : bitIndex < width)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hstartSize : Nat.size start <= bitBound) :
    tokenSliceAtValuationBitAtomStructuralEnvelope expected valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm start)
        (shortBinaryNumeralTerm width) offset bitIndex <=
      tokenSliceBitAtomFixedPayloadPolynomial numericBound bitBound := by
  let branchValuation :=
    extendValuation bitIndex (extendValuation offset valuation)
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let startTerm := shortBinaryNumeralTerm start
  let indexTerm := tokenSliceAtValuationBitIndexTerm startTerm widthTerm
  let valueTerm := Rew.shift (Rew.shift tableTerm)
  have hvariables :=
    tokenSliceBitTerms_freeVariables tokenTable width start
  have hcodes := tokenSliceBitTermCodes_le tokenTable width start bitBound
    htableSize hwidthSize hstartSize
  have hindexValue :
      termValue branchValuation indexTerm =
        (start + offset) * width + bitIndex := by
    simpa only [branchValuation, indexTerm, widthTerm, startTerm] using
      tokenSliceBitIndex_value valuation width start offset bitIndex
  have hvalueValue : termValue branchValuation valueTerm = tokenTable := by
    simpa only [branchValuation, valueTerm, tableTerm] using
      tokenSliceBitValue_value valuation tokenTable offset bitIndex
  have hunion :
      indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆ {0, 1} := by
    have hindex : indexTerm.freeVariables ⊆ {0, 1} := by
      simpa only [indexTerm, widthTerm, startTerm] using hvariables.1
    have hvalue : valueTerm.freeVariables = ∅ := by
      simpa only [valueTerm, tableTerm] using hvariables.2
    rw [hvalue, Finset.union_empty]
    exact hindex
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
      omega
    · simp only [branchValuation, extendValuation_succ,
        extendValuation_zero]
      exact hoffset
  have hindexCode :
      (binaryTermCode indexTerm).length <=
        tokenSliceBitTermCodeCeiling bitBound := by
    simpa only [indexTerm, widthTerm, startTerm] using hcodes.1
  have hvalueCode :
      (binaryTermCode valueTerm).length <=
        tokenSliceBitTermCodeCeiling bitBound := by
    simpa only [valueTerm, tableTerm] using hcodes.2
  have hindexTrace :
      termValue branchValuation indexTerm <
        tokenSliceBitPositionTraceWidth numericBound := by
    rw [hindexValue]
    exact tokenSliceBitPosition_lt_traceWidth width start offset bitIndex
      numericBound hwidth hstart hoffset hbitIndex
  have hvalueSize :
      Nat.size (termValue branchValuation valueTerm) <= bitBound := by
    rw [hvalueValue]
    exact htableSize
  have hraw := binaryBitLiteralAtValuationStructuralEnvelope_le_fixed
    expected branchValuation indexTerm valueTerm numericBound
    (tokenSliceBitTermCodeCeiling bitBound)
    (tokenSliceBitPositionTraceWidth numericBound) bitBound hcard hvalues
    hindexCode hvalueCode hindexTrace hvalueSize
  simpa only [tokenSliceAtValuationBitAtomStructuralEnvelope,
    tokenSliceBitAtomFixedPayloadPolynomial, branchValuation, tableTerm,
    widthTerm, startTerm, indexTerm, valueTerm] using hraw

theorem tokenSliceAtValuationBitBranchStructuralEnvelope_le_fixed_aux
    (expected : Bool) (valuation : Nat -> Nat)
    (tokenTable width sourceStart targetStart offset bitIndex numericBound
      bitBound : Nat)
    (hwidth : width <= numericBound)
    (hsourceStart : sourceStart <= numericBound)
    (htargetStart : targetStart <= numericBound)
    (hoffset : offset <= numericBound)
    (hbitIndex : bitIndex < width)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound) :
    (if expected then
      tokenSliceAtValuationBitTrueBranchStructuralEnvelope valuation
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm sourceStart)
          (shortBinaryNumeralTerm targetStart) offset bitIndex
    else
      tokenSliceAtValuationBitFalseBranchStructuralEnvelope valuation
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm sourceStart)
          (shortBinaryNumeralTerm targetStart) offset bitIndex) <=
      tokenSliceBitSingleBranchFixedPayloadPolynomial numericBound
        bitBound := by
  let branchValuation :=
    extendValuation bitIndex (extendValuation offset valuation)
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let sourceStartTerm := shortBinaryNumeralTerm sourceStart
  let targetStartTerm := shortBinaryNumeralTerm targetStart
  let sourceAtom :=
    tokenSliceAtValuationBitAtom tableTerm sourceStartTerm widthTerm
  let targetAtom :=
    tokenSliceAtValuationBitAtom tableTerm targetStartTerm widthTerm
  let forwardFormula := (∼sourceAtom) ⋎ targetAtom
  let backwardFormula := (∼targetAtom) ⋎ sourceAtom
  let branchFormula := forwardFormula ⋏ backwardFormula
  let atomResource :=
    tokenSliceBitAtomFixedPayloadPolynomial numericBound bitBound
  let syntaxResource :=
    tokenSliceBitBranchSyntaxPolynomial numericBound bitBound
  let disjunctionResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource atomResource
  have hbitIndexBound : bitIndex <= numericBound :=
    (Nat.le_of_lt hbitIndex).trans hwidth
  have hsourceVars : sourceAtom.freeVariables ⊆ {0, 1} := by
    simpa only [sourceAtom, tableTerm, sourceStartTerm, widthTerm] using
      tokenSliceBitAtom_freeVariables_subset tokenTable width sourceStart
  have htargetVars : targetAtom.freeVariables ⊆ {0, 1} := by
    simpa only [targetAtom, tableTerm, targetStartTerm, widthTerm] using
      tokenSliceBitAtom_freeVariables_subset tokenTable width targetStart
  have hnegSourceVars : (∼sourceAtom).freeVariables ⊆ {0, 1} := by
    simpa using hsourceVars
  have hnegTargetVars : (∼targetAtom).freeVariables ⊆ {0, 1} := by
    simpa using htargetVars
  have hforwardVars : forwardFormula.freeVariables ⊆ {0, 1} := by
    dsimp only [forwardFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_or]
    exact Finset.union_subset hnegSourceVars htargetVars
  have hbackwardVars : backwardFormula.freeVariables ⊆ {0, 1} := by
    dsimp only [backwardFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_or]
    exact Finset.union_subset hnegTargetVars hsourceVars
  have hbranchVars : branchFormula.freeVariables ⊆ {0, 1} := by
    dsimp only [branchFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hforwardVars hbackwardVars
  have hsourceCode :
      (binaryFormulaCode sourceAtom).length <=
        tokenSliceBitAtomCodePolynomial bitBound := by
    simpa only [sourceAtom, tableTerm, sourceStartTerm, widthTerm] using
      tokenSliceBitAtom_code_le tokenTable width sourceStart bitBound
        htableSize hwidthSize hsourceStartSize
  have htargetCode :
      (binaryFormulaCode targetAtom).length <=
        tokenSliceBitAtomCodePolynomial bitBound := by
    simpa only [targetAtom, tableTerm, targetStartTerm, widthTerm] using
      tokenSliceBitAtom_code_le tokenTable width targetStart bitBound
        htableSize hwidthSize htargetStartSize
  have hnegSourceRaw := binaryFormulaCode_neg_length_le sourceAtom
  have hnegTargetRaw := binaryFormulaCode_neg_length_le targetAtom
  have hforwardRaw :=
    binaryFormulaCode_or_length_le (∼sourceAtom) targetAtom
  have hbackwardRaw :=
    binaryFormulaCode_or_length_le (∼targetAtom) sourceAtom
  have hbranchRaw :=
    binaryFormulaCode_and_length_le forwardFormula backwardFormula
  have hsyntaxPositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold tokenSliceBitBranchSyntaxPolynomial
    omega
  have hsourceSyntax :
      (binaryFormulaCode sourceAtom).length <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold tokenSliceBitBranchSyntaxPolynomial
    omega
  have htargetSyntax :
      (binaryFormulaCode targetAtom).length <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold tokenSliceBitBranchSyntaxPolynomial
    omega
  have hnegSourceSyntax :
      (binaryFormulaCode (∼sourceAtom)).length <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold tokenSliceBitBranchSyntaxPolynomial
    omega
  have hnegTargetSyntax :
      (binaryFormulaCode (∼targetAtom)).length <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold tokenSliceBitBranchSyntaxPolynomial
    omega
  have hforwardSyntax :
      (binaryFormulaCode forwardFormula).length <= syntaxResource := by
    dsimp only [forwardFormula, syntaxResource] at hforwardRaw ⊢
    unfold tokenSliceBitBranchSyntaxPolynomial
    omega
  have hbackwardSyntax :
      (binaryFormulaCode backwardFormula).length <= syntaxResource := by
    dsimp only [backwardFormula, syntaxResource] at hbackwardRaw ⊢
    unfold tokenSliceBitBranchSyntaxPolynomial
    omega
  have hbranchSyntax :
      (binaryFormulaCode branchFormula).length <= syntaxResource := by
    dsimp only [branchFormula, forwardFormula, backwardFormula,
      syntaxResource] at hbranchRaw ⊢
    unfold tokenSliceBitBranchSyntaxPolynomial
    omega
  have hforwardContext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext forwardFormula.freeVariables branchValuation) <=
        syntaxResource := by
    have hraw := tokenSliceBitBranchContext_formulaCodeSum_le valuation
      forwardFormula.freeVariables offset bitIndex numericBound hforwardVars
      hoffset hbitIndexBound
    dsimp only [branchValuation, syntaxResource]
    exact hraw.trans (by
      unfold tokenSliceBitBranchSyntaxPolynomial
      omega)
  have hbackwardContext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext backwardFormula.freeVariables branchValuation) <=
        syntaxResource := by
    have hraw := tokenSliceBitBranchContext_formulaCodeSum_le valuation
      backwardFormula.freeVariables offset bitIndex numericBound hbackwardVars
      hoffset hbitIndexBound
    dsimp only [branchValuation, syntaxResource]
    exact hraw.trans (by
      unfold tokenSliceBitBranchSyntaxPolynomial
      omega)
  have hbranchContext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext branchFormula.freeVariables branchValuation) <=
        syntaxResource := by
    have hraw := tokenSliceBitBranchContext_formulaCodeSum_le valuation
      branchFormula.freeVariables offset bitIndex numericBound hbranchVars
      hoffset hbitIndexBound
    dsimp only [branchValuation, syntaxResource]
    exact hraw.trans (by
      unfold tokenSliceBitBranchSyntaxPolynomial
      omega)
  have hsourceResource :
      tokenSliceAtValuationBitAtomStructuralEnvelope expected valuation
          tableTerm sourceStartTerm widthTerm offset bitIndex <=
        atomResource := by
    simpa only [tableTerm, sourceStartTerm, widthTerm, atomResource] using
      tokenSliceAtValuationBitAtomStructuralEnvelope_le_fixed expected valuation
        tokenTable width sourceStart offset bitIndex numericBound bitBound
        hwidth hsourceStart hoffset hbitIndex htableSize hwidthSize
        hsourceStartSize
  have htargetResource :
      tokenSliceAtValuationBitAtomStructuralEnvelope expected valuation
          tableTerm targetStartTerm widthTerm offset bitIndex <=
        atomResource := by
    simpa only [tableTerm, targetStartTerm, widthTerm, atomResource] using
      tokenSliceAtValuationBitAtomStructuralEnvelope_le_fixed expected valuation
        tokenTable width targetStart offset bitIndex numericBound bitBound
        hwidth htargetStart hoffset hbitIndex htableSize hwidthSize
        htargetStartSize
  have hconjunctionEnvelope :=
    hybridConjunctionStructuralPayloadEnvelope_le_general branchValuation
      forwardFormula backwardFormula disjunctionResource
      disjunctionResource syntaxResource hsyntaxPositive hbranchContext
      hforwardSyntax hbackwardSyntax hbranchSyntax
  cases expected with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hforwardEnvelope :=
        transparentHybridDisjunctionLeftPayloadEnvelope_le_general
          branchValuation (∼sourceAtom) targetAtom atomResource syntaxResource
          hsyntaxPositive hforwardContext hnegSourceSyntax htargetSyntax
          hforwardSyntax
      have hbackwardEnvelope :=
        transparentHybridDisjunctionLeftPayloadEnvelope_le_general
          branchValuation (∼targetAtom) sourceAtom atomResource syntaxResource
          hsyntaxPositive hbackwardContext hnegTargetSyntax hsourceSyntax
          hbackwardSyntax
      have hforwardFixed :
          transparentHybridDisjunctionLeftPayloadEnvelope branchValuation
              (∼sourceAtom) targetAtom
              (tokenSliceAtValuationBitAtomStructuralEnvelope false valuation
                tableTerm sourceStartTerm widthTerm offset bitIndex) <=
            disjunctionResource :=
        (transparentHybridDisjunctionLeftPayloadEnvelope_mono branchValuation
          (∼sourceAtom) targetAtom hsourceResource).trans hforwardEnvelope
      have hbackwardFixed :
          transparentHybridDisjunctionLeftPayloadEnvelope branchValuation
              (∼targetAtom) sourceAtom
              (tokenSliceAtValuationBitAtomStructuralEnvelope false valuation
                tableTerm targetStartTerm widthTerm offset bitIndex) <=
            disjunctionResource :=
        (transparentHybridDisjunctionLeftPayloadEnvelope_mono branchValuation
          (∼targetAtom) sourceAtom htargetResource).trans hbackwardEnvelope
      unfold tokenSliceAtValuationBitFalseBranchStructuralEnvelope
      dsimp only [branchValuation, tableTerm, widthTerm, sourceStartTerm,
        targetStartTerm, sourceAtom, targetAtom, forwardFormula,
        backwardFormula, branchFormula, atomResource, syntaxResource,
        disjunctionResource] at *
      exact
        (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
          hforwardFixed hbackwardFixed).trans
          (hconjunctionEnvelope.trans (by
            unfold tokenSliceBitSingleBranchFixedPayloadPolynomial
            rfl))
  | true =>
      simp only [↓reduceIte]
      have hforwardEnvelope :=
        transparentHybridDisjunctionRightPayloadEnvelope_le_general
          branchValuation (∼sourceAtom) targetAtom atomResource syntaxResource
          hsyntaxPositive hforwardContext hnegSourceSyntax htargetSyntax
          hforwardSyntax
      have hbackwardEnvelope :=
        transparentHybridDisjunctionRightPayloadEnvelope_le_general
          branchValuation (∼targetAtom) sourceAtom atomResource syntaxResource
          hsyntaxPositive hbackwardContext hnegTargetSyntax hsourceSyntax
          hbackwardSyntax
      have hforwardFixed :
          transparentHybridDisjunctionRightPayloadEnvelope branchValuation
              (∼sourceAtom) targetAtom
              (tokenSliceAtValuationBitAtomStructuralEnvelope true valuation
                tableTerm targetStartTerm widthTerm offset bitIndex) <=
            disjunctionResource :=
        (transparentHybridDisjunctionRightPayloadEnvelope_mono branchValuation
          (∼sourceAtom) targetAtom htargetResource).trans hforwardEnvelope
      have hbackwardFixed :
          transparentHybridDisjunctionRightPayloadEnvelope branchValuation
              (∼targetAtom) sourceAtom
              (tokenSliceAtValuationBitAtomStructuralEnvelope true valuation
                tableTerm sourceStartTerm widthTerm offset bitIndex) <=
            disjunctionResource :=
        (transparentHybridDisjunctionRightPayloadEnvelope_mono branchValuation
          (∼targetAtom) sourceAtom hsourceResource).trans hbackwardEnvelope
      unfold tokenSliceAtValuationBitTrueBranchStructuralEnvelope
      dsimp only [branchValuation, tableTerm, widthTerm, sourceStartTerm,
        targetStartTerm, sourceAtom, targetAtom, forwardFormula,
        backwardFormula, branchFormula, atomResource, syntaxResource,
        disjunctionResource] at *
      exact
        (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
          hforwardFixed hbackwardFixed).trans
          (hconjunctionEnvelope.trans (by
            unfold tokenSliceBitSingleBranchFixedPayloadPolynomial
            rfl))

theorem tokenSliceAtValuationBitFalseBranchStructuralEnvelope_le_fixed
    (valuation : Nat -> Nat)
    (tokenTable width sourceStart targetStart offset bitIndex numericBound
      bitBound : Nat)
    (hwidth : width <= numericBound)
    (hsourceStart : sourceStart <= numericBound)
    (htargetStart : targetStart <= numericBound)
    (hoffset : offset <= numericBound)
    (hbitIndex : bitIndex < width)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound) :
    tokenSliceAtValuationBitFalseBranchStructuralEnvelope valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm sourceStart)
        (shortBinaryNumeralTerm targetStart) offset bitIndex <=
      tokenSliceBitSingleBranchFixedPayloadPolynomial numericBound
        bitBound := by
  simpa using
    tokenSliceAtValuationBitBranchStructuralEnvelope_le_fixed_aux false
      valuation tokenTable width sourceStart targetStart offset bitIndex
      numericBound bitBound hwidth hsourceStart htargetStart hoffset hbitIndex
      htableSize hwidthSize hsourceStartSize htargetStartSize

theorem tokenSliceAtValuationBitTrueBranchStructuralEnvelope_le_fixed
    (valuation : Nat -> Nat)
    (tokenTable width sourceStart targetStart offset bitIndex numericBound
      bitBound : Nat)
    (hwidth : width <= numericBound)
    (hsourceStart : sourceStart <= numericBound)
    (htargetStart : targetStart <= numericBound)
    (hoffset : offset <= numericBound)
    (hbitIndex : bitIndex < width)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound) :
    tokenSliceAtValuationBitTrueBranchStructuralEnvelope valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm sourceStart)
        (shortBinaryNumeralTerm targetStart) offset bitIndex <=
      tokenSliceBitSingleBranchFixedPayloadPolynomial numericBound
        bitBound := by
  simpa using
    tokenSliceAtValuationBitBranchStructuralEnvelope_le_fixed_aux true
      valuation tokenTable width sourceStart targetStart offset bitIndex
      numericBound bitBound hwidth hsourceStart htargetStart hoffset hbitIndex
      htableSize hwidthSize hsourceStartSize htargetStartSize

theorem tokenSliceAtValuationBitBranchStructuralEnvelope_le_fixed
    (valuation : Nat -> Nat)
    (tokenTable width sourceStart targetStart offset bitIndex numericBound
      bitBound : Nat)
    (hwidth : width <= numericBound)
    (hsourceStart : sourceStart <= numericBound)
    (htargetStart : targetStart <= numericBound)
    (hoffset : offset <= numericBound)
    (hbitIndex : bitIndex < width)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound) :
    tokenSliceAtValuationBitBranchStructuralEnvelope valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm sourceStart)
        (shortBinaryNumeralTerm targetStart) offset bitIndex <=
      tokenSliceBitBranchesFixedPayloadPolynomial numericBound bitBound := by
  have hfalse :=
    tokenSliceAtValuationBitFalseBranchStructuralEnvelope_le_fixed valuation
      tokenTable width sourceStart targetStart offset bitIndex numericBound
      bitBound hwidth hsourceStart htargetStart hoffset hbitIndex htableSize
      hwidthSize hsourceStartSize htargetStartSize
  have htrue :=
    tokenSliceAtValuationBitTrueBranchStructuralEnvelope_le_fixed valuation
      tokenTable width sourceStart targetStart offset bitIndex numericBound
      bitBound hwidth hsourceStart htargetStart hoffset hbitIndex htableSize
      hwidthSize hsourceStartSize htargetStartSize
  unfold tokenSliceAtValuationBitBranchStructuralEnvelope
    tokenSliceBitBranchesFixedPayloadPolynomial
  omega

def tokenSliceAtValuationBitBranchPayloadSumFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound *
    tokenSliceBitBranchesFixedPayloadPolynomial numericBound bitBound

theorem tokenSliceAtValuationBitBranchPayloadResourceSum_le_fixed
    (valuation : Nat -> Nat)
    (tokenTable width sourceStart targetStart offset numericBound bitBound :
      Nat)
    (hwidth : width <= numericBound)
    (hsourceStart : sourceStart <= numericBound)
    (htargetStart : targetStart <= numericBound)
    (hoffset : offset <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound) :
    tokenSliceAtValuationBitBranchPayloadResourceSum valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm sourceStart)
        (shortBinaryNumeralTerm targetStart) offset <=
      tokenSliceAtValuationBitBranchPayloadSumFixedPolynomial numericBound
        bitBound := by
  unfold tokenSliceAtValuationBitBranchPayloadResourceSum
  rw [termValue_shortBinaryNumeralTerm valuation width]
  calc
    (∑ bitIndex : Fin width,
      tokenSliceAtValuationBitBranchStructuralEnvelope valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm sourceStart)
        (shortBinaryNumeralTerm targetStart) offset bitIndex) <=
      ∑ _bitIndex : Fin width,
        tokenSliceBitBranchesFixedPayloadPolynomial numericBound
          bitBound := by
      apply Finset.sum_le_sum
      intro bitIndex _
      exact tokenSliceAtValuationBitBranchStructuralEnvelope_le_fixed
        valuation tokenTable width sourceStart targetStart offset bitIndex
        numericBound bitBound hwidth hsourceStart htargetStart hoffset
        bitIndex.isLt htableSize hwidthSize hsourceStartSize htargetStartSize
    _ = width *
        tokenSliceBitBranchesFixedPayloadPolynomial numericBound bitBound := by
      simp
    _ <= numericBound *
        tokenSliceBitBranchesFixedPayloadPolynomial numericBound bitBound :=
      Nat.mul_le_mul_right
        (tokenSliceBitBranchesFixedPayloadPolynomial numericBound bitBound)
        hwidth
    _ = tokenSliceAtValuationBitBranchPayloadSumFixedPolynomial numericBound
        bitBound := by
      rfl

#print axioms tokenSliceBitPosition_lt_traceWidth
#print axioms tokenSliceAtValuationBitAtomStructuralEnvelope_le_fixed
#print axioms tokenSliceAtValuationBitBranchStructuralEnvelope_le_fixed
#print axioms tokenSliceAtValuationBitBranchPayloadResourceSum_le_fixed

end FoundationCompactNumericListedDirectTokenSliceBitAtomFixedBounds
