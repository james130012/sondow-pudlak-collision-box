import integration.FoundationCompactNumericListedDirectAtomicRowEqualityPublicBounds
import integration.FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
import integration.FoundationCompactPABitMembershipTraceBudgetBounds
import integration.FoundationCompactPAValuationTermCompilerFixedPolynomialBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexScalarBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalFixedBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexContextualBranchesFixedBounds
import integration.FoundationCompactPAHybridDisjunctionGeneralContextBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds

/-!
# Fixed-polynomial bounds for direct atomic-row equality

This layer starts with the genuinely checked atomic-row certificate and removes
the varying bit position from its four bit-literal compiler resources.  The
resulting per-bit resource depends only on a numeric coordinate and a common
binary-width coordinate.  No represented table-value range is enumerated.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAtomicRowEqualityFixedPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPABoundedUniversalCompiler
open FoundationCompactPABoundedUniversalCompilerBounds
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABitMembershipRuleCompilerBounds
open FoundationCompactPABitMembershipTraceBudgetBounds
open FoundationCompactPABitMembershipValuationContextCompiler
open FoundationCompactPABitMembershipValuationCompilerPublicBounds
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionSuccessor
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexScalarBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexContextualBranchesFixedBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerFixedPolynomialBounds
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationTermCompilerUniformBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactNumericListedDirectAtomicRowEqualityExplicitHybridCertificate
open FoundationCompactNumericListedDirectAtomicRowEqualityPublicBounds

private theorem binaryFunctionTerm_freeVariables_atomicRowFixed
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

private theorem paMulTerm_freeVariables_atomicRowFixed
    (left right : ValuationTerm) :
    (paMulTerm left right).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [← finiteCaseMulTerm_eq_paMulTerm]
  exact binaryFunctionTerm_freeVariables_atomicRowFixed
    Language.Mul.mul left right

private theorem arithmeticAddTerm_eq_func_atomicRowFixed
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticOneTerm_freeVariables_eq_empty_atomicRowFixed :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem arithmeticAddTerm_freeVariables_atomicRowFixed
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [arithmeticAddTerm_eq_func_atomicRowFixed]
  exact binaryFunctionTerm_freeVariables_atomicRowFixed
    Language.Add.add left right

private theorem arithmeticAddTerm_code_length_le_atomicRowFixed
    {arity : Nat}
    (left right : ArithmeticSemiterm Nat arity) :
    (binaryTermCode ‘!!left + !!right’).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        binaryFunctionTermCodeOverhead Language.Add.add := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Matrix.fun_eq_vec_two, binaryTermCode,
    binaryFunctionTermCodeOverhead]
  omega

private theorem binaryRelationFormula_freeVariables_atomicRowFixed
    {boundArity : Nat}
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
    (LO.FirstOrder.Semiformula.rel relationSymbol ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiformula.freeVariables_rel] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiformula.freeVariables_rel]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem termValue_paMulTerm_atomicRowFixed
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (paMulTerm left right) =
      termValue valuation left * termValue valuation right := by
  rw [← finiteCaseMulTerm_eq_paMulTerm]
  exact termValue_mul valuation ![left, right]

private theorem termValue_languageAdd_atomicRowFixed
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation
        (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]) =
      termValue valuation left + termValue valuation right :=
  termValue_add valuation ![left, right]

/-- Uniform syntax coordinate for the two row-offset bit-index terms and the
shifted token-table term. -/
def atomicRowEqShortNumeralBitTermCodeCeiling (bitBound : Nat) : Nat :=
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let productCode := 2 * numeralCode +
    binaryFunctionTermCodeOverhead Language.Mul.mul
  let indexCode := 2 * productCode +
    (binaryTermCode (&0 : ValuationTerm)).length +
      binaryFunctionTermCodeOverhead Language.Add.add
  indexCode + 2 * numeralCode + 1

/-- Strict upper bound for every visited table-bit position. -/
def atomicRowEqBitPositionTraceWidth (numericBound : Nat) : Nat :=
  numericBound * numericBound + numericBound + 1

def atomicRowEqBitValueWidthCeiling
    (numericBound bitBound : Nat) : Nat :=
  atomicRowEqBitPositionTraceWidth numericBound + bitBound + 1

def atomicRowEqBitValuationTermResourcePolynomial
    (numericBound bitBound : Nat) : Nat :=
  2 * binaryNumeralTermCodeEnvelope
      (atomicRowEqBitValueWidthCeiling numericBound bitBound) +
    2 * atomicRowEqShortNumeralBitTermCodeCeiling bitBound + 1

def atomicRowEqBitContextFormulaCodeSumEnvelope
    (numericBound : Nat) : Nat :=
  valuationContextFormulaCodeSumEnvelope 1 numericBound
    (binaryTermCode (&0 : ValuationTerm)).length

def atomicRowEqBitEqualityPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compileTermValueEqualityFixedPayloadPolynomial numericBound
    (atomicRowEqShortNumeralBitTermCodeCeiling bitBound)

def atomicRowEqBitSourcePayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  binaryBitTraceBudgetPayloadPolynomial bitBound
    (atomicRowEqBitPositionTraceWidth numericBound)

def atomicRowEqBitConnectorPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  binaryBitValuationConnectorUniformPolynomial
    (atomicRowEqBitContextFormulaCodeSumEnvelope numericBound)
    (atomicRowEqBitValuationTermResourcePolynomial numericBound bitBound)
    (atomicRowEqBitEqualityPayloadPolynomial numericBound bitBound)

def atomicRowEqBitLiteralFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  atomicRowEqBitSourcePayloadPolynomial numericBound bitBound +
    atomicRowEqBitConnectorPayloadPolynomial numericBound bitBound

theorem atomicRowEqBitTerms_freeVariables_of_shortNumerals
    (tokenTable width left otherLeft : Nat) :
    let tableTerm := shortBinaryNumeralTerm tokenTable
    let widthTerm := shortBinaryNumeralTerm width
    let leftTerm := shortBinaryNumeralTerm left
    let otherLeftTerm := shortBinaryNumeralTerm otherLeft
    (atomicRowEqLeftBitIndexTerm widthTerm leftTerm).freeVariables ⊆ {0} ∧
      (atomicRowEqOtherLeftBitIndexTerm widthTerm
        otherLeftTerm).freeVariables ⊆ {0} ∧
      (atomicRowEqBitValueTerm tableTerm).freeVariables = ∅ := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let leftTerm := shortBinaryNumeralTerm left
  let otherLeftTerm := shortBinaryNumeralTerm otherLeft
  have htable : tableTerm.freeVariables = ∅ := by
    dsimp only [tableTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  have hwidth : widthTerm.freeVariables = ∅ := by
    dsimp only [widthTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  have hleft : leftTerm.freeVariables = ∅ := by
    dsimp only [leftTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty left
  have hother : otherLeftTerm.freeVariables = ∅ := by
    dsimp only [otherLeftTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty otherLeft
  have hleftMul : (paMulTerm leftTerm widthTerm).freeVariables = ∅ := by
    rw [paMulTerm_freeVariables_atomicRowFixed, hleft, hwidth]
    simp
  have hotherMul :
      (paMulTerm otherLeftTerm widthTerm).freeVariables = ∅ := by
    rw [paMulTerm_freeVariables_atomicRowFixed, hother, hwidth]
    simp
  have hleftShift := shiftedTerm_freeVariables_eq_empty_of_closed
    (paMulTerm leftTerm widthTerm) hleftMul
  have hotherShift := shiftedTerm_freeVariables_eq_empty_of_closed
    (paMulTerm otherLeftTerm widthTerm) hotherMul
  have htableShift := shiftedTerm_freeVariables_eq_empty_of_closed
    tableTerm htable
  constructor
  · rw [atomicRowEqLeftBitIndexTerm,
      binaryFunctionTerm_freeVariables_atomicRowFixed, hleftShift]
    simp
  constructor
  · rw [atomicRowEqOtherLeftBitIndexTerm,
      binaryFunctionTerm_freeVariables_atomicRowFixed, hotherShift]
    simp
  · simpa only [atomicRowEqBitValueTerm] using htableShift

theorem atomicRowEqBitTermCodes_le_shortNumeralCeiling
    (tokenTable width left otherLeft bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hleftSize : Nat.size left <= bitBound)
    (hotherSize : Nat.size otherLeft <= bitBound) :
    let tableTerm := shortBinaryNumeralTerm tokenTable
    let widthTerm := shortBinaryNumeralTerm width
    let leftTerm := shortBinaryNumeralTerm left
    let otherLeftTerm := shortBinaryNumeralTerm otherLeft
    (binaryTermCode
      (atomicRowEqLeftBitIndexTerm widthTerm leftTerm)).length <=
        atomicRowEqShortNumeralBitTermCodeCeiling bitBound ∧
      (binaryTermCode
        (atomicRowEqOtherLeftBitIndexTerm widthTerm
          otherLeftTerm)).length <=
        atomicRowEqShortNumeralBitTermCodeCeiling bitBound ∧
      (binaryTermCode
        (atomicRowEqBitValueTerm tableTerm)).length <=
        atomicRowEqShortNumeralBitTermCodeCeiling bitBound := by
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let leftTerm := shortBinaryNumeralTerm left
  let otherLeftTerm := shortBinaryNumeralTerm otherLeft
  have htableCode : (binaryTermCode tableTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope tokenTable bitBound htableSize
  have hwidthCode : (binaryTermCode widthTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope width bitBound hwidthSize
  have hleftCode : (binaryTermCode leftTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope left bitBound hleftSize
  have hotherCode : (binaryTermCode otherLeftTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope otherLeft bitBound hotherSize
  have hleftProduct := paMulTerm_code_length_le leftTerm widthTerm
  have hotherProduct := paMulTerm_code_length_le otherLeftTerm widthTerm
  have hleftShift :=
    binaryTermCode_shift_length_le (paMulTerm leftTerm widthTerm)
  have hotherShift :=
    binaryTermCode_shift_length_le (paMulTerm otherLeftTerm widthTerm)
  have hleftIndexRaw := paAddTerm_code_length_le
    (Rew.shift (paMulTerm leftTerm widthTerm)) (&0 : ValuationTerm)
  have hotherIndexRaw := paAddTerm_code_length_le
    (Rew.shift (paMulTerm otherLeftTerm widthTerm)) (&0 : ValuationTerm)
  have htableShift := binaryTermCode_shift_length_le tableTerm
  constructor
  · unfold atomicRowEqLeftBitIndexTerm
    change (binaryTermCode
      (paAddTerm (Rew.shift (paMulTerm leftTerm widthTerm))
        (&0 : ValuationTerm))).length <= _
    exact hleftIndexRaw.trans (by
      unfold atomicRowEqShortNumeralBitTermCodeCeiling
      dsimp only [numeralCode]
      omega)
  constructor
  · unfold atomicRowEqOtherLeftBitIndexTerm
    change (binaryTermCode
      (paAddTerm (Rew.shift (paMulTerm otherLeftTerm widthTerm))
        (&0 : ValuationTerm))).length <= _
    exact hotherIndexRaw.trans (by
      unfold atomicRowEqShortNumeralBitTermCodeCeiling
      dsimp only [numeralCode]
      omega)
  · unfold atomicRowEqBitValueTerm
    exact htableShift.trans (by
      unfold atomicRowEqShortNumeralBitTermCodeCeiling
      dsimp only [numeralCode]
      omega)

private theorem atomicRowEqLeftBitIndex_value_short
    (valuation : Nat -> Nat) (width left bitIndex : Nat) :
    termValue (extendValuation bitIndex valuation)
        (atomicRowEqLeftBitIndexTerm
          (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm left)) =
      left * width + bitIndex := by
  rw [atomicRowEqLeftBitIndexTerm, termValue_languageAdd_atomicRowFixed,
    termValue_shift, termValue_paMulTerm_atomicRowFixed,
    termValue_shortBinaryNumeralTerm, termValue_shortBinaryNumeralTerm,
    termValue_fvar, extendValuation_zero]

private theorem atomicRowEqOtherLeftBitIndex_value_short
    (valuation : Nat -> Nat) (width otherLeft bitIndex : Nat) :
    termValue (extendValuation bitIndex valuation)
        (atomicRowEqOtherLeftBitIndexTerm
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm otherLeft)) =
      otherLeft * width + bitIndex := by
  rw [atomicRowEqOtherLeftBitIndexTerm,
    termValue_languageAdd_atomicRowFixed, termValue_shift,
    termValue_paMulTerm_atomicRowFixed, termValue_shortBinaryNumeralTerm,
    termValue_shortBinaryNumeralTerm, termValue_fvar,
    extendValuation_zero]

private theorem atomicRowEqBitValue_value_short
    (valuation : Nat -> Nat) (tokenTable bitIndex : Nat) :
    termValue (extendValuation bitIndex valuation)
        (atomicRowEqBitValueTerm (shortBinaryNumeralTerm tokenTable)) =
      tokenTable := by
  rw [atomicRowEqBitValueTerm, termValue_shift,
    termValue_shortBinaryNumeralTerm]

theorem atomicRowEqBitPositions_lt_traceWidth
    (width left otherLeft numericBound bitIndex : Nat)
    (hwidth : width <= numericBound)
    (hleft : left <= numericBound)
    (hother : otherLeft <= numericBound)
    (hbitIndex : bitIndex < width) :
    left * width + bitIndex <
        atomicRowEqBitPositionTraceWidth numericBound ∧
      otherLeft * width + bitIndex <
        atomicRowEqBitPositionTraceWidth numericBound := by
  have hleftMul : left * width <= numericBound * numericBound :=
    Nat.mul_le_mul hleft hwidth
  have hotherMul : otherLeft * width <= numericBound * numericBound :=
    Nat.mul_le_mul hother hwidth
  unfold atomicRowEqBitPositionTraceWidth
  omega

theorem valuationContextFormulaCodeSum_le_atomicRowEqBitEnvelope
    (valuation : Nat -> Nat) (vars : Finset Nat)
    (numericBound : Nat)
    (hvariables : vars ⊆ {0})
    (hvaluation : valuation 0 <= numericBound) :
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
        (valuationContext vars valuation) <=
      atomicRowEqBitContextFormulaCodeSumEnvelope numericBound := by
  have hcard : vars.card <= 1 :=
    (Finset.card_le_card hvariables).trans (by simp)
  have hvalues : forall index, index ∈ vars ->
      valuation index <= numericBound := by
    intro index hindex
    have hsingleton := hvariables hindex
    simp only [Finset.mem_singleton] at hsingleton
    subst index
    exact hvaluation
  have htermCodes : forall index, index ∈ vars ->
      (binaryTermCode (&index : ValuationTerm)).length <=
        (binaryTermCode (&0 : ValuationTerm)).length := by
    intro index hindex
    have hsingleton := hvariables hindex
    simp only [Finset.mem_singleton] at hsingleton
    subst index
    exact le_rfl
  have hraw := valuationContext_formulaCodeSum_le_uniform
    vars valuation 1 numericBound
      (binaryTermCode (&0 : ValuationTerm)).length hcard hvalues htermCodes
  simpa only [
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum,
    FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum,
    atomicRowEqBitContextFormulaCodeSumEnvelope] using hraw

private theorem compileTermValueEqualityPayloadPolynomial_le_atomicRowEqBit
    (valuation : Nat -> Nat) (term : ValuationTerm)
    (numericBound bitBound : Nat)
    (hvariables : term.freeVariables ⊆ {0})
    (hvaluation : valuation 0 <= numericBound)
    (hcode : (binaryTermCode term).length <=
      atomicRowEqShortNumeralBitTermCodeCeiling bitBound) :
    compileTermValueEqualityPayloadPolynomial valuation term <=
      atomicRowEqBitEqualityPayloadPolynomial numericBound bitBound := by
  have hcard : term.freeVariables.card <= 4 :=
    (Finset.card_le_card hvariables).trans (by simp)
  have hvalues : forall index, index ∈ term.freeVariables ->
      valuation index <= numericBound := by
    intro index hindex
    have hsingleton := hvariables hindex
    simp only [Finset.mem_singleton] at hsingleton
    subst index
    exact hvaluation
  have hcoordinate :=
    compileTermValueEqualityPayloadPolynomial_le_coordinate valuation
      numericBound term hcard hvalues
  have hfixed :=
    compileTermValueEqualityUniformPayloadPolynomial_le_fixed numericBound
      (atomicRowEqShortNumeralBitTermCodeCeiling bitBound) term hcard hcode
  exact hcoordinate.trans (by
    simpa only [atomicRowEqBitEqualityPayloadPolynomial] using hfixed)

theorem atomicRowEqBitValuationTermResources_le_fixed
    (valuation : Nat -> Nat)
    (tokenTable width left otherLeft numericBound bitBound bitIndex : Nat)
    (hwidth : width <= numericBound)
    (hleft : left <= numericBound)
    (hother : otherLeft <= numericBound)
    (hbitIndex : bitIndex < width)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hleftSize : Nat.size left <= bitBound)
    (hotherSize : Nat.size otherLeft <= bitBound) :
    let branchValuation := extendValuation bitIndex valuation
    let tableTerm := shortBinaryNumeralTerm tokenTable
    let widthTerm := shortBinaryNumeralTerm width
    let leftTerm := shortBinaryNumeralTerm left
    let otherLeftTerm := shortBinaryNumeralTerm otherLeft
    let leftIndexTerm := atomicRowEqLeftBitIndexTerm widthTerm leftTerm
    let otherIndexTerm :=
      atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm
    let valueTerm := atomicRowEqBitValueTerm tableTerm
    binaryBitValuationTermCodeResource branchValuation leftIndexTerm
        valueTerm <=
          atomicRowEqBitValuationTermResourcePolynomial numericBound
            bitBound ∧
      binaryBitValuationTermCodeResource branchValuation otherIndexTerm
        valueTerm <=
          atomicRowEqBitValuationTermResourcePolynomial numericBound
            bitBound := by
  let branchValuation := extendValuation bitIndex valuation
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let leftTerm := shortBinaryNumeralTerm left
  let otherLeftTerm := shortBinaryNumeralTerm otherLeft
  let leftIndexTerm := atomicRowEqLeftBitIndexTerm widthTerm leftTerm
  let otherIndexTerm :=
    atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm
  let valueTerm := atomicRowEqBitValueTerm tableTerm
  let valueWidth :=
    atomicRowEqBitValueWidthCeiling numericBound bitBound
  let numeralCode := binaryNumeralTermCodeEnvelope valueWidth
  have hpositions := atomicRowEqBitPositions_lt_traceWidth width left
    otherLeft numericBound bitIndex hwidth hleft hother hbitIndex
  have hcodes := atomicRowEqBitTermCodes_le_shortNumeralCeiling tokenTable
    width left otherLeft bitBound htableSize hwidthSize hleftSize hotherSize
  have hleftValue :
      termValue branchValuation leftIndexTerm = left * width + bitIndex := by
    simpa only [branchValuation, leftIndexTerm, widthTerm, leftTerm] using
      atomicRowEqLeftBitIndex_value_short valuation width left bitIndex
  have hotherValue :
      termValue branchValuation otherIndexTerm =
        otherLeft * width + bitIndex := by
    simpa only [branchValuation, otherIndexTerm, widthTerm, otherLeftTerm] using
      atomicRowEqOtherLeftBitIndex_value_short valuation width otherLeft
        bitIndex
  have htableValue : termValue branchValuation valueTerm = tokenTable := by
    simpa only [branchValuation, valueTerm, tableTerm] using
      atomicRowEqBitValue_value_short valuation tokenTable bitIndex
  have hleftSizeValue :
      Nat.size (termValue branchValuation leftIndexTerm) <= valueWidth := by
    rw [hleftValue]
    exact (natSize_le_self_uniform (left * width + bitIndex)).trans (by
      unfold valueWidth atomicRowEqBitValueWidthCeiling
      omega)
  have hotherSizeValue :
      Nat.size (termValue branchValuation otherIndexTerm) <= valueWidth := by
    rw [hotherValue]
    exact (natSize_le_self_uniform (otherLeft * width + bitIndex)).trans (by
      unfold valueWidth atomicRowEqBitValueWidthCeiling
      omega)
  have htableSizeValue :
      Nat.size (termValue branchValuation valueTerm) <= valueWidth := by
    rw [htableValue]
    exact htableSize.trans (by
      unfold valueWidth atomicRowEqBitValueWidthCeiling
      omega)
  have hleftNumeral :=
    binaryNumeralTerm_code_length_le_envelope
      (termValue branchValuation leftIndexTerm) valueWidth hleftSizeValue
  have hotherNumeral :=
    binaryNumeralTerm_code_length_le_envelope
      (termValue branchValuation otherIndexTerm) valueWidth hotherSizeValue
  have htableNumeral :=
    binaryNumeralTerm_code_length_le_envelope
      (termValue branchValuation valueTerm) valueWidth htableSizeValue
  unfold binaryBitValuationTermCodeResource
    atomicRowEqBitValuationTermResourcePolynomial
  dsimp only [branchValuation, tableTerm, widthTerm, leftTerm, otherLeftTerm,
    leftIndexTerm, otherIndexTerm, valueTerm, valueWidth, numeralCode] at *
  constructor <;> omega

theorem compileBinaryBitLiteralAtAtomicRowShortNumeralsPayloadPolynomial_le_fixed
    (expected : Bool) (valuation : Nat -> Nat)
    (tokenTable width left otherLeft numericBound bitBound bitIndex : Nat)
    (useOther : Bool)
    (hwidth : width <= numericBound)
    (hleft : left <= numericBound)
    (hother : otherLeft <= numericBound)
    (hbitIndex : bitIndex < width)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hleftSize : Nat.size left <= bitBound)
    (hotherSize : Nat.size otherLeft <= bitBound) :
    let branchValuation := extendValuation bitIndex valuation
    let tableTerm := shortBinaryNumeralTerm tokenTable
    let widthTerm := shortBinaryNumeralTerm width
    let indexTerm := if useOther then
      atomicRowEqOtherLeftBitIndexTerm widthTerm
        (shortBinaryNumeralTerm otherLeft) else
      atomicRowEqLeftBitIndexTerm widthTerm (shortBinaryNumeralTerm left)
    let valueTerm := atomicRowEqBitValueTerm tableTerm
    compileBinaryBitLiteralAtValuationPayloadPolynomial expected
        branchValuation indexTerm valueTerm <=
      atomicRowEqBitLiteralFixedPayloadPolynomial numericBound bitBound := by
  let branchValuation := extendValuation bitIndex valuation
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let leftTerm := shortBinaryNumeralTerm left
  let otherLeftTerm := shortBinaryNumeralTerm otherLeft
  let leftIndexTerm := atomicRowEqLeftBitIndexTerm widthTerm leftTerm
  let otherIndexTerm :=
    atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm
  let valueTerm := atomicRowEqBitValueTerm tableTerm
  let indexTerm := if useOther then otherIndexTerm else leftIndexTerm
  have hpositions := atomicRowEqBitPositions_lt_traceWidth width left
    otherLeft numericBound bitIndex hwidth hleft hother hbitIndex
  have hterms := atomicRowEqBitTerms_freeVariables_of_shortNumerals
    tokenTable width left otherLeft
  have hcodes := atomicRowEqBitTermCodes_le_shortNumeralCeiling tokenTable
    width left otherLeft bitBound htableSize hwidthSize hleftSize hotherSize
  have hresources := atomicRowEqBitValuationTermResources_le_fixed valuation
    tokenTable width left otherLeft numericBound bitBound bitIndex hwidth hleft
    hother hbitIndex htableSize hwidthSize hleftSize hotherSize
  have hbranchZero : branchValuation 0 <= numericBound := by
    simp only [branchValuation, extendValuation_zero]
    omega
  have hleftVariables : leftIndexTerm.freeVariables ⊆ {0} := by
    simpa only [leftIndexTerm, widthTerm, leftTerm] using hterms.1
  have hotherVariables : otherIndexTerm.freeVariables ⊆ {0} := by
    simpa only [otherIndexTerm, widthTerm, otherLeftTerm] using hterms.2.1
  have hindexVariables : indexTerm.freeVariables ⊆ {0} := by
    dsimp only [indexTerm]
    split
    · exact hotherVariables
    · exact hleftVariables
  have hvalueVariables : valueTerm.freeVariables ⊆ {0} := by
    have hempty : valueTerm.freeVariables = ∅ := hterms.2.2
    rw [hempty]
    simp
  have hindexCode : (binaryTermCode indexTerm).length <=
      atomicRowEqShortNumeralBitTermCodeCeiling bitBound := by
    have hleftCode :
        (binaryTermCode leftIndexTerm).length <=
          atomicRowEqShortNumeralBitTermCodeCeiling bitBound := by
      simpa only [leftIndexTerm, widthTerm, leftTerm] using hcodes.1
    have hotherCode :
        (binaryTermCode otherIndexTerm).length <=
          atomicRowEqShortNumeralBitTermCodeCeiling bitBound := by
      simpa only [otherIndexTerm, widthTerm, otherLeftTerm] using hcodes.2.1
    dsimp only [indexTerm]
    split
    · exact hotherCode
    · exact hleftCode
  have hvalueCode : (binaryTermCode valueTerm).length <=
      atomicRowEqShortNumeralBitTermCodeCeiling bitBound := hcodes.2.2
  have hindexValue :
      termValue branchValuation indexTerm =
        if useOther then otherLeft * width + bitIndex
        else left * width + bitIndex := by
    dsimp only [indexTerm]
    split
    · simpa only [branchValuation, otherIndexTerm, widthTerm, otherLeftTerm]
        using atomicRowEqOtherLeftBitIndex_value_short valuation width
          otherLeft bitIndex
    · simpa only [branchValuation, leftIndexTerm, widthTerm, leftTerm]
        using atomicRowEqLeftBitIndex_value_short valuation width left bitIndex
  have hvalueValue : termValue branchValuation valueTerm = tokenTable := by
    simpa only [branchValuation, valueTerm, tableTerm] using
      atomicRowEqBitValue_value_short valuation tokenTable bitIndex
  have hsource :
      binaryBitLiteralPayloadPolynomial
          (termValue branchValuation indexTerm)
          (termValue branchValuation valueTerm) <=
        atomicRowEqBitSourcePayloadPolynomial numericBound bitBound := by
    apply binaryBitLiteralPayloadPolynomial_le_traceBudget
    · rw [hindexValue]
      split
      · exact hpositions.2
      · exact hpositions.1
    · rw [hvalueValue]
      exact htableSize
  have hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (binaryBitValuationContext branchValuation indexTerm valueTerm) <=
        atomicRowEqBitContextFormulaCodeSumEnvelope numericBound := by
    unfold binaryBitValuationContext
    apply valuationContextFormulaCodeSum_le_atomicRowEqBitEnvelope
    · exact Finset.union_subset hindexVariables hvalueVariables
    · exact hbranchZero
  have htermResource :
      binaryBitValuationTermCodeResource branchValuation indexTerm
          valueTerm <=
        atomicRowEqBitValuationTermResourcePolynomial numericBound
          bitBound := by
    dsimp only [indexTerm]
    split
    · exact hresources.2
    · exact hresources.1
  have hindexEquality :=
    compileTermValueEqualityPayloadPolynomial_le_atomicRowEqBit
      branchValuation indexTerm numericBound bitBound hindexVariables
      hbranchZero hindexCode
  have hvalueEquality :=
    compileTermValueEqualityPayloadPolynomial_le_atomicRowEqBit
      branchValuation valueTerm numericBound bitBound hvalueVariables
      hbranchZero hvalueCode
  have hconnector :=
    compileBinaryBitLiteralAtValuationConnectorPolynomial_le_uniform
      expected branchValuation indexTerm valueTerm
      (atomicRowEqBitContextFormulaCodeSumEnvelope numericBound)
      (atomicRowEqBitValuationTermResourcePolynomial numericBound bitBound)
      (atomicRowEqBitEqualityPayloadPolynomial numericBound bitBound)
      hcontext htermResource hindexEquality hvalueEquality
  cases expected with
  | false =>
      have hnegative :
          compileNegativeBinaryBitAtValuationConnectorPolynomial
              branchValuation indexTerm valueTerm <=
            atomicRowEqBitConnectorPayloadPolynomial numericBound
              bitBound := by
        simpa only [compileBinaryBitLiteralAtValuationConnectorPolynomial,
          Bool.false_eq_true, ↓reduceIte,
          atomicRowEqBitConnectorPayloadPolynomial] using hconnector
      simp only [compileBinaryBitLiteralAtValuationPayloadPolynomial,
        Bool.false_eq_true, ↓reduceIte]
      unfold compileNegativeBinaryBitAtValuationPayloadPolynomial
        atomicRowEqBitLiteralFixedPayloadPolynomial
      exact Nat.add_le_add hsource hnegative
  | true =>
      have hpositive :
          compilePositiveBinaryBitAtValuationConnectorPolynomial
              branchValuation indexTerm valueTerm <=
            atomicRowEqBitConnectorPayloadPolynomial numericBound
              bitBound := by
        simpa only [compileBinaryBitLiteralAtValuationConnectorPolynomial,
          ↓reduceIte, atomicRowEqBitConnectorPayloadPolynomial] using hconnector
      simp only [compileBinaryBitLiteralAtValuationPayloadPolynomial,
        ↓reduceIte]
      unfold compilePositiveBinaryBitAtValuationPayloadPolynomial
        atomicRowEqBitLiteralFixedPayloadPolynomial
      exact Nat.add_le_add hsource hpositive

def atomicRowEqBitLiteralFormulaCodeEnvelope (bitBound : Nat) : Nat :=
  binaryBitLiteralFormulaCodeEnvelope
    (atomicRowEqShortNumeralBitTermCodeCeiling bitBound)

def atomicRowEqBitBranchAssemblySyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  atomicRowEqBitContextFormulaCodeSumEnvelope numericBound +
    16 * (atomicRowEqBitLiteralFormulaCodeEnvelope bitBound +
      (binaryNatCode 4).length + (binaryNatCode 5).length + 1) + 1

def atomicRowEqBitBranchFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  4 * atomicRowEqBitLiteralFixedPayloadPolynomial numericBound bitBound +
    13 * generalContextAssemblyEnvelope
      (atomicRowEqBitBranchAssemblySyntaxPolynomial numericBound bitBound)

private theorem weakeningFullAssemblyCost_insert_le_atomicRowEqGeneral
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (hGamma :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          Gamma <= resource)
    (hformula : (binaryFormulaCode formula).length <= resource) :
    weakeningFullAssemblyCost (insert formula Gamma) <=
      generalContextAssemblyEnvelope resource := by
  apply weakeningFullAssemblyCost_le_general
  have hraw :=
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds.formulaCodeSum_insert_le
      Gamma formula
  unfold generalContextCoordinate
  omega

theorem atomicRowEqBitBranchFormulaCodes_le_fixed
    (tokenTable width left otherLeft bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hleftSize : Nat.size left <= bitBound)
    (hotherSize : Nat.size otherLeft <= bitBound) :
    let tableTerm := shortBinaryNumeralTerm tokenTable
    let widthTerm := shortBinaryNumeralTerm width
    let leftTerm := shortBinaryNumeralTerm left
    let otherLeftTerm := shortBinaryNumeralTerm otherLeft
    let leftIndexTerm := atomicRowEqLeftBitIndexTerm widthTerm leftTerm
    let otherIndexTerm :=
      atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm
    let valueTerm := atomicRowEqBitValueTerm tableTerm
    let leftAtom := binaryBitAtomAtTerms leftIndexTerm valueTerm
    let otherAtom := binaryBitAtomAtTerms otherIndexTerm valueTerm
    let leftTrue := binaryBitAtValuationFormula true leftIndexTerm valueTerm
    let leftFalse := binaryBitAtValuationFormula false leftIndexTerm valueTerm
    let otherTrue := binaryBitAtValuationFormula true otherIndexTerm valueTerm
    let otherFalse :=
      binaryBitAtValuationFormula false otherIndexTerm valueTerm
    let forward := (∼leftAtom ⋎ otherAtom)
    let backward := (∼otherAtom ⋎ leftAtom)
    let target := forward ⋏ backward
    let resource := atomicRowEqBitBranchAssemblySyntaxPolynomial 0 bitBound
    (binaryFormulaCode leftTrue).length <= resource ∧
      (binaryFormulaCode leftFalse).length <= resource ∧
      (binaryFormulaCode otherTrue).length <= resource ∧
      (binaryFormulaCode otherFalse).length <= resource ∧
      (binaryFormulaCode forward).length <= resource ∧
      (binaryFormulaCode backward).length <= resource ∧
      (binaryFormulaCode target).length <= resource := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let leftTerm := shortBinaryNumeralTerm left
  let otherLeftTerm := shortBinaryNumeralTerm otherLeft
  let leftIndexTerm := atomicRowEqLeftBitIndexTerm widthTerm leftTerm
  let otherIndexTerm :=
    atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm
  let valueTerm := atomicRowEqBitValueTerm tableTerm
  let leftAtom := binaryBitAtomAtTerms leftIndexTerm valueTerm
  let otherAtom := binaryBitAtomAtTerms otherIndexTerm valueTerm
  let leftTrue := binaryBitAtValuationFormula true leftIndexTerm valueTerm
  let leftFalse := binaryBitAtValuationFormula false leftIndexTerm valueTerm
  let otherTrue := binaryBitAtValuationFormula true otherIndexTerm valueTerm
  let otherFalse :=
    binaryBitAtValuationFormula false otherIndexTerm valueTerm
  let forward := (∼leftAtom ⋎ otherAtom)
  let backward := (∼otherAtom ⋎ leftAtom)
  let target := forward ⋏ backward
  let literalCode := atomicRowEqBitLiteralFormulaCodeEnvelope bitBound
  let resource := atomicRowEqBitBranchAssemblySyntaxPolynomial 0 bitBound
  have htermCodes := atomicRowEqBitTermCodes_le_shortNumeralCeiling
    tokenTable width left otherLeft bitBound htableSize hwidthSize hleftSize
      hotherSize
  have hleftIndex :
      (binaryTermCode leftIndexTerm).length <=
        atomicRowEqShortNumeralBitTermCodeCeiling bitBound := by
    simpa only [leftIndexTerm, widthTerm, leftTerm] using htermCodes.1
  have hotherIndex :
      (binaryTermCode otherIndexTerm).length <=
        atomicRowEqShortNumeralBitTermCodeCeiling bitBound := by
    simpa only [otherIndexTerm, widthTerm, otherLeftTerm] using
      htermCodes.2.1
  have hvalue :
      (binaryTermCode valueTerm).length <=
        atomicRowEqShortNumeralBitTermCodeCeiling bitBound := by
    simpa only [valueTerm, tableTerm] using htermCodes.2.2
  have hleftTrueRaw := binaryBitLiteralAtTerms_code_length_le_uniform true
    leftIndexTerm valueTerm
    (atomicRowEqShortNumeralBitTermCodeCeiling bitBound) hleftIndex hvalue
  have hleftFalseRaw := binaryBitLiteralAtTerms_code_length_le_uniform false
    leftIndexTerm valueTerm
    (atomicRowEqShortNumeralBitTermCodeCeiling bitBound) hleftIndex hvalue
  have hotherTrueRaw := binaryBitLiteralAtTerms_code_length_le_uniform true
    otherIndexTerm valueTerm
    (atomicRowEqShortNumeralBitTermCodeCeiling bitBound) hotherIndex hvalue
  have hotherFalseRaw := binaryBitLiteralAtTerms_code_length_le_uniform false
    otherIndexTerm valueTerm
    (atomicRowEqShortNumeralBitTermCodeCeiling bitBound) hotherIndex hvalue
  have hleftTrue : (binaryFormulaCode leftTrue).length <= literalCode := by
    simpa only [leftTrue, binaryBitAtValuationFormula,
      literalCode, atomicRowEqBitLiteralFormulaCodeEnvelope] using hleftTrueRaw
  have hleftFalse : (binaryFormulaCode leftFalse).length <= literalCode := by
    simpa only [leftFalse, binaryBitAtValuationFormula,
      literalCode, atomicRowEqBitLiteralFormulaCodeEnvelope] using hleftFalseRaw
  have hotherTrue : (binaryFormulaCode otherTrue).length <= literalCode := by
    simpa only [otherTrue, binaryBitAtValuationFormula,
      literalCode, atomicRowEqBitLiteralFormulaCodeEnvelope] using hotherTrueRaw
  have hotherFalse : (binaryFormulaCode otherFalse).length <= literalCode := by
    simpa only [otherFalse, binaryBitAtValuationFormula,
      literalCode, atomicRowEqBitLiteralFormulaCodeEnvelope] using
      hotherFalseRaw
  have hforwardRaw := binaryFormulaCode_or_length_le_local
    (∼leftAtom) otherAtom
  have hbackwardRaw := binaryFormulaCode_or_length_le_local
    (∼otherAtom) leftAtom
  have hforward : (binaryFormulaCode forward).length <=
      2 * literalCode + (binaryNatCode 5).length := by
    dsimp only [forward]
    have hleftNeg :
        (binaryFormulaCode (∼leftAtom)).length <= literalCode := by
      simpa [leftFalse, leftAtom, binaryBitAtValuationFormula,
        binaryBitLiteralAtTerms] using hleftFalse
    have hotherAtom : (binaryFormulaCode otherAtom).length <= literalCode := by
      simpa [otherTrue, otherAtom, binaryBitAtValuationFormula,
        binaryBitLiteralAtTerms] using hotherTrue
    omega
  have hbackward : (binaryFormulaCode backward).length <=
      2 * literalCode + (binaryNatCode 5).length := by
    dsimp only [backward]
    have hotherNeg :
        (binaryFormulaCode (∼otherAtom)).length <= literalCode := by
      simpa [otherFalse, otherAtom, binaryBitAtValuationFormula,
        binaryBitLiteralAtTerms] using hotherFalse
    have hleftAtom : (binaryFormulaCode leftAtom).length <= literalCode := by
      simpa [leftTrue, leftAtom, binaryBitAtValuationFormula,
        binaryBitLiteralAtTerms] using hleftTrue
    omega
  have htargetRaw := binaryFormulaCode_and_length_le_local forward backward
  have htarget : (binaryFormulaCode target).length <=
      4 * literalCode + 2 * (binaryNatCode 5).length +
        (binaryNatCode 4).length := by
    dsimp only [target] at htargetRaw ⊢
    omega
  have hliteral : literalCode <= resource := by
    dsimp only [literalCode, resource]
    unfold atomicRowEqBitBranchAssemblySyntaxPolynomial
    omega
  have hforwardResource :
      (binaryFormulaCode forward).length <= resource :=
    hforward.trans (by
      dsimp only [literalCode, resource]
      unfold atomicRowEqBitBranchAssemblySyntaxPolynomial
      omega)
  have hbackwardResource :
      (binaryFormulaCode backward).length <= resource :=
    hbackward.trans (by
      dsimp only [literalCode, resource]
      unfold atomicRowEqBitBranchAssemblySyntaxPolynomial
      omega)
  have htargetResource :
      (binaryFormulaCode target).length <= resource :=
    htarget.trans (by
      dsimp only [literalCode, resource]
      unfold atomicRowEqBitBranchAssemblySyntaxPolynomial
      omega)
  exact ⟨hleftTrue.trans hliteral, hleftFalse.trans hliteral,
    hotherTrue.trans hliteral, hotherFalse.trans hliteral,
    hforwardResource, hbackwardResource, htargetResource⟩

theorem atomicRowEqBitBranchFormulaVariables_subset_singleton
    (tokenTable width left otherLeft : Nat) :
    let tableTerm := shortBinaryNumeralTerm tokenTable
    let widthTerm := shortBinaryNumeralTerm width
    let leftTerm := shortBinaryNumeralTerm left
    let otherLeftTerm := shortBinaryNumeralTerm otherLeft
    let leftIndexTerm := atomicRowEqLeftBitIndexTerm widthTerm leftTerm
    let otherIndexTerm :=
      atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm
    let valueTerm := atomicRowEqBitValueTerm tableTerm
    let leftAtom := binaryBitAtomAtTerms leftIndexTerm valueTerm
    let otherAtom := binaryBitAtomAtTerms otherIndexTerm valueTerm
    let leftTrue := binaryBitAtValuationFormula true leftIndexTerm valueTerm
    let leftFalse := binaryBitAtValuationFormula false leftIndexTerm valueTerm
    let otherTrue := binaryBitAtValuationFormula true otherIndexTerm valueTerm
    let otherFalse :=
      binaryBitAtValuationFormula false otherIndexTerm valueTerm
    let forward := (∼leftAtom ⋎ otherAtom)
    let backward := (∼otherAtom ⋎ leftAtom)
    let target := forward ⋏ backward
    leftTrue.freeVariables ⊆ {0} ∧ leftFalse.freeVariables ⊆ {0} ∧
      otherTrue.freeVariables ⊆ {0} ∧ otherFalse.freeVariables ⊆ {0} ∧
      forward.freeVariables ⊆ {0} ∧ backward.freeVariables ⊆ {0} ∧
      target.freeVariables ⊆ {0} := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let leftTerm := shortBinaryNumeralTerm left
  let otherLeftTerm := shortBinaryNumeralTerm otherLeft
  let leftIndexTerm := atomicRowEqLeftBitIndexTerm widthTerm leftTerm
  let otherIndexTerm :=
    atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm
  let valueTerm := atomicRowEqBitValueTerm tableTerm
  let leftAtom := binaryBitAtomAtTerms leftIndexTerm valueTerm
  let otherAtom := binaryBitAtomAtTerms otherIndexTerm valueTerm
  let leftTrue := binaryBitAtValuationFormula true leftIndexTerm valueTerm
  let leftFalse := binaryBitAtValuationFormula false leftIndexTerm valueTerm
  let otherTrue := binaryBitAtValuationFormula true otherIndexTerm valueTerm
  let otherFalse :=
    binaryBitAtValuationFormula false otherIndexTerm valueTerm
  let forward := (∼leftAtom ⋎ otherAtom)
  let backward := (∼otherAtom ⋎ leftAtom)
  let target := forward ⋏ backward
  have hterms := atomicRowEqBitTerms_freeVariables_of_shortNumerals
    tokenTable width left otherLeft
  have hleftTerm : leftIndexTerm.freeVariables ∪ valueTerm.freeVariables ⊆
      {0} := by
    apply Finset.union_subset
    · simpa only [leftIndexTerm, widthTerm, leftTerm] using hterms.1
    · rw [show valueTerm.freeVariables = ∅ by
        simpa only [valueTerm, tableTerm] using hterms.2.2]
      simp
  have hotherTerm :
      otherIndexTerm.freeVariables ∪ valueTerm.freeVariables ⊆ {0} := by
    apply Finset.union_subset
    · simpa only [otherIndexTerm, widthTerm, otherLeftTerm] using hterms.2.1
    · rw [show valueTerm.freeVariables = ∅ by
        simpa only [valueTerm, tableTerm] using hterms.2.2]
      simp
  have hleftTrue : leftTrue.freeVariables ⊆ {0} :=
    (binaryBitAtValuationFormula_freeVariables_subset true leftIndexTerm
      valueTerm).trans hleftTerm
  have hleftFalse : leftFalse.freeVariables ⊆ {0} :=
    (binaryBitAtValuationFormula_freeVariables_subset false leftIndexTerm
      valueTerm).trans hleftTerm
  have hotherTrue : otherTrue.freeVariables ⊆ {0} :=
    (binaryBitAtValuationFormula_freeVariables_subset true otherIndexTerm
      valueTerm).trans hotherTerm
  have hotherFalse : otherFalse.freeVariables ⊆ {0} :=
    (binaryBitAtValuationFormula_freeVariables_subset false otherIndexTerm
      valueTerm).trans hotherTerm
  have hleftAtom : leftAtom.freeVariables ⊆ {0} := by
    simpa [leftTrue, leftAtom, binaryBitAtValuationFormula,
      binaryBitLiteralAtTerms] using hleftTrue
  have hotherAtom : otherAtom.freeVariables ⊆ {0} := by
    simpa [otherTrue, otherAtom, binaryBitAtValuationFormula,
      binaryBitLiteralAtTerms] using hotherTrue
  have hforward : forward.freeVariables ⊆ {0} := by
    dsimp only [forward]
    rw [LO.FirstOrder.Semiformula.freeVariables_or]
    exact Finset.union_subset (by simpa using hleftAtom) hotherAtom
  have hbackward : backward.freeVariables ⊆ {0} := by
    dsimp only [backward]
    rw [LO.FirstOrder.Semiformula.freeVariables_or]
    exact Finset.union_subset (by simpa using hotherAtom) hleftAtom
  have htarget : target.freeVariables ⊆ {0} := by
    dsimp only [target]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hforward hbackward
  exact ⟨hleftTrue, hleftFalse, hotherTrue, hotherFalse, hforward,
    hbackward, htarget⟩

theorem atomicRowEqBitBranchPublicPayloadEnvelope_le_fixed
    (valuation : Nat -> Nat)
    (tokenTable width left otherLeft numericBound bitBound bitIndex : Nat)
    (hwidth : width <= numericBound)
    (hleft : left <= numericBound)
    (hother : otherLeft <= numericBound)
    (hbitIndex : bitIndex < width)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hleftSize : Nat.size left <= bitBound)
    (hotherSize : Nat.size otherLeft <= bitBound) :
    atomicRowEqBitBranchPublicPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm otherLeft)
        bitIndex <=
      atomicRowEqBitBranchFixedPayloadPolynomial numericBound bitBound := by
  let branchValuation := extendValuation bitIndex valuation
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let leftTerm := shortBinaryNumeralTerm left
  let otherLeftTerm := shortBinaryNumeralTerm otherLeft
  let leftIndexTerm := atomicRowEqLeftBitIndexTerm widthTerm leftTerm
  let otherIndexTerm :=
    atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm
  let valueTerm := atomicRowEqBitValueTerm tableTerm
  let leftAtom := binaryBitAtomAtTerms leftIndexTerm valueTerm
  let otherAtom := binaryBitAtomAtTerms otherIndexTerm valueTerm
  let leftTrue := binaryBitAtValuationFormula true leftIndexTerm valueTerm
  let leftFalse := binaryBitAtValuationFormula false leftIndexTerm valueTerm
  let otherTrue := binaryBitAtValuationFormula true otherIndexTerm valueTerm
  let otherFalse :=
    binaryBitAtValuationFormula false otherIndexTerm valueTerm
  let forward := (∼leftAtom ⋎ otherAtom)
  let backward := (∼otherAtom ⋎ leftAtom)
  let target := forward ⋏ backward
  let leftTrueContext := valuationContext leftTrue.freeVariables
    branchValuation
  let leftFalseContext := valuationContext leftFalse.freeVariables
    branchValuation
  let otherTrueContext := valuationContext otherTrue.freeVariables
    branchValuation
  let otherFalseContext := valuationContext otherFalse.freeVariables
    branchValuation
  let forwardContext := valuationContext forward.freeVariables branchValuation
  let backwardContext :=
    valuationContext backward.freeVariables branchValuation
  let targetContext := valuationContext target.freeVariables branchValuation
  let syntaxResource :=
    atomicRowEqBitBranchAssemblySyntaxPolynomial numericBound bitBound
  let assemblyResource := generalContextAssemblyEnvelope syntaxResource
  have hliteral := fun (expected : Bool) (useOther : Bool) =>
    compileBinaryBitLiteralAtAtomicRowShortNumeralsPayloadPolynomial_le_fixed
      expected valuation tokenTable width left otherLeft numericBound bitBound
      bitIndex useOther hwidth hleft hother hbitIndex htableSize hwidthSize
      hleftSize hotherSize
  have hleftTruePayload := hliteral true false
  have hleftFalsePayload := hliteral false false
  have hotherTruePayload := hliteral true true
  have hotherFalsePayload := hliteral false true
  have hcodesZero := atomicRowEqBitBranchFormulaCodes_le_fixed tokenTable width
    left otherLeft bitBound htableSize hwidthSize hleftSize hotherSize
  have hcodeScale :
      atomicRowEqBitBranchAssemblySyntaxPolynomial 0 bitBound <=
        syntaxResource := by
    have hcontextMono :=
      valuationContextFormulaCodeSumEnvelope_mono_numeric_openIndex
        1 (binaryTermCode (&0 : ValuationTerm)).length
          (Nat.zero_le numericBound)
    dsimp only [syntaxResource]
    unfold atomicRowEqBitBranchAssemblySyntaxPolynomial
      atomicRowEqBitContextFormulaCodeSumEnvelope
    omega
  have hleftTrueCode :
      (binaryFormulaCode leftTrue).length <= syntaxResource := by
    have hzero :
        (binaryFormulaCode leftTrue).length <=
          atomicRowEqBitBranchAssemblySyntaxPolynomial 0 bitBound := by
      simpa only [tableTerm, widthTerm, leftTerm, otherLeftTerm,
      leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
        using hcodesZero.1
    exact hzero.trans hcodeScale
  have hleftFalseCode :
      (binaryFormulaCode leftFalse).length <= syntaxResource := by
    have hzero :
        (binaryFormulaCode leftFalse).length <=
          atomicRowEqBitBranchAssemblySyntaxPolynomial 0 bitBound := by
      simpa only [tableTerm, widthTerm, leftTerm, otherLeftTerm,
      leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
        using hcodesZero.2.1
    exact hzero.trans hcodeScale
  have hotherTrueCode :
      (binaryFormulaCode otherTrue).length <= syntaxResource := by
    have hzero :
        (binaryFormulaCode otherTrue).length <=
          atomicRowEqBitBranchAssemblySyntaxPolynomial 0 bitBound := by
      simpa only [tableTerm, widthTerm, leftTerm, otherLeftTerm,
      leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
        using hcodesZero.2.2.1
    exact hzero.trans hcodeScale
  have hotherFalseCode :
      (binaryFormulaCode otherFalse).length <= syntaxResource := by
    have hzero :
        (binaryFormulaCode otherFalse).length <=
          atomicRowEqBitBranchAssemblySyntaxPolynomial 0 bitBound := by
      simpa only [tableTerm, widthTerm, leftTerm, otherLeftTerm,
      leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
        using hcodesZero.2.2.2.1
    exact hzero.trans hcodeScale
  have hforwardCode :
      (binaryFormulaCode forward).length <= syntaxResource := by
    have hzero :
        (binaryFormulaCode forward).length <=
          atomicRowEqBitBranchAssemblySyntaxPolynomial 0 bitBound := by
      simpa only [tableTerm, widthTerm, leftTerm, otherLeftTerm,
      leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
        using hcodesZero.2.2.2.2.1
    exact hzero.trans hcodeScale
  have hbackwardCode :
      (binaryFormulaCode backward).length <= syntaxResource := by
    have hzero :
        (binaryFormulaCode backward).length <=
          atomicRowEqBitBranchAssemblySyntaxPolynomial 0 bitBound := by
      simpa only [tableTerm, widthTerm, leftTerm, otherLeftTerm,
      leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
        using hcodesZero.2.2.2.2.2.1
    exact hzero.trans hcodeScale
  have htargetCode :
      (binaryFormulaCode target).length <= syntaxResource := by
    have hzero :
        (binaryFormulaCode target).length <=
          atomicRowEqBitBranchAssemblySyntaxPolynomial 0 bitBound := by
      simpa only [tableTerm, widthTerm, leftTerm, otherLeftTerm,
      leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
        using hcodesZero.2.2.2.2.2.2
    exact hzero.trans hcodeScale
  have hvars := atomicRowEqBitBranchFormulaVariables_subset_singleton
    tokenTable width left otherLeft
  have hleftTrueVars : leftTrue.freeVariables ⊆ {0} := by
    simpa only [tableTerm, widthTerm, leftTerm, otherLeftTerm,
      leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
      using hvars.1
  have hleftFalseVars : leftFalse.freeVariables ⊆ {0} := by
    simpa only [tableTerm, widthTerm, leftTerm, otherLeftTerm,
      leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
      using hvars.2.1
  have hotherTrueVars : otherTrue.freeVariables ⊆ {0} := by
    simpa only [tableTerm, widthTerm, leftTerm, otherLeftTerm,
      leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
      using hvars.2.2.1
  have hotherFalseVars : otherFalse.freeVariables ⊆ {0} := by
    simpa only [tableTerm, widthTerm, leftTerm, otherLeftTerm,
      leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
      using hvars.2.2.2.1
  have hforwardVars : forward.freeVariables ⊆ {0} := by
    simpa only [tableTerm, widthTerm, leftTerm, otherLeftTerm,
      leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
      using hvars.2.2.2.2.1
  have hbackwardVars : backward.freeVariables ⊆ {0} := by
    simpa only [tableTerm, widthTerm, leftTerm, otherLeftTerm,
      leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
      using hvars.2.2.2.2.2.1
  have htargetVars : target.freeVariables ⊆ {0} := by
    simpa only [tableTerm, widthTerm, leftTerm, otherLeftTerm,
      leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
      leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target]
      using hvars.2.2.2.2.2.2
  have hbranchZero : branchValuation 0 <= numericBound := by
    simp only [branchValuation, extendValuation_zero]
    omega
  have hcontext :
      ∀ formula : ValuationFormula, formula.freeVariables ⊆ {0} ->
        FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
            (valuationContext formula.freeVariables branchValuation) <=
          syntaxResource := by
    intro formula hformula
    have hraw :=
      valuationContextFormulaCodeSum_le_atomicRowEqBitEnvelope branchValuation
        formula.freeVariables numericBound hformula hbranchZero
    apply hraw.trans
    dsimp only [syntaxResource]
    unfold atomicRowEqBitBranchAssemblySyntaxPolynomial
    omega
  have hleftTrueContext := hcontext leftTrue hleftTrueVars
  have hleftFalseContext := hcontext leftFalse hleftFalseVars
  have hotherTrueContext := hcontext otherTrue hotherTrueVars
  have hotherFalseContext := hcontext otherFalse hotherFalseVars
  have hforwardContext := hcontext forward hforwardVars
  have hbackwardContext := hcontext backward hbackwardVars
  have htargetContext := hcontext target htargetVars
  have hweakLeftTrue :=
    weakeningFullAssemblyCost_insert_le_atomicRowEqGeneral leftTrueContext
      leftTrue syntaxResource hleftTrueContext hleftTrueCode
  have hweakLeftFalse :=
    weakeningFullAssemblyCost_insert_le_atomicRowEqGeneral leftFalseContext
      leftFalse syntaxResource hleftFalseContext hleftFalseCode
  have hweakOtherTrue :=
    weakeningFullAssemblyCost_insert_le_atomicRowEqGeneral otherTrueContext
      otherTrue syntaxResource hotherTrueContext hotherTrueCode
  have hweakOtherFalse :=
    weakeningFullAssemblyCost_insert_le_atomicRowEqGeneral otherFalseContext
      otherFalse syntaxResource hotherFalseContext hotherFalseCode
  have hweakLeftFalseForward :=
    weakeningFullAssemblyCost_insert_le_atomicRowEqGeneral forwardContext
      leftFalse syntaxResource hforwardContext hleftFalseCode
  have hweakOtherTrueForward :=
    weakeningFullAssemblyCost_insert_le_atomicRowEqGeneral forwardContext
      otherTrue syntaxResource hforwardContext hotherTrueCode
  have hweakOtherFalseBackward :=
    weakeningFullAssemblyCost_insert_le_atomicRowEqGeneral backwardContext
      otherFalse syntaxResource hbackwardContext hotherFalseCode
  have hweakLeftTrueBackward :=
    weakeningFullAssemblyCost_insert_le_atomicRowEqGeneral backwardContext
      leftTrue syntaxResource hbackwardContext hleftTrueCode
  have hdisjunctionForward := disjunctionFullAssemblyCost_le_general
    forwardContext (∼leftAtom) otherAtom syntaxResource (by
      dsimp only [syntaxResource]
      unfold atomicRowEqBitBranchAssemblySyntaxPolynomial
      omega) hforwardContext (by
        simpa [leftFalse, leftAtom, binaryBitAtValuationFormula,
          binaryBitLiteralAtTerms] using hleftFalseCode) (by
        simpa [otherTrue, otherAtom, binaryBitAtValuationFormula,
          binaryBitLiteralAtTerms] using hotherTrueCode) (by
        simpa only [forward] using hforwardCode)
  have hdisjunctionBackward := disjunctionFullAssemblyCost_le_general
    backwardContext (∼otherAtom) leftAtom syntaxResource (by
      dsimp only [syntaxResource]
      unfold atomicRowEqBitBranchAssemblySyntaxPolynomial
      omega) hbackwardContext (by
        simpa [otherFalse, otherAtom, binaryBitAtValuationFormula,
          binaryBitLiteralAtTerms] using hotherFalseCode) (by
        simpa [leftTrue, leftAtom, binaryBitAtValuationFormula,
          binaryBitLiteralAtTerms] using hleftTrueCode) (by
        simpa only [backward] using hbackwardCode)
  have hweakForwardTarget :=
    weakeningFullAssemblyCost_insert_le_atomicRowEqGeneral targetContext
      forward syntaxResource htargetContext hforwardCode
  have hweakBackwardTarget :=
    weakeningFullAssemblyCost_insert_le_atomicRowEqGeneral targetContext
      backward syntaxResource htargetContext hbackwardCode
  have hconjunction := conjunctionFullAssemblyCost_le_general targetContext
    forward backward syntaxResource (by
      dsimp only [syntaxResource]
      unfold atomicRowEqBitBranchAssemblySyntaxPolynomial
      omega) htargetContext hforwardCode hbackwardCode htargetCode
  simp only [Bool.false_eq_true, ↓reduceIte] at hleftTruePayload
  simp only [Bool.false_eq_true, ↓reduceIte] at hleftFalsePayload
  simp only [↓reduceIte] at hotherTruePayload
  simp only [↓reduceIte] at hotherFalsePayload
  unfold atomicRowEqBitBranchPublicPayloadEnvelope
    atomicRowEqBitBranchFixedPayloadPolynomial
  dsimp only [branchValuation, tableTerm, widthTerm, leftTerm, otherLeftTerm,
    leftIndexTerm, otherIndexTerm, valueTerm, leftAtom, otherAtom,
    leftTrue, leftFalse, otherTrue, otherFalse, forward, backward, target,
    leftTrueContext, leftFalseContext, otherTrueContext, otherFalseContext,
    forwardContext, backwardContext, targetContext, syntaxResource,
    assemblyResource] at *
  omega

def atomicRowEqBitBranchPublicPayloadSumFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound *
    atomicRowEqBitBranchFixedPayloadPolynomial numericBound bitBound

theorem atomicRowEqBitBranchPublicPayloadSum_le_fixed
    (valuation : Nat -> Nat)
    (tokenTable width left otherLeft numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (hleft : left <= numericBound)
    (hother : otherLeft <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hleftSize : Nat.size left <= bitBound)
    (hotherSize : Nat.size otherLeft <= bitBound) :
    atomicRowEqBitBranchPublicPayloadSum valuation
        (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm otherLeft) <=
      atomicRowEqBitBranchPublicPayloadSumFixedPolynomial
        numericBound bitBound := by
  unfold atomicRowEqBitBranchPublicPayloadSum
  rw [termValue_shortBinaryNumeralTerm valuation width]
  calc
    (∑ bitIndex : Fin width,
        atomicRowEqBitBranchPublicPayloadEnvelope valuation
          (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm otherLeft) bitIndex) <=
      ∑ _bitIndex : Fin width,
        atomicRowEqBitBranchFixedPayloadPolynomial numericBound bitBound := by
          apply Finset.sum_le_sum
          intro bitIndex _
          exact atomicRowEqBitBranchPublicPayloadEnvelope_le_fixed valuation
            tokenTable width left otherLeft numericBound bitBound bitIndex
              hwidth hleft hother bitIndex.isLt htableSize hwidthSize hleftSize
                hotherSize
    _ = width *
        atomicRowEqBitBranchFixedPayloadPolynomial numericBound bitBound := by
          simp
    _ <= numericBound *
        atomicRowEqBitBranchFixedPayloadPolynomial numericBound bitBound :=
          Nat.mul_le_mul_right
            (atomicRowEqBitBranchFixedPayloadPolynomial numericBound bitBound)
              hwidth
    _ = atomicRowEqBitBranchPublicPayloadSumFixedPolynomial
        numericBound bitBound := by
          rfl

private theorem binaryAddTerm_code_length_le_atomicRowUniversal
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermCode
      (LO.FirstOrder.Semiterm.func Language.Add.add
        ![left, right])).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        binaryFunctionTermCodeOverhead Language.Add.add := by
  simp [binaryTermCode, binaryFunctionTermCodeOverhead,
    Matrix.fun_eq_vec_two]
  omega

def atomicRowEqUniversalBitAtomCodePolynomial (termBound : Nat) : Nat :=
  uniformRewritingFormulaFactor (termBound + 4) (termBound + 1)
      (formulaSymbolCount binaryBitEmbeddedFormula) *
    (binaryFormulaCode binaryBitEmbeddedFormula).length

private theorem binaryBitAtomAtTerms_code_length_le_atomicRowUniversal
    {arity : Nat}
    (index value : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (termBound : Nat)
    (hindex : (binaryTermCode index).length <= termBound)
    (hvalue : (binaryTermCode value).length <= termBound) :
    (binaryFormulaCode (binaryBitAtomAtTerms index value)).length <=
      atomicRowEqUniversalBitAtomCodePolynomial termBound := by
  let rewriting : Rew ℒₒᵣ Nat 2 Nat arity := Rew.subst ![index, value]
  have hindexSymbols : termSymbolCount index <= termBound :=
    (termSymbolCount_le_binaryTermCode_length index).trans hindex
  have hvalueSymbols : termSymbolCount value <= termBound :=
    (termSymbolCount_le_binaryTermCode_length value).trans hvalue
  have hbound : UniformRewritingImageBound rewriting (termBound + 4)
      (termBound + 1) := by
    constructor
    · intro coordinate
      cases coordinate using Fin.cases with
      | zero =>
          simp [rewriting, Rew.subst_bvar]
          omega
      | succ coordinate =>
          cases coordinate using Fin.cases with
          | zero =>
              simp [rewriting, Rew.subst_bvar]
              omega
          | succ coordinate => exact Fin.elim0 coordinate
    · constructor
      · intro coordinate
        cases coordinate using Fin.cases with
        | zero =>
            simp [rewriting, Rew.subst_bvar]
            omega
        | succ coordinate =>
            cases coordinate using Fin.cases with
            | zero =>
                simp [rewriting, Rew.subst_bvar]
                omega
            | succ coordinate => exact Fin.elim0 coordinate
      · exact fun freeIndex => by
          change (Rew.subst ![index, value])
            (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat 2) =
              (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat arity)
          exact Rew.subst_fvar ![index, value] freeIndex
  have hraw := binaryFormulaCode_rewriting_length_le_factor
    binaryBitEmbeddedFormula rewriting (by omega) (by omega) hbound
  have hatomEq : binaryBitAtomAtTerms index value =
      rewriting ▹ binaryBitEmbeddedFormula := by
    unfold binaryBitAtomAtTerms binaryBitEmbeddedFormula
    rfl
  rw [hatomEq]
  unfold atomicRowEqUniversalBitAtomCodePolynomial
  exact hraw

def atomicRowEqUniversalBodyTermCodePolynomial (bitBound : Nat) : Nat :=
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  8 * numeralCode +
    3 * binaryFunctionTermCodeOverhead Language.Mul.mul +
    binaryFunctionTermCodeOverhead Language.Add.add +
    (binaryTermCode
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length + 1

def atomicRowEqUniversalBodyCodePolynomial (bitBound : Nat) : Nat :=
  64 * (atomicRowEqUniversalBitAtomCodePolynomial
    (atomicRowEqUniversalBodyTermCodePolynomial bitBound) + 1)

theorem atomicRowEqBitBody_code_length_le_fixed
    (tokenTable width left otherLeft bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hleftSize : Nat.size left <= bitBound)
    (hotherSize : Nat.size otherLeft <= bitBound) :
    (binaryFormulaCode
      (atomicRowEqBitBody (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm left)
        (shortBinaryNumeralTerm otherLeft))).length <=
      atomicRowEqUniversalBodyCodePolynomial bitBound := by
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let leftTerm := shortBinaryNumeralTerm left
  let otherLeftTerm := shortBinaryNumeralTerm otherLeft
  let leftProduct := paMulTerm leftTerm widthTerm
  let otherProduct := paMulTerm otherLeftTerm widthTerm
  let leftIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    .func Language.Add.add ![Rew.bShift leftProduct, #0]
  let otherIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    .func Language.Add.add ![Rew.bShift otherProduct, #0]
  let tableValue : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift tableTerm
  let termBound := atomicRowEqUniversalBodyTermCodePolynomial bitBound
  let leftAtom := binaryBitAtomAtTerms leftIndex tableValue
  let otherAtom := binaryBitAtomAtTerms otherIndex tableValue
  have htableCode : (binaryTermCode tableTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope tokenTable bitBound htableSize
  have hwidthCode : (binaryTermCode widthTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope width bitBound hwidthSize
  have hleftCode : (binaryTermCode leftTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope left bitBound hleftSize
  have hotherCode : (binaryTermCode otherLeftTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope otherLeft bitBound hotherSize
  have hleftProductRaw := paMulTerm_code_length_le leftTerm widthTerm
  have hotherProductRaw := paMulTerm_code_length_le otherLeftTerm widthTerm
  have hleftProduct :
      (binaryTermCode leftProduct).length <=
        2 * numeralCode +
          binaryFunctionTermCodeOverhead Language.Mul.mul := by
    dsimp only [leftProduct]
    omega
  have hotherProduct :
      (binaryTermCode otherProduct).length <=
        2 * numeralCode +
          binaryFunctionTermCodeOverhead Language.Mul.mul := by
    dsimp only [otherProduct]
    omega
  have hleftSymbols := termSymbolCount_le_binaryTermCode_length leftProduct
  have hotherSymbols := termSymbolCount_le_binaryTermCode_length otherProduct
  have hleftShiftRaw :=
    binaryTermCode_bShift_length_le_add_symbols leftProduct
  have hotherShiftRaw :=
    binaryTermCode_bShift_length_le_add_symbols otherProduct
  have hleftShift :
      (binaryTermCode (Rew.bShift leftProduct)).length <=
        3 * (2 * numeralCode +
          binaryFunctionTermCodeOverhead Language.Mul.mul) := by
    omega
  have hotherShift :
      (binaryTermCode (Rew.bShift otherProduct)).length <=
        3 * (2 * numeralCode +
          binaryFunctionTermCodeOverhead Language.Mul.mul) := by
    omega
  have hleftIndexRaw :=
    binaryAddTerm_code_length_le_atomicRowUniversal
      (Rew.bShift leftProduct)
        (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)
  have hotherIndexRaw :=
    binaryAddTerm_code_length_le_atomicRowUniversal
      (Rew.bShift otherProduct)
        (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)
  have hleftIndex : (binaryTermCode leftIndex).length <= termBound := by
    dsimp only [leftIndex, termBound,
      atomicRowEqUniversalBodyTermCodePolynomial]
    omega
  have hotherIndex : (binaryTermCode otherIndex).length <= termBound := by
    dsimp only [otherIndex, termBound,
      atomicRowEqUniversalBodyTermCodePolynomial]
    omega
  have htableSymbols := termSymbolCount_le_binaryTermCode_length tableTerm
  have htableShiftRaw :=
    binaryTermCode_bShift_length_le_add_symbols tableTerm
  have htableValue : (binaryTermCode tableValue).length <= termBound := by
    dsimp only [tableValue, termBound,
      atomicRowEqUniversalBodyTermCodePolynomial]
    omega
  have hleftAtom :
      (binaryFormulaCode leftAtom).length <=
        atomicRowEqUniversalBitAtomCodePolynomial termBound :=
    binaryBitAtomAtTerms_code_length_le_atomicRowUniversal leftIndex tableValue
      termBound hleftIndex htableValue
  have hotherAtom :
      (binaryFormulaCode otherAtom).length <=
        atomicRowEqUniversalBitAtomCodePolynomial termBound :=
    binaryBitAtomAtTerms_code_length_le_atomicRowUniversal otherIndex tableValue
      termBound hotherIndex htableValue
  have hnegLeft := binaryFormulaCode_neg_length_le leftAtom
  have hnegRight := binaryFormulaCode_neg_length_le otherAtom
  change (binaryFormulaCode
    (LO.FirstOrder.Semiformula.neg leftAtom)).length <=
      2 * (binaryFormulaCode leftAtom).length at hnegLeft
  change (binaryFormulaCode
    (LO.FirstOrder.Semiformula.neg otherAtom)).length <=
      2 * (binaryFormulaCode otherAtom).length at hnegRight
  have htagFour : (binaryNatCode 4).length <= 8 := by decide
  have htagFive : (binaryNatCode 5).length <= 8 := by decide
  unfold atomicRowEqBitBody
  change (binaryFormulaCode (leftAtom 🡘 otherAtom)).length <= _
  simp only [binaryFormulaCode, List.length_append]
  unfold atomicRowEqUniversalBodyCodePolynomial
  dsimp only [termBound] at hleftAtom hotherAtom
  omega

private theorem binaryFunctionTerm_freeVariables_atomicRowUniversal
    {boundArity : Nat}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
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

theorem atomicRowEqBitBody_freeVariables_eq_empty_shortNumerals
    (tokenTable width left otherLeft : Nat) :
    (atomicRowEqBitBody (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm left)
      (shortBinaryNumeralTerm otherLeft)).freeVariables = ∅ := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let leftTerm := shortBinaryNumeralTerm left
  let otherLeftTerm := shortBinaryNumeralTerm otherLeft
  let leftProduct := paMulTerm leftTerm widthTerm
  let otherProduct := paMulTerm otherLeftTerm widthTerm
  let leftIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    .func Language.Add.add ![Rew.bShift leftProduct, #0]
  let otherIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    .func Language.Add.add ![Rew.bShift otherProduct, #0]
  let tableValue : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift tableTerm
  have htable : tableTerm.freeVariables = ∅ := by
    exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  have hwidth : widthTerm.freeVariables = ∅ := by
    exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  have hleft : leftTerm.freeVariables = ∅ := by
    exact shortBinaryNumeralTerm_freeVariables_eq_empty left
  have hother : otherLeftTerm.freeVariables = ∅ := by
    exact shortBinaryNumeralTerm_freeVariables_eq_empty otherLeft
  have hleftProduct : leftProduct.freeVariables = ∅ := by
    dsimp only [leftProduct]
    rw [paMulTerm_freeVariables_atomicRowFixed, hleft, hwidth]
    simp
  have hotherProduct : otherProduct.freeVariables = ∅ := by
    dsimp only [otherProduct]
    rw [paMulTerm_freeVariables_atomicRowFixed, hother, hwidth]
    simp
  have hleftShift : (Rew.bShift leftProduct).freeVariables = ∅ :=
    bShift_freeVariables_eq_empty_of_empty leftProduct hleftProduct
  have hotherShift : (Rew.bShift otherProduct).freeVariables = ∅ :=
    bShift_freeVariables_eq_empty_of_empty otherProduct hotherProduct
  have hleftIndex : leftIndex.freeVariables = ∅ := by
    dsimp only [leftIndex]
    rw [binaryFunctionTerm_freeVariables_atomicRowUniversal, hleftShift]
    simp
  have hotherIndex : otherIndex.freeVariables = ∅ := by
    dsimp only [otherIndex]
    rw [binaryFunctionTerm_freeVariables_atomicRowUniversal, hotherShift]
    simp
  have htableValue : tableValue.freeVariables = ∅ := by
    dsimp only [tableValue]
    exact bShift_freeVariables_eq_empty_of_empty tableTerm htable
  have hleftAtom :=
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      bitDef.val ![leftIndex, tableValue] (by
        intro coordinate
        cases coordinate using Fin.cases with
        | zero => exact hleftIndex
        | succ coordinate =>
            cases coordinate using Fin.cases with
            | zero => exact htableValue
            | succ coordinate => exact Fin.elim0 coordinate)
  have hotherAtom :=
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      bitDef.val ![otherIndex, tableValue] (by
        intro coordinate
        cases coordinate using Fin.cases with
        | zero => exact hotherIndex
        | succ coordinate =>
            cases coordinate using Fin.cases with
            | zero => exact htableValue
            | succ coordinate => exact Fin.elim0 coordinate)
  unfold atomicRowEqBitBody binaryBitAtomAtTerms
  dsimp only [tableTerm, widthTerm, leftTerm, otherLeftTerm, leftProduct,
    otherProduct, leftIndex, otherIndex, tableValue] at hleftAtom hotherAtom ⊢
  simp only [LogicalConnective.iff,
    LO.FirstOrder.Semiformula.freeVariables_and,
    LO.FirstOrder.Semiformula.freeVariables_imp,
    hleftAtom, hotherAtom, Finset.empty_union]

theorem atomicRowEqUniversalOuterFormula_freeVariables_eq_empty_shortNumerals
    (tokenTable width left otherLeft : Nat) :
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm width))
      (atomicRowEqBitBody (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm left)
        (shortBinaryNumeralTerm otherLeft))).freeVariables = ∅ := by
  have hwidth :
      (shortBinaryNumeralTerm width : ValuationTerm).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty width
  have hshiftWidth :
      (Rew.bShift (shortBinaryNumeralTerm width : ValuationTerm)).freeVariables =
        ∅ :=
    bShift_freeVariables_eq_empty_of_empty (shortBinaryNumeralTerm width) hwidth
  have hbody :=
    atomicRowEqBitBody_freeVariables_eq_empty_shortNumerals tokenTable width
      left otherLeft
  have htermBound :
      (termBoundFormula
        (Rew.bShift (shortBinaryNumeralTerm width : ValuationTerm))).freeVariables =
          ∅ := by
    unfold termBoundFormula finiteCaseLessThanFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_rel]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro candidate hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero =>
        simp at hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero =>
            change candidate ∈ (Rew.bShift
              (shortBinaryNumeralTerm width : ValuationTerm)).freeVariables at hcoordinate
            rw [hshiftWidth] at hcoordinate
            simp at hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  simp only [LO.FirstOrder.Semiformula.freeVariables_all,
    termBoundedUniversalBody, LO.FirstOrder.Semiformula.freeVariables_imp,
    htermBound, hbody, Finset.empty_union]

private theorem finiteCaseFormulaEnvelope_mono_atomicRow
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    {small large : Nat} (hbound : small <= large) :
    finiteCaseFormulaEnvelope subject small <=
      finiteCaseFormulaEnvelope subject large := by
  have hshift : small + 2 <= large + 2 := by omega
  have hequality := finiteEqualityCasesCodePolynomial_mono subject hshift
  have hlower := finiteLowerBoundFormulaCodePolynomial_mono subject hshift
  have hexhaustion := finiteExhaustionFormulaCodePolynomial_mono subject hshift
  have hsteps : (small + 3) * finiteEqualityCaseStepEnvelope subject <=
      (large + 3) * finiteEqualityCaseStepEnvelope subject :=
    Nat.mul_le_mul_right _ (by omega)
  unfold finiteCaseFormulaEnvelope
  omega

private theorem boundedUniversalClosedFormulaEnvelope_mono_atomicRow
    {small large : Nat} (hbound : small <= large) :
    boundedUniversalClosedFormulaEnvelope small <=
      boundedUniversalClosedFormulaEnvelope large := by
  have hseed : boundedUniversalSyntaxSeed small <=
      boundedUniversalSyntaxSeed large := by
    unfold boundedUniversalSyntaxSeed
    omega
  have hbody := substitutionFormulaCodeEnvelope_mono_local hseed hseed
  have hcase := finiteCaseFormulaEnvelope_mono_atomicRow
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0) hbound
  unfold boundedUniversalClosedFormulaEnvelope
    boundedUniversalClosedBodyCodeEnvelope
  omega

def atomicRowEqBranchesFormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  let bodyCode := atomicRowEqUniversalBodyCodePolynomial bitBound
  boundedUniversalClosedFormulaEnvelope (numericBound + bodyCode) +
    2 * bodyCode

def atomicRowEqBranchesFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  (numericBound + 1) *
    (atomicRowEqBitBranchPublicPayloadSumFixedPolynomial numericBound bitBound +
      3 * smallContextAssemblyEnvelope
        (atomicRowEqBranchesFormulaCodePolynomial numericBound bitBound))

theorem atomicRowEqBranchesTransparentStructuralEnvelope_le_fixed
    (valuation : Nat -> Nat)
    (tokenTable width left otherLeft numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (hleft : left <= numericBound)
    (hother : otherLeft <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hleftSize : Nat.size left <= bitBound)
    (hotherSize : Nat.size otherLeft <= bitBound) :
    atomicRowEqBranchesTransparentStructuralEnvelope valuation
        (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm otherLeft) <=
      atomicRowEqBranchesFixedPayloadPolynomial numericBound bitBound := by
  let body := atomicRowEqBitBody (shortBinaryNumeralTerm tokenTable)
    (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm left)
    (shortBinaryNumeralTerm otherLeft)
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm width)) body
  let outerVariables := outerFormula.freeVariables
  let leafResource :=
    atomicRowEqBitBranchPublicPayloadSum valuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm otherLeft)
  let bodyCode := atomicRowEqUniversalBodyCodePolynomial bitBound
  let formulaResource :=
    atomicRowEqBranchesFormulaCodePolynomial numericBound bitBound
  have houter : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      atomicRowEqUniversalOuterFormula_freeVariables_eq_empty_shortNumerals
        tokenTable width left otherLeft
  have hGammaCard :
      ((valuationContext outerVariables valuation).image
        Rewriting.shift).card <= 1 := by
    rw [houter]
    simp [valuationContext]
  have hraw :=
    hybridBranchesUniformStructuralPayloadEnvelope_le_contextualPolynomial
      width outerVariables valuation body leafResource hGammaCard
        (caseCount := width) le_rfl
  have hleaf : leafResource <=
      atomicRowEqBitBranchPublicPayloadSumFixedPolynomial numericBound
        bitBound := by
    dsimp only [leafResource]
    exact atomicRowEqBitBranchPublicPayloadSum_le_fixed valuation tokenTable
      width left otherLeft numericBound bitBound hwidth hleft hother htableSize
        hwidthSize hleftSize hotherSize
  have hbodyCode : (binaryFormulaCode body).length <= bodyCode := by
    dsimp only [body, bodyCode]
    exact atomicRowEqBitBody_code_length_le_fixed tokenTable width left
      otherLeft bitBound htableSize hwidthSize hleftSize hotherSize
  have hsyntax :
      explicitHybridUniversalSyntaxResource width body <=
        numericBound + bodyCode := by
    unfold explicitHybridUniversalSyntaxResource
    omega
  have hclosed :=
    boundedUniversalClosedFormulaEnvelope_mono_atomicRow hsyntax
  have hexplicit :
      explicitHybridUniversalFormulaEnvelope width body <= formulaResource := by
    unfold explicitHybridUniversalFormulaEnvelope
    dsimp only [formulaResource, bodyCode,
      atomicRowEqBranchesFormulaCodePolynomial] at hclosed ⊢
    exact Nat.add_le_add hclosed (Nat.mul_le_mul_left 2 hbodyCode)
  have hcontextual :
      contextualHybridUniversalFormulaEnvelope
          ((valuationContext outerVariables valuation).image Rewriting.shift)
          width body <= formulaResource := by
    rw [houter]
    simp only [valuationContext, Finset.image_empty,
      contextualHybridUniversalFormulaEnvelope,
      contextualHybridUniversalFormulaCodeSum, Finset.sum_empty, Nat.add_zero]
    exact hexplicit
  have hlocal :=
    smallContextAssemblyEnvelope_mono_local hcontextual
  have hinner :
      leafResource +
          3 * contextualHybridUniversalLocalPayloadEnvelope
            ((valuationContext outerVariables valuation).image Rewriting.shift)
              width body <=
        atomicRowEqBitBranchPublicPayloadSumFixedPolynomial numericBound
            bitBound +
          3 * smallContextAssemblyEnvelope formulaResource := by
    unfold contextualHybridUniversalLocalPayloadEnvelope at hlocal ⊢
    omega
  have hfactor : width + 1 <= numericBound + 1 := by omega
  have hproduct := Nat.mul_le_mul hfactor hinner
  unfold atomicRowEqBranchesTransparentStructuralEnvelope
    atomicRowEqBranchesFixedPayloadPolynomial
  dsimp only [body, outerFormula, outerVariables, leafResource, bodyCode,
    formulaResource] at hraw hproduct ⊢
  simpa only [termValue_shortBinaryNumeralTerm] using hraw.trans hproduct

def atomicRowEqContextualBranchesFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxBound :=
    numericBound + atomicRowEqUniversalBodyCodePolynomial bitBound
  let formulaBound :=
    atomicRowEqBranchesFormulaCodePolynomial numericBound bitBound
  atomicRowEqBranchesFixedPayloadPolynomial numericBound bitBound +
    cumulativeFiniteExhaustionPayloadPolynomial syntaxBound +
    boundedUniversalFiniteExhaustionSpecializationEnvelope syntaxBound +
    4 * smallContextAssemblyEnvelope formulaBound

theorem atomicRowEqContextualBranchesResource_le_fixed
    (valuation : Nat -> Nat)
    (tokenTable width left otherLeft numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (hleft : left <= numericBound)
    (hother : otherLeft <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hleftSize : Nat.size left <= bitBound)
    (hotherSize : Nat.size otherLeft <= bitBound) :
    let body :=
      atomicRowEqBitBody (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm left)
        (shortBinaryNumeralTerm otherLeft)
    let outerFormula := ∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm width)) body
    let outerVariables := outerFormula.freeVariables
    let Gamma := valuationContext outerVariables valuation
    contextualBranchesUnderBoundPayloadEnvelope
        (Gamma.image Rewriting.shift) width (Rewriting.free body)
        (atomicRowEqBranchesTransparentStructuralEnvelope valuation
          (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm otherLeft)) <=
      atomicRowEqContextualBranchesFixedPayloadPolynomial numericBound
        bitBound := by
  let body :=
    atomicRowEqBitBody (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm left)
      (shortBinaryNumeralTerm otherLeft)
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm width)) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let shiftedGamma := Gamma.image Rewriting.shift
  let bound := width
  let bodyCode := atomicRowEqUniversalBodyCodePolynomial bitBound
  let syntaxBound := numericBound + bodyCode
  let formulaBound :=
    atomicRowEqBranchesFormulaCodePolynomial numericBound bitBound
  let caseResource :=
    atomicRowEqBranchesTransparentStructuralEnvelope valuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm otherLeft)
  let caseBound :=
    atomicRowEqBranchesFixedPayloadPolynomial numericBound bitBound
  let targetFormula := Rewriting.free body
  let finiteContext := contextualFiniteBoundContext shiftedGamma bound
  let localBound := smallContextAssemblyEnvelope formulaBound
  have houter : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      atomicRowEqUniversalOuterFormula_freeVariables_eq_empty_shortNumerals
        tokenTable width left otherLeft
  have hshiftedEmpty : shiftedGamma = ∅ := by
    dsimp only [shiftedGamma, Gamma]
    rw [houter]
    simp [valuationContext]
  have hboundSyntax : bound <= syntaxBound := by
    dsimp only [bound, syntaxBound]
    omega
  have hbodyCode : (binaryFormulaCode body).length <= bodyCode := by
    dsimp only [body, bodyCode]
    exact atomicRowEqBitBody_code_length_le_fixed tokenTable width left
      otherLeft bitBound htableSize hwidthSize hleftSize hotherSize
  have hclosedLe :
      boundedUniversalClosedFormulaEnvelope syntaxBound <= formulaBound := by
    change
      boundedUniversalClosedFormulaEnvelope
          (numericBound + atomicRowEqUniversalBodyCodePolynomial bitBound) <=
        boundedUniversalClosedFormulaEnvelope
            (numericBound + atomicRowEqUniversalBodyCodePolynomial bitBound) +
          2 * atomicRowEqUniversalBodyCodePolynomial bitBound
    omega
  have hshiftedBound : FormulaCodeBound shiftedGamma formulaBound := by
    intro formula hformula
    rw [hshiftedEmpty] at hformula
    simp at hformula
  have hshiftedCard : shiftedGamma.card <= 1 := by
    rw [hshiftedEmpty]
    simp
  have htargetFree := binaryFormulaCode_free_length_le body
  have htargetCode :
      (binaryFormulaCode targetFormula).length <= formulaBound := by
    change
      (binaryFormulaCode (Rewriting.free body)).length <=
        boundedUniversalClosedFormulaEnvelope
            (numericBound + atomicRowEqUniversalBodyCodePolynomial bitBound) +
          2 * atomicRowEqUniversalBodyCodePolynomial bitBound
    omega
  have hnegatedFiniteBound :=
    negatedFiniteBoundFormula_code_le_boundedUniversal bound syntaxBound
      hboundSyntax
  have hdoubleNegatedFiniteBound :=
    doubleNegatedFiniteBoundFormula_code_le_boundedUniversal bound syntaxBound
      hboundSyntax
  have hnegatedCases :=
    negatedFiniteEqualityCases_code_le_boundedUniversal bound syntaxBound
      (by omega)
  have hfiniteExhaustion :=
    finiteExhaustionFormula_code_le_boundedUniversal bound syntaxBound
      hboundSyntax
  have hnegatedFiniteExhaustion :=
    negatedFiniteExhaustionFormula_code_le_boundedUniversal bound syntaxBound
      hboundSyntax
  have hfiniteContextBound : FormulaCodeBound finiteContext formulaBound := by
    dsimp only [finiteContext]
    unfold contextualFiniteBoundContext
    exact hshiftedBound.insert (hnegatedFiniteBound.trans hclosedLe)
  have hfiniteContextCard : finiteContext.card <= 4 := by
    have hstep :=
      Finset.card_insert_le (∼finiteBoundFormula bound) shiftedGamma
    dsimp only [finiteContext]
    unfold contextualFiniteBoundContext
    omega
  have hlower :
      lowerBoundContradictionFullPayloadCost bound targetFormula <=
        localBound := by
    dsimp only [localBound]
    exact lowerBoundContradictionFullPayloadCost_le_openIndexUniversal bound
      targetFormula formulaBound htargetCode
      ((finiteBoundFormula_code_le_boundedUniversal bound syntaxBound
        hboundSyntax).trans hclosedLe)
      (hnegatedFiniteBound.trans hclosedLe)
      (hdoubleNegatedFiniteBound.trans hclosedLe)
  have hweakContextBound : FormulaCodeBound
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula bound (&0)) finiteContext))
      formulaBound :=
    (hfiniteContextBound.insert
      (hdoubleNegatedFiniteBound.trans hclosedLe)).insert htargetCode
  have hweakContextCard :
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula bound (&0)) finiteContext)).card <=
          8 := by
    have hfirst := Finset.card_insert_le
      (∼finiteLowerBoundFormula bound (&0)) finiteContext
    have hsecond := Finset.card_insert_le targetFormula
      (insert (∼finiteLowerBoundFormula bound (&0)) finiteContext)
    omega
  have hweak : weakeningFullAssemblyCost
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula bound (&0)) finiteContext)) <=
        localBound := by
    dsimp only [localBound]
    exact weakeningFullAssemblyCost_le_small
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula bound (&0)) finiteContext))
      formulaBound hweakContextCard hweakContextBound
  have heliminate :
      CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
        finiteContext targetFormula (finiteEqualityCases (&0) bound)
          (finiteLowerBoundFormula bound (&0)) <= localBound := by
    dsimp only [localBound]
    exact eliminateDisjunctionAssumptionFullAssemblyCost_le_small
      finiteContext targetFormula (finiteEqualityCases (&0) bound)
      (finiteLowerBoundFormula bound (&0)) formulaBound hfiniteContextCard
      hfiniteContextBound htargetCode (hnegatedCases.trans hclosedLe)
      (hdoubleNegatedFiniteBound.trans hclosedLe) (by
        simpa only [finiteExhaustionFormula, finiteLowerBoundFormula] using
          hnegatedFiniteExhaustion.trans hclosedLe)
  have hcut : cutClosedAssumptionFullAssemblyCost finiteContext
      (finiteExhaustionFormula bound (&0)) targetFormula <= localBound := by
    dsimp only [localBound]
    exact cutClosedAssumptionFullAssemblyCost_le_openIndexUniversal
      finiteContext (finiteExhaustionFormula bound (&0)) targetFormula
      formulaBound hfiniteContextCard hfiniteContextBound
      (hfiniteExhaustion.trans hclosedLe)
      (hnegatedFiniteExhaustion.trans hclosedLe) htargetCode
  have hexhaustion :=
    finiteExhaustionAtEigenvariableStructuralPayloadBound_le_polynomial
      bound syntaxBound hboundSyntax
  have hcase : caseResource <= caseBound := by
    dsimp only [caseResource, caseBound]
    exact atomicRowEqBranchesTransparentStructuralEnvelope_le_fixed
      valuation tokenTable width left otherLeft numericBound bitBound hwidth
      hleft hother htableSize hwidthSize hleftSize hotherSize
  change contextualBranchesUnderBoundPayloadEnvelope shiftedGamma bound
      targetFormula caseResource <= _
  unfold atomicRowEqContextualBranchesFixedPayloadPolynomial
  dsimp only [syntaxBound, formulaBound, bodyCode, caseBound, localBound]
  exact contextualBranchesUnderBoundPayloadEnvelope_le_components shiftedGamma
    bound targetFormula caseResource caseBound
    (cumulativeFiniteExhaustionPayloadPolynomial syntaxBound)
    (boundedUniversalFiniteExhaustionSpecializationEnvelope syntaxBound)
    localBound hcase hexhaustion hlower hweak heliminate hcut

def atomicRowEqUniversalShellScale
    (numericBound bitBound : Nat) : Nat :=
  numericBound + binaryNumeralTermCodeEnvelope bitBound + 1

def atomicRowEqUniversalFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let bodyCode := atomicRowEqUniversalBodyCodePolynomial bitBound
  let syntaxCode := numericBound + bodyCode
  let scale := atomicRowEqUniversalShellScale numericBound bitBound
  closedShortUniversalShellFixedPayloadPolynomial numericBound bitBound
    syntaxCode bodyCode
    (atomicRowEqContextualBranchesFixedPayloadPolynomial numericBound bitBound)
    (compileShiftedBoundEqualityFixedPayloadPolynomial scale)

theorem atomicRowEqUniversalStructuralPayloadEnvelope_le_fixed
    (valuation : Nat -> Nat)
    (tokenTable width left otherLeft numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (hleft : left <= numericBound)
    (hother : otherLeft <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hleftSize : Nat.size left <= bitBound)
    (hotherSize : Nat.size otherLeft <= bitBound) :
    atomicRowEqUniversalStructuralPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm otherLeft) <=
      atomicRowEqUniversalFixedPayloadPolynomial numericBound bitBound := by
  let body :=
    atomicRowEqBitBody (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm left)
      (shortBinaryNumeralTerm otherLeft)
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm width)) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let boundEqualityResource :=
    compileShiftedBoundEqualityPayloadResource valuation outerVariables
      (shortBinaryNumeralTerm width)
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) width (Rewriting.free body)
    (atomicRowEqBranchesTransparentStructuralEnvelope valuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm otherLeft))
  let bodyCode := atomicRowEqUniversalBodyCodePolynomial bitBound
  let syntaxCode := numericBound + bodyCode
  let scale := atomicRowEqUniversalShellScale numericBound bitBound
  let boundEqualityBound :=
    compileShiftedBoundEqualityFixedPayloadPolynomial scale
  let branchBound :=
    atomicRowEqContextualBranchesFixedPayloadPolynomial numericBound bitBound
  have houter : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      atomicRowEqUniversalOuterFormula_freeVariables_eq_empty_shortNumerals
        tokenTable width left otherLeft
  have hbody : (binaryFormulaCode body).length <= bodyCode := by
    dsimp only [body, bodyCode]
    exact atomicRowEqBitBody_code_length_le_fixed tokenTable width left
      otherLeft bitBound htableSize hwidthSize hleftSize hotherSize
  have hsyntax : width <= syntaxCode := by
    dsimp only [syntaxCode, bodyCode]
    omega
  have hbranch : branchResource <= branchBound := by
    dsimp only [branchResource, branchBound, Gamma, outerVariables,
      outerFormula, body]
    exact atomicRowEqContextualBranchesResource_le_fixed valuation tokenTable
      width left otherLeft numericBound bitBound hwidth hleft hother
      htableSize hwidthSize hleftSize hotherSize
  have hclosed :
      (shortBinaryNumeralTerm width : ValuationTerm).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty width
  have houterSubset : outerVariables ⊆ {0} := by
    rw [houter]
    simp
  have houterValues : forall index, index ∈ outerVariables ->
      valuation index <= scale := by
    intro index hindex
    rw [houter] at hindex
    simp at hindex
  have hvalue :
      termValue valuation (shortBinaryNumeralTerm width) <= scale := by
    simp only [termValue_shortBinaryNumeralTerm]
    dsimp only [scale]
    unfold atomicRowEqUniversalShellScale
    omega
  have hshortCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <=
        binaryNumeralTermCodeEnvelope bitBound :=
    binaryNumeralTerm_code_length_le_envelope width bitBound hwidthSize
  have hcode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= scale := by
    dsimp only [scale]
    unfold atomicRowEqUniversalShellScale
    omega
  have hboundPublic :=
    compileShiftedBoundEqualityPayloadResource_le_publicPolynomial valuation
      outerVariables (shortBinaryNumeralTerm width) hclosed
  have hboundFixed :=
    compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq_of_values
      valuation outerVariables (shortBinaryNumeralTerm width)
      (compileShiftedBoundEqualityPayloadPublicPolynomial valuation
        outerVariables (shortBinaryNumeralTerm width))
      boundEqualityBound scale rfl rfl hclosed houterSubset houterValues
      hvalue hcode
  have hbound : boundEqualityResource <= boundEqualityBound := by
    dsimp only [boundEqualityResource]
    exact hboundPublic.trans hboundFixed
  have hshell :=
    compileContextualTermBoundedUniversalPayloadEnvelope_empty_short_le_fixed
      body width numericBound bitBound syntaxCode bodyCode
      boundEqualityResource branchResource boundEqualityBound branchBound
      hwidth hwidthSize hsyntax hbody hbound hbranch
  simpa only [atomicRowEqUniversalStructuralPayloadEnvelope, body,
    outerFormula, outerVariables, Gamma, boundEqualityResource,
    branchResource,
    atomicRowEqUniversalOuterFormula_freeVariables_eq_empty_shortNumerals
      tokenTable width left otherLeft,
    valuationContext, Finset.image_empty, termValue_shortBinaryNumeralTerm,
    atomicRowEqUniversalFixedPayloadPolynomial, bodyCode, syntaxCode, scale,
    boundEqualityBound, branchBound] using hshell

def atomicRowEqOuterTermCodePolynomial (bitBound : Nat) : Nat :=
  2 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (‘1’ : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

def atomicRowEqOuterAtomicFormulaCodePolynomial (bitBound : Nat) : Nat :=
  orderAtomicFormulaCodeEnvelope
    (atomicRowEqOuterTermCodePolynomial bitBound)

def atomicRowEqOuterUniversalFormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  let bodyCode := atomicRowEqUniversalBodyCodePolynomial bitBound
  let syntaxCode := numericBound + bodyCode
  closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
    syntaxCode bodyCode

def atomicRowEqAssemblySyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  4 * atomicRowEqOuterAtomicFormulaCodePolynomial bitBound +
    atomicRowEqOuterUniversalFormulaCodePolynomial numericBound bitBound +
    4 * (binaryNatCode 4).length + 1

def compactAdditiveAtomicRowEqFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    atomicRowEqAssemblySyntaxPolynomial numericBound bitBound
  let atomicResource := compilePositiveRelationFixedPayloadPolynomial
    numericBound (atomicRowEqOuterTermCodePolynomial bitBound)
  let universalResource :=
    atomicRowEqUniversalFixedPayloadPolynomial numericBound bitBound
  let resource45 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource universalResource
  let resource345 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource resource45
  let resource2345 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource resource345
  hybridConjunctionGeneralPayloadEnvelope syntaxResource atomicResource
    resource2345

theorem
    compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope_le_fixed
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount left right otherLeft otherRight
      numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hleft : left <= numericBound)
    (hright : right <= numericBound)
    (hotherLeft : otherLeft <= numericBound)
    (hotherRight : otherRight <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm left)
        (shortBinaryNumeralTerm right) (shortBinaryNumeralTerm otherLeft)
        (shortBinaryNumeralTerm otherRight) <=
      compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound
        bitBound := by
  let tableTerm : ValuationTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm : ValuationTerm := shortBinaryNumeralTerm width
  let tokenCountTerm : ValuationTerm := shortBinaryNumeralTerm tokenCount
  let leftTerm : ValuationTerm := shortBinaryNumeralTerm left
  let rightTerm : ValuationTerm := shortBinaryNumeralTerm right
  let otherLeftTerm : ValuationTerm := shortBinaryNumeralTerm otherLeft
  let otherRightTerm : ValuationTerm := shortBinaryNumeralTerm otherRight
  let leftSumTerm : ValuationTerm := ‘!!leftTerm + 1’
  let otherSumTerm : ValuationTerm := ‘!!otherLeftTerm + 1’
  let leftStrictFormula : ValuationFormula :=
    “!!leftTerm < !!tokenCountTerm”
  let leftSuccessorFormula : ValuationFormula :=
    “!!rightTerm = !!leftSumTerm”
  let otherStrictFormula : ValuationFormula :=
    “!!otherLeftTerm < !!tokenCountTerm”
  let otherSuccessorFormula : ValuationFormula :=
    “!!otherRightTerm = !!otherSumTerm”
  let body := atomicRowEqBitBody tableTerm widthTerm leftTerm otherLeftTerm
  let universalFormula : ValuationFormula := body.ballLT widthTerm
  let formula45 := otherSuccessorFormula ⋏ universalFormula
  let formula345 := otherStrictFormula ⋏ formula45
  let formula2345 := leftSuccessorFormula ⋏ formula345
  let termCode := atomicRowEqOuterTermCodePolynomial bitBound
  let atomicCode := atomicRowEqOuterAtomicFormulaCodePolynomial bitBound
  let universalCode :=
    atomicRowEqOuterUniversalFormulaCodePolynomial numericBound bitBound
  let conjunctionTag := (binaryNatCode 4).length
  let syntaxResource :=
    atomicRowEqAssemblySyntaxPolynomial numericBound bitBound
  let leftStrictResource := atomicRowEqStrictStructuralPayloadResource
    valuation leftTerm tokenCountTerm
  let leftSuccessorResource := atomicRowEqSuccessorStructuralPayloadResource
    valuation leftTerm rightTerm
  let otherStrictResource := atomicRowEqStrictStructuralPayloadResource
    valuation otherLeftTerm tokenCountTerm
  let otherSuccessorResource := atomicRowEqSuccessorStructuralPayloadResource
    valuation otherLeftTerm otherRightTerm
  let universalResource := atomicRowEqUniversalStructuralPayloadEnvelope
    valuation tableTerm widthTerm leftTerm otherLeftTerm
  let atomicResource := compilePositiveRelationFixedPayloadPolynomial
    numericBound termCode
  let universalFixed :=
    atomicRowEqUniversalFixedPayloadPolynomial numericBound bitBound
  let resource45 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource universalFixed
  let resource345 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource resource45
  let resource2345 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource resource345
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hleftSize : Nat.size left <= bitBound :=
    (Nat.size_le_size hleft).trans hnumericSize
  have hrightSize : Nat.size right <= bitBound :=
    (Nat.size_le_size hright).trans hnumericSize
  have hotherLeftSize : Nat.size otherLeft <= bitBound :=
    (Nat.size_le_size hotherLeft).trans hnumericSize
  have hotherRightSize : Nat.size otherRight <= bitBound :=
    (Nat.size_le_size hotherRight).trans hnumericSize
  have htableClosed : tableTerm.freeVariables = ∅ := by
    dsimp only [tableTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  have hwidthClosed : widthTerm.freeVariables = ∅ := by
    dsimp only [widthTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  have htokenCountClosed : tokenCountTerm.freeVariables = ∅ := by
    dsimp only [tokenCountTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hleftClosed : leftTerm.freeVariables = ∅ := by
    dsimp only [leftTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty left
  have hrightClosed : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty right
  have hotherLeftClosed : otherLeftTerm.freeVariables = ∅ := by
    dsimp only [otherLeftTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty otherLeft
  have hotherRightClosed : otherRightTerm.freeVariables = ∅ := by
    dsimp only [otherRightTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty otherRight
  have hleftSumClosed : leftSumTerm.freeVariables = ∅ := by
    dsimp only [leftSumTerm]
    rw [arithmeticAddTerm_freeVariables_atomicRowFixed, hleftClosed,
      arithmeticOneTerm_freeVariables_eq_empty_atomicRowFixed]
    simp
  have hotherSumClosed : otherSumTerm.freeVariables = ∅ := by
    dsimp only [otherSumTerm]
    rw [arithmeticAddTerm_freeVariables_atomicRowFixed, hotherLeftClosed,
      arithmeticOneTerm_freeVariables_eq_empty_atomicRowFixed]
    simp
  have htableCode :
      (binaryTermCode tableTerm).length <= termCode := by
    have hraw := binaryNumeralTerm_code_length_le_envelope tokenTable
      bitBound htableSize
    dsimp only [tableTerm, termCode]
    unfold atomicRowEqOuterTermCodePolynomial
    omega
  have hwidthCode :
      (binaryTermCode widthTerm).length <= termCode := by
    have hraw := binaryNumeralTerm_code_length_le_envelope width bitBound
      hwidthSize
    dsimp only [widthTerm, termCode]
    unfold atomicRowEqOuterTermCodePolynomial
    omega
  have htokenCountCode :
      (binaryTermCode tokenCountTerm).length <= termCode := by
    have hraw := binaryNumeralTerm_code_length_le_envelope tokenCount bitBound
      htokenCountSize
    dsimp only [tokenCountTerm, termCode]
    unfold atomicRowEqOuterTermCodePolynomial
    omega
  have hleftCode : (binaryTermCode leftTerm).length <= termCode := by
    have hraw := binaryNumeralTerm_code_length_le_envelope left bitBound
      hleftSize
    dsimp only [leftTerm, termCode]
    unfold atomicRowEqOuterTermCodePolynomial
    omega
  have hrightCode : (binaryTermCode rightTerm).length <= termCode := by
    have hraw := binaryNumeralTerm_code_length_le_envelope right bitBound
      hrightSize
    dsimp only [rightTerm, termCode]
    unfold atomicRowEqOuterTermCodePolynomial
    omega
  have hotherLeftCode :
      (binaryTermCode otherLeftTerm).length <= termCode := by
    have hraw := binaryNumeralTerm_code_length_le_envelope otherLeft bitBound
      hotherLeftSize
    dsimp only [otherLeftTerm, termCode]
    unfold atomicRowEqOuterTermCodePolynomial
    omega
  have hotherRightCode :
      (binaryTermCode otherRightTerm).length <= termCode := by
    have hraw := binaryNumeralTerm_code_length_le_envelope otherRight bitBound
      hotherRightSize
    dsimp only [otherRightTerm, termCode]
    unfold atomicRowEqOuterTermCodePolynomial
    omega
  have hleftNumeralCode :
      (binaryTermCode leftTerm).length <=
        binaryNumeralTermCodeEnvelope bitBound := by
    dsimp only [leftTerm]
    exact binaryNumeralTerm_code_length_le_envelope left bitBound hleftSize
  have hleftSumRaw := arithmeticAddTerm_code_length_le_atomicRowFixed
    leftTerm (‘1’ : ValuationTerm)
  have hleftSumCode : (binaryTermCode leftSumTerm).length <= termCode := by
    dsimp only [leftSumTerm, termCode]
    unfold atomicRowEqOuterTermCodePolynomial
    omega
  have hotherLeftNumeralCode :
      (binaryTermCode otherLeftTerm).length <=
        binaryNumeralTermCodeEnvelope bitBound := by
    dsimp only [otherLeftTerm]
    exact binaryNumeralTerm_code_length_le_envelope otherLeft bitBound
      hotherLeftSize
  have hotherSumRaw := arithmeticAddTerm_code_length_le_atomicRowFixed
    otherLeftTerm (‘1’ : ValuationTerm)
  have hotherSumCode :
      (binaryTermCode otherSumTerm).length <= termCode := by
    dsimp only [otherSumTerm, termCode]
    unfold atomicRowEqOuterTermCodePolynomial
    omega
  have hleftStrictResource : leftStrictResource <= atomicResource := by
    dsimp only [leftStrictResource, atomicResource]
    unfold atomicRowEqStrictStructuralPayloadResource
    exact compilePositiveRelationPayloadResource_le_fixed_of_closed valuation
      Language.ORing.Rel.lt leftTerm tokenCountTerm numericBound termCode
      hleftClosed htokenCountClosed hleftCode htokenCountCode
  have hleftSuccessorResource :
      leftSuccessorResource <= atomicResource := by
    dsimp only [leftSuccessorResource, atomicResource]
    unfold atomicRowEqSuccessorStructuralPayloadResource
    exact compilePositiveRelationPayloadResource_le_fixed_of_closed valuation
      Language.Eq.eq rightTerm leftSumTerm numericBound termCode
      hrightClosed hleftSumClosed hrightCode hleftSumCode
  have hotherStrictResource : otherStrictResource <= atomicResource := by
    dsimp only [otherStrictResource, atomicResource]
    unfold atomicRowEqStrictStructuralPayloadResource
    exact compilePositiveRelationPayloadResource_le_fixed_of_closed valuation
      Language.ORing.Rel.lt otherLeftTerm tokenCountTerm numericBound termCode
      hotherLeftClosed htokenCountClosed hotherLeftCode htokenCountCode
  have hotherSuccessorResource :
      otherSuccessorResource <= atomicResource := by
    dsimp only [otherSuccessorResource, atomicResource]
    unfold atomicRowEqSuccessorStructuralPayloadResource
    exact compilePositiveRelationPayloadResource_le_fixed_of_closed valuation
      Language.Eq.eq otherRightTerm otherSumTerm numericBound termCode
      hotherRightClosed hotherSumClosed hotherRightCode hotherSumCode
  have huniversalResource : universalResource <= universalFixed := by
    dsimp only [universalResource, universalFixed, tableTerm, widthTerm,
      leftTerm, otherLeftTerm]
    exact atomicRowEqUniversalStructuralPayloadEnvelope_le_fixed valuation
      tokenTable width left otherLeft numericBound bitBound hwidth hleft
      hotherLeft htableSize hwidthSize hleftSize hotherLeftSize
  have hleftStrictCodeAtomic :
      (binaryFormulaCode leftStrictFormula).length <= atomicCode := by
    dsimp only [leftStrictFormula, atomicCode, termCode]
    unfold atomicRowEqOuterAtomicFormulaCodePolynomial
    simpa only [LO.FirstOrder.Semiformula.Operator.lt_def,
      binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.LT.lt leftTerm
        tokenCountTerm termCode hleftCode htokenCountCode)
  have hleftSuccessorCodeAtomic :
      (binaryFormulaCode leftSuccessorFormula).length <= atomicCode := by
    dsimp only [leftSuccessorFormula, atomicCode, termCode]
    unfold atomicRowEqOuterAtomicFormulaCodePolynomial
    simpa only [LO.FirstOrder.Semiformula.Operator.eq_def,
      binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.Eq.eq rightTerm
        leftSumTerm termCode hrightCode hleftSumCode)
  have hotherStrictCodeAtomic :
      (binaryFormulaCode otherStrictFormula).length <= atomicCode := by
    dsimp only [otherStrictFormula, atomicCode, termCode]
    unfold atomicRowEqOuterAtomicFormulaCodePolynomial
    simpa only [LO.FirstOrder.Semiformula.Operator.lt_def,
      binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.LT.lt otherLeftTerm
        tokenCountTerm termCode hotherLeftCode htokenCountCode)
  have hotherSuccessorCodeAtomic :
      (binaryFormulaCode otherSuccessorFormula).length <= atomicCode := by
    dsimp only [otherSuccessorFormula, atomicCode, termCode]
    unfold atomicRowEqOuterAtomicFormulaCodePolynomial
    simpa only [LO.FirstOrder.Semiformula.Operator.eq_def,
      binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.Eq.eq otherRightTerm
        otherSumTerm termCode hotherRightCode hotherSumCode)
  have hbodyCode : (binaryFormulaCode body).length <=
      atomicRowEqUniversalBodyCodePolynomial bitBound := by
    dsimp only [body, tableTerm, widthTerm, leftTerm, otherLeftTerm]
    exact atomicRowEqBitBody_code_length_le_fixed tokenTable width left
      otherLeft bitBound htableSize hwidthSize hleftSize hotherLeftSize
  have huniversalCode :
      (binaryFormulaCode universalFormula).length <= universalCode := by
    have hraw :=
      closedShortTermBoundedUniversalFormula_code_length_le_source body width
        numericBound bitBound
        (numericBound + atomicRowEqUniversalBodyCodePolynomial bitBound)
        (atomicRowEqUniversalBodyCodePolynomial bitBound) hwidthSize hbodyCode
    have halign :
        (∀⁰ termBoundedUniversalBody (Rew.bShift widthTerm) body) =
          universalFormula := by
      dsimp only [universalFormula]
      rw [termBoundedUniversal_eq_ball]
      rfl
    rw [← halign]
    dsimp only [universalCode]
    unfold atomicRowEqOuterUniversalFormulaCodePolynomial
    exact hraw
  have hleftStrictClosed : leftStrictFormula.freeVariables = ∅ := by
    change
      (LO.FirstOrder.Semiformula.rel Language.LT.lt
        ![leftTerm, tokenCountTerm]).freeVariables = ∅
    rw [binaryRelationFormula_freeVariables_atomicRowFixed, hleftClosed,
      htokenCountClosed]
    simp
  have hleftSuccessorClosed :
      leftSuccessorFormula.freeVariables = ∅ := by
    change
      (LO.FirstOrder.Semiformula.rel Language.Eq.eq
        ![rightTerm, leftSumTerm]).freeVariables = ∅
    rw [binaryRelationFormula_freeVariables_atomicRowFixed, hrightClosed,
      hleftSumClosed]
    simp
  have hotherStrictClosed : otherStrictFormula.freeVariables = ∅ := by
    change
      (LO.FirstOrder.Semiformula.rel Language.LT.lt
        ![otherLeftTerm, tokenCountTerm]).freeVariables = ∅
    rw [binaryRelationFormula_freeVariables_atomicRowFixed, hotherLeftClosed,
      htokenCountClosed]
    simp
  have hotherSuccessorClosed :
      otherSuccessorFormula.freeVariables = ∅ := by
    change
      (LO.FirstOrder.Semiformula.rel Language.Eq.eq
        ![otherRightTerm, otherSumTerm]).freeVariables = ∅
    rw [binaryRelationFormula_freeVariables_atomicRowFixed, hotherRightClosed,
      hotherSumClosed]
    simp
  have huniversalClosed : universalFormula.freeVariables = ∅ := by
    have halign :
        (∀⁰ termBoundedUniversalBody (Rew.bShift widthTerm) body) =
          universalFormula := by
      dsimp only [universalFormula]
      rw [termBoundedUniversal_eq_ball]
      rfl
    rw [← halign]
    dsimp only [body, tableTerm, widthTerm, leftTerm, otherLeftTerm]
    exact
      atomicRowEqUniversalOuterFormula_freeVariables_eq_empty_shortNumerals
        tokenTable width left otherLeft
  have hformula45Closed : formula45.freeVariables = ∅ := by
    dsimp only [formula45]
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      hotherSuccessorClosed, huniversalClosed]
    simp
  have hformula345Closed : formula345.freeVariables = ∅ := by
    dsimp only [formula345]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hotherStrictClosed,
      hformula45Closed]
    simp
  have hformula2345Closed : formula2345.freeVariables = ∅ := by
    dsimp only [formula2345]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hleftSuccessorClosed,
      hformula345Closed]
    simp
  have hcode45Raw := binaryFormulaCode_and_length_le_local
    otherSuccessorFormula universalFormula
  have hcode45 : (binaryFormulaCode formula45).length <=
      atomicCode + universalCode + conjunctionTag := by
    dsimp only [formula45, conjunctionTag] at hcode45Raw ⊢
    omega
  have hcode345Raw := binaryFormulaCode_and_length_le_local
    otherStrictFormula formula45
  have hcode345 : (binaryFormulaCode formula345).length <=
      2 * atomicCode + universalCode + 2 * conjunctionTag := by
    dsimp only [formula345] at hcode345Raw ⊢
    omega
  have hcode2345Raw := binaryFormulaCode_and_length_le_local
    leftSuccessorFormula formula345
  have hcode2345 : (binaryFormulaCode formula2345).length <=
      3 * atomicCode + universalCode + 3 * conjunctionTag := by
    dsimp only [formula2345] at hcode2345Raw ⊢
    omega
  have hcodeTotalRaw := binaryFormulaCode_and_length_le_local
    leftStrictFormula formula2345
  have hcodeTotal :
      (binaryFormulaCode (leftStrictFormula ⋏ formula2345)).length <=
        4 * atomicCode + universalCode + 4 * conjunctionTag := by
    omega
  have hsyntaxPositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource, atomicCode, universalCode, conjunctionTag]
    unfold atomicRowEqAssemblySyntaxPolynomial
    omega
  have hatomicSyntax : atomicCode <= syntaxResource := by
    dsimp only [syntaxResource, atomicCode, universalCode, conjunctionTag]
    unfold atomicRowEqAssemblySyntaxPolynomial
    omega
  have huniversalSyntax : universalCode <= syntaxResource := by
    dsimp only [syntaxResource, atomicCode, universalCode, conjunctionTag]
    unfold atomicRowEqAssemblySyntaxPolynomial
    omega
  have hcode45Syntax :
      (binaryFormulaCode formula45).length <= syntaxResource :=
    hcode45.trans (by
      dsimp only [syntaxResource, atomicCode, universalCode, conjunctionTag]
      unfold atomicRowEqAssemblySyntaxPolynomial
      omega)
  have hcode345Syntax :
      (binaryFormulaCode formula345).length <= syntaxResource :=
    hcode345.trans (by
      dsimp only [syntaxResource, atomicCode, universalCode, conjunctionTag]
      unfold atomicRowEqAssemblySyntaxPolynomial
      omega)
  have hcode2345Syntax :
      (binaryFormulaCode formula2345).length <= syntaxResource :=
    hcode2345.trans (by
      dsimp only [syntaxResource, atomicCode, universalCode, conjunctionTag]
      unfold atomicRowEqAssemblySyntaxPolynomial
      omega)
  have hcodeTotalSyntax :
      (binaryFormulaCode (leftStrictFormula ⋏ formula2345)).length <=
        syntaxResource :=
    hcodeTotal.trans (by
      dsimp only [syntaxResource, atomicCode, universalCode, conjunctionTag]
      unfold atomicRowEqAssemblySyntaxPolynomial
      omega)
  have h45Mono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    otherSuccessorFormula universalFormula hotherSuccessorResource
      huniversalResource
  have h45General :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      otherSuccessorFormula universalFormula atomicResource universalFixed
      syntaxResource hsyntaxPositive hotherSuccessorClosed huniversalClosed
      (hotherSuccessorCodeAtomic.trans hatomicSyntax)
      (huniversalCode.trans huniversalSyntax) hcode45Syntax
  have h45 :
      transparentHybridConjunctionPayloadEnvelope valuation
          otherSuccessorFormula universalFormula otherSuccessorResource
          universalResource <= resource45 := by
    exact h45Mono.trans h45General
  have h345Mono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    otherStrictFormula formula45 hotherStrictResource h45
  have h345General :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      otherStrictFormula formula45 atomicResource resource45 syntaxResource
      hsyntaxPositive hotherStrictClosed hformula45Closed
      (hotherStrictCodeAtomic.trans hatomicSyntax) hcode45Syntax
      hcode345Syntax
  have h345 :
      transparentHybridConjunctionPayloadEnvelope valuation
          otherStrictFormula formula45 otherStrictResource
          (transparentHybridConjunctionPayloadEnvelope valuation
            otherSuccessorFormula universalFormula otherSuccessorResource
            universalResource) <= resource345 := by
    exact h345Mono.trans h345General
  have h2345Mono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    leftSuccessorFormula formula345 hleftSuccessorResource h345
  have h2345General :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      leftSuccessorFormula formula345 atomicResource resource345
      syntaxResource hsyntaxPositive hleftSuccessorClosed hformula345Closed
      (hleftSuccessorCodeAtomic.trans hatomicSyntax) hcode345Syntax
      hcode2345Syntax
  have h2345 :
      transparentHybridConjunctionPayloadEnvelope valuation
          leftSuccessorFormula formula345 leftSuccessorResource
          (transparentHybridConjunctionPayloadEnvelope valuation
            otherStrictFormula formula45 otherStrictResource
            (transparentHybridConjunctionPayloadEnvelope valuation
              otherSuccessorFormula universalFormula otherSuccessorResource
              universalResource)) <= resource2345 := by
    exact h2345Mono.trans h2345General
  have htotalMono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    leftStrictFormula formula2345 hleftStrictResource h2345
  have htotalGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      leftStrictFormula formula2345 atomicResource resource2345 syntaxResource
      hsyntaxPositive hleftStrictClosed hformula2345Closed
      (hleftStrictCodeAtomic.trans hatomicSyntax) hcode2345Syntax
      hcodeTotalSyntax
  have htotal :=
    htotalMono.trans htotalGeneral
  simpa only [
    compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope,
    tableTerm, widthTerm, tokenCountTerm, leftTerm, rightTerm,
    otherLeftTerm, otherRightTerm, leftSumTerm, otherSumTerm,
    leftStrictFormula, leftSuccessorFormula, otherStrictFormula,
    otherSuccessorFormula, body, universalFormula, formula45, formula345,
    formula2345, leftStrictResource, leftSuccessorResource,
    otherStrictResource, otherSuccessorResource, universalResource,
    compactAdditiveAtomicRowEqFixedPayloadPolynomial, syntaxResource,
    atomicResource, universalFixed, resource45, resource345, resource2345]
    using htotal

#print axioms
  compileBinaryBitLiteralAtAtomicRowShortNumeralsPayloadPolynomial_le_fixed
#print axioms atomicRowEqBitBranchPublicPayloadEnvelope_le_fixed
#print axioms atomicRowEqBitBranchPublicPayloadSum_le_fixed
#print axioms atomicRowEqBitBody_code_length_le_fixed
#print axioms
  atomicRowEqBranchesTransparentStructuralEnvelope_le_fixed
#print axioms atomicRowEqContextualBranchesResource_le_fixed
#print axioms atomicRowEqUniversalStructuralPayloadEnvelope_le_fixed
#print axioms
  compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope_le_fixed

end FoundationCompactNumericListedDirectAtomicRowEqualityFixedPolynomialBounds
