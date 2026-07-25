import integration.FoundationCompactNumericListedDirectNatListDropOneRowsUniversalFullyFixedBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds

/-!
# Fully fixed outer count leaves for drop-one natural-list rows

The formulas `1 <= sourceCount` and
`sourceCount = 1 + targetCount` are closed.  Their original public payload
polynomials and formula codes are bounded only by the shared bit coordinate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListDropOneRowsCountLeavesFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds

private abbrev dropOneRowsZeroValuationCount : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation

def dropOneRowsCountTermCodePolynomial (bitBound : Nat) : Nat :=
  (binaryTermCode (fixedNumeralTerm 1)).length +
    2 * binaryNumeralTermCodeEnvelope bitBound +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

def dropOneRowsCountAtomicCodePolynomial (bitBound : Nat) : Nat :=
  orderAtomicFormulaCodeEnvelope
    (dropOneRowsCountTermCodePolynomial bitBound)

def dropOneRowsCountBoundFormulaCodePolynomial (bitBound : Nat) : Nat :=
  2 * dropOneRowsCountAtomicCodePolynomial bitBound + 8

def dropOneRowsCountEqualityFormulaCodePolynomial (bitBound : Nat) : Nat :=
  dropOneRowsCountAtomicCodePolynomial bitBound

def dropOneRowsCountBoundFullyFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  2 * compilePositiveRelationFixedPayloadPolynomial 0
      (dropOneRowsCountTermCodePolynomial bitBound) +
    3 * smallContextAssemblyEnvelope
      (dropOneRowsCountBoundFormulaCodePolynomial bitBound) + 1

def dropOneRowsCountEqualityFullyFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (dropOneRowsCountTermCodePolynomial bitBound)

private theorem dropOneArithmeticAdd_freeVariables_count
    {Variable : Type*} [DecidableEq Variable] {arity : Nat}
    (left right : ArithmeticSemiterm Variable arity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable arity).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables
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

private theorem dropOneBinaryRelation_freeVariables_count
    (relation : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiformula.rel relation
      ![left, right]).freeVariables =
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

@[simp] private theorem dropOneFixedOne_freeVariables_eq_empty :
    (fixedNumeralTerm 1).freeVariables = ∅ := by
  unfold fixedNumeralTerm Semiterm.Operator.operator
  simp

private theorem dropOneCountTerms_code_length_le
    (sourceCount targetCount bitBound : Nat)
    (hsourceCountSize : Nat.size sourceCount <= bitBound)
    (htargetCountSize : Nat.size targetCount <= bitBound) :
    (binaryTermCode (fixedNumeralTerm 1)).length <=
        dropOneRowsCountTermCodePolynomial bitBound ∧
      (binaryTermCode (shortBinaryNumeralTerm sourceCount)).length <=
        dropOneRowsCountTermCodePolynomial bitBound ∧
      (binaryTermCode
        (‘!!(fixedNumeralTerm 1) +
          !!(shortBinaryNumeralTerm targetCount)’ : ValuationTerm)).length <=
        dropOneRowsCountTermCodePolynomial bitBound := by
  have hsource := binaryNumeralTerm_code_length_le_envelope sourceCount
    bitBound hsourceCountSize
  have htarget := binaryNumeralTerm_code_length_le_envelope targetCount
    bitBound htargetCountSize
  have hadd := arithmeticAddTerm_code_length_le
    (fixedNumeralTerm 1) (shortBinaryNumeralTerm targetCount)
  unfold dropOneRowsCountTermCodePolynomial
  omega

theorem dropOneRowsCountBoundFormula_code_length_le_fixed
    (sourceCount bitBound : Nat)
    (hsourceCountSize : Nat.size sourceCount <= bitBound) :
    (binaryFormulaCode
      (“!!(fixedNumeralTerm 1) ≤
        !!(shortBinaryNumeralTerm sourceCount)” :
        ValuationFormula)).length <=
      dropOneRowsCountBoundFormulaCodePolynomial bitBound := by
  let leftTerm : ValuationTerm := fixedNumeralTerm 1
  let rightTerm : ValuationTerm := shortBinaryNumeralTerm sourceCount
  let equalityFormula :=
    LO.FirstOrder.Semiformula.rel Language.Eq.eq ![leftTerm, rightTerm]
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.LT.lt ![leftTerm, rightTerm]
  let termCode := dropOneRowsCountTermCodePolynomial bitBound
  let atomicCode := dropOneRowsCountAtomicCodePolynomial bitBound
  have hterms := dropOneCountTerms_code_length_le sourceCount 0 bitBound
    hsourceCountSize (Nat.zero_le bitBound)
  have hleft := hterms.1
  have hright := hterms.2.1
  have hequality :
      (binaryFormulaCode equalityFormula).length <= atomicCode := by
    dsimp only [equalityFormula, atomicCode]
    have hraw := binaryRelationFormula_code_le_orderAtomic Language.Eq.eq
      leftTerm rightTerm termCode hleft hright
    simpa only [
      FoundationCompactPAQuantitativeRelationCongruence.binaryRelationFormula,
      atomicCode, termCode, dropOneRowsCountAtomicCodePolynomial]
      using hraw
  have hstrict :
      (binaryFormulaCode strictFormula).length <= atomicCode := by
    dsimp only [strictFormula, atomicCode]
    have hraw := binaryRelationFormula_code_le_orderAtomic Language.LT.lt
      leftTerm rightTerm termCode hleft hright
    simpa only [
      FoundationCompactPAQuantitativeRelationCongruence.binaryRelationFormula,
      atomicCode, termCode, dropOneRowsCountAtomicCodePolynomial]
      using hraw
  have hor := binaryFormulaCode_or_length_le_local equalityFormula
    strictFormula
  have htag : (binaryNatCode 5).length <= 8 := by decide
  change
    (binaryFormulaCode (equalityFormula ⋎ strictFormula)).length <= _
  unfold dropOneRowsCountBoundFormulaCodePolynomial
  omega

theorem dropOneRowsCountEqualityFormula_code_length_le_fixed
    (sourceCount targetCount bitBound : Nat)
    (hsourceCountSize : Nat.size sourceCount <= bitBound)
    (htargetCountSize : Nat.size targetCount <= bitBound) :
    (binaryFormulaCode
      (“!!(shortBinaryNumeralTerm sourceCount) =
        !!(fixedNumeralTerm 1) +
          !!(shortBinaryNumeralTerm targetCount)” :
        ValuationFormula)).length <=
      dropOneRowsCountEqualityFormulaCodePolynomial bitBound := by
  let rightTerm : ValuationTerm :=
    ‘!!(fixedNumeralTerm 1) +
      !!(shortBinaryNumeralTerm targetCount)’
  have hterms := dropOneCountTerms_code_length_le sourceCount targetCount
    bitBound hsourceCountSize htargetCountSize
  unfold dropOneRowsCountEqualityFormulaCodePolynomial
    dropOneRowsCountAtomicCodePolynomial
  exact binaryRelationFormula_code_le_orderAtomic Language.Eq.eq
    (shortBinaryNumeralTerm sourceCount) rightTerm
    (dropOneRowsCountTermCodePolynomial bitBound) hterms.2.1 hterms.2.2

@[simp] theorem dropOneRowsCountBoundFormula_freeVariables_eq_empty
    (sourceCount : Nat) :
    (“!!(fixedNumeralTerm 1) ≤
      !!(shortBinaryNumeralTerm sourceCount)” :
      ValuationFormula).freeVariables = ∅ := by
  let leftTerm : ValuationTerm := fixedNumeralTerm 1
  let rightTerm : ValuationTerm := shortBinaryNumeralTerm sourceCount
  let equalityFormula :=
    LO.FirstOrder.Semiformula.rel Language.Eq.eq ![leftTerm, rightTerm]
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.LT.lt ![leftTerm, rightTerm]
  have hleft : leftTerm.freeVariables = ∅ := by
    simp only [leftTerm, dropOneFixedOne_freeVariables_eq_empty]
  have hright : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty sourceCount
  change (equalityFormula ⋎ strictFormula).freeVariables = ∅
  rw [LO.FirstOrder.Semiformula.freeVariables_or]
  dsimp only [equalityFormula, strictFormula]
  rw [dropOneBinaryRelation_freeVariables_count,
    dropOneBinaryRelation_freeVariables_count, hleft, hright]
  simp

@[simp] theorem dropOneRowsCountEqualityFormula_freeVariables_eq_empty
    (sourceCount targetCount : Nat) :
    (“!!(shortBinaryNumeralTerm sourceCount) =
      !!(fixedNumeralTerm 1) +
        !!(shortBinaryNumeralTerm targetCount)” :
      ValuationFormula).freeVariables = ∅ := by
  let leftTerm : ValuationTerm := shortBinaryNumeralTerm sourceCount
  let rightTerm : ValuationTerm :=
    ‘!!(fixedNumeralTerm 1) +
      !!(shortBinaryNumeralTerm targetCount)’
  have hleft : leftTerm.freeVariables = ∅ := by
    dsimp only [leftTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty sourceCount
  have hright : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    rw [dropOneArithmeticAdd_freeVariables_count,
      dropOneFixedOne_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  change
    (LO.FirstOrder.Semiformula.rel Language.Eq.eq
      ![leftTerm, rightTerm]).freeVariables = ∅
  rw [dropOneBinaryRelation_freeVariables_count, hleft, hright]
  simp

theorem dropOneRowsCountBoundPayloadPolynomial_le_fullyFixed
    (sourceCount bitBound : Nat)
    (hsourceCountSize : Nat.size sourceCount <= bitBound) :
    compactAdditiveNatListDropFixedNumeralRowsCountBoundPayloadPolynomial
        1 sourceCount <=
      dropOneRowsCountBoundFullyFixedPayloadPolynomial bitBound := by
  let leftTerm : ValuationTerm := fixedNumeralTerm 1
  let rightTerm : ValuationTerm := shortBinaryNumeralTerm sourceCount
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula :=
    LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.LT.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables
    dropOneRowsZeroValuationCount
  let termCode := dropOneRowsCountTermCodePolynomial bitBound
  let formulaCode := dropOneRowsCountBoundFormulaCodePolynomial bitBound
  have hterms := dropOneCountTerms_code_length_le sourceCount 0 bitBound
    hsourceCountSize (Nat.zero_le bitBound)
  have hleftCode := hterms.1
  have hrightCode := hterms.2.1
  have hleftClosed : leftTerm.freeVariables = ∅ := by
    simp only [leftTerm, dropOneFixedOne_freeVariables_eq_empty]
  have hrightClosed : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty sourceCount
  have hfirst : (args 0).freeVariables ⊆ {0} := by
    change leftTerm.freeVariables ⊆ {0}
    rw [hleftClosed]
    simp
  have hsecond : (args 1).freeVariables ⊆ {0} := by
    change rightTerm.freeVariables ⊆ {0}
    rw [hrightClosed]
    simp
  have hequalityResource :=
    compilePositiveRelationPayloadPolynomial_le_fixed
      dropOneRowsZeroValuationCount Language.Eq.eq args 0 termCode
      hfirst hsecond (by rfl) hleftCode hrightCode
  have hstrictResource :=
    compilePositiveRelationPayloadPolynomial_le_fixed
      dropOneRowsZeroValuationCount Language.ORing.Rel.lt args 0 termCode
      hfirst hsecond (by rfl) hleftCode hrightCode
  have hequalityAtomic :
      (binaryFormulaCode equalityFormula).length <=
        dropOneRowsCountAtomicCodePolynomial bitBound := by
    have hraw := binaryRelationFormula_code_le_orderAtomic Language.Eq.eq
      leftTerm rightTerm termCode hleftCode hrightCode
    simpa only [equalityFormula, args,
      FoundationCompactPAQuantitativeRelationCongruence.binaryRelationFormula,
      dropOneRowsCountAtomicCodePolynomial, termCode] using hraw
  have hstrictAtomic :
      (binaryFormulaCode strictFormula).length <=
        dropOneRowsCountAtomicCodePolynomial bitBound := by
    have hraw := binaryRelationFormula_code_le_orderAtomic Language.LT.lt
      leftTerm rightTerm termCode hleftCode hrightCode
    simpa only [strictFormula, args,
      FoundationCompactPAQuantitativeRelationCongruence.binaryRelationFormula,
      dropOneRowsCountAtomicCodePolynomial, termCode] using hraw
  have hequalityCode :
      (binaryFormulaCode equalityFormula).length <= formulaCode := by
    unfold formulaCode dropOneRowsCountBoundFormulaCodePolynomial
    omega
  have hstrictCode :
      (binaryFormulaCode strictFormula).length <= formulaCode := by
    unfold formulaCode dropOneRowsCountBoundFormulaCodePolynomial
    omega
  have htargetCode :
      (binaryFormulaCode targetFormula).length <= formulaCode := by
    have hraw := binaryFormulaCode_or_length_le_local equalityFormula
      strictFormula
    have htag : (binaryNatCode 5).length <= 8 := by decide
    dsimp only [targetFormula]
    unfold formulaCode dropOneRowsCountBoundFormulaCodePolynomial
    omega
  have htargetClosed : targetFormula.freeVariables = ∅ := by
    dsimp only [targetFormula, equalityFormula, strictFormula, args]
    rw [LO.FirstOrder.Semiformula.freeVariables_or,
      dropOneBinaryRelation_freeVariables_count,
      dropOneBinaryRelation_freeVariables_count,
      hleftClosed, hrightClosed]
    simp
  have hGammaEmpty : Gamma = ∅ := by
    unfold Gamma valuationContext
    rw [htargetClosed]
    simp
  have hcontext : FormulaCodeBound Gamma formulaCode := by
    rw [hGammaEmpty]
    intro formula hformula
    simp at hformula
  have hGammaCard : Gamma.card <= 4 := by
    rw [hGammaEmpty]
    simp
  have hequalityContext :
      FormulaCodeBound (insert equalityFormula Gamma) formulaCode :=
    hcontext.insert hequalityCode
  have hstrictContext :
      FormulaCodeBound (insert strictFormula Gamma) formulaCode :=
    hcontext.insert hstrictCode
  have hequalityCard : (insert equalityFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le equalityFormula Gamma
    omega
  have hstrictCard : (insert strictFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le strictFormula Gamma
    omega
  have hweakEquality := weakeningFullAssemblyCost_le_small
    (insert equalityFormula Gamma) formulaCode hequalityCard hequalityContext
  have hweakStrict := weakeningFullAssemblyCost_le_small
    (insert strictFormula Gamma) formulaCode hstrictCard hstrictContext
  have hdisjunction := disjunctionFullAssemblyCost_le_small Gamma
    equalityFormula strictFormula formulaCode hGammaCard hcontext
    hequalityCode hstrictCode htargetCode
  change
    compilePositiveRelationPayloadPolynomial dropOneRowsZeroValuationCount
          Language.Eq.eq args +
        compilePositiveRelationPayloadPolynomial dropOneRowsZeroValuationCount
          Language.ORing.Rel.lt args +
        weakeningFullAssemblyCost (insert equalityFormula Gamma) +
        weakeningFullAssemblyCost (insert strictFormula Gamma) +
        CertifiedPAContextProof.disjunctionFullAssemblyCost Gamma
          equalityFormula strictFormula <=
      dropOneRowsCountBoundFullyFixedPayloadPolynomial bitBound
  unfold dropOneRowsCountBoundFullyFixedPayloadPolynomial
  dsimp only [termCode, formulaCode] at *
  omega

theorem dropOneRowsCountEqualityPayloadPolynomial_le_fullyFixed
    (sourceCount targetCount bitBound : Nat)
    (hsourceCountSize : Nat.size sourceCount <= bitBound)
    (htargetCountSize : Nat.size targetCount <= bitBound) :
    compactAdditiveNatListDropFixedNumeralRowsCountEqualityPayloadPolynomial
        sourceCount 1 targetCount <=
      dropOneRowsCountEqualityFullyFixedPayloadPolynomial bitBound := by
  let leftTerm : ValuationTerm := shortBinaryNumeralTerm sourceCount
  let rightTerm : ValuationTerm :=
    ‘!!(fixedNumeralTerm 1) +
      !!(shortBinaryNumeralTerm targetCount)’
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  have hterms := dropOneCountTerms_code_length_le sourceCount targetCount
    bitBound hsourceCountSize htargetCountSize
  have hleftClosed : leftTerm.freeVariables = ∅ := by
    dsimp only [leftTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty sourceCount
  have hrightClosed : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    rw [dropOneArithmeticAdd_freeVariables_count,
      dropOneFixedOne_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  unfold
    compactAdditiveNatListDropFixedNumeralRowsCountEqualityPayloadPolynomial
    dropOneRowsCountEqualityFullyFixedPayloadPolynomial
  exact compilePositiveRelationPayloadPolynomial_le_fixed
    dropOneRowsZeroValuationCount Language.Eq.eq args 0
    (dropOneRowsCountTermCodePolynomial bitBound)
    (by
      change leftTerm.freeVariables ⊆ {0}
      rw [hleftClosed]
      simp)
    (by
      change rightTerm.freeVariables ⊆ {0}
      rw [hrightClosed]
      simp)
    (by rfl) hterms.2.1 hterms.2.2

#print axioms dropOneRowsCountBoundFormula_code_length_le_fixed
#print axioms dropOneRowsCountEqualityFormula_code_length_le_fixed
#print axioms dropOneRowsCountBoundPayloadPolynomial_le_fullyFixed
#print axioms dropOneRowsCountEqualityPayloadPolynomial_le_fullyFixed

end FoundationCompactNumericListedDirectNatListDropOneRowsCountLeavesFullyFixedBounds
