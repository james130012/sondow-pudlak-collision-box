import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsUniversalFullyFixedBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds

/-!
# Fully fixed outer count leaves for drop-two syntax-task-list rows

The formulas `2 <= sourceCount` and
`sourceCount = 2 + targetCount` are closed.  Their original public payload
polynomials and formula codes are bounded only by the shared bit coordinate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsCountLeavesFullyFixedBounds

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
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds

private abbrev taskDropTwoZeroValuationCount : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation

def taskDropTwoCountTermCodePolynomial (bitBound : Nat) : Nat :=
  (binaryTermCode (fixedNumeralTerm 2)).length +
    2 * binaryNumeralTermCodeEnvelope bitBound +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

def taskDropTwoCountAtomicCodePolynomial (bitBound : Nat) : Nat :=
  orderAtomicFormulaCodeEnvelope
    (taskDropTwoCountTermCodePolynomial bitBound)

def taskDropTwoCountBoundFormulaCodePolynomial (bitBound : Nat) : Nat :=
  2 * taskDropTwoCountAtomicCodePolynomial bitBound + 8

def taskDropTwoCountEqualityFormulaCodePolynomial (bitBound : Nat) : Nat :=
  taskDropTwoCountAtomicCodePolynomial bitBound

def taskDropTwoCountBoundFullyFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  2 * compilePositiveRelationFixedPayloadPolynomial 0
      (taskDropTwoCountTermCodePolynomial bitBound) +
    3 * smallContextAssemblyEnvelope
      (taskDropTwoCountBoundFormulaCodePolynomial bitBound) + 1

def taskDropTwoCountEqualityFullyFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (taskDropTwoCountTermCodePolynomial bitBound)

private theorem taskDropTwoArithmeticAdd_freeVariables_count
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

private theorem taskDropTwoBinaryRelation_freeVariables_count
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

@[simp] private theorem taskDropTwoFixedTwo_freeVariables_eq_empty :
    (fixedNumeralTerm 2).freeVariables = ∅ := by
  unfold fixedNumeralTerm Semiterm.Operator.operator
  simp

private theorem taskDropTwoCountTerms_code_length_le
    (sourceCount targetCount bitBound : Nat)
    (hsourceCountSize : Nat.size sourceCount <= bitBound)
    (htargetCountSize : Nat.size targetCount <= bitBound) :
    (binaryTermCode (fixedNumeralTerm 2)).length <=
        taskDropTwoCountTermCodePolynomial bitBound ∧
      (binaryTermCode (shortBinaryNumeralTerm sourceCount)).length <=
        taskDropTwoCountTermCodePolynomial bitBound ∧
      (binaryTermCode
        (‘!!(fixedNumeralTerm 2) +
          !!(shortBinaryNumeralTerm targetCount)’ : ValuationTerm)).length <=
        taskDropTwoCountTermCodePolynomial bitBound := by
  have hsource := binaryNumeralTerm_code_length_le_envelope sourceCount
    bitBound hsourceCountSize
  have htarget := binaryNumeralTerm_code_length_le_envelope targetCount
    bitBound htargetCountSize
  have hadd := arithmeticAddTerm_code_length_le
    (fixedNumeralTerm 2) (shortBinaryNumeralTerm targetCount)
  unfold taskDropTwoCountTermCodePolynomial
  omega

theorem taskDropTwoCountBoundFormula_code_length_le_fixed
    (sourceCount bitBound : Nat)
    (hsourceCountSize : Nat.size sourceCount <= bitBound) :
    (binaryFormulaCode
      (“!!(fixedNumeralTerm 2) ≤
        !!(shortBinaryNumeralTerm sourceCount)” :
        ValuationFormula)).length <=
      taskDropTwoCountBoundFormulaCodePolynomial bitBound := by
  let leftTerm : ValuationTerm := fixedNumeralTerm 2
  let rightTerm : ValuationTerm := shortBinaryNumeralTerm sourceCount
  let equalityFormula :=
    LO.FirstOrder.Semiformula.rel Language.Eq.eq ![leftTerm, rightTerm]
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.LT.lt ![leftTerm, rightTerm]
  let termCode := taskDropTwoCountTermCodePolynomial bitBound
  let atomicCode := taskDropTwoCountAtomicCodePolynomial bitBound
  have hterms := taskDropTwoCountTerms_code_length_le sourceCount 0 bitBound
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
      atomicCode, termCode, taskDropTwoCountAtomicCodePolynomial]
      using hraw
  have hstrict :
      (binaryFormulaCode strictFormula).length <= atomicCode := by
    dsimp only [strictFormula, atomicCode]
    have hraw := binaryRelationFormula_code_le_orderAtomic Language.LT.lt
      leftTerm rightTerm termCode hleft hright
    simpa only [
      FoundationCompactPAQuantitativeRelationCongruence.binaryRelationFormula,
      atomicCode, termCode, taskDropTwoCountAtomicCodePolynomial]
      using hraw
  have hor := binaryFormulaCode_or_length_le_local equalityFormula
    strictFormula
  have htag : (binaryNatCode 5).length <= 8 := by decide
  change
    (binaryFormulaCode (equalityFormula ⋎ strictFormula)).length <= _
  unfold taskDropTwoCountBoundFormulaCodePolynomial
  omega

theorem taskDropTwoCountEqualityFormula_code_length_le_fixed
    (sourceCount targetCount bitBound : Nat)
    (hsourceCountSize : Nat.size sourceCount <= bitBound)
    (htargetCountSize : Nat.size targetCount <= bitBound) :
    (binaryFormulaCode
      (“!!(shortBinaryNumeralTerm sourceCount) =
        !!(fixedNumeralTerm 2) +
          !!(shortBinaryNumeralTerm targetCount)” :
        ValuationFormula)).length <=
      taskDropTwoCountEqualityFormulaCodePolynomial bitBound := by
  let rightTerm : ValuationTerm :=
    ‘!!(fixedNumeralTerm 2) +
      !!(shortBinaryNumeralTerm targetCount)’
  have hterms := taskDropTwoCountTerms_code_length_le sourceCount targetCount
    bitBound hsourceCountSize htargetCountSize
  unfold taskDropTwoCountEqualityFormulaCodePolynomial
    taskDropTwoCountAtomicCodePolynomial
  exact binaryRelationFormula_code_le_orderAtomic Language.Eq.eq
    (shortBinaryNumeralTerm sourceCount) rightTerm
    (taskDropTwoCountTermCodePolynomial bitBound) hterms.2.1 hterms.2.2

@[simp] theorem taskDropTwoCountBoundFormula_freeVariables_eq_empty
    (sourceCount : Nat) :
    (“!!(fixedNumeralTerm 2) ≤
      !!(shortBinaryNumeralTerm sourceCount)” :
      ValuationFormula).freeVariables = ∅ := by
  let leftTerm : ValuationTerm := fixedNumeralTerm 2
  let rightTerm : ValuationTerm := shortBinaryNumeralTerm sourceCount
  let equalityFormula :=
    LO.FirstOrder.Semiformula.rel Language.Eq.eq ![leftTerm, rightTerm]
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.LT.lt ![leftTerm, rightTerm]
  have hleft : leftTerm.freeVariables = ∅ := by
    simp only [leftTerm, taskDropTwoFixedTwo_freeVariables_eq_empty]
  have hright : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty sourceCount
  change (equalityFormula ⋎ strictFormula).freeVariables = ∅
  rw [LO.FirstOrder.Semiformula.freeVariables_or]
  dsimp only [equalityFormula, strictFormula]
  rw [taskDropTwoBinaryRelation_freeVariables_count,
    taskDropTwoBinaryRelation_freeVariables_count, hleft, hright]
  simp

@[simp] theorem taskDropTwoCountEqualityFormula_freeVariables_eq_empty
    (sourceCount targetCount : Nat) :
    (“!!(shortBinaryNumeralTerm sourceCount) =
      !!(fixedNumeralTerm 2) +
        !!(shortBinaryNumeralTerm targetCount)” :
      ValuationFormula).freeVariables = ∅ := by
  let leftTerm : ValuationTerm := shortBinaryNumeralTerm sourceCount
  let rightTerm : ValuationTerm :=
    ‘!!(fixedNumeralTerm 2) +
      !!(shortBinaryNumeralTerm targetCount)’
  have hleft : leftTerm.freeVariables = ∅ := by
    dsimp only [leftTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty sourceCount
  have hright : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    rw [taskDropTwoArithmeticAdd_freeVariables_count,
      taskDropTwoFixedTwo_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  change
    (LO.FirstOrder.Semiformula.rel Language.Eq.eq
      ![leftTerm, rightTerm]).freeVariables = ∅
  rw [taskDropTwoBinaryRelation_freeVariables_count, hleft, hright]
  simp

theorem taskDropTwoCountBoundPayloadPolynomial_le_fullyFixed
    (sourceCount bitBound : Nat)
    (hsourceCountSize : Nat.size sourceCount <= bitBound) :
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsCountBoundPayloadPolynomial
        2 sourceCount <=
      taskDropTwoCountBoundFullyFixedPayloadPolynomial bitBound := by
  let leftTerm : ValuationTerm := fixedNumeralTerm 2
  let rightTerm : ValuationTerm := shortBinaryNumeralTerm sourceCount
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula :=
    LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.LT.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables
    taskDropTwoZeroValuationCount
  let termCode := taskDropTwoCountTermCodePolynomial bitBound
  let formulaCode := taskDropTwoCountBoundFormulaCodePolynomial bitBound
  have hterms := taskDropTwoCountTerms_code_length_le sourceCount 0 bitBound
    hsourceCountSize (Nat.zero_le bitBound)
  have hleftCode := hterms.1
  have hrightCode := hterms.2.1
  have hleftClosed : leftTerm.freeVariables = ∅ := by
    simp only [leftTerm, taskDropTwoFixedTwo_freeVariables_eq_empty]
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
      taskDropTwoZeroValuationCount Language.Eq.eq args 0 termCode
      hfirst hsecond (by rfl) hleftCode hrightCode
  have hstrictResource :=
    compilePositiveRelationPayloadPolynomial_le_fixed
      taskDropTwoZeroValuationCount Language.ORing.Rel.lt args 0 termCode
      hfirst hsecond (by rfl) hleftCode hrightCode
  have hequalityAtomic :
      (binaryFormulaCode equalityFormula).length <=
        taskDropTwoCountAtomicCodePolynomial bitBound := by
    have hraw := binaryRelationFormula_code_le_orderAtomic Language.Eq.eq
      leftTerm rightTerm termCode hleftCode hrightCode
    simpa only [equalityFormula, args,
      FoundationCompactPAQuantitativeRelationCongruence.binaryRelationFormula,
      taskDropTwoCountAtomicCodePolynomial, termCode] using hraw
  have hstrictAtomic :
      (binaryFormulaCode strictFormula).length <=
        taskDropTwoCountAtomicCodePolynomial bitBound := by
    have hraw := binaryRelationFormula_code_le_orderAtomic Language.LT.lt
      leftTerm rightTerm termCode hleftCode hrightCode
    simpa only [strictFormula, args,
      FoundationCompactPAQuantitativeRelationCongruence.binaryRelationFormula,
      taskDropTwoCountAtomicCodePolynomial, termCode] using hraw
  have hequalityCode :
      (binaryFormulaCode equalityFormula).length <= formulaCode := by
    unfold formulaCode taskDropTwoCountBoundFormulaCodePolynomial
    omega
  have hstrictCode :
      (binaryFormulaCode strictFormula).length <= formulaCode := by
    unfold formulaCode taskDropTwoCountBoundFormulaCodePolynomial
    omega
  have htargetCode :
      (binaryFormulaCode targetFormula).length <= formulaCode := by
    have hraw := binaryFormulaCode_or_length_le_local equalityFormula
      strictFormula
    have htag : (binaryNatCode 5).length <= 8 := by decide
    dsimp only [targetFormula]
    unfold formulaCode taskDropTwoCountBoundFormulaCodePolynomial
    omega
  have htargetClosed : targetFormula.freeVariables = ∅ := by
    dsimp only [targetFormula, equalityFormula, strictFormula, args]
    rw [LO.FirstOrder.Semiformula.freeVariables_or,
      taskDropTwoBinaryRelation_freeVariables_count,
      taskDropTwoBinaryRelation_freeVariables_count,
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
    compilePositiveRelationPayloadPolynomial taskDropTwoZeroValuationCount
          Language.Eq.eq args +
        compilePositiveRelationPayloadPolynomial taskDropTwoZeroValuationCount
          Language.ORing.Rel.lt args +
        weakeningFullAssemblyCost (insert equalityFormula Gamma) +
        weakeningFullAssemblyCost (insert strictFormula Gamma) +
        CertifiedPAContextProof.disjunctionFullAssemblyCost Gamma
          equalityFormula strictFormula <=
      taskDropTwoCountBoundFullyFixedPayloadPolynomial bitBound
  unfold taskDropTwoCountBoundFullyFixedPayloadPolynomial
  dsimp only [termCode, formulaCode] at *
  omega

theorem taskDropTwoCountEqualityPayloadPolynomial_le_fullyFixed
    (sourceCount targetCount bitBound : Nat)
    (hsourceCountSize : Nat.size sourceCount <= bitBound)
    (htargetCountSize : Nat.size targetCount <= bitBound) :
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsCountEqualityPayloadPolynomial
        sourceCount 2 targetCount <=
      taskDropTwoCountEqualityFullyFixedPayloadPolynomial bitBound := by
  let leftTerm : ValuationTerm := shortBinaryNumeralTerm sourceCount
  let rightTerm : ValuationTerm :=
    ‘!!(fixedNumeralTerm 2) +
      !!(shortBinaryNumeralTerm targetCount)’
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  have hterms := taskDropTwoCountTerms_code_length_le sourceCount targetCount
    bitBound hsourceCountSize htargetCountSize
  have hleftClosed : leftTerm.freeVariables = ∅ := by
    dsimp only [leftTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty sourceCount
  have hrightClosed : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    rw [taskDropTwoArithmeticAdd_freeVariables_count,
      taskDropTwoFixedTwo_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  unfold
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsCountEqualityPayloadPolynomial
    taskDropTwoCountEqualityFullyFixedPayloadPolynomial
  exact compilePositiveRelationPayloadPolynomial_le_fixed
    taskDropTwoZeroValuationCount Language.Eq.eq args 0
    (taskDropTwoCountTermCodePolynomial bitBound)
    (by
      change leftTerm.freeVariables ⊆ {0}
      rw [hleftClosed]
      simp)
    (by
      change rightTerm.freeVariables ⊆ {0}
      rw [hrightClosed]
      simp)
    (by rfl) hterms.2.1 hterms.2.2

#print axioms taskDropTwoCountBoundFormula_code_length_le_fixed
#print axioms taskDropTwoCountEqualityFormula_code_length_le_fixed
#print axioms taskDropTwoCountBoundPayloadPolynomial_le_fullyFixed
#print axioms taskDropTwoCountEqualityPayloadPolynomial_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsCountLeavesFullyFixedBounds
