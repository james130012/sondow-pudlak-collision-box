import integration.FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
import integration.FoundationCompactPAValuationTermCompilerFixedPolynomialBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds

/-! # Fixed code and proof bounds for the exact parser fuel term -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 350000

namespace FoundationCompactNumericListedDirectParserSyntaxExactFuelFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerBounds
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationTermCompilerUniformBounds
open FoundationCompactPAValuationTermCompilerFixedPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality

private theorem exactFuelBinaryFunctionTerm_code_length_le
    {arity : Nat}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermCode
      (LO.FirstOrder.Semiterm.func functionSymbol ![left, right])).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        binaryFunctionTermCodeOverhead functionSymbol := by
  simp [binaryTermCode, binaryFunctionTermCodeOverhead,
    Matrix.fun_eq_vec_two]
  omega

private theorem exactFuelArithmeticAddTerm_code_length_le
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermCode
      (‘!!left + !!right’ :
        LO.FirstOrder.ArithmeticSemiterm Nat arity)).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        binaryFunctionTermCodeOverhead Language.Add.add := by
  rw [show (‘!!left + !!right’ :
      LO.FirstOrder.ArithmeticSemiterm Nat arity) =
      LO.FirstOrder.Semiterm.func Language.Add.add ![left, right] by
    simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
      Rew.func, Matrix.fun_eq_vec_two]]
  exact exactFuelBinaryFunctionTerm_code_length_le Language.Add.add left right

private theorem exactFuelArithmeticMulTerm_code_length_le
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermCode
      (‘!!left * !!right’ :
        LO.FirstOrder.ArithmeticSemiterm Nat arity)).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        binaryFunctionTermCodeOverhead Language.Mul.mul := by
  rw [show (‘!!left * !!right’ :
      LO.FirstOrder.ArithmeticSemiterm Nat arity) =
      LO.FirstOrder.Semiterm.func Language.Mul.mul ![left, right] by
    simp [Semiterm.Operator.operator, Semiterm.Operator.Mul.term_eq,
      Rew.func, Matrix.fun_eq_vec_two]]
  exact exactFuelBinaryFunctionTerm_code_length_le Language.Mul.mul left right

def compactParserSyntaxExactFuelTermFixedCodePolynomial
    (numericBound : Nat) : Nat :=
  2 * boundedWitnessNumeralTermCodeEnvelope numericBound +
    (binaryTermCode
      (compactParserSyntaxExactNativeNumeralTerm 16)).length +
    (binaryTermCode
      (compactParserSyntaxExactNativeNumeralTerm 8)).length +
    2 * (binaryTermCode (‘1’ : ValuationTerm)).length +
    3 * binaryFunctionTermCodeOverhead Language.Add.add +
    2 * binaryFunctionTermCodeOverhead Language.Mul.mul + 1

theorem compactParserSyntaxExactFuelTerm_code_length_le_fixed
    (inputCount numericBound : Nat)
    (hinputCount : inputCount <= numericBound) :
    (binaryTermCode (compactParserSyntaxExactFuelTerm inputCount)).length <=
      compactParserSyntaxExactFuelTermFixedCodePolynomial numericBound := by
  have hcount := shortBinaryNumeralTerm_code_length_le_bound inputCount
    numericBound hinputCount
  let countTerm : ValuationTerm := shortBinaryNumeralTerm inputCount
  let successorTerm : ValuationTerm := ‘!!countTerm + 1’
  let firstProduct : ValuationTerm :=
    ‘!!(compactParserSyntaxExactNativeNumeralTerm 16) * !!successorTerm’
  let product : ValuationTerm := ‘!!firstProduct * !!successorTerm’
  have hsuccessor := exactFuelArithmeticAddTerm_code_length_le countTerm
    (‘1’ : ValuationTerm)
  have hfirst := exactFuelArithmeticMulTerm_code_length_le
    (compactParserSyntaxExactNativeNumeralTerm 16) successorTerm
  have hproduct := exactFuelArithmeticMulTerm_code_length_le firstProduct
    successorTerm
  have htotal := exactFuelArithmeticAddTerm_code_length_le product
    (compactParserSyntaxExactNativeNumeralTerm 8)
  change (binaryTermCode
    (‘!!product +
      !!(compactParserSyntaxExactNativeNumeralTerm 8)’ :
      ValuationTerm)).length <= _
  exact htotal.trans (by
    dsimp only [product, firstProduct, successorTerm, countTerm] at hsuccessor hfirst hproduct htotal
    dsimp only [product, firstProduct, successorTerm, countTerm]
    unfold compactParserSyntaxExactFuelTermFixedCodePolynomial
    omega)

def compactParserSyntaxExactStateCountTerm
    (inputCount : Nat) : ValuationTerm :=
  ‘!!(compactParserSyntaxExactFuelTerm inputCount) + 1’

def compactParserSyntaxExactStateCountTermFixedCodePolynomial
    (numericBound : Nat) : Nat :=
  compactParserSyntaxExactFuelTermFixedCodePolynomial numericBound +
    (binaryTermCode (‘1’ : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

theorem compactParserSyntaxExactStateCountTerm_code_length_le_fixed
    (inputCount numericBound : Nat)
    (hinputCount : inputCount <= numericBound) :
    (binaryTermCode
      (compactParserSyntaxExactStateCountTerm inputCount)).length <=
      compactParserSyntaxExactStateCountTermFixedCodePolynomial
        numericBound := by
  have hfuel := compactParserSyntaxExactFuelTerm_code_length_le_fixed
    inputCount numericBound hinputCount
  have hadd := exactFuelArithmeticAddTerm_code_length_le
    (compactParserSyntaxExactFuelTerm inputCount) (‘1’ : ValuationTerm)
  unfold compactParserSyntaxExactStateCountTerm
    compactParserSyntaxExactStateCountTermFixedCodePolynomial
  omega

def compactParserSyntaxExactStateCountEqualityFixedPayloadPolynomial
    (numericBound : Nat) : Nat :=
  compileTermValueEqualityFixedPayloadPolynomial numericBound
    (compactParserSyntaxExactStateCountTermFixedCodePolynomial numericBound)

theorem compactParserSyntaxExactStateCountEqualityPayloadResource_le_fixed
    (inputCount numericBound : Nat)
    (hinputCount : inputCount <= numericBound) :
    compileTermValueEqualityPayloadResource (fun _ => 0)
        (compactParserSyntaxExactStateCountTerm inputCount) <=
      compactParserSyntaxExactStateCountEqualityFixedPayloadPolynomial
        numericBound := by
  let term := compactParserSyntaxExactStateCountTerm inputCount
  have hclosed : term.freeVariables = ∅ := by
    dsimp only [term, compactParserSyntaxExactStateCountTerm]
    rw [arithmeticAddTerm_freeVariables_eq_union,
      compactParserSyntaxExactFuelTerm_freeVariables_eq_empty]
    simp [
      Semiterm.Operator.operator, Semiterm.Operator.numeral_one,
      Semiterm.Operator.One.term_eq]
  have hcard : term.freeVariables.card <= 4 := by
    rw [hclosed]
    simp
  have hcode : (binaryTermCode term).length <=
      compactParserSyntaxExactStateCountTermFixedCodePolynomial
        numericBound := by
    exact compactParserSyntaxExactStateCountTerm_code_length_le_fixed
      inputCount numericBound hinputCount
  have hpublic :=
    compileTermValueEqualityPayloadResource_le_publicPolynomial_of_card
      (fun _ => 0) term hcard
  have hcoordinate := compileTermValueEqualityPayloadPolynomial_le_coordinate
    (fun _ => 0) numericBound term hcard (by simp [hclosed])
  have hfixed := compileTermValueEqualityUniformPayloadPolynomial_le_fixed
    numericBound (compactParserSyntaxExactStateCountTermFixedCodePolynomial
      numericBound) term hcard hcode
  exact hpublic.trans (hcoordinate.trans hfixed)

def compactParserSyntaxExactFuelEqualityFixedPayloadPolynomial
    (numericBound : Nat) : Nat :=
  compileTermValueEqualityFixedPayloadPolynomial numericBound
    (compactParserSyntaxExactFuelTermFixedCodePolynomial numericBound)

theorem compactParserSyntaxExactFuelEqualityPayloadResource_le_fixed
    (inputCount numericBound : Nat)
    (hinputCount : inputCount <= numericBound) :
    compactParserSyntaxExactFuelEqualityPayloadResource inputCount <=
      compactParserSyntaxExactFuelEqualityFixedPayloadPolynomial
        numericBound := by
  let term := compactParserSyntaxExactFuelTerm inputCount
  have hcard : term.freeVariables.card <= 4 := by
    rw [show term.freeVariables = ∅ by
      exact compactParserSyntaxExactFuelTerm_freeVariables_eq_empty inputCount]
    simp
  have hcode : (binaryTermCode term).length <=
      compactParserSyntaxExactFuelTermFixedCodePolynomial numericBound := by
    exact compactParserSyntaxExactFuelTerm_code_length_le_fixed inputCount
      numericBound hinputCount
  have hpublic :=
    compileTermValueEqualityPayloadResource_le_publicPolynomial_of_card
      (fun _ => 0) term hcard
  have hcoordinate := compileTermValueEqualityPayloadPolynomial_le_coordinate
    (fun _ => 0) numericBound term hcard (by simp)
  have hfixed := compileTermValueEqualityUniformPayloadPolynomial_le_fixed
    numericBound (compactParserSyntaxExactFuelTermFixedCodePolynomial
      numericBound) term hcard hcode
  exact hpublic.trans (hcoordinate.trans hfixed)

#print axioms compactParserSyntaxExactFuelTerm_code_length_le_fixed
#print axioms compactParserSyntaxExactFuelEqualityPayloadResource_le_fixed
#print axioms compactParserSyntaxExactStateCountTerm_code_length_le_fixed
#print axioms
  compactParserSyntaxExactStateCountEqualityPayloadResource_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxExactFuelFixedBounds
