import integration.FoundationCompactPABinaryNumeralAdditionBounds

/-!
# Proof-producing binary-numeral multiplication

This module constructs real certified PA proofs of multiplication identities
for short binary numerals.  The recursion follows the binary height of the
right input and reuses the checked addition normalizer for odd bit steps.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABinaryNumeralMultiplication

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAAxiomCertificate
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeEqualityTransitivity
open FoundationCompactPAQuantitativeFunctionCongruence
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds

/-! ## Multiplicative PA algebra -/

def mulCommutativityOuterBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰ (#1 * #0 = #0 * #1)”

theorem mulCommutativityAxiom_formula :
    (Rewriting.emb PAAxiomCertificate.mulComm.sentence :
        LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ mulCommutativityOuterBody := by
  simp [mulCommutativityOuterBody, PAAxiomCertificate.sentence]

def mulCommutativityAxiomProof :
    CertifiedPAProof (∀⁰ mulCommutativityOuterBody) :=
  cast mulCommutativityAxiom_formula (ofAxiom .mulComm)

def mulCommutativityInnerBody
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!!(Rew.bShift left) * #0 = #0 * !!(Rew.bShift left)”

theorem mulCommutativityAfterFirst_formula
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    mulCommutativityOuterBody/[left] =
      ∀⁰ mulCommutativityInnerBody left := by
  simp [mulCommutativityOuterBody, mulCommutativityInnerBody,
    substQ_bvarOne]

theorem mulCommutativityFinal_formula
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (mulCommutativityInnerBody left)/[right] =
      (“!!left * !!right = !!right * !!left” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [mulCommutativityInnerBody]

def proveMulCommutativity
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!left * !!right = !!right * !!left” :
        LO.FirstOrder.ArithmeticProposition) :=
  specializeTwiceWithCasts mulCommutativityAxiomProof left right
    (mulCommutativityAfterFirst_formula left)
    (mulCommutativityFinal_formula left right)

theorem mulCommutativityAxiomProof_payloadLength_le :
    mulCommutativityAxiomProof.payloadLength <=
      32 + 10 * axiomSyntaxBudget .mulComm := by
  calc
    mulCommutativityAxiomProof.payloadLength =
        (ofAxiom .mulComm).payloadLength := by
      change
        (cast mulCommutativityAxiom_formula
          (ofAxiom .mulComm)).payloadLength = _
      exact cast_payloadLength _ _
    _ <= _ := ofAxiom_payloadLength_le .mulComm

theorem proveMulCommutativity_payloadLength_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveMulCommutativity left right).payloadLength <=
      mulCommutativityAxiomProof.payloadLength +
        specializationCost mulCommutativityOuterBody left +
        specializationCost (mulCommutativityInnerBody left) right :=
  specializeTwiceWithCasts_payloadLength_le
    mulCommutativityAxiomProof left right
      (mulCommutativityAfterFirst_formula left)
      (mulCommutativityFinal_formula left right)

def mulAssociativityOuterBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰ ∀⁰ ((#2 * #1) * #0 = #2 * (#1 * #0))”

theorem mulAssociativityAxiom_formula :
    (Rewriting.emb PAAxiomCertificate.mulAssoc.sentence :
        LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ mulAssociativityOuterBody := by
  simp [mulAssociativityOuterBody, PAAxiomCertificate.sentence]

def mulAssociativityAxiomProof :
    CertifiedPAProof (∀⁰ mulAssociativityOuterBody) :=
  cast mulAssociativityAxiom_formula (ofAxiom .mulAssoc)

def mulAssociativityMiddleBody
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰
    ((!!(Rew.bShift (Rew.bShift left)) * #1) * #0 =
      !!(Rew.bShift (Rew.bShift left)) * (#1 * #0))”

theorem mulAssociativityAfterFirst_formula
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    mulAssociativityOuterBody/[left] =
      ∀⁰ mulAssociativityMiddleBody left := by
  simp [mulAssociativityOuterBody, mulAssociativityMiddleBody,
    substQQ_bvarOne, substQQ_bvarTwo]

def mulAssociativityInnerBody
    (left middle : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “(!!(Rew.bShift left) * !!(Rew.bShift middle)) * #0 =
    !!(Rew.bShift left) * (!!(Rew.bShift middle) * #0)”

theorem mulAssociativityAfterSecond_formula
    (left middle : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (mulAssociativityMiddleBody left)/[middle] =
      ∀⁰ mulAssociativityInnerBody left middle := by
  simp [mulAssociativityMiddleBody, mulAssociativityInnerBody,
    substQ_bvarOne]

theorem mulAssociativityFinal_formula
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (mulAssociativityInnerBody left middle)/[right] =
      (“(!!left * !!middle) * !!right =
        !!left * (!!middle * !!right)” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [mulAssociativityInnerBody]

def proveMulAssociativity
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“(!!left * !!middle) * !!right =
        !!left * (!!middle * !!right)” :
        LO.FirstOrder.ArithmeticProposition) :=
  specializeThriceWithCasts mulAssociativityAxiomProof left middle right
    (mulAssociativityAfterFirst_formula left)
    (mulAssociativityAfterSecond_formula left middle)
    (mulAssociativityFinal_formula left middle right)

theorem mulAssociativityAxiomProof_payloadLength_le :
    mulAssociativityAxiomProof.payloadLength <=
      32 + 10 * axiomSyntaxBudget .mulAssoc := by
  calc
    mulAssociativityAxiomProof.payloadLength =
        (ofAxiom .mulAssoc).payloadLength := by
      change
        (cast mulAssociativityAxiom_formula
          (ofAxiom .mulAssoc)).payloadLength = _
      exact cast_payloadLength _ _
    _ <= _ := ofAxiom_payloadLength_le .mulAssoc

theorem proveMulAssociativity_payloadLength_le
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveMulAssociativity left middle right).payloadLength <=
      mulAssociativityAxiomProof.payloadLength +
        specializationCost mulAssociativityOuterBody left +
        specializationCost (mulAssociativityMiddleBody left) middle +
        specializationCost (mulAssociativityInnerBody left middle) right :=
  specializeThriceWithCasts_payloadLength_le
    mulAssociativityAxiomProof left middle right
      (mulAssociativityAfterFirst_formula left)
      (mulAssociativityAfterSecond_formula left middle)
      (mulAssociativityFinal_formula left middle right)

def proveMulAssociativityReverse
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!left * (!!middle * !!right) =
        (!!left * !!middle) * !!right” :
        LO.FirstOrder.ArithmeticProposition) :=
  proveEqualitySymmetry
    (paMulTerm (paMulTerm left middle) right)
    (paMulTerm left (paMulTerm middle right))
    (proveMulAssociativity left middle right)

/-! ## Base products -/

def proveZeroMul
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!paZeroTerm * !!term = !!paZeroTerm” :
        LO.FirstOrder.ArithmeticProposition) :=
  proveEqualityTransitivity
    (paMulTerm paZeroTerm term)
    (paMulTerm term paZeroTerm)
    paZeroTerm
    (proveMulCommutativity paZeroTerm term)
    (proveMulZeroAtPaZero term)

def proveShortBinaryOneEqualsPaOne :
    CertifiedPAProof
      (“!!(shortBinaryNumeralTerm 1) = !!paOneTerm” :
        LO.FirstOrder.ArithmeticProposition) := by
  have hformula :
      (“!!binaryOneAlgebraTerm = !!paOneTerm” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(shortBinaryNumeralTerm 1) = !!paOneTerm” :
          LO.FirstOrder.ArithmeticProposition) := by
    rw [binaryNumeralTerm_one_formula]
  exact cast hformula proveBinaryOneAlgebraEqualsOne

def proveBinaryNumeralMultiplicationZeroLeft
    (right : Nat) :
    CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm 0)
          (shortBinaryNumeralTerm right)) =
        !!(shortBinaryNumeralTerm (0 * right))” :
        LO.FirstOrder.ArithmeticProposition) := by
  let rightTerm := shortBinaryNumeralTerm right
  let raw := proveZeroMul rightTerm
  have hformula :
      (“!!paZeroTerm * !!rightTerm = !!paZeroTerm” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(paMulTerm (shortBinaryNumeralTerm 0)
            (shortBinaryNumeralTerm right)) =
          !!(shortBinaryNumeralTerm (0 * right))” :
          LO.FirstOrder.ArithmeticProposition) := by
    simp [rightTerm, paMulTerm, paZeroTerm,
      FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero]
  exact cast hformula raw

def proveBinaryNumeralMultiplicationZeroRight
    (left : Nat) :
    CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm 0)) =
        !!(shortBinaryNumeralTerm (left * 0))” :
        LO.FirstOrder.ArithmeticProposition) := by
  let leftTerm := shortBinaryNumeralTerm left
  let raw := proveMulZeroAtPaZero leftTerm
  have hformula :
      (“!!(paMulTerm leftTerm paZeroTerm) = !!paZeroTerm” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(paMulTerm (shortBinaryNumeralTerm left)
            (shortBinaryNumeralTerm 0)) =
          !!(shortBinaryNumeralTerm (left * 0))” :
          LO.FirstOrder.ArithmeticProposition) := by
    simp [leftTerm, paZeroTerm,
      FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero]
  exact cast hformula raw

def proveBinaryNumeralMultiplicationOneRight
    (left : Nat) :
    CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm 1)) =
        !!(shortBinaryNumeralTerm (left * 1))” :
        LO.FirstOrder.ArithmeticProposition) := by
  let leftTerm := shortBinaryNumeralTerm left
  let source := paMulTerm leftTerm (shortBinaryNumeralTerm 1)
  let middle := paMulTerm leftTerm paOneTerm
  let rewriteRightRaw := proveMulCongruence
    leftTerm (shortBinaryNumeralTerm 1) leftTerm paOneTerm
    (proveEqualityReflexivityAtTerm leftTerm)
    proveShortBinaryOneEqualsPaOne
  let rewriteRight : CertifiedPAProof
      (“!!source = !!middle” : LO.FirstOrder.ArithmeticProposition) := by
    have hformula := mulEqualityAsTerm_formula
      leftTerm (shortBinaryNumeralTerm 1) leftTerm paOneTerm
    simpa [source, middle] using (cast hformula rewriteRightRaw)
  let collapseOne := proveMulOneAtPaOne leftTerm
  let through := proveEqualityTransitivity source middle leftTerm
    rewriteRight collapseOne
  have hformula :
      (“!!source = !!leftTerm” : LO.FirstOrder.ArithmeticProposition) =
        (“!!(paMulTerm (shortBinaryNumeralTerm left)
            (shortBinaryNumeralTerm 1)) =
          !!(shortBinaryNumeralTerm (left * 1))” :
          LO.FirstOrder.ArithmeticProposition) := by
    simp [source, leftTerm]
  exact cast hformula through

/-! ## Doubling a recursive product -/

def proveBinaryMultiplicationDoubleHighAlgebra
    (left high : Nat)
    (highProof : CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm high)) =
        !!(shortBinaryNumeralTerm (left * high))” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (paMulTerm arithmeticTwoTerm
            (shortBinaryNumeralTerm high))) =
        !!(paMulTerm arithmeticTwoTerm
          (shortBinaryNumeralTerm (left * high)))” :
        LO.FirstOrder.ArithmeticProposition) := by
  let leftTerm := shortBinaryNumeralTerm left
  let highTerm := shortBinaryNumeralTerm high
  let productTerm := shortBinaryNumeralTerm (left * high)
  let source := paMulTerm leftTerm (paMulTerm arithmeticTwoTerm highTerm)
  let leftTwoHigh := paMulTerm
    (paMulTerm leftTerm arithmeticTwoTerm) highTerm
  let twoLeftHigh := paMulTerm
    (paMulTerm arithmeticTwoTerm leftTerm) highTerm
  let grouped := paMulTerm arithmeticTwoTerm
    (paMulTerm leftTerm highTerm)
  let result := paMulTerm arithmeticTwoTerm productTerm
  let associationReverse : CertifiedPAProof
      (“!!source = !!leftTwoHigh” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula :
        (“!!leftTerm * (!!arithmeticTwoTerm * !!highTerm) =
          (!!leftTerm * !!arithmeticTwoTerm) * !!highTerm” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!source = !!leftTwoHigh” :
          LO.FirstOrder.ArithmeticProposition) := by
      simp [source, leftTwoHigh, paMulTerm]
    exact cast hformula
      (proveMulAssociativityReverse
        leftTerm arithmeticTwoTerm highTerm)
  let commuteRaw := proveMulCongruence
    (paMulTerm leftTerm arithmeticTwoTerm) highTerm
    (paMulTerm arithmeticTwoTerm leftTerm) highTerm
    (proveMulCommutativity leftTerm arithmeticTwoTerm)
    (proveEqualityReflexivityAtTerm highTerm)
  let commute : CertifiedPAProof
      (“!!leftTwoHigh = !!twoLeftHigh” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := mulEqualityAsTerm_formula
      (paMulTerm leftTerm arithmeticTwoTerm) highTerm
      (paMulTerm arithmeticTwoTerm leftTerm) highTerm
    simpa [leftTwoHigh, twoLeftHigh] using (cast hformula commuteRaw)
  let association : CertifiedPAProof
      (“!!twoLeftHigh = !!grouped” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula :
        (“(!!arithmeticTwoTerm * !!leftTerm) * !!highTerm =
          !!arithmeticTwoTerm * (!!leftTerm * !!highTerm)” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!twoLeftHigh = !!grouped” :
          LO.FirstOrder.ArithmeticProposition) := by
      simp [twoLeftHigh, grouped, paMulTerm]
    exact cast hformula
      (proveMulAssociativity arithmeticTwoTerm leftTerm highTerm)
  let recurseRaw := proveMulCongruence
    arithmeticTwoTerm (paMulTerm leftTerm highTerm)
    arithmeticTwoTerm productTerm
    (proveEqualityReflexivityAtTerm arithmeticTwoTerm) highProof
  let recurse : CertifiedPAProof
      (“!!grouped = !!result” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := mulEqualityAsTerm_formula
      arithmeticTwoTerm (paMulTerm leftTerm highTerm)
      arithmeticTwoTerm productTerm
    simpa [grouped, result] using (cast hformula recurseRaw)
  let first := proveEqualityTransitivity source leftTwoHigh twoLeftHigh
    associationReverse commute
  let second := proveEqualityTransitivity source twoLeftHigh grouped
    first association
  let third := proveEqualityTransitivity source grouped result
    second recurse
  simpa [source, result, leftTerm, highTerm, productTerm] using third

/-! ## Binary multiplication bit steps -/

theorem nat_mul_bit_false (left high : Nat) :
    left * Nat.bit false high = Nat.bit false (left * high) := by
  simp [Nat.bit_val, Nat.mul_assoc, Nat.mul_comm]

theorem nat_mul_bit_true (left high : Nat) :
    left * Nat.bit true high =
      Nat.bit false (left * high) + left := by
  simp [Nat.bit_val, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm]

def proveBinaryNumeralMultiplicationEven
    (left high : Nat) (hleft : left ≠ 0) (hhigh : high ≠ 0)
    (highProof : CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm high)) =
        !!(shortBinaryNumeralTerm (left * high))” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm (Nat.bit false high))) =
        !!(shortBinaryNumeralTerm
          (left * Nat.bit false high))” :
        LO.FirstOrder.ArithmeticProposition) := by
  have hproduct : left * high ≠ 0 := Nat.mul_ne_zero hleft hhigh
  let algebra :=
    proveBinaryMultiplicationDoubleHighAlgebra left high highProof
  have hformula :
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (paMulTerm arithmeticTwoTerm
            (shortBinaryNumeralTerm high))) =
        !!(paMulTerm arithmeticTwoTerm
          (shortBinaryNumeralTerm (left * high)))” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(paMulTerm (shortBinaryNumeralTerm left)
            (shortBinaryNumeralTerm (Nat.bit false high))) =
          !!(shortBinaryNumeralTerm
            (left * Nat.bit false high))” :
          LO.FirstOrder.ArithmeticProposition) := by
    rw [shortBinaryNumeralTerm_bit_false high hhigh,
      nat_mul_bit_false,
      shortBinaryNumeralTerm_bit_false (left * high) hproduct]
  exact cast hformula algebra

def proveBinaryMultiplicationOddAlgebra
    (left high : Nat)
    (highProof : CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm high)) =
        !!(shortBinaryNumeralTerm (left * high))” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (paAddTerm
            (paMulTerm arithmeticTwoTerm
              (shortBinaryNumeralTerm high)) paOneTerm)) =
        !!(paAddTerm
          (paMulTerm arithmeticTwoTerm
            (shortBinaryNumeralTerm (left * high)))
          (shortBinaryNumeralTerm left))” :
        LO.FirstOrder.ArithmeticProposition) := by
  let leftTerm := shortBinaryNumeralTerm left
  let highTerm := shortBinaryNumeralTerm high
  let productTerm := shortBinaryNumeralTerm (left * high)
  let doubleHigh := paMulTerm arithmeticTwoTerm highTerm
  let source := paMulTerm leftTerm (paAddTerm doubleHigh paOneTerm)
  let distributed := paAddTerm
    (paMulTerm leftTerm doubleHigh) (paMulTerm leftTerm paOneTerm)
  let doubledProduct := paMulTerm arithmeticTwoTerm productTerm
  let result := paAddTerm doubledProduct leftTerm
  let distributionRaw :=
    proveLeftDistributivity leftTerm doubleHigh paOneTerm
  let distribution : CertifiedPAProof
      (“!!source = !!distributed” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula :
        (“!!leftTerm * (!!doubleHigh + !!paOneTerm) =
          !!leftTerm * !!doubleHigh + !!leftTerm * !!paOneTerm” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!source = !!distributed” :
          LO.FirstOrder.ArithmeticProposition) := by
      simp [source, distributed, paAddTerm, paMulTerm]
    exact cast hformula distributionRaw
  let doubled :=
    proveBinaryMultiplicationDoubleHighAlgebra left high highProof
  let collapseOne := proveMulOneAtPaOne leftTerm
  let normalizeRaw := proveAddCongruence
    (paMulTerm leftTerm doubleHigh) (paMulTerm leftTerm paOneTerm)
    doubledProduct leftTerm doubled collapseOne
  let normalize : CertifiedPAProof
      (“!!distributed = !!result” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      (paMulTerm leftTerm doubleHigh) (paMulTerm leftTerm paOneTerm)
      doubledProduct leftTerm
    simpa [distributed, result] using (cast hformula normalizeRaw)
  let through := proveEqualityTransitivity source distributed result
    distribution normalize
  simpa [source, result, leftTerm, highTerm, productTerm, doubleHigh,
    doubledProduct] using through

def proveBinaryNumeralMultiplicationOdd
    (left high : Nat) (hleft : left ≠ 0) (hhigh : high ≠ 0)
    (highProof : CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm high)) =
        !!(shortBinaryNumeralTerm (left * high))” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm (Nat.bit true high))) =
        !!(shortBinaryNumeralTerm
          (left * Nat.bit true high))” :
        LO.FirstOrder.ArithmeticProposition) := by
  have hproduct : left * high ≠ 0 := Nat.mul_ne_zero hleft hhigh
  let doubledProductValue := Nat.bit false (left * high)
  let algebra := proveBinaryMultiplicationOddAlgebra left high highProof
  let additionRaw := proveBinaryNumeralAddition doubledProductValue left
  let addition : CertifiedPAProof
      (“!!(paAddTerm
          (paMulTerm arithmeticTwoTerm
            (shortBinaryNumeralTerm (left * high)))
          (shortBinaryNumeralTerm left)) =
        !!(shortBinaryNumeralTerm (doubledProductValue + left))” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula :
        (“!!(paAddTerm (shortBinaryNumeralTerm doubledProductValue)
            (shortBinaryNumeralTerm left)) =
          !!(shortBinaryNumeralTerm (doubledProductValue + left))” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(paAddTerm
            (paMulTerm arithmeticTwoTerm
              (shortBinaryNumeralTerm (left * high)))
            (shortBinaryNumeralTerm left)) =
          !!(shortBinaryNumeralTerm (doubledProductValue + left))” :
          LO.FirstOrder.ArithmeticProposition) := by
      simp only [doubledProductValue]
      rw [shortBinaryNumeralTerm_bit_false (left * high) hproduct]
    exact cast hformula additionRaw
  let middle := paAddTerm
    (paMulTerm arithmeticTwoTerm
      (shortBinaryNumeralTerm (left * high)))
    (shortBinaryNumeralTerm left)
  let through := proveEqualityTransitivity
    (paMulTerm (shortBinaryNumeralTerm left)
      (paAddTerm
        (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm high))
        paOneTerm))
    middle
    (shortBinaryNumeralTerm (doubledProductValue + left))
    algebra addition
  have hformula :
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (paAddTerm
            (paMulTerm arithmeticTwoTerm
              (shortBinaryNumeralTerm high)) paOneTerm)) =
        !!(shortBinaryNumeralTerm (doubledProductValue + left))” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(paMulTerm (shortBinaryNumeralTerm left)
            (shortBinaryNumeralTerm (Nat.bit true high))) =
          !!(shortBinaryNumeralTerm
            (left * Nat.bit true high))” :
          LO.FirstOrder.ArithmeticProposition) := by
    rw [shortBinaryNumeralTerm_bit_true high, nat_mul_bit_true]
  exact cast hformula through

def proveBinaryNumeralMultiplicationBitStep
    (left : Nat) (rightBit : Bool) (rightHigh : Nat)
    (hrightCanonical : rightHigh = 0 → rightBit = true)
    (highProof : CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(shortBinaryNumeralTerm (left * rightHigh))” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm (Nat.bit rightBit rightHigh))) =
        !!(shortBinaryNumeralTerm
          (left * Nat.bit rightBit rightHigh))” :
        LO.FirstOrder.ArithmeticProposition) := by
  by_cases hleft : left = 0
  · subst left
    exact proveBinaryNumeralMultiplicationZeroLeft
      (Nat.bit rightBit rightHigh)
  · cases rightBit with
    | false =>
        have hhigh : rightHigh ≠ 0 := by
          intro hz
          have himpossible := hrightCanonical hz
          simp at himpossible
        exact proveBinaryNumeralMultiplicationEven
          left rightHigh hleft hhigh highProof
    | true =>
        by_cases hhigh : rightHigh = 0
        · subst rightHigh
          simpa [Nat.bit_val] using
            proveBinaryNumeralMultiplicationOneRight left
        · exact proveBinaryNumeralMultiplicationOdd
            left rightHigh hleft hhigh highProof

theorem proveBinaryNumeralMultiplicationBitStep_left_zero
    (rightBit : Bool) (rightHigh : Nat)
    (hrightCanonical : rightHigh = 0 → rightBit = true)
    (highProof : CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm 0)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(shortBinaryNumeralTerm (0 * rightHigh))” :
        LO.FirstOrder.ArithmeticProposition)) :
    proveBinaryNumeralMultiplicationBitStep
        0 rightBit rightHigh hrightCanonical highProof =
      proveBinaryNumeralMultiplicationZeroLeft
        (Nat.bit rightBit rightHigh) := by
  simp [proveBinaryNumeralMultiplicationBitStep]

theorem proveBinaryNumeralMultiplicationBitStep_false
    (left rightHigh : Nat) (hleft : left ≠ 0)
    (hrightCanonical : rightHigh = 0 → false = true)
    (highProof : CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(shortBinaryNumeralTerm (left * rightHigh))” :
        LO.FirstOrder.ArithmeticProposition)) :
    proveBinaryNumeralMultiplicationBitStep
        left false rightHigh hrightCanonical highProof =
      proveBinaryNumeralMultiplicationEven left rightHigh hleft
        (fun hz => Bool.false_eq_true.mp (hrightCanonical hz)) highProof := by
  simp [proveBinaryNumeralMultiplicationBitStep, hleft]

theorem proveBinaryNumeralMultiplicationBitStep_true_zero
    (left : Nat) (hleft : left ≠ 0)
    (hrightCanonical : (0 : Nat) = 0 → true = true)
    (highProof : CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm 0)) =
        !!(shortBinaryNumeralTerm (left * 0))” :
        LO.FirstOrder.ArithmeticProposition)) :
    proveBinaryNumeralMultiplicationBitStep
        left true 0 hrightCanonical highProof =
      proveBinaryNumeralMultiplicationOneRight left := by
  simp [proveBinaryNumeralMultiplicationBitStep, hleft]

theorem proveBinaryNumeralMultiplicationBitStep_true_nonzero
    (left rightHigh : Nat) (hleft : left ≠ 0)
    (hhigh : rightHigh ≠ 0)
    (hrightCanonical : rightHigh = 0 → true = true)
    (highProof : CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(shortBinaryNumeralTerm (left * rightHigh))” :
        LO.FirstOrder.ArithmeticProposition)) :
    proveBinaryNumeralMultiplicationBitStep
        left true rightHigh hrightCanonical highProof =
      proveBinaryNumeralMultiplicationOdd
        left rightHigh hleft hhigh highProof := by
  simp [proveBinaryNumeralMultiplicationBitStep, hleft, hhigh]

/-! ## Complete recursive normalizer -/

noncomputable def proveBinaryNumeralMultiplication
    (left : Nat) : (right : Nat) →
    CertifiedPAProof
      (“!!(paMulTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm right)) =
        !!(shortBinaryNumeralTerm (left * right))” :
        LO.FirstOrder.ArithmeticProposition) :=
  Nat.binaryRec'
    (motive := fun right =>
      CertifiedPAProof
        (“!!(paMulTerm (shortBinaryNumeralTerm left)
            (shortBinaryNumeralTerm right)) =
          !!(shortBinaryNumeralTerm (left * right))” :
          LO.FirstOrder.ArithmeticProposition))
    (proveBinaryNumeralMultiplicationZeroRight left)
    (fun rightBit rightHigh hrightCanonical highProof =>
      proveBinaryNumeralMultiplicationBitStep
        left rightBit rightHigh hrightCanonical highProof)

@[simp] theorem proveBinaryNumeralMultiplication_zero
    (left : Nat) :
    proveBinaryNumeralMultiplication left 0 =
      proveBinaryNumeralMultiplicationZeroRight left := by
  simp [proveBinaryNumeralMultiplication]

theorem proveBinaryNumeralMultiplication_bit
    (left : Nat) (rightBit : Bool) (rightHigh : Nat)
    (hrightCanonical : rightHigh = 0 → rightBit = true) :
    proveBinaryNumeralMultiplication left
        (Nat.bit rightBit rightHigh) =
      proveBinaryNumeralMultiplicationBitStep
        left rightBit rightHigh hrightCanonical
        (proveBinaryNumeralMultiplication left rightHigh) := by
  unfold proveBinaryNumeralMultiplication
  rw [Nat.binaryRec'_eq
    (motive := fun right =>
      CertifiedPAProof
        (“!!(paMulTerm (shortBinaryNumeralTerm left)
            (shortBinaryNumeralTerm right)) =
          !!(shortBinaryNumeralTerm (left * right))” :
          LO.FirstOrder.ArithmeticProposition))
    rightBit rightHigh hrightCanonical]

theorem proveBinaryNumeralMultiplication_verifier_eq_true
    (left right : Nat) :
    listedCompactCertifiedPAProofVerifier
      (proveBinaryNumeralMultiplication left right).code
      (compactFormulaCode
        (“!!(paMulTerm (shortBinaryNumeralTerm left)
            (shortBinaryNumeralTerm right)) =
          !!(shortBinaryNumeralTerm (left * right))” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  (proveBinaryNumeralMultiplication left right).verifier_eq_true

#print axioms proveMulCommutativity
#print axioms proveMulAssociativity
#print axioms proveBinaryNumeralMultiplicationZeroLeft
#print axioms proveBinaryNumeralMultiplicationOneRight
#print axioms proveBinaryMultiplicationDoubleHighAlgebra
#print axioms proveBinaryNumeralMultiplicationEven
#print axioms proveBinaryNumeralMultiplicationOdd
#print axioms proveBinaryNumeralMultiplication_verifier_eq_true

end FoundationCompactPABinaryNumeralMultiplication
