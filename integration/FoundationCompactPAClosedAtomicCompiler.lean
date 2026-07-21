import integration.FoundationCompactPABinaryNumeralMultiplicationBounds
import integration.FoundationCompactPAQuantitativeOrder
import integration.FoundationCompactCertifiedDisjunction
import integration.FoundationCompactPANegativeEquality
import integration.FoundationCompactPANegativeOrder
import integration.FoundationCompactCertifiedModusTollens

/-!
# Proof-producing compiler for closed arithmetic atoms

The first layer normalizes arbitrary closed `0/1/+/*` expressions to the
short binary numeral of their computed value.  Positive equality atoms are
then compiled by joining two normalization proofs at the same numeral.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAClosedAtomicCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeEqualityTransitivity
open FoundationCompactPAQuantitativeFunctionCongruence
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralMultiplication
open FoundationCompactPAQuantitativeOrder
open FoundationCompactCertifiedDisjunction
open FoundationCompactPANegativeEquality
open FoundationCompactPANegativeOrder
open FoundationCompactCertifiedModusTollens

/-! ## Closed arithmetic expression language -/

inductive ClosedPATerm where
  | numeral (value : Nat)
  | add (left right : ClosedPATerm)
  | mul (left right : ClosedPATerm)
deriving Repr, DecidableEq

namespace ClosedPATerm

def value : ClosedPATerm → Nat
  | .numeral n => n
  | .add left right => left.value + right.value
  | .mul left right => left.value * right.value

def term : ClosedPATerm → LO.FirstOrder.ArithmeticSemiterm Nat 0
  | .numeral n => shortBinaryNumeralTerm n
  | .add left right => paAddTerm left.term right.term
  | .mul left right => paMulTerm left.term right.term

def nodeCount : ClosedPATerm → Nat
  | .numeral _ => 1
  | .add left right => left.nodeCount + right.nodeCount + 1
  | .mul left right => left.nodeCount + right.nodeCount + 1

def leafBitWeight : ClosedPATerm → Nat
  | .numeral n => Nat.size n + 1
  | .add left right => left.leafBitWeight + right.leafBitWeight
  | .mul left right => left.leafBitWeight + right.leafBitWeight

theorem nodeCount_pos (expression : ClosedPATerm) :
    0 < expression.nodeCount := by
  induction expression with
  | numeral => simp [nodeCount]
  | add left right ihLeft ihRight =>
      simp [nodeCount]
  | mul left right ihLeft ihRight =>
      simp [nodeCount]

theorem value_size_le_leafBitWeight (expression : ClosedPATerm) :
    Nat.size expression.value + 1 <= expression.leafBitWeight := by
  induction expression with
  | numeral value =>
      simp [ClosedPATerm.value, leafBitWeight]
  | add left right ihLeft ihRight =>
      have hsum :=
        FoundationCompactPABinaryNumeralAdditionBounds.natSize_add_le
          left.value right.value
      simp only [ClosedPATerm.value, leafBitWeight]
      omega
  | mul left right ihLeft ihRight =>
      have hproduct :=
        FoundationCompactPABinaryNumeralMultiplicationBounds.natSize_mul_le
          left.value right.value
      simp only [ClosedPATerm.value, leafBitWeight]
      omega

/-! ## Proof-producing normalization -/

noncomputable def proveNormalization :
    (expression : ClosedPATerm) →
    CertifiedPAProof
      (“!!expression.term =
        !!(shortBinaryNumeralTerm expression.value)” :
        LO.FirstOrder.ArithmeticProposition)
  | .numeral value =>
      proveEqualityReflexivityAtTerm (shortBinaryNumeralTerm value)
  | .add left right => by
      let leftProof := proveNormalization left
      let rightProof := proveNormalization right
      let normalizedLeft := shortBinaryNumeralTerm left.value
      let normalizedRight := shortBinaryNumeralTerm right.value
      let source := paAddTerm left.term right.term
      let middle := paAddTerm normalizedLeft normalizedRight
      let congruenceRaw := proveAddCongruence
        left.term right.term normalizedLeft normalizedRight
        leftProof rightProof
      let congruence : CertifiedPAProof
          (“!!source = !!middle” :
            LO.FirstOrder.ArithmeticProposition) := by
        have hformula := addEqualityAsTerm_formula
          left.term right.term normalizedLeft normalizedRight
        simpa [source, middle] using
          (CertifiedPAProof.cast hformula congruenceRaw)
      let arithmetic :=
        proveBinaryNumeralAddition left.value right.value
      let through := proveEqualityTransitivity source middle
        (shortBinaryNumeralTerm (left.value + right.value))
        congruence arithmetic
      simpa [ClosedPATerm.term, ClosedPATerm.value, source, middle,
        normalizedLeft, normalizedRight] using through
  | .mul left right => by
      let leftProof := proveNormalization left
      let rightProof := proveNormalization right
      let normalizedLeft := shortBinaryNumeralTerm left.value
      let normalizedRight := shortBinaryNumeralTerm right.value
      let source := paMulTerm left.term right.term
      let middle := paMulTerm normalizedLeft normalizedRight
      let congruenceRaw := proveMulCongruence
        left.term right.term normalizedLeft normalizedRight
        leftProof rightProof
      let congruence : CertifiedPAProof
          (“!!source = !!middle” :
            LO.FirstOrder.ArithmeticProposition) := by
        have hformula := mulEqualityAsTerm_formula
          left.term right.term normalizedLeft normalizedRight
        simpa [source, middle] using
          (CertifiedPAProof.cast hformula congruenceRaw)
      let arithmetic :=
        proveBinaryNumeralMultiplication left.value right.value
      let through := proveEqualityTransitivity source middle
        (shortBinaryNumeralTerm (left.value * right.value))
        congruence arithmetic
      simpa [ClosedPATerm.term, ClosedPATerm.value, source, middle,
        normalizedLeft, normalizedRight] using through

theorem proveNormalization_verifier_eq_true
    (expression : ClosedPATerm) :
    listedCompactCertifiedPAProofVerifier
      (proveNormalization expression).code
      (compactFormulaCode
        (“!!expression.term =
          !!(shortBinaryNumeralTerm expression.value)” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  (proveNormalization expression).verifier_eq_true

/-! ## Positive closed equality atoms -/

def PositiveEqualityCertificate
    (left right : ClosedPATerm) : Prop :=
  left.value = right.value

instance positiveEqualityCertificateDecidable
    (left right : ClosedPATerm) :
    Decidable (PositiveEqualityCertificate left right) :=
  by
    unfold PositiveEqualityCertificate
    infer_instance

noncomputable def provePositiveEquality
    (left right : ClosedPATerm)
    (hvalue : PositiveEqualityCertificate left right) :
    CertifiedPAProof
      (“!!left.term = !!right.term” :
        LO.FirstOrder.ArithmeticProposition) := by
  let middle := shortBinaryNumeralTerm left.value
  let leftProof := proveNormalization left
  let rightForwardRaw := proveNormalization right
  let rightForward : CertifiedPAProof
      (“!!right.term = !!middle” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula :
        (“!!right.term =
          !!(shortBinaryNumeralTerm right.value)” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!right.term = !!middle” :
          LO.FirstOrder.ArithmeticProposition) := by
      simp only [middle]
      rw [hvalue]
    exact CertifiedPAProof.cast hformula rightForwardRaw
  let rightBackward := proveEqualitySymmetry right.term middle rightForward
  exact proveEqualityTransitivity left.term middle right.term
    leftProof rightBackward

theorem provePositiveEquality_verifier_eq_true
    (left right : ClosedPATerm)
    (hvalue : PositiveEqualityCertificate left right) :
    listedCompactCertifiedPAProofVerifier
      (provePositiveEquality left right hvalue).code
      (compactFormulaCode
        (“!!left.term = !!right.term” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  (provePositiveEquality left right hvalue).verifier_eq_true

theorem positiveEqualityCertificate_iff_check
    (left right : ClosedPATerm) :
    PositiveEqualityCertificate left right ↔
      decide (left.value = right.value) = true := by
  simp [PositiveEqualityCertificate]

/-! ## Positive closed strict-order atoms -/

def PositiveLessThanCertificate
    (left right : ClosedPATerm) : Prop :=
  left.value < right.value

instance positiveLessThanCertificateDecidable
    (left right : ClosedPATerm) :
    Decidable (PositiveLessThanCertificate left right) := by
  unfold PositiveLessThanCertificate
  infer_instance

theorem shiftedGapLessThan_formula
    (left right : Nat) (hvalue : left < right) :
    (“!!(shortBinaryNumeralTerm (0 + left)) <
        !!(shortBinaryNumeralTerm ((right - left) + left))” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!(shortBinaryNumeralTerm left) <
        !!(shortBinaryNumeralTerm right)” :
        LO.FirstOrder.ArithmeticProposition) := by
  rw [Nat.zero_add, Nat.sub_add_cancel (Nat.le_of_lt hvalue)]

noncomputable def provePositiveLessThan
    (left right : ClosedPATerm)
    (hvalue : PositiveLessThanCertificate left right) :
    CertifiedPAProof
      (“!!left.term < !!right.term” :
        LO.FirstOrder.ArithmeticProposition) := by
  let gap := right.value - left.value
  have hgapPositive : 0 < gap := by
    exact Nat.sub_pos_of_lt hvalue
  let gapProof := provePositiveBinaryNumeral gap hgapPositive
  let shiftedRaw :=
    proveBinaryNumeralAddLtAdd 0 gap left.value gapProof
  let numeralProof := CertifiedPAProof.cast
    (shiftedGapLessThan_formula left.value right.value hvalue)
    shiftedRaw
  let leftBackward := proveEqualitySymmetry left.term
    (shortBinaryNumeralTerm left.value) (proveNormalization left)
  let rightBackward := proveEqualitySymmetry right.term
    (shortBinaryNumeralTerm right.value) (proveNormalization right)
  exact proveLtTransport
    (shortBinaryNumeralTerm left.value)
    (shortBinaryNumeralTerm right.value)
    left.term right.term leftBackward rightBackward numeralProof

theorem provePositiveLessThan_verifier_eq_true
    (left right : ClosedPATerm)
    (hvalue : PositiveLessThanCertificate left right) :
    listedCompactCertifiedPAProofVerifier
      (provePositiveLessThan left right hvalue).code
      (compactFormulaCode
        (“!!left.term < !!right.term” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  (provePositiveLessThan left right hvalue).verifier_eq_true

theorem positiveLessThanCertificate_iff_check
    (left right : ClosedPATerm) :
    PositiveLessThanCertificate left right ↔
      decide (left.value < right.value) = true := by
  simp [PositiveLessThanCertificate]

/-! ## Positive closed non-strict-order atoms -/

def PositiveLessEqualCertificate
    (left right : ClosedPATerm) : Prop :=
  left.value <= right.value

instance positiveLessEqualCertificateDecidable
    (left right : ClosedPATerm) :
    Decidable (PositiveLessEqualCertificate left right) := by
  unfold PositiveLessEqualCertificate
  infer_instance

theorem lessEqualAsEqualityOrLessThan_formula
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    ((“!!left = !!right” : LO.FirstOrder.ArithmeticProposition) ⋎
        (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)) =
      (“!!left ≤ !!right” : LO.FirstOrder.ArithmeticProposition) := by
  simp [Semiformula.Operator.le_def, Semiformula.Operator.eq_def,
    Semiformula.Operator.lt_def, Matrix.fun_eq_vec_two]

noncomputable def provePositiveLessEqual
    (left right : ClosedPATerm)
    (hvalue : PositiveLessEqualCertificate left right) :
    CertifiedPAProof
      (“!!left.term ≤ !!right.term” :
        LO.FirstOrder.ArithmeticProposition) := by
  by_cases hequal : left.value = right.value
  · let equalityProof := provePositiveEquality left right hequal
    let disjunction := disjunctionLeft
      (right := (“!!left.term < !!right.term” :
        LO.FirstOrder.ArithmeticProposition)) equalityProof
    exact CertifiedPAProof.cast
      (lessEqualAsEqualityOrLessThan_formula left.term right.term)
      disjunction
  · have hstrict : left.value < right.value :=
      Nat.lt_of_le_of_ne hvalue hequal
    let strictProof := provePositiveLessThan left right hstrict
    let disjunction := disjunctionRight
      (left := (“!!left.term = !!right.term” :
        LO.FirstOrder.ArithmeticProposition)) strictProof
    exact CertifiedPAProof.cast
      (lessEqualAsEqualityOrLessThan_formula left.term right.term)
      disjunction

theorem provePositiveLessEqual_verifier_eq_true
    (left right : ClosedPATerm)
    (hvalue : PositiveLessEqualCertificate left right) :
    listedCompactCertifiedPAProofVerifier
      (provePositiveLessEqual left right hvalue).code
      (compactFormulaCode
        (“!!left.term ≤ !!right.term” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  (provePositiveLessEqual left right hvalue).verifier_eq_true

theorem positiveLessEqualCertificate_iff_check
    (left right : ClosedPATerm) :
    PositiveLessEqualCertificate left right ↔
      decide (left.value <= right.value) = true := by
  simp [PositiveLessEqualCertificate]

/-! ## Negative closed equality atoms -/

def NegativeEqualityCertificate
    (left right : ClosedPATerm) : Prop :=
  left.value ≠ right.value

instance negativeEqualityCertificateDecidable
    (left right : ClosedPATerm) :
    Decidable (NegativeEqualityCertificate left right) := by
  unfold NegativeEqualityCertificate
  infer_instance

noncomputable def proveNegativeEquality
    (left right : ClosedPATerm)
    (hvalue : NegativeEqualityCertificate left right) :
    CertifiedPAProof
      (∼(“!!left.term = !!right.term” :
        LO.FirstOrder.ArithmeticProposition)) := by
  by_cases hforward : left.value < right.value
  · let strictProof := provePositiveLessThan left right hforward
    exact proveNotEqualityOfLessThan left.term right.term strictProof
  · have hreverse : right.value < left.value := by
      unfold NegativeEqualityCertificate at hvalue
      omega
    let reverseStrictProof := provePositiveLessThan right left hreverse
    let reverseNegative :=
      proveNotEqualityOfLessThan right.term left.term reverseStrictProof
    exact modusTollens
      (equalitySymmetryImplication left.term right.term)
      reverseNegative

theorem proveNegativeEquality_verifier_eq_true
    (left right : ClosedPATerm)
    (hvalue : NegativeEqualityCertificate left right) :
    listedCompactCertifiedPAProofVerifier
      (proveNegativeEquality left right hvalue).code
      (compactFormulaCode
        (∼(“!!left.term = !!right.term” :
          LO.FirstOrder.ArithmeticProposition))) = true :=
  (proveNegativeEquality left right hvalue).verifier_eq_true

theorem negativeEqualityCertificate_iff_check
    (left right : ClosedPATerm) :
    NegativeEqualityCertificate left right ↔
      decide (left.value ≠ right.value) = true := by
  simp [NegativeEqualityCertificate]

/-! ## Negative closed strict-order atoms -/

def NegativeLessThanCertificate
    (left right : ClosedPATerm) : Prop :=
  ¬left.value < right.value

instance negativeLessThanCertificateDecidable
    (left right : ClosedPATerm) :
    Decidable (NegativeLessThanCertificate left right) := by
  unfold NegativeLessThanCertificate
  infer_instance

noncomputable def proveNegativeLessThan
    (left right : ClosedPATerm)
    (hvalue : NegativeLessThanCertificate left right) :
    CertifiedPAProof
      (∼(“!!left.term < !!right.term” :
        LO.FirstOrder.ArithmeticProposition)) := by
  by_cases hequal : left.value = right.value
  · let equalityProof := provePositiveEquality left right hequal
    exact proveNotLessThanOfEquality
      left.term right.term equalityProof
  · have hreverse : right.value < left.value := by
      unfold NegativeLessThanCertificate at hvalue
      omega
    let reverseProof := provePositiveLessThan right left hreverse
    exact proveNotLessThanOfReverseLessThan
      left.term right.term reverseProof

theorem proveNegativeLessThan_verifier_eq_true
    (left right : ClosedPATerm)
    (hvalue : NegativeLessThanCertificate left right) :
    listedCompactCertifiedPAProofVerifier
      (proveNegativeLessThan left right hvalue).code
      (compactFormulaCode
        (∼(“!!left.term < !!right.term” :
          LO.FirstOrder.ArithmeticProposition))) = true :=
  (proveNegativeLessThan left right hvalue).verifier_eq_true

theorem negativeLessThanCertificate_iff_check
    (left right : ClosedPATerm) :
    NegativeLessThanCertificate left right ↔
      decide (¬left.value < right.value) = true := by
  simp [NegativeLessThanCertificate]

/-! ## Negative closed non-strict-order atoms -/

def NegativeLessEqualCertificate
    (left right : ClosedPATerm) : Prop :=
  ¬left.value <= right.value

instance negativeLessEqualCertificateDecidable
    (left right : ClosedPATerm) :
    Decidable (NegativeLessEqualCertificate left right) := by
  unfold NegativeLessEqualCertificate
  infer_instance

theorem negativeLessEqualAsNegativeConjunction_formula
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    ((∼(“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)) ⋏
        (∼(“!!left < !!right” : LO.FirstOrder.ArithmeticProposition))) =
      (∼(“!!left ≤ !!right” :
        LO.FirstOrder.ArithmeticProposition)) := by
  rw [← DeMorgan.or]
  rw [lessEqualAsEqualityOrLessThan_formula]

noncomputable def proveNegativeLessEqual
    (left right : ClosedPATerm)
    (hvalue : NegativeLessEqualCertificate left right) :
    CertifiedPAProof
      (∼(“!!left.term ≤ !!right.term” :
        LO.FirstOrder.ArithmeticProposition)) := by
  have hnotLe : ¬left.value <= right.value := by
    exact hvalue
  have hreverse : right.value < left.value :=
    Nat.lt_of_not_ge hnotLe
  have hnotEqual : NegativeEqualityCertificate left right := by
    intro hequal
    rw [hequal] at hreverse
    exact (Nat.lt_irrefl right.value) hreverse
  have hnotLess : NegativeLessThanCertificate left right := by
    unfold NegativeLessThanCertificate
    exact Nat.not_lt_of_ge (Nat.le_of_lt hreverse)
  let negativeEquality := proveNegativeEquality left right hnotEqual
  let negativeLessThan := proveNegativeLessThan left right hnotLess
  let conjunctionProof := conjunction negativeEquality negativeLessThan
  exact CertifiedPAProof.cast
    (negativeLessEqualAsNegativeConjunction_formula left.term right.term)
    conjunctionProof

theorem proveNegativeLessEqual_verifier_eq_true
    (left right : ClosedPATerm)
    (hvalue : NegativeLessEqualCertificate left right) :
    listedCompactCertifiedPAProofVerifier
      (proveNegativeLessEqual left right hvalue).code
      (compactFormulaCode
        (∼(“!!left.term ≤ !!right.term” :
          LO.FirstOrder.ArithmeticProposition))) = true :=
  (proveNegativeLessEqual left right hvalue).verifier_eq_true

theorem negativeLessEqualCertificate_iff_check
    (left right : ClosedPATerm) :
    NegativeLessEqualCertificate left right ↔
      decide (¬left.value <= right.value) = true := by
  simp [NegativeLessEqualCertificate]

/-! ## Unified closed atomic-literal compiler -/

inductive ClosedPAAtomicLiteral where
  | equality (left right : ClosedPATerm)
  | disequality (left right : ClosedPATerm)
  | lessThan (left right : ClosedPATerm)
  | notLessThan (left right : ClosedPATerm)
  | lessEqual (left right : ClosedPATerm)
  | notLessEqual (left right : ClosedPATerm)
deriving Repr, DecidableEq

namespace ClosedPAAtomicLiteral

def formula : ClosedPAAtomicLiteral →
    LO.FirstOrder.ArithmeticProposition
  | .equality left right =>
      (“!!left.term = !!right.term” :
        LO.FirstOrder.ArithmeticProposition)
  | .disequality left right =>
      ∼(“!!left.term = !!right.term” :
        LO.FirstOrder.ArithmeticProposition)
  | .lessThan left right =>
      (“!!left.term < !!right.term” :
        LO.FirstOrder.ArithmeticProposition)
  | .notLessThan left right =>
      ∼(“!!left.term < !!right.term” :
        LO.FirstOrder.ArithmeticProposition)
  | .lessEqual left right =>
      (“!!left.term ≤ !!right.term” :
        LO.FirstOrder.ArithmeticProposition)
  | .notLessEqual left right =>
      ∼(“!!left.term ≤ !!right.term” :
        LO.FirstOrder.ArithmeticProposition)

def Truth : ClosedPAAtomicLiteral → Prop
  | .equality left right => left.value = right.value
  | .disequality left right => left.value ≠ right.value
  | .lessThan left right => left.value < right.value
  | .notLessThan left right => ¬left.value < right.value
  | .lessEqual left right => left.value <= right.value
  | .notLessEqual left right => ¬left.value <= right.value

instance truthDecidable (literal : ClosedPAAtomicLiteral) :
    Decidable literal.Truth := by
  cases literal <;> simp only [Truth] <;> infer_instance

noncomputable def compile :
    (literal : ClosedPAAtomicLiteral) →
    literal.Truth → CertifiedPAProof literal.formula
  | .equality left right, hvalue =>
      provePositiveEquality left right hvalue
  | .disequality left right, hvalue =>
      proveNegativeEquality left right hvalue
  | .lessThan left right, hvalue =>
      provePositiveLessThan left right hvalue
  | .notLessThan left right, hvalue =>
      proveNegativeLessThan left right hvalue
  | .lessEqual left right, hvalue =>
      provePositiveLessEqual left right hvalue
  | .notLessEqual left right, hvalue =>
      proveNegativeLessEqual left right hvalue

theorem compile_verifier_eq_true
    (literal : ClosedPAAtomicLiteral)
    (hvalue : literal.Truth) :
    listedCompactCertifiedPAProofVerifier
      (literal.compile hvalue).code
      (compactFormulaCode literal.formula) = true :=
  (literal.compile hvalue).verifier_eq_true

theorem truth_iff_check (literal : ClosedPAAtomicLiteral) :
    literal.Truth ↔ decide literal.Truth = true := by
  simp

end ClosedPAAtomicLiteral

#print axioms ClosedPATerm.value_size_le_leafBitWeight
#print axioms ClosedPATerm.proveNormalization_verifier_eq_true
#print axioms ClosedPATerm.provePositiveEquality_verifier_eq_true
#print axioms ClosedPATerm.provePositiveLessThan_verifier_eq_true
#print axioms ClosedPATerm.provePositiveLessEqual_verifier_eq_true
#print axioms ClosedPATerm.proveNegativeEquality_verifier_eq_true
#print axioms ClosedPATerm.proveNegativeLessThan_verifier_eq_true
#print axioms ClosedPATerm.proveNegativeLessEqual_verifier_eq_true
#print axioms ClosedPATerm.ClosedPAAtomicLiteral.compile_verifier_eq_true

end ClosedPATerm

end FoundationCompactPAClosedAtomicCompiler
