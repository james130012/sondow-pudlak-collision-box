import integration.FoundationCompactPABoundedUniversalCertificateCode
import integration.FoundationCompactPAFiniteExhaustionPolynomialBounds
import integration.FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
import integration.FoundationCompactPAContextCostPolynomialBounds
import integration.FoundationCompactPAUnaryAtomicTransportPolynomialBounds

/-!
# Uniform polynomial envelopes for bounded-universal compilation

The first layer below puts all six closed arithmetic literal compilers on one
proof-free resource coordinate.  A finite cumulative envelope avoids assuming
unproved monotonicity of the lower-level named polynomial components.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped BigOperators

noncomputable section

namespace FoundationCompactPABoundedUniversalPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPANegativeEqualityBounds
open FoundationCompactPANegativeOrderBounds
open FoundationCompactPAClosedAtomicCompiler
open FoundationCompactPAClosedAtomicCompiler.ClosedPATerm
open FoundationCompactPAClosedAtomicCompiler.ClosedPATerm.ClosedPAAtomicLiteral
open FoundationCompactPAClosedAtomicCompilerBounds
open FoundationCompactPAClosedAtomicCompilerBounds.ClosedPATerm
open FoundationCompactPAClosedAtomicCompilerBounds.ClosedPATerm.ClosedPAAtomicLiteralBounds
open FoundationCompactPABoundedUniversalCertificateCode
open FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAUnaryTermEqualityImplication
open FoundationCompactPAUnaryAtomicTransport
open FoundationCompactPAUnaryBoundedFormulaTransport
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionSuccessor
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactCertifiedUniversalIntroduction
open FoundationCompactPABoundedUniversalCompiler
open FoundationCompactPABoundedUniversalCompiler.CheckedFiniteBoundedUniversalCertificate
open FoundationCompactPABoundedUniversalCompilerBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds

def atomicPrimitiveEnvelope (nodeBudget bitWidth : Nat) : Nat :=
  let termBound := compilerTermCodeEnvelope nodeBudget bitWidth
  (8 * nodeBudget) * compilerLocalCostEnvelope nodeBudget bitWidth +
    positiveBinaryNumeralPayloadPolynomial bitWidth +
    orderStepCostEnvelope bitWidth +
    2 * paPrimitiveCostEnvelope termBound +
    2 * orderPrimitiveCostEnvelope termBound +
    closedOrderDisjunctionPayloadCostEnvelope termBound +
    2 * negativeEqualityPrimitiveCostEnvelope termBound +
    negativeEqualityModusTollensCostEnvelope termBound +
    negativeOrderEqualityPrimitiveCostEnvelope termBound +
    negativeOrderReversePrimitiveCostEnvelope termBound +
    closedNegativeOrderConjunctionPayloadCostEnvelope termBound + 1

def cumulativeAtomicPrimitiveEnvelope (resource : Nat) : Nat :=
  ∑ nodeBudget ∈ Finset.range (resource + 1),
    ∑ bitWidth ∈ Finset.range (resource + 1),
      atomicPrimitiveEnvelope nodeBudget bitWidth

theorem atomicPrimitiveEnvelope_le_cumulative
    {nodeBudget bitWidth resource : Nat}
    (hnodes : nodeBudget <= resource)
    (hbits : bitWidth <= resource) :
    atomicPrimitiveEnvelope nodeBudget bitWidth <=
      cumulativeAtomicPrimitiveEnvelope resource := by
  have hnodeMem : nodeBudget ∈ Finset.range (resource + 1) := by
    simp
    omega
  have hbitMem : bitWidth ∈ Finset.range (resource + 1) := by
    simp
    omega
  have hinner : atomicPrimitiveEnvelope nodeBudget bitWidth <=
      ∑ candidate ∈ Finset.range (resource + 1),
        atomicPrimitiveEnvelope nodeBudget candidate :=
    Finset.single_le_sum
      (f := fun candidate => atomicPrimitiveEnvelope nodeBudget candidate)
      (s := Finset.range (resource + 1))
      (fun candidate _ => Nat.zero_le
        (atomicPrimitiveEnvelope nodeBudget candidate))
      hbitMem
  have houter :
      (∑ candidate ∈ Finset.range (resource + 1),
        atomicPrimitiveEnvelope nodeBudget candidate) <=
      cumulativeAtomicPrimitiveEnvelope resource := by
    unfold cumulativeAtomicPrimitiveEnvelope
    exact Finset.single_le_sum
      (f := fun candidate =>
        ∑ bit ∈ Finset.range (resource + 1),
          atomicPrimitiveEnvelope candidate bit)
      (s := Finset.range (resource + 1))
      (fun candidate _ => Nat.zero_le
        (∑ bit ∈ Finset.range (resource + 1),
          atomicPrimitiveEnvelope candidate bit))
      hnodeMem
  exact hinner.trans houter

theorem cumulativeAtomicPrimitiveEnvelope_mono
    {small large : Nat}
    (hresource : small <= large) :
    cumulativeAtomicPrimitiveEnvelope small <=
      cumulativeAtomicPrimitiveEnvelope large := by
  have hrange : Finset.range (small + 1) ⊆
      Finset.range (large + 1) := by
    intro candidate hcandidate
    simp only [Finset.mem_range] at hcandidate ⊢
    omega
  have hinner :
      (∑ nodeBudget ∈ Finset.range (small + 1),
        ∑ bitWidth ∈ Finset.range (small + 1),
          atomicPrimitiveEnvelope nodeBudget bitWidth) <=
      ∑ nodeBudget ∈ Finset.range (small + 1),
        ∑ bitWidth ∈ Finset.range (large + 1),
          atomicPrimitiveEnvelope nodeBudget bitWidth := by
    apply Finset.sum_le_sum
    intro nodeBudget hnode
    exact Finset.sum_le_sum_of_subset hrange
  have houter :
      (∑ nodeBudget ∈ Finset.range (small + 1),
        ∑ bitWidth ∈ Finset.range (large + 1),
          atomicPrimitiveEnvelope nodeBudget bitWidth) <=
      ∑ nodeBudget ∈ Finset.range (large + 1),
        ∑ bitWidth ∈ Finset.range (large + 1),
          atomicPrimitiveEnvelope nodeBudget bitWidth :=
    Finset.sum_le_sum_of_subset hrange
  unfold cumulativeAtomicPrimitiveEnvelope
  exact hinner.trans houter

namespace ClosedPAAtomicLiteralBounds

def uniformPayloadPolynomial (literal : ClosedPAAtomicLiteral) : Nat :=
  8 * cumulativeAtomicPrimitiveEnvelope
    (FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight
      literal)

def encodedPayloadPolynomial (literalCodeLength : Nat) : Nat :=
  8 * cumulativeAtomicPrimitiveEnvelope (4 * literalCodeLength)

theorem positiveEqualityPayloadPolynomial_le_cumulative
    (left right : ClosedPATerm) :
    positiveEqualityPayloadPolynomial left right <=
      cumulativeAtomicPrimitiveEnvelope
        (FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight
          (.equality left right)) := by
  let nodeBudget := positiveEqualityNodeBudget left right
  let bitWidth := positiveEqualityBitWidth left right
  let resource :=
    FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight
      (.equality left right)
  have hnodes : nodeBudget <= resource := by
    simp only [nodeBudget, resource, positiveEqualityNodeBudget,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.resourceWeight]
    omega
  have hbits : bitWidth <= resource := by
    simp only [bitWidth, resource, positiveEqualityBitWidth,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.resourceWeight]
    omega
  have hlocal := atomicPrimitiveEnvelope_le_cumulative hnodes hbits
  have hcoefficient : 4 * nodeBudget <= 8 * nodeBudget := by omega
  have hnormalization := Nat.mul_le_mul_right
    (compilerLocalCostEnvelope nodeBudget bitWidth) hcoefficient
  unfold positiveEqualityPayloadPolynomial
  dsimp only [nodeBudget, bitWidth, resource] at hlocal hnormalization ⊢
  exact hnormalization.trans (by
    apply hlocal.trans'
    unfold atomicPrimitiveEnvelope
    dsimp only
    omega)

theorem positiveLessThanPayloadPolynomial_le_cumulative
    (left right : ClosedPATerm) :
    positiveLessThanPayloadPolynomial left right <=
      cumulativeAtomicPrimitiveEnvelope
        (FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight
          (.lessThan left right)) := by
  let nodeBudget := positiveLessThanNodeBudget left right
  let bitWidth := positiveLessThanBitWidth left right
  let resource :=
    FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight
      (.lessThan left right)
  let localCost := compilerLocalCostEnvelope nodeBudget bitWidth
  have hnodes : nodeBudget <= resource := by
    simp only [nodeBudget, resource, positiveLessThanNodeBudget,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.resourceWeight]
    omega
  have hbits : bitWidth <= resource := by
    simp only [bitWidth, resource, positiveLessThanBitWidth,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.resourceWeight]
    omega
  have hlocal := atomicPrimitiveEnvelope_le_cumulative hnodes hbits
  have hcoefficient :
      4 * left.nodeCount + 4 * right.nodeCount <=
        8 * nodeBudget := by
    simp only [nodeBudget, positiveLessThanNodeBudget]
    omega
  have hnormalization :
      (4 * left.nodeCount) * localCost +
          (4 * right.nodeCount) * localCost <=
        (8 * nodeBudget) * localCost := by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right localCost hcoefficient
  unfold positiveLessThanPayloadPolynomial
  dsimp only [nodeBudget, bitWidth, resource, localCost] at hlocal
  dsimp only [localCost, nodeBudget, bitWidth] at hnormalization
  dsimp only
  exact hlocal.trans' (by
    unfold atomicPrimitiveEnvelope
    dsimp only
    omega)

theorem positiveLessEqualPayloadPolynomial_le_uniform
    (left right : ClosedPATerm) :
    positiveLessEqualPayloadPolynomial left right <=
      uniformPayloadPolynomial (.lessEqual left right) := by
  let resource :=
    FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight
      (.lessEqual left right)
  let cumulative := cumulativeAtomicPrimitiveEnvelope resource
  let nodeBudget := positiveLessThanNodeBudget left right
  let bitWidth := positiveLessThanBitWidth left right
  let termBound := compilerTermCodeEnvelope nodeBudget bitWidth
  have hequality := positiveEqualityPayloadPolynomial_le_cumulative left right
  have hless := positiveLessThanPayloadPolynomial_le_cumulative left right
  change positiveEqualityPayloadPolynomial left right <= cumulative at hequality
  change positiveLessThanPayloadPolynomial left right <= cumulative at hless
  have hnodes : nodeBudget <= resource := by
    simp only [nodeBudget, resource, positiveLessThanNodeBudget,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.resourceWeight]
    omega
  have hbits : bitWidth <= resource := by
    simp only [bitWidth, resource, positiveLessThanBitWidth,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.resourceWeight]
    omega
  have hlocal := atomicPrimitiveEnvelope_le_cumulative hnodes hbits
  have hextra : closedOrderDisjunctionPayloadCostEnvelope termBound <=
      cumulative := by
    apply hlocal.trans'
    unfold atomicPrimitiveEnvelope
    dsimp only [termBound, cumulative, nodeBudget, bitWidth, resource]
    omega
  unfold positiveLessEqualPayloadPolynomial uniformPayloadPolynomial
  dsimp only [resource, cumulative, nodeBudget, bitWidth, termBound] at *
  omega

theorem negativeEqualityPayloadPolynomial_le_three_cumulative
    (left right : ClosedPATerm) :
    negativeEqualityPayloadPolynomial left right <=
      3 * cumulativeAtomicPrimitiveEnvelope
        (FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight
          (.disequality left right)) := by
  let resource :=
    FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight
      (.disequality left right)
  let cumulative := cumulativeAtomicPrimitiveEnvelope resource
  let nodeBudget := negativeEqualityNodeBudget left right
  let bitWidth := negativeEqualityBitWidth left right
  let termBound := compilerTermCodeEnvelope nodeBudget bitWidth
  have hforward := positiveLessThanPayloadPolynomial_le_cumulative left right
  have hreverse := positiveLessThanPayloadPolynomial_le_cumulative right left
  change positiveLessThanPayloadPolynomial left right <= cumulative at hforward
  have hreverseResource :
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight
          (.lessThan right left) = resource := by
    simp only [resource,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.resourceWeight]
    omega
  rw [hreverseResource] at hreverse
  change positiveLessThanPayloadPolynomial right left <= cumulative at hreverse
  have hnodes : nodeBudget <= resource := by
    simp only [nodeBudget, resource, negativeEqualityNodeBudget,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.resourceWeight]
    have hleft := left.nodeCount_pos
    have hright := right.nodeCount_pos
    omega
  have hbits : bitWidth <= resource := by
    simp only [bitWidth, resource, negativeEqualityBitWidth,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.resourceWeight]
    have hleft := left.nodeCount_pos
    have hright := right.nodeCount_pos
    omega
  have hlocal := atomicPrimitiveEnvelope_le_cumulative hnodes hbits
  have hextra :
      2 * negativeEqualityPrimitiveCostEnvelope termBound +
          negativeEqualityModusTollensCostEnvelope termBound <= cumulative := by
    apply hlocal.trans'
    unfold atomicPrimitiveEnvelope
    dsimp only [termBound, cumulative, nodeBudget, bitWidth, resource]
    omega
  unfold negativeEqualityPayloadPolynomial
  dsimp only [resource, cumulative, nodeBudget, bitWidth, termBound] at *
  omega

theorem negativeEqualityPayloadPolynomial_le_uniform
    (left right : ClosedPATerm) :
    negativeEqualityPayloadPolynomial left right <=
      uniformPayloadPolynomial (.disequality left right) := by
  have h := negativeEqualityPayloadPolynomial_le_three_cumulative left right
  unfold uniformPayloadPolynomial
  omega

theorem negativeLessThanPayloadPolynomial_le_three_cumulative
    (left right : ClosedPATerm) :
    negativeLessThanPayloadPolynomial left right <=
      3 * cumulativeAtomicPrimitiveEnvelope
        (FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight
          (.notLessThan left right)) := by
  let resource :=
    FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight
      (.notLessThan left right)
  let cumulative := cumulativeAtomicPrimitiveEnvelope resource
  let nodeBudget := negativeLessThanNodeBudget left right
  let bitWidth := negativeLessThanBitWidth left right
  let termBound := compilerTermCodeEnvelope nodeBudget bitWidth
  have hequality := positiveEqualityPayloadPolynomial_le_cumulative left right
  have hreverse := positiveLessThanPayloadPolynomial_le_cumulative right left
  change positiveEqualityPayloadPolynomial left right <= cumulative at hequality
  have hreverseResource :
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight
          (.lessThan right left) = resource := by
    simp only [resource,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.resourceWeight]
    omega
  rw [hreverseResource] at hreverse
  change positiveLessThanPayloadPolynomial right left <= cumulative at hreverse
  have hnodes : nodeBudget <= resource := by
    simp only [nodeBudget, resource, negativeLessThanNodeBudget,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.resourceWeight]
    have hleft := left.nodeCount_pos
    have hright := right.nodeCount_pos
    omega
  have hbits : bitWidth <= resource := by
    simp only [bitWidth, resource, negativeLessThanBitWidth,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.resourceWeight]
    have hleft := left.nodeCount_pos
    have hright := right.nodeCount_pos
    omega
  have hlocal := atomicPrimitiveEnvelope_le_cumulative hnodes hbits
  have hextra :
      negativeOrderEqualityPrimitiveCostEnvelope termBound +
          negativeOrderReversePrimitiveCostEnvelope termBound <= cumulative := by
    apply hlocal.trans'
    unfold atomicPrimitiveEnvelope
    dsimp only [termBound, cumulative, nodeBudget, bitWidth, resource]
    omega
  unfold negativeLessThanPayloadPolynomial
  dsimp only [resource, cumulative, nodeBudget, bitWidth, termBound] at *
  omega

theorem negativeLessThanPayloadPolynomial_le_uniform
    (left right : ClosedPATerm) :
    negativeLessThanPayloadPolynomial left right <=
      uniformPayloadPolynomial (.notLessThan left right) := by
  have h := negativeLessThanPayloadPolynomial_le_three_cumulative left right
  unfold uniformPayloadPolynomial
  omega

theorem negativeLessEqualPayloadPolynomial_le_uniform
    (left right : ClosedPATerm) :
    negativeLessEqualPayloadPolynomial left right <=
      uniformPayloadPolynomial (.notLessEqual left right) := by
  let resource :=
    FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight
      (.notLessEqual left right)
  let cumulative := cumulativeAtomicPrimitiveEnvelope resource
  let nodeBudget := negativeLessEqualNodeBudget left right
  let bitWidth := negativeLessEqualBitWidth left right
  let termBound := compilerTermCodeEnvelope nodeBudget bitWidth
  have hequality :=
    negativeEqualityPayloadPolynomial_le_three_cumulative left right
  have hless :=
    negativeLessThanPayloadPolynomial_le_three_cumulative left right
  change negativeEqualityPayloadPolynomial left right <=
    3 * cumulative at hequality
  change negativeLessThanPayloadPolynomial left right <=
    3 * cumulative at hless
  have hnodes : nodeBudget <= resource := by
    simp only [nodeBudget, resource, negativeLessEqualNodeBudget,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.resourceWeight]
    have hleft := left.nodeCount_pos
    have hright := right.nodeCount_pos
    omega
  have hbits : bitWidth <= resource := by
    simp only [bitWidth, resource, negativeLessEqualBitWidth,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight,
      FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.resourceWeight]
    have hleft := left.nodeCount_pos
    have hright := right.nodeCount_pos
    omega
  have hlocal := atomicPrimitiveEnvelope_le_cumulative hnodes hbits
  have hextra : closedNegativeOrderConjunctionPayloadCostEnvelope termBound <=
      cumulative := by
    apply hlocal.trans'
    unfold atomicPrimitiveEnvelope
    dsimp only [termBound, cumulative, nodeBudget, bitWidth, resource]
    omega
  unfold negativeLessEqualPayloadPolynomial uniformPayloadPolynomial
  dsimp only [resource, cumulative, nodeBudget, bitWidth, termBound] at *
  omega

theorem payloadPolynomial_le_uniform
    (literal : ClosedPAAtomicLiteral) :
    payloadPolynomial literal <= uniformPayloadPolynomial literal := by
  cases literal with
  | equality left right =>
      have h := positiveEqualityPayloadPolynomial_le_cumulative left right
      change positiveEqualityPayloadPolynomial left right <=
        uniformPayloadPolynomial (.equality left right)
      unfold uniformPayloadPolynomial
      omega
  | disequality left right =>
      exact negativeEqualityPayloadPolynomial_le_uniform left right
  | lessThan left right =>
      have h := positiveLessThanPayloadPolynomial_le_cumulative left right
      change positiveLessThanPayloadPolynomial left right <=
        uniformPayloadPolynomial (.lessThan left right)
      unfold uniformPayloadPolynomial
      omega
  | notLessThan left right =>
      exact negativeLessThanPayloadPolynomial_le_uniform left right
  | lessEqual left right =>
      exact positiveLessEqualPayloadPolynomial_le_uniform left right
  | notLessEqual left right =>
      exact negativeLessEqualPayloadPolynomial_le_uniform left right

theorem payloadPolynomial_le_encoded
    (literal : ClosedPAAtomicLiteral) :
    payloadPolynomial literal <=
      encodedPayloadPolynomial
        (FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.proofFreeCode
          literal).length := by
  have huniform := payloadPolynomial_le_uniform literal
  have hresource := resourceWeight_le_four_mul_code_length literal
  have hcumulative := cumulativeAtomicPrimitiveEnvelope_mono hresource
  unfold uniformPayloadPolynomial at huniform
  unfold encodedPayloadPolynomial
  exact huniform.trans (Nat.mul_le_mul_left 8 hcumulative)

theorem encodedPayloadPolynomial_mono
    {small large : Nat} (h : small <= large) :
    encodedPayloadPolynomial small <= encodedPayloadPolynomial large := by
  have hresource : 4 * small <= 4 * large := Nat.mul_le_mul_left 4 h
  exact Nat.mul_le_mul_left 8
    (cumulativeAtomicPrimitiveEnvelope_mono hresource)

end ClosedPAAtomicLiteralBounds

def replacementSyntaxEnvelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (certificateCodeLength : Nat) : Nat :=
  let parameterTermBound :=
    (binaryTermCode left).length + (binaryTermCode right).length
  certificateCodeLength +
    compilerTermCodeEnvelope certificateCodeLength certificateCodeLength +
    2 * paFormulaCodeEnvelope parameterTermBound + 1

theorem certificateCodeLength_le_replacementSyntaxEnvelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (certificateCodeLength : Nat) :
    certificateCodeLength <=
      replacementSyntaxEnvelope left right certificateCodeLength := by
  unfold replacementSyntaxEnvelope
  dsimp only
  omega

theorem compilerTermCodeEnvelope_diagonal_mono
    {small large : Nat}
    (h : small <= large) :
    compilerTermCodeEnvelope small small <=
      compilerTermCodeEnvelope large large := by
  unfold compilerTermCodeEnvelope paGeneratedTermAtomEnvelope
    paTermCodeBaseEnvelope binaryNumeralTermCodeEnvelope
  gcongr

theorem closedTermCodeLength_le_replacementSyntaxEnvelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (certificateCodeLength : Nat)
    (witness : ClosedPATerm)
    (hwitness :
      (FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.proofFreeCode
        witness).length <= certificateCodeLength) :
    (binaryTermCode witness.term).length <=
      replacementSyntaxEnvelope left right certificateCodeLength := by
  have hterm :=
    FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.termCode_length_le_compilerCode
      witness
  have henvelope := compilerTermCodeEnvelope_diagonal_mono hwitness
  exact hterm.trans (henvelope.trans (by
    unfold replacementSyntaxEnvelope
    dsimp only
    omega))

theorem parameterEqualityContext_formulaCodeBound
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (certificateCodeLength : Nat) :
    FormulaCodeBound (parameterEqualityContext left right)
      (replacementSyntaxEnvelope left right certificateCodeLength) := by
  let parameterTermBound :=
    (binaryTermCode left).length + (binaryTermCode right).length
  have hleft : (binaryTermCode left).length <= parameterTermBound := by
    simp only [parameterTermBound]
    omega
  have hright : (binaryTermCode right).length <= parameterTermBound := by
    simp only [parameterTermBound]
    omega
  have hequality := equalityFormula_code_length_le_paEnvelope
    left right parameterTermBound hleft hright
  change (binaryFormulaCode (parameterEqualityFormula left right)).length <=
    paFormulaCodeEnvelope parameterTermBound at hequality
  have hnegative := binaryFormulaCode_neg_length_le
    (parameterEqualityFormula left right)
  intro formula hformula
  simp only [parameterEqualityContext, Finset.mem_singleton] at hformula
  subst formula
  unfold replacementSyntaxEnvelope
  dsimp only [parameterTermBound] at hequality hnegative ⊢
  omega

theorem parameterEqualityContext_card_le_four
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (parameterEqualityContext left right).card <= 4 := by
  simp [parameterEqualityContext]

theorem targetFormulaCodeLength_le_replacementSyntaxEnvelope
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula)
    (certificateCodeLength : Nat)
    (hcertificate :
      (FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.proofFreeCode
        certificate).length <= certificateCodeLength) :
    (binaryFormulaCode formula).length <=
      replacementSyntaxEnvelope left right certificateCodeLength := by
  have htarget :=
    FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.targetFormulaCodeLength_le_proofFreeCode_length
      certificate
  exact htarget.trans (hcertificate.trans
    (certificateCodeLength_le_replacementSyntaxEnvelope
      left right certificateCodeLength))

namespace CheckedUnaryReplacementCertificate

open FoundationCompactPAUnaryBoundedFormulaTransport.CheckedUnaryReplacementCertificate
open FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate

def encodedLeafStructuralPayloadBound
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0} :
    {formula : LO.FirstOrder.ArithmeticProposition} →
      CheckedUnaryReplacementCertificate left right formula → Nat
  | _, .verum =>
      verumProof.payloadLength +
        FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
          (insert (⊤ : LO.FirstOrder.ArithmeticProposition)
            (parameterEqualityContext left right))
  | _, .positiveAtomic relationSymbol arguments literal _ _ =>
      positiveTransportUnderAssumptionStructuralPayloadBound
        relationSymbol arguments left right
        (ClosedPAAtomicLiteralBounds.encodedPayloadPolynomial
          (FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.proofFreeCode
            literal).length)
  | _, .negativeAtomic relationSymbol arguments literal _ _ =>
      negativeTransportUnderAssumptionStructuralPayloadBound
        relationSymbol arguments left right
        (ClosedPAAtomicLiteralBounds.encodedPayloadPolynomial
          (FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.proofFreeCode
            literal).length)
  | _, .conjunction (leftFormula := leftFormula)
      (rightFormula := rightFormula) leftCertificate rightCertificate =>
      encodedLeafStructuralPayloadBound leftCertificate +
        encodedLeafStructuralPayloadBound rightCertificate +
        CertifiedPAContextProof.conjunctionFullAssemblyCost
          (parameterEqualityContext left right)
          leftFormula rightFormula
  | _, .disjunctionLeft (leftFormula := leftFormula)
      (rightFormula := rightFormula) leftCertificate =>
      encodedLeafStructuralPayloadBound leftCertificate +
        CertifiedPAContextProof.disjunctionFullAssemblyCost
          (parameterEqualityContext left right)
          leftFormula rightFormula
  | _, .disjunctionRight (leftFormula := leftFormula)
      (rightFormula := rightFormula) rightCertificate =>
      encodedLeafStructuralPayloadBound rightCertificate +
        CertifiedPAContextProof.disjunctionFullAssemblyCost
          (parameterEqualityContext left right)
          leftFormula rightFormula
  | _, .existsWitness body witness bodyCertificate =>
      encodedLeafStructuralPayloadBound bodyCertificate +
        CertifiedPAContextProof.existsIntroFullAssemblyCost
          (parameterEqualityContext left right) body witness.term

def localConnectorAssemblyCost
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0} :
    {formula : LO.FirstOrder.ArithmeticProposition} →
      CheckedUnaryReplacementCertificate left right formula → Nat
  | _, .verum =>
      FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
        (insert (⊤ : LO.FirstOrder.ArithmeticProposition)
          (parameterEqualityContext left right))
  | _, .positiveAtomic _ _ _ _ _ => 0
  | _, .negativeAtomic _ _ _ _ _ => 0
  | _, .conjunction (leftFormula := leftFormula)
      (rightFormula := rightFormula) _ _ =>
      CertifiedPAContextProof.conjunctionFullAssemblyCost
        (parameterEqualityContext left right) leftFormula rightFormula
  | _, .disjunctionLeft (leftFormula := leftFormula)
      (rightFormula := rightFormula) _ =>
      CertifiedPAContextProof.disjunctionFullAssemblyCost
        (parameterEqualityContext left right) leftFormula rightFormula
  | _, .disjunctionRight (leftFormula := leftFormula)
      (rightFormula := rightFormula) _ =>
      CertifiedPAContextProof.disjunctionFullAssemblyCost
        (parameterEqualityContext left right) leftFormula rightFormula
  | _, .existsWitness body witness _ =>
      CertifiedPAContextProof.existsIntroFullAssemblyCost
        (parameterEqualityContext left right) body witness.term

theorem localConnectorAssemblyCost_le_small
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula)
    (certificateCodeLength : Nat)
    (hcertificate : (proofFreeCode certificate).length <=
      certificateCodeLength) :
    localConnectorAssemblyCost certificate <=
      smallContextAssemblyEnvelope
        (replacementSyntaxEnvelope left right certificateCodeLength) := by
  let resource := replacementSyntaxEnvelope
    left right certificateCodeLength
  have hcontext : FormulaCodeBound (parameterEqualityContext left right)
      resource := by
    simpa only [resource] using
      parameterEqualityContext_formulaCodeBound
        left right certificateCodeLength
  have hcontextCard : (parameterEqualityContext left right).card <= 4 :=
    parameterEqualityContext_card_le_four left right
  cases certificate with
  | verum =>
      have htarget := targetFormulaCodeLength_le_replacementSyntaxEnvelope
        (CheckedUnaryReplacementCertificate.verum :
          CheckedUnaryReplacementCertificate left right
            (⊤ : LO.FirstOrder.ArithmeticProposition))
        certificateCodeLength hcertificate
      have hinsert := hcontext.insert htarget
      have hcard :
          (insert (⊤ : LO.FirstOrder.ArithmeticProposition)
            (parameterEqualityContext left right)).card <= 8 := by
        have hstep := Finset.card_insert_le
          (⊤ : LO.FirstOrder.ArithmeticProposition)
          (parameterEqualityContext left right)
        omega
      simpa only [localConnectorAssemblyCost, resource] using
        weakeningFullAssemblyCost_le_small
          (insert (⊤ : LO.FirstOrder.ArithmeticProposition)
            (parameterEqualityContext left right))
          resource hcard hinsert
  | positiveAtomic relationSymbol arguments literal sourceFormula hvalue =>
      simp [localConnectorAssemblyCost]
  | negativeAtomic relationSymbol arguments literal sourceFormula hvalue =>
      simp [localConnectorAssemblyCost]
  | @conjunction leftFormula rightFormula leftCertificate rightCertificate =>
      have hroot := targetFormulaCodeLength_le_replacementSyntaxEnvelope
        (CheckedUnaryReplacementCertificate.conjunction
          leftCertificate rightCertificate)
        certificateCodeLength hcertificate
      have hleftSub :
          (binaryFormulaCode leftFormula).length <=
            (binaryFormulaCode (leftFormula ⋏ rightFormula)).length := by
        simp [binaryFormulaCode]
        omega
      have hrightSub :
          (binaryFormulaCode rightFormula).length <=
            (binaryFormulaCode (leftFormula ⋏ rightFormula)).length := by
        simp [binaryFormulaCode]
        omega
      have hleft := hleftSub.trans hroot
      have hright := hrightSub.trans hroot
      simpa only [localConnectorAssemblyCost, resource] using
        conjunctionFullAssemblyCost_le_small
          (parameterEqualityContext left right)
          leftFormula rightFormula resource
          hcontextCard hcontext hleft hright hroot
  | @disjunctionLeft leftFormula rightFormula leftCertificate =>
      have hroot := targetFormulaCodeLength_le_replacementSyntaxEnvelope
        (CheckedUnaryReplacementCertificate.disjunctionLeft leftCertificate)
        certificateCodeLength hcertificate
      have hleftSub :
          (binaryFormulaCode leftFormula).length <=
            (binaryFormulaCode (leftFormula ⋎ rightFormula)).length := by
        simp [binaryFormulaCode]
        omega
      have hrightSub :
          (binaryFormulaCode rightFormula).length <=
            (binaryFormulaCode (leftFormula ⋎ rightFormula)).length := by
        simp [binaryFormulaCode]
        omega
      have hleft := hleftSub.trans hroot
      have hright := hrightSub.trans hroot
      simpa only [localConnectorAssemblyCost, resource] using
        disjunctionFullAssemblyCost_le_small
          (parameterEqualityContext left right)
          leftFormula rightFormula resource
          hcontextCard hcontext hleft hright hroot
  | @disjunctionRight leftFormula rightFormula rightCertificate =>
      have hroot := targetFormulaCodeLength_le_replacementSyntaxEnvelope
        (CheckedUnaryReplacementCertificate.disjunctionRight rightCertificate)
        certificateCodeLength hcertificate
      have hleftSub :
          (binaryFormulaCode leftFormula).length <=
            (binaryFormulaCode (leftFormula ⋎ rightFormula)).length := by
        simp [binaryFormulaCode]
        omega
      have hrightSub :
          (binaryFormulaCode rightFormula).length <=
            (binaryFormulaCode (leftFormula ⋎ rightFormula)).length := by
        simp [binaryFormulaCode]
        omega
      have hleft := hleftSub.trans hroot
      have hright := hrightSub.trans hroot
      simpa only [localConnectorAssemblyCost, resource] using
        disjunctionFullAssemblyCost_le_small
          (parameterEqualityContext left right)
          leftFormula rightFormula resource
          hcontextCard hcontext hleft hright hroot
  | existsWitness body witness bodyCertificate =>
      have hroot := targetFormulaCodeLength_le_replacementSyntaxEnvelope
        (CheckedUnaryReplacementCertificate.existsWitness
          body witness bodyCertificate)
        certificateCodeLength hcertificate
      have hbodySub :
          (binaryFormulaCode body).length <=
            (binaryFormulaCode
              (∃⁰ body : LO.FirstOrder.ArithmeticProposition)).length := by
        simp [binaryFormulaCode]
      have hbody := hbodySub.trans hroot
      have hchildCode : (proofFreeCode bodyCertificate).length <=
          (proofFreeCode
            (CheckedUnaryReplacementCertificate.existsWitness
              body witness bodyCertificate)).length := by
        simp [FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.proofFreeCode]
        omega
      have hchildInput := hchildCode.trans hcertificate
      have hinstance := targetFormulaCodeLength_le_replacementSyntaxEnvelope
        bodyCertificate certificateCodeLength hchildInput
      have hwitnessCode :
          (FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.proofFreeCode
            witness).length <=
          (proofFreeCode
            (CheckedUnaryReplacementCertificate.existsWitness
              body witness bodyCertificate)).length := by
        simp [FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.proofFreeCode]
        omega
      have hwitnessInput := hwitnessCode.trans hcertificate
      have hwitness := closedTermCodeLength_le_replacementSyntaxEnvelope
        left right certificateCodeLength witness hwitnessInput
      simpa only [localConnectorAssemblyCost, resource] using
        existsIntroFullAssemblyCost_le_small
          (parameterEqualityContext left right) body witness.term resource
          hcontextCard hcontext hbody hwitness hinstance hroot

def encodedAtomicLeafPayloadSum
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0} :
    {formula : LO.FirstOrder.ArithmeticProposition} →
      CheckedUnaryReplacementCertificate left right formula → Nat
  | _, .verum => verumProof.payloadLength
  | _, .positiveAtomic relationSymbol arguments literal _ _ =>
      positiveTransportUnderAssumptionStructuralPayloadBound
        relationSymbol arguments left right
        (ClosedPAAtomicLiteralBounds.encodedPayloadPolynomial
          (FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.proofFreeCode
            literal).length)
  | _, .negativeAtomic relationSymbol arguments literal _ _ =>
      negativeTransportUnderAssumptionStructuralPayloadBound
        relationSymbol arguments left right
        (ClosedPAAtomicLiteralBounds.encodedPayloadPolynomial
          (FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.proofFreeCode
            literal).length)
  | _, .conjunction leftCertificate rightCertificate =>
      encodedAtomicLeafPayloadSum leftCertificate +
        encodedAtomicLeafPayloadSum rightCertificate
  | _, .disjunctionLeft leftCertificate =>
      encodedAtomicLeafPayloadSum leftCertificate
  | _, .disjunctionRight rightCertificate =>
      encodedAtomicLeafPayloadSum rightCertificate
  | _, .existsWitness _ _ bodyCertificate =>
      encodedAtomicLeafPayloadSum bodyCertificate

def connectorAssemblyCostSum
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0} :
    {formula : LO.FirstOrder.ArithmeticProposition} →
      CheckedUnaryReplacementCertificate left right formula → Nat
  | _, .verum =>
      FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
        (insert (⊤ : LO.FirstOrder.ArithmeticProposition)
          (parameterEqualityContext left right))
  | _, .positiveAtomic _ _ _ _ _ => 0
  | _, .negativeAtomic _ _ _ _ _ => 0
  | _, .conjunction (leftFormula := leftFormula)
      (rightFormula := rightFormula) leftCertificate rightCertificate =>
      connectorAssemblyCostSum leftCertificate +
        connectorAssemblyCostSum rightCertificate +
        CertifiedPAContextProof.conjunctionFullAssemblyCost
          (parameterEqualityContext left right) leftFormula rightFormula
  | _, .disjunctionLeft (leftFormula := leftFormula)
      (rightFormula := rightFormula) leftCertificate =>
      connectorAssemblyCostSum leftCertificate +
        CertifiedPAContextProof.disjunctionFullAssemblyCost
          (parameterEqualityContext left right) leftFormula rightFormula
  | _, .disjunctionRight (leftFormula := leftFormula)
      (rightFormula := rightFormula) rightCertificate =>
      connectorAssemblyCostSum rightCertificate +
        CertifiedPAContextProof.disjunctionFullAssemblyCost
          (parameterEqualityContext left right) leftFormula rightFormula
  | _, .existsWitness body witness bodyCertificate =>
      connectorAssemblyCostSum bodyCertificate +
        CertifiedPAContextProof.existsIntroFullAssemblyCost
          (parameterEqualityContext left right) body witness.term

theorem encodedLeafStructuralPayloadBound_eq_atomic_add_connectors
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula) :
    encodedLeafStructuralPayloadBound certificate =
      encodedAtomicLeafPayloadSum certificate +
        connectorAssemblyCostSum certificate := by
  induction certificate with
  | verum =>
      simp [encodedLeafStructuralPayloadBound,
        encodedAtomicLeafPayloadSum, connectorAssemblyCostSum]
  | positiveAtomic relationSymbol arguments literal sourceFormula hvalue =>
      simp [encodedLeafStructuralPayloadBound,
        encodedAtomicLeafPayloadSum, connectorAssemblyCostSum]
  | negativeAtomic relationSymbol arguments literal sourceFormula hvalue =>
      simp [encodedLeafStructuralPayloadBound,
        encodedAtomicLeafPayloadSum, connectorAssemblyCostSum]
  | @conjunction leftFormula rightFormula leftCertificate rightCertificate ihLeft ihRight =>
      simp only [encodedLeafStructuralPayloadBound,
        encodedAtomicLeafPayloadSum, connectorAssemblyCostSum,
        ihLeft, ihRight]
      omega
  | disjunctionLeft leftCertificate ihLeft =>
      simp only [encodedLeafStructuralPayloadBound,
        encodedAtomicLeafPayloadSum, connectorAssemblyCostSum, ihLeft]
      omega
  | disjunctionRight rightCertificate ihRight =>
      simp only [encodedLeafStructuralPayloadBound,
        encodedAtomicLeafPayloadSum, connectorAssemblyCostSum, ihRight]
      omega
  | existsWitness body witness bodyCertificate ihBody =>
      simp only [encodedLeafStructuralPayloadBound,
        encodedAtomicLeafPayloadSum, connectorAssemblyCostSum, ihBody]
      omega

abbrev replacementNodeCount
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula) : Nat :=
  FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.nodeCount
    certificate

theorem connectorAssemblyCostSum_le_small_mul_nodeCount
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula)
    (certificateCodeLength : Nat)
    (hcertificate : (proofFreeCode certificate).length <=
      certificateCodeLength) :
    connectorAssemblyCostSum certificate <=
      replacementNodeCount certificate *
        smallContextAssemblyEnvelope
          (replacementSyntaxEnvelope left right certificateCodeLength) := by
  induction certificate generalizing certificateCodeLength with
  | verum =>
      have hlocal := localConnectorAssemblyCost_le_small
        (CheckedUnaryReplacementCertificate.verum :
          CheckedUnaryReplacementCertificate left right
            (⊤ : LO.FirstOrder.ArithmeticProposition))
        certificateCodeLength hcertificate
      change
        FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
            (insert (⊤ : LO.FirstOrder.ArithmeticProposition)
              (parameterEqualityContext left right)) <=
          smallContextAssemblyEnvelope
            (replacementSyntaxEnvelope left right certificateCodeLength)
        at hlocal
      simpa only [connectorAssemblyCostSum, replacementNodeCount,
        FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.nodeCount,
        Nat.one_mul] using hlocal
  | positiveAtomic relationSymbol arguments literal sourceFormula hvalue =>
      simp [connectorAssemblyCostSum]
  | negativeAtomic relationSymbol arguments literal sourceFormula hvalue =>
      simp [connectorAssemblyCostSum]
  | @conjunction leftFormula rightFormula leftCertificate rightCertificate ihLeft ihRight =>
      have hleftCode : (proofFreeCode leftCertificate).length <=
          certificateCodeLength := by
        apply le_trans ?_ hcertificate
        simp [FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.proofFreeCode]
        omega
      have hrightCode : (proofFreeCode rightCertificate).length <=
          certificateCodeLength := by
        apply le_trans ?_ hcertificate
        simp [FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.proofFreeCode]
        omega
      have hleft := ihLeft certificateCodeLength hleftCode
      have hright := ihRight certificateCodeLength hrightCode
      have hlocal := localConnectorAssemblyCost_le_small
        (CheckedUnaryReplacementCertificate.conjunction
          leftCertificate rightCertificate)
        certificateCodeLength hcertificate
      change CertifiedPAContextProof.conjunctionFullAssemblyCost
          (parameterEqualityContext left right) leftFormula rightFormula <=
        smallContextAssemblyEnvelope
          (replacementSyntaxEnvelope left right certificateCodeLength)
        at hlocal
      simp only [connectorAssemblyCostSum, replacementNodeCount,
        FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.nodeCount]
      calc
        connectorAssemblyCostSum leftCertificate +
              connectorAssemblyCostSum rightCertificate +
              CertifiedPAContextProof.conjunctionFullAssemblyCost
                (parameterEqualityContext left right)
                leftFormula rightFormula <=
            replacementNodeCount leftCertificate *
                smallContextAssemblyEnvelope
                  (replacementSyntaxEnvelope left right certificateCodeLength) +
              replacementNodeCount rightCertificate *
                smallContextAssemblyEnvelope
                  (replacementSyntaxEnvelope left right certificateCodeLength) +
              smallContextAssemblyEnvelope
                (replacementSyntaxEnvelope left right certificateCodeLength) := by
          omega
        _ = (1 + replacementNodeCount leftCertificate +
              replacementNodeCount rightCertificate) *
              smallContextAssemblyEnvelope
                (replacementSyntaxEnvelope left right certificateCodeLength) := by
          ring
  | @disjunctionLeft leftFormula rightFormula leftCertificate ihLeft =>
      have hleftCode : (proofFreeCode leftCertificate).length <=
          certificateCodeLength := by
        apply le_trans ?_ hcertificate
        simp [FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.proofFreeCode]
        omega
      have hleft := ihLeft certificateCodeLength hleftCode
      have hlocal := localConnectorAssemblyCost_le_small
        (CheckedUnaryReplacementCertificate.disjunctionLeft leftCertificate)
        certificateCodeLength hcertificate
      change CertifiedPAContextProof.disjunctionFullAssemblyCost
          (parameterEqualityContext left right) leftFormula rightFormula <=
        smallContextAssemblyEnvelope
          (replacementSyntaxEnvelope left right certificateCodeLength)
        at hlocal
      simp only [connectorAssemblyCostSum, replacementNodeCount,
        FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.nodeCount]
      calc
        connectorAssemblyCostSum leftCertificate +
              CertifiedPAContextProof.disjunctionFullAssemblyCost
                (parameterEqualityContext left right)
                leftFormula rightFormula <=
            replacementNodeCount leftCertificate *
                smallContextAssemblyEnvelope
                  (replacementSyntaxEnvelope left right certificateCodeLength) +
              smallContextAssemblyEnvelope
                (replacementSyntaxEnvelope left right certificateCodeLength) := by
          omega
        _ = (1 + replacementNodeCount leftCertificate) *
              smallContextAssemblyEnvelope
                (replacementSyntaxEnvelope left right certificateCodeLength) := by
          ring
  | @disjunctionRight leftFormula rightFormula rightCertificate ihRight =>
      have hrightCode : (proofFreeCode rightCertificate).length <=
          certificateCodeLength := by
        apply le_trans ?_ hcertificate
        simp [FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.proofFreeCode]
        omega
      have hright := ihRight certificateCodeLength hrightCode
      have hlocal := localConnectorAssemblyCost_le_small
        (CheckedUnaryReplacementCertificate.disjunctionRight rightCertificate)
        certificateCodeLength hcertificate
      change CertifiedPAContextProof.disjunctionFullAssemblyCost
          (parameterEqualityContext left right) leftFormula rightFormula <=
        smallContextAssemblyEnvelope
          (replacementSyntaxEnvelope left right certificateCodeLength)
        at hlocal
      simp only [connectorAssemblyCostSum, replacementNodeCount,
        FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.nodeCount]
      calc
        connectorAssemblyCostSum rightCertificate +
              CertifiedPAContextProof.disjunctionFullAssemblyCost
                (parameterEqualityContext left right)
                leftFormula rightFormula <=
            replacementNodeCount rightCertificate *
                smallContextAssemblyEnvelope
                  (replacementSyntaxEnvelope left right certificateCodeLength) +
              smallContextAssemblyEnvelope
                (replacementSyntaxEnvelope left right certificateCodeLength) := by
          omega
        _ = (1 + replacementNodeCount rightCertificate) *
              smallContextAssemblyEnvelope
                (replacementSyntaxEnvelope left right certificateCodeLength) := by
          ring
  | existsWitness body witness bodyCertificate ihBody =>
      have hbodyCode : (proofFreeCode bodyCertificate).length <=
          certificateCodeLength := by
        apply le_trans ?_ hcertificate
        simp [FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.proofFreeCode]
        omega
      have hbody := ihBody certificateCodeLength hbodyCode
      have hlocal := localConnectorAssemblyCost_le_small
        (CheckedUnaryReplacementCertificate.existsWitness
          body witness bodyCertificate)
        certificateCodeLength hcertificate
      change CertifiedPAContextProof.existsIntroFullAssemblyCost
          (parameterEqualityContext left right) body witness.term <=
        smallContextAssemblyEnvelope
          (replacementSyntaxEnvelope left right certificateCodeLength)
        at hlocal
      simp only [connectorAssemblyCostSum, replacementNodeCount,
        FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.nodeCount]
      calc
        connectorAssemblyCostSum bodyCertificate +
              CertifiedPAContextProof.existsIntroFullAssemblyCost
                (parameterEqualityContext left right) body witness.term <=
            replacementNodeCount bodyCertificate *
                smallContextAssemblyEnvelope
                  (replacementSyntaxEnvelope left right certificateCodeLength) +
              smallContextAssemblyEnvelope
                (replacementSyntaxEnvelope left right certificateCodeLength) := by
          omega
        _ = (1 + replacementNodeCount bodyCertificate) *
              smallContextAssemblyEnvelope
                (replacementSyntaxEnvelope left right certificateCodeLength) := by
          ring

theorem encodedLeafStructuralPayloadBound_le_atomic_add_uniformConnectors
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula) :
    encodedLeafStructuralPayloadBound certificate <=
      encodedAtomicLeafPayloadSum certificate +
        replacementNodeCount certificate *
          smallContextAssemblyEnvelope
            (replacementSyntaxEnvelope left right
              (proofFreeCode certificate).length) := by
  rw [encodedLeafStructuralPayloadBound_eq_atomic_add_connectors]
  exact Nat.add_le_add_left
    (connectorAssemblyCostSum_le_small_mul_nodeCount
      certificate (proofFreeCode certificate).length le_rfl) _

def atomicLeafUniformEnvelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (certificateCodeLength : Nat) : Nat :=
  verumProof.payloadLength +
    atomicTransportPayloadEnvelope left right certificateCodeLength
      (ClosedPAAtomicLiteralBounds.encodedPayloadPolynomial
        certificateCodeLength) + 1

theorem encodedAtomicLeafPayloadSum_le_uniform_mul_nodeCount
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula)
    (certificateCodeLength : Nat)
    (hcertificate : (proofFreeCode certificate).length <=
      certificateCodeLength) :
    encodedAtomicLeafPayloadSum certificate <=
      replacementNodeCount certificate *
        atomicLeafUniformEnvelope left right certificateCodeLength := by
  induction certificate generalizing certificateCodeLength with
  | verum =>
      simp only [encodedAtomicLeafPayloadSum, replacementNodeCount,
        FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.nodeCount,
        Nat.one_mul]
      unfold atomicLeafUniformEnvelope
      omega
  | positiveAtomic relationSymbol arguments literal sourceFormula hvalue =>
      have hfirst : (binaryTermCode (arguments 0)).length <=
          certificateCodeLength := by
        apply le_trans ?_ hcertificate
        simp [FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.proofFreeCode]
        omega
      have hsecond : (binaryTermCode (arguments 1)).length <=
          certificateCodeLength := by
        apply le_trans ?_ hcertificate
        simp [FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.proofFreeCode]
        omega
      have hliteral :
          (FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.proofFreeCode
            literal).length <= certificateCodeLength := by
        apply le_trans ?_ hcertificate
        simp [FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.proofFreeCode]
        omega
      have htransport :=
        positiveTransportUnderAssumptionStructuralPayloadBound_le_polynomial
          relationSymbol arguments left right
          (ClosedPAAtomicLiteralBounds.encodedPayloadPolynomial
            (FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.proofFreeCode
              literal).length)
          certificateCodeLength hfirst hsecond
      have hsource := ClosedPAAtomicLiteralBounds.encodedPayloadPolynomial_mono
        hliteral
      have hmono := atomicTransportPayloadEnvelope_mono left right
        (smallOpen := certificateCodeLength)
        (largeOpen := certificateCodeLength)
        le_rfl hsource
      have hleaf := htransport.trans hmono
      simp only [encodedAtomicLeafPayloadSum, replacementNodeCount,
        FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.nodeCount,
        Nat.one_mul]
      unfold atomicLeafUniformEnvelope
      omega
  | negativeAtomic relationSymbol arguments literal sourceFormula hvalue =>
      have hfirst : (binaryTermCode (arguments 0)).length <=
          certificateCodeLength := by
        apply le_trans ?_ hcertificate
        simp [FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.proofFreeCode]
        omega
      have hsecond : (binaryTermCode (arguments 1)).length <=
          certificateCodeLength := by
        apply le_trans ?_ hcertificate
        simp [FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.proofFreeCode]
        omega
      have hliteral :
          (FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.proofFreeCode
            literal).length <= certificateCodeLength := by
        apply le_trans ?_ hcertificate
        simp [FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.proofFreeCode]
        omega
      have htransport :=
        negativeTransportUnderAssumptionStructuralPayloadBound_le_polynomial
          relationSymbol arguments left right
          (ClosedPAAtomicLiteralBounds.encodedPayloadPolynomial
            (FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.proofFreeCode
              literal).length)
          certificateCodeLength hfirst hsecond
      have hsource := ClosedPAAtomicLiteralBounds.encodedPayloadPolynomial_mono
        hliteral
      have hmono := atomicTransportPayloadEnvelope_mono left right
        (smallOpen := certificateCodeLength)
        (largeOpen := certificateCodeLength)
        le_rfl hsource
      have hleaf := htransport.trans hmono
      simp only [encodedAtomicLeafPayloadSum, replacementNodeCount,
        FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.nodeCount,
        Nat.one_mul]
      unfold atomicLeafUniformEnvelope
      omega
  | @conjunction leftFormula rightFormula leftCertificate rightCertificate ihLeft ihRight =>
      have hleftCode : (proofFreeCode leftCertificate).length <=
          certificateCodeLength := by
        apply le_trans ?_ hcertificate
        simp [FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.proofFreeCode]
        omega
      have hrightCode : (proofFreeCode rightCertificate).length <=
          certificateCodeLength := by
        apply le_trans ?_ hcertificate
        simp [FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.proofFreeCode]
        omega
      have hleft := ihLeft certificateCodeLength hleftCode
      have hright := ihRight certificateCodeLength hrightCode
      simp only [encodedAtomicLeafPayloadSum, replacementNodeCount,
        FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.nodeCount]
      calc
        encodedAtomicLeafPayloadSum leftCertificate +
              encodedAtomicLeafPayloadSum rightCertificate <=
            replacementNodeCount leftCertificate *
                atomicLeafUniformEnvelope
                  left right certificateCodeLength +
              replacementNodeCount rightCertificate *
                atomicLeafUniformEnvelope
                  left right certificateCodeLength := by
          omega
        _ = (replacementNodeCount leftCertificate +
              replacementNodeCount rightCertificate) *
                atomicLeafUniformEnvelope
                  left right certificateCodeLength := by
          ring
        _ <= (1 + replacementNodeCount leftCertificate +
              replacementNodeCount rightCertificate) *
                atomicLeafUniformEnvelope
                  left right certificateCodeLength := by
          gcongr
          omega
  | @disjunctionLeft leftFormula rightFormula leftCertificate ihLeft =>
      have hleftCode : (proofFreeCode leftCertificate).length <=
          certificateCodeLength := by
        apply le_trans ?_ hcertificate
        simp [FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.proofFreeCode]
        omega
      have hleft := ihLeft certificateCodeLength hleftCode
      simp only [encodedAtomicLeafPayloadSum, replacementNodeCount,
        FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.nodeCount]
      calc
        encodedAtomicLeafPayloadSum leftCertificate <=
            replacementNodeCount leftCertificate *
              atomicLeafUniformEnvelope
                left right certificateCodeLength := hleft
        _ <= (1 + replacementNodeCount leftCertificate) *
              atomicLeafUniformEnvelope
                left right certificateCodeLength := by
          exact Nat.mul_le_mul_right _ (by omega)
  | @disjunctionRight leftFormula rightFormula rightCertificate ihRight =>
      have hrightCode : (proofFreeCode rightCertificate).length <=
          certificateCodeLength := by
        apply le_trans ?_ hcertificate
        simp [FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.proofFreeCode]
        omega
      have hright := ihRight certificateCodeLength hrightCode
      simp only [encodedAtomicLeafPayloadSum, replacementNodeCount,
        FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.nodeCount]
      calc
        encodedAtomicLeafPayloadSum rightCertificate <=
            replacementNodeCount rightCertificate *
              atomicLeafUniformEnvelope
                left right certificateCodeLength := hright
        _ <= (1 + replacementNodeCount rightCertificate) *
              atomicLeafUniformEnvelope
                left right certificateCodeLength := by
          exact Nat.mul_le_mul_right _ (by omega)
  | existsWitness body witness bodyCertificate ihBody =>
      have hbodyCode : (proofFreeCode bodyCertificate).length <=
          certificateCodeLength := by
        apply le_trans ?_ hcertificate
        simp [FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.proofFreeCode]
        omega
      have hbody := ihBody certificateCodeLength hbodyCode
      simp only [encodedAtomicLeafPayloadSum, replacementNodeCount,
        FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.nodeCount]
      calc
        encodedAtomicLeafPayloadSum bodyCertificate <=
            replacementNodeCount bodyCertificate *
              atomicLeafUniformEnvelope
                left right certificateCodeLength := hbody
        _ <= (1 + replacementNodeCount bodyCertificate) *
              atomicLeafUniformEnvelope
                left right certificateCodeLength := by
          exact Nat.mul_le_mul_right _ (by omega)

def replacementPayloadPolynomial
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (certificateCodeLength : Nat) : Nat :=
  certificateCodeLength *
    (atomicLeafUniformEnvelope left right certificateCodeLength +
      smallContextAssemblyEnvelope
        (replacementSyntaxEnvelope left right certificateCodeLength) + 1)

theorem encodedLeafStructuralPayloadBound_le_polynomial
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula) :
    encodedLeafStructuralPayloadBound certificate <=
      replacementPayloadPolynomial left right
        (proofFreeCode certificate).length := by
  let codeLength := (proofFreeCode certificate).length
  let leafEnvelope := atomicLeafUniformEnvelope left right codeLength
  let connectorEnvelope := smallContextAssemblyEnvelope
    (replacementSyntaxEnvelope left right codeLength)
  have hatomic := encodedAtomicLeafPayloadSum_le_uniform_mul_nodeCount
    certificate codeLength le_rfl
  have hconnectors := connectorAssemblyCostSum_le_small_mul_nodeCount
    certificate codeLength le_rfl
  have hnodes :=
    FoundationCompactPABoundedUniversalCertificateCode.CheckedUnaryReplacementCertificate.nodeCount_le_proofFreeCode_length
      certificate
  rw [encodedLeafStructuralPayloadBound_eq_atomic_add_connectors]
  calc
    encodedAtomicLeafPayloadSum certificate +
          connectorAssemblyCostSum certificate <=
        replacementNodeCount certificate * leafEnvelope +
          replacementNodeCount certificate * connectorEnvelope := by
      exact Nat.add_le_add hatomic hconnectors
    _ = replacementNodeCount certificate *
          (leafEnvelope + connectorEnvelope) := by ring
    _ <= codeLength * (leafEnvelope + connectorEnvelope) :=
      Nat.mul_le_mul_right _ hnodes
    _ <= codeLength * (leafEnvelope + connectorEnvelope + 1) := by
      exact Nat.mul_le_mul_left codeLength (by omega)
    _ = replacementPayloadPolynomial left right codeLength := by
      rfl

theorem structuralPayloadBound_le_encodedLeaf
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula) :
    structuralPayloadBound certificate <=
      encodedLeafStructuralPayloadBound certificate := by
  induction certificate with
  | verum => exact le_rfl
  | positiveAtomic relationSymbol arguments literal sourceFormula hvalue =>
      have hsource := ClosedPAAtomicLiteralBounds.payloadPolynomial_le_encoded
        literal
      simp only [
        structuralPayloadBound,
        encodedLeafStructuralPayloadBound]
      exact positiveTransportUnderAssumptionStructuralPayloadBound_mono_source
        relationSymbol arguments left right hsource
  | negativeAtomic relationSymbol arguments literal sourceFormula hvalue =>
      have hsource := ClosedPAAtomicLiteralBounds.payloadPolynomial_le_encoded
        literal
      simp only [
        structuralPayloadBound,
        encodedLeafStructuralPayloadBound]
      exact negativeTransportUnderAssumptionStructuralPayloadBound_mono_source
        relationSymbol arguments left right hsource
  | conjunction leftCertificate rightCertificate ihLeft ihRight =>
      simp only [
        structuralPayloadBound,
        encodedLeafStructuralPayloadBound]
      omega
  | @disjunctionLeft leftFormula rightFormula leftCertificate ihLeft =>
      simp only [
        structuralPayloadBound,
        encodedLeafStructuralPayloadBound]
      omega
  | @disjunctionRight leftFormula rightFormula rightCertificate ihRight =>
      simp only [
        structuralPayloadBound,
        encodedLeafStructuralPayloadBound]
      omega
  | existsWitness body witness bodyCertificate ihBody =>
      simp only [
        structuralPayloadBound,
        encodedLeafStructuralPayloadBound]
      omega

theorem compileUnderAssumption_payloadLength_le_encodedLeaf
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula) :
    certificate.compileUnderAssumption.payloadLength <=
      encodedLeafStructuralPayloadBound certificate := by
  have hstructural :=
    compileUnderAssumption_payloadLength_le_structuralPayloadBound certificate
  exact hstructural.trans (structuralPayloadBound_le_encodedLeaf certificate)

theorem compileUnderAssumption_payloadLength_le_polynomial
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula) :
    certificate.compileUnderAssumption.payloadLength <=
      replacementPayloadPolynomial left right
        (proofFreeCode certificate).length :=
  (compileUnderAssumption_payloadLength_le_encodedLeaf certificate).trans
    (encodedLeafStructuralPayloadBound_le_polynomial certificate)

end CheckedUnaryReplacementCertificate

/-! ## One replacement envelope for every finite branch -/

def boundedUniversalClosedTermEnvelope (resource : Nat) : Nat :=
  finiteClosedTermEnvelope
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0) resource

def boundedUniversalReplacementSyntaxEnvelope
    (closedTermCodeBound certificateCodeLength : Nat) : Nat :=
  certificateCodeLength +
    compilerTermCodeEnvelope certificateCodeLength certificateCodeLength +
    2 * paFormulaCodeEnvelope (2 * closedTermCodeBound) + 1

theorem replacementSyntaxEnvelope_le_boundedUniversal
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (closedTermCodeBound certificateCodeLength : Nat)
    (hleft : (binaryTermCode left).length <= closedTermCodeBound)
    (hright : (binaryTermCode right).length <= closedTermCodeBound) :
    replacementSyntaxEnvelope left right certificateCodeLength <=
      boundedUniversalReplacementSyntaxEnvelope
        closedTermCodeBound certificateCodeLength := by
  have hterms :
      (binaryTermCode left).length + (binaryTermCode right).length <=
        2 * closedTermCodeBound := by omega
  have hformula := paFormulaCodeEnvelope_mono_local hterms
  unfold replacementSyntaxEnvelope
    boundedUniversalReplacementSyntaxEnvelope
  dsimp only
  omega

def boundedUniversalAtomicLeafEnvelope
    (closedTermCodeBound certificateCodeLength : Nat) : Nat :=
  verumProof.payloadLength +
    uniformAtomicTransportPayloadEnvelope
      closedTermCodeBound certificateCodeLength
      (ClosedPAAtomicLiteralBounds.encodedPayloadPolynomial
        certificateCodeLength) + 1

theorem atomicLeafUniformEnvelope_le_boundedUniversal
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (closedTermCodeBound certificateCodeLength : Nat)
    (hleft : (binaryTermCode left).length <= closedTermCodeBound)
    (hright : (binaryTermCode right).length <= closedTermCodeBound) :
    CheckedUnaryReplacementCertificate.atomicLeafUniformEnvelope
        left right certificateCodeLength <=
      boundedUniversalAtomicLeafEnvelope
        closedTermCodeBound certificateCodeLength := by
  have htransport := atomicTransportPayloadEnvelope_le_uniform
    left right closedTermCodeBound certificateCodeLength
    (ClosedPAAtomicLiteralBounds.encodedPayloadPolynomial
      certificateCodeLength) hleft hright
  unfold CheckedUnaryReplacementCertificate.atomicLeafUniformEnvelope
    boundedUniversalAtomicLeafEnvelope
  omega

def boundedUniversalReplacementPayloadEnvelope
    (closedTermCodeBound certificateCodeLength : Nat) : Nat :=
  certificateCodeLength *
    (boundedUniversalAtomicLeafEnvelope
        closedTermCodeBound certificateCodeLength +
      smallContextAssemblyEnvelope
        (boundedUniversalReplacementSyntaxEnvelope
          closedTermCodeBound certificateCodeLength) + 1)

theorem encodedLeafStructuralPayloadBound_le_boundedUniversal
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula)
    (closedTermCodeBound certificateCodeLength : Nat)
    (hleft : (binaryTermCode left).length <= closedTermCodeBound)
    (hright : (binaryTermCode right).length <= closedTermCodeBound)
    (hcertificate :
      (CheckedUnaryReplacementCertificate.proofFreeCode certificate).length <=
        certificateCodeLength) :
    CheckedUnaryReplacementCertificate.encodedLeafStructuralPayloadBound
        certificate <=
      boundedUniversalReplacementPayloadEnvelope
        closedTermCodeBound certificateCodeLength := by
  let nodeCount := CheckedUnaryReplacementCertificate.replacementNodeCount
    certificate
  let leafEnvelope := boundedUniversalAtomicLeafEnvelope
    closedTermCodeBound certificateCodeLength
  let syntaxEnvelope := boundedUniversalReplacementSyntaxEnvelope
    closedTermCodeBound certificateCodeLength
  have hatomic :=
    CheckedUnaryReplacementCertificate.encodedAtomicLeafPayloadSum_le_uniform_mul_nodeCount
      certificate certificateCodeLength hcertificate
  have hconnectors :=
    CheckedUnaryReplacementCertificate.connectorAssemblyCostSum_le_small_mul_nodeCount
      certificate certificateCodeLength hcertificate
  have hleaf := atomicLeafUniformEnvelope_le_boundedUniversal
    left right closedTermCodeBound certificateCodeLength hleft hright
  have hsyntax := replacementSyntaxEnvelope_le_boundedUniversal
    left right closedTermCodeBound certificateCodeLength hleft hright
  have hcontext := smallContextAssemblyEnvelope_mono_local hsyntax
  have hnodes :=
    CheckedUnaryReplacementCertificate.nodeCount_le_proofFreeCode_length
      certificate
  rw [CheckedUnaryReplacementCertificate.encodedLeafStructuralPayloadBound_eq_atomic_add_connectors]
  calc
    CheckedUnaryReplacementCertificate.encodedAtomicLeafPayloadSum certificate +
          CheckedUnaryReplacementCertificate.connectorAssemblyCostSum
            certificate <=
        nodeCount * leafEnvelope +
          nodeCount * smallContextAssemblyEnvelope syntaxEnvelope := by
      exact Nat.add_le_add
        (hatomic.trans (Nat.mul_le_mul_left nodeCount hleaf))
        (hconnectors.trans (Nat.mul_le_mul_left nodeCount hcontext))
    _ = nodeCount *
        (leafEnvelope + smallContextAssemblyEnvelope syntaxEnvelope) := by
      ring
    _ <= certificateCodeLength *
        (leafEnvelope + smallContextAssemblyEnvelope syntaxEnvelope) := by
      exact Nat.mul_le_mul_right _ (hnodes.trans hcertificate)
    _ <= certificateCodeLength *
        (leafEnvelope + smallContextAssemblyEnvelope syntaxEnvelope + 1) := by
      exact Nat.mul_le_mul_left certificateCodeLength (by omega)
    _ = boundedUniversalReplacementPayloadEnvelope
        closedTermCodeBound certificateCodeLength := by
      rfl

/-! ## One syntax coordinate for the complete bounded-universal compiler -/

def boundedUniversalSyntaxSeed (resource : Nat) : Nat :=
  resource +
    (binaryTermCode
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)).length + 1

def boundedUniversalClosedBodyCodeEnvelope (resource : Nat) : Nat :=
  substitutionFormulaCodeEnvelope
    (boundedUniversalSyntaxSeed resource)
    (boundedUniversalSyntaxSeed resource)

def boundedUniversalClosedFormulaEnvelope (resource : Nat) : Nat :=
  32 * (boundedUniversalClosedBodyCodeEnvelope resource +
    finiteCaseFormulaEnvelope
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0) resource +
    (binaryNatCode 5).length + 1)

theorem closedBodyInstance_code_le_envelope
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (resource : Nat)
    (hbody : (binaryFormulaCode body).length <= resource) :
    (binaryFormulaCode
      (body/[(&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)])).length <=
      boundedUniversalClosedBodyCodeEnvelope resource := by
  let seed := boundedUniversalSyntaxSeed resource
  have hformula : (binaryFormulaCode body).length <= seed := by
    dsimp only [seed]
    unfold boundedUniversalSyntaxSeed
    omega
  have hwitness :
      (binaryTermCode
        (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)).length <= seed := by
    dsimp only [seed]
    unfold boundedUniversalSyntaxSeed
    omega
  have hsubstitution :=
    binaryFormulaCode_substitution_one_length_le_envelope
      body (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      seed seed hformula hwitness
  unfold boundedUniversalClosedBodyCodeEnvelope
  dsimp only [seed] at hsubstitution ⊢
  exact hsubstitution

theorem closedBodyInstance_code_le_boundedUniversal
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (resource : Nat)
    (hbody : (binaryFormulaCode body).length <= resource) :
    (binaryFormulaCode
      (body/[(&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)])).length <=
      boundedUniversalClosedFormulaEnvelope resource := by
  have htight := closedBodyInstance_code_le_envelope body resource hbody
  unfold boundedUniversalClosedFormulaEnvelope
  omega

theorem finiteBoundFormula_code_le_caseEnvelope_tight
    (bound resource : Nat) (hbound : bound <= resource) :
    (binaryFormulaCode (finiteBoundFormula bound)).length <=
      finiteCaseFormulaEnvelope
        (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0) resource := by
  let subject := (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
  let boundTerm := iteratedSuccessorTerm 0 bound
  have htermRaw := iteratedSuccessorTerm_code_length_le_polynomial 0 bound
  have htermMono := iteratedSuccessorTermCodePolynomial_mono
    0 (show bound <= resource + 2 by omega)
  have hformula := finiteCaseLessThanFormula_code_length_le
    subject boundTerm
  unfold finiteBoundFormula finiteCaseFormulaEnvelope
    finiteLowerBoundFormulaCodePolynomial
  dsimp only [subject, boundTerm] at hformula ⊢
  omega

theorem finiteBoundFormula_code_le_boundedUniversal
    (bound resource : Nat) (hbound : bound <= resource) :
    (binaryFormulaCode (finiteBoundFormula bound)).length <=
      boundedUniversalClosedFormulaEnvelope resource := by
  have htight := finiteBoundFormula_code_le_caseEnvelope_tight
    bound resource hbound
  unfold boundedUniversalClosedFormulaEnvelope
  omega

theorem negatedFiniteBoundFormula_code_le_boundedUniversal
    (bound resource : Nat) (hbound : bound <= resource) :
    (binaryFormulaCode (∼finiteBoundFormula bound)).length <=
      boundedUniversalClosedFormulaEnvelope resource := by
  have hnegative := finiteLowerBoundFormula_code_le_caseEnvelope
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    bound resource (by omega)
  simpa only [finiteBoundFormula, finiteLowerBoundFormula] using
    hnegative.trans (by
      unfold boundedUniversalClosedFormulaEnvelope
      omega)

theorem doubleNegatedFiniteBoundFormula_code_le_boundedUniversal
    (bound resource : Nat) (hbound : bound <= resource) :
    (binaryFormulaCode (∼finiteLowerBoundFormula bound (&0))).length <=
      boundedUniversalClosedFormulaEnvelope resource := by
  have hnegative := finiteLowerBoundFormula_code_le_caseEnvelope
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    bound resource (by omega)
  have hraw := binaryFormulaCode_neg_length_le
    (finiteLowerBoundFormula bound
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0))
  unfold boundedUniversalClosedFormulaEnvelope
  omega

theorem negatedFalse_code_le_boundedUniversal
    (resource : Nat) :
    (binaryFormulaCode
      (∼(⊥ : LO.FirstOrder.ArithmeticProposition))).length <=
      boundedUniversalClosedFormulaEnvelope resource := by
  have hfalse := negatedFalse_code_le_caseEnvelope
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0) resource
  unfold boundedUniversalClosedFormulaEnvelope
  omega

theorem finiteEqualityCases_code_le_boundedUniversal
    (index resource : Nat) (hindex : index <= resource + 2) :
    (binaryFormulaCode
      (finiteEqualityCases
        (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0) index)).length <=
      boundedUniversalClosedFormulaEnvelope resource := by
  have hcases := finiteEqualityCases_code_le_caseEnvelope
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    index resource hindex
  unfold boundedUniversalClosedFormulaEnvelope
  omega

theorem negatedFiniteEqualityCases_code_le_boundedUniversal
    (index resource : Nat) (hindex : index <= resource + 2) :
    (binaryFormulaCode
      (∼finiteEqualityCases
        (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0) index)).length <=
      boundedUniversalClosedFormulaEnvelope resource := by
  have hcases := negatedFiniteEqualityCases_code_le_caseEnvelope
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    index resource hindex
  unfold boundedUniversalClosedFormulaEnvelope
  omega

theorem finiteCaseEqualityFormula_code_le_boundedUniversal
    (index resource : Nat) (hindex : index <= resource + 2) :
    (binaryFormulaCode
      (finiteCaseEqualityFormula
        (iteratedSuccessorTerm 0 index) (&0))).length <=
      boundedUniversalClosedFormulaEnvelope resource := by
  have hequality := finiteCaseEqualityFormula_code_le_caseEnvelope
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    index resource hindex
  unfold boundedUniversalClosedFormulaEnvelope
  omega

theorem negatedFiniteCaseEqualityFormula_code_le_boundedUniversal
    (index resource : Nat) (hindex : index <= resource + 2) :
    (binaryFormulaCode
      (∼finiteCaseEqualityFormula
        (iteratedSuccessorTerm 0 index) (&0))).length <=
      boundedUniversalClosedFormulaEnvelope resource := by
  have hequality := negatedFiniteCaseEqualityFormula_code_le_caseEnvelope
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    index resource hindex
  unfold boundedUniversalClosedFormulaEnvelope
  omega

theorem finiteLowerBoundFormula_code_le_boundedUniversal
    (bound resource : Nat) (hbound : bound <= resource) :
    (binaryFormulaCode (finiteLowerBoundFormula bound (&0))).length <=
      boundedUniversalClosedFormulaEnvelope resource := by
  simpa only [finiteLowerBoundFormula, finiteBoundFormula] using
    negatedFiniteBoundFormula_code_le_boundedUniversal
      bound resource hbound

theorem finiteExhaustionFormula_code_le_boundedUniversal
    (bound resource : Nat) (hbound : bound <= resource) :
    (binaryFormulaCode (finiteExhaustionFormula bound (&0))).length <=
      boundedUniversalClosedFormulaEnvelope resource := by
  have hexhaustion := finiteExhaustionFormula_code_le_caseEnvelope
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    bound resource (by omega)
  unfold boundedUniversalClosedFormulaEnvelope
  omega

theorem negatedFiniteExhaustionFormula_code_le_boundedUniversal
    (bound resource : Nat) (hbound : bound <= resource) :
    (binaryFormulaCode (∼finiteExhaustionFormula bound (&0))).length <=
      boundedUniversalClosedFormulaEnvelope resource := by
  have hexhaustion := negatedFiniteExhaustionFormula_code_le_caseEnvelope
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    bound resource (by omega)
  unfold boundedUniversalClosedFormulaEnvelope
  omega

theorem boundedImplication_code_le_boundedUniversal
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (resource : Nat)
    (hbound : bound <= resource)
    (hbody : (binaryFormulaCode body).length <= resource) :
    (binaryFormulaCode
      (finiteBoundFormula bound 🡒
        body/[(&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)])).length <=
      boundedUniversalClosedFormulaEnvelope resource := by
  have hantecedentTight := finiteBoundFormula_code_le_caseEnvelope_tight
    bound resource hbound
  have hconsequent := closedBodyInstance_code_le_envelope
    body resource hbody
  have hraw := binaryFormulaCode_implication_length_le
    (finiteBoundFormula bound)
    (body/[(&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)])
  unfold boundedUniversalClosedFormulaEnvelope
  omega

theorem finiteBoundContext_formulaCodeBound_boundedUniversal
    (bound resource : Nat) (hbound : bound <= resource) :
    FormulaCodeBound (finiteBoundContext bound)
      (boundedUniversalClosedFormulaEnvelope resource) := by
  intro formula hformula
  simp only [finiteBoundContext, Finset.mem_singleton] at hformula
  subst formula
  exact negatedFiniteBoundFormula_code_le_boundedUniversal
    bound resource hbound

def boundedUniversalOpenBodyCodeEnvelope (resource : Nat) : Nat :=
  16 * (finiteLowerBoundFormulaCodePolynomial
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) resource +
    resource + (binaryNatCode 5).length + 1)

theorem finiteBoundedUniversalBody_code_le_envelope
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (resource : Nat)
    (hbound : bound <= resource)
    (hbody : (binaryFormulaCode body).length <= resource) :
    (binaryFormulaCode (finiteBoundedUniversalBody bound body)).length <=
      boundedUniversalOpenBodyCodeEnvelope resource := by
  let subject := (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)
  let boundTerm := iteratedSuccessorTerm 1 bound
  let antecedent := finiteCaseLessThanFormula subject boundTerm
  have htermRaw := iteratedSuccessorTerm_code_length_le_polynomial 1 bound
  have htermMono := iteratedSuccessorTermCodePolynomial_mono 1 hbound
  have hantecedentRaw := finiteCaseLessThanFormula_code_length_le
    subject boundTerm
  have hantecedent :
      (binaryFormulaCode antecedent).length <=
        finiteLowerBoundFormulaCodePolynomial subject resource := by
    dsimp only [antecedent, boundTerm, subject] at hantecedentRaw ⊢
    unfold finiteLowerBoundFormulaCodePolynomial
    omega
  have himplication := binarySemiformulaCode_implication_length_le
    antecedent body
  unfold finiteBoundedUniversalBody boundedUniversalOpenBodyCodeEnvelope
  dsimp only [antecedent, boundTerm, subject] at himplication hantecedent ⊢
  omega

namespace CheckedFiniteUniversalBranches

open FoundationCompactPABoundedUniversalCompilerBounds.CheckedFiniteUniversalBranches

def encodedLeafStructuralPayloadBound
    (totalBound : Nat)
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1} :
    {caseCount : Nat} →
      CheckedFiniteUniversalBranches body caseCount → Nat
  | 0, .nil =>
      CertifiedPAContextProof.exFalsoAssumptionFullPayloadCost (body/[&0]) +
        FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
          (insert (body/[&0])
            (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
              (finiteBoundContext totalBound)))
  | bound + 1, .snoc initial last =>
      encodedLeafStructuralPayloadBound totalBound initial +
        (CheckedUnaryReplacementCertificate.encodedLeafStructuralPayloadBound
            last +
          FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
            (insert (body/[&0])
              (insert
                (∼finiteCaseEqualityFormula
                  (iteratedSuccessorTerm 0 bound) (&0))
                (finiteBoundContext totalBound)))) +
        CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
          (finiteBoundContext totalBound) (body/[&0])
          (finiteEqualityCases (&0) bound)
          (finiteCaseEqualityFormula
            (iteratedSuccessorTerm 0 bound) (&0))

theorem structuralPayloadBound_le_encodedLeaf
    (totalBound : Nat)
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    {caseCount : Nat}
    (branches : CheckedFiniteUniversalBranches body caseCount) :
    structuralPayloadBound totalBound branches <=
      encodedLeafStructuralPayloadBound totalBound branches := by
  induction branches with
  | nil => exact le_rfl
  | @snoc bound initial last ih =>
      have hlast :=
        CheckedUnaryReplacementCertificate.structuralPayloadBound_le_encodedLeaf
          last
      simp only [
        structuralPayloadBound,
        encodedLeafStructuralPayloadBound]
      omega

theorem compileCasesUnderBoundAssumption_payloadLength_le_encodedLeaf
    (totalBound : Nat)
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    {caseCount : Nat}
    (branches : CheckedFiniteUniversalBranches body caseCount) :
    (branches.compileCasesUnderBoundAssumption totalBound).payloadLength <=
      encodedLeafStructuralPayloadBound totalBound branches := by
  have hstructural :=
    compileCasesUnderBoundAssumption_payloadLength_le_structural
      totalBound branches
  exact hstructural.trans
    (structuralPayloadBound_le_encodedLeaf totalBound branches)

def boundedUniversalBranchLocalPayloadEnvelope (resource : Nat) : Nat :=
  boundedUniversalReplacementPayloadEnvelope
      (boundedUniversalClosedTermEnvelope resource) resource +
    2 * smallContextAssemblyEnvelope
      (boundedUniversalClosedFormulaEnvelope resource)

def boundedUniversalBranchPayloadPolynomial (resource : Nat) : Nat :=
  (resource + 1) * boundedUniversalBranchLocalPayloadEnvelope resource

theorem encodedLeafStructuralPayloadBound_le_caseCount_mul_local
    (totalBound resource : Nat)
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    {caseCount : Nat}
    (branches : CheckedFiniteUniversalBranches body caseCount)
    (hbody : (binaryFormulaCode body).length <= resource)
    (htotalBound : totalBound <= resource)
    (hcaseCount : caseCount <= totalBound)
    (hcode :
      (FoundationCompactPABoundedUniversalCertificateCode.CheckedFiniteUniversalBranches.proofFreeCode
        branches).length <= resource) :
    encodedLeafStructuralPayloadBound totalBound branches <=
      (caseCount + 1) *
        boundedUniversalBranchLocalPayloadEnvelope resource := by
  induction branches generalizing totalBound resource with
  | nil =>
      let target := body/[(&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)]
      let formulaEnvelope := boundedUniversalClosedFormulaEnvelope resource
      let localEnvelope := boundedUniversalBranchLocalPayloadEnvelope resource
      have htarget : (binaryFormulaCode target).length <= formulaEnvelope := by
        dsimp only [target, formulaEnvelope]
        exact closedBodyInstance_code_le_boundedUniversal body resource hbody
      have hfalse :
          (binaryFormulaCode
            (∼(⊥ : LO.FirstOrder.ArithmeticProposition))).length <=
            formulaEnvelope := by
        dsimp only [formulaEnvelope]
        exact negatedFalse_code_le_boundedUniversal resource
      have hboundContext : FormulaCodeBound
          (finiteBoundContext totalBound) formulaEnvelope := by
        dsimp only [formulaEnvelope]
        exact finiteBoundContext_formulaCodeBound_boundedUniversal
          totalBound resource htotalBound
      have hweakContext : FormulaCodeBound
          (insert target
            (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
              (finiteBoundContext totalBound))) formulaEnvelope :=
        (hboundContext.insert hfalse).insert htarget
      have hweakCard :
          (insert target
            (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
              (finiteBoundContext totalBound))).card <= 8 := by
        have hbase : (finiteBoundContext totalBound).card <= 1 := by
          simp [finiteBoundContext]
        have hfirst := Finset.card_insert_le
          (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
          (finiteBoundContext totalBound)
        have hsecond := Finset.card_insert_le target
          (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
            (finiteBoundContext totalBound))
        omega
      have hexFalso := exFalsoAssumptionFullPayloadCost_le_small
        target formulaEnvelope htarget hfalse
      have hweakening := weakeningFullAssemblyCost_le_small
        (insert target
          (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
            (finiteBoundContext totalBound)))
        formulaEnvelope hweakCard hweakContext
      simp only [encodedLeafStructuralPayloadBound]
      dsimp only [target, formulaEnvelope, localEnvelope] at *
      unfold boundedUniversalBranchLocalPayloadEnvelope
      omega
  | @snoc bound initial last ih =>
      let target := body/[(&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)]
      let formulaEnvelope := boundedUniversalClosedFormulaEnvelope resource
      let localEnvelope := boundedUniversalBranchLocalPayloadEnvelope resource
      let termEnvelope := boundedUniversalClosedTermEnvelope resource
      have hbound : bound <= resource := by omega
      have hinitialCode :
          (FoundationCompactPABoundedUniversalCertificateCode.CheckedFiniteUniversalBranches.proofFreeCode
            initial).length <= resource := by
        apply le_trans ?_ hcode
        simp only [
          FoundationCompactPABoundedUniversalCertificateCode.CheckedFiniteUniversalBranches.proofFreeCode,
          List.length_append]
        omega
      have hlastCode :
          (CheckedUnaryReplacementCertificate.proofFreeCode last).length <=
            resource := by
        apply le_trans ?_ hcode
        simp only [
          FoundationCompactPABoundedUniversalCertificateCode.CheckedFiniteUniversalBranches.proofFreeCode,
          List.length_append]
        omega
      have hinitial := ih totalBound resource hbody htotalBound
        (by omega) hinitialCode
      have hleft :
          (binaryTermCode (iteratedSuccessorTerm 0 bound)).length <=
            termEnvelope := by
        dsimp only [termEnvelope, boundedUniversalClosedTermEnvelope]
        exact iteratedSuccessorTerm_code_le_finiteClosedTermEnvelope
          (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
          bound resource (by omega)
      have hright :
          (binaryTermCode
            (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)).length <=
            termEnvelope := by
        dsimp only [termEnvelope, boundedUniversalClosedTermEnvelope]
        exact subject_code_le_finiteClosedTermEnvelope
          (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0) resource
      have hlast := encodedLeafStructuralPayloadBound_le_boundedUniversal
        last termEnvelope resource hleft hright hlastCode
      have htarget : (binaryFormulaCode target).length <= formulaEnvelope := by
        dsimp only [target, formulaEnvelope]
        exact closedBodyInstance_code_le_boundedUniversal body resource hbody
      have hboundContext : FormulaCodeBound
          (finiteBoundContext totalBound) formulaEnvelope := by
        dsimp only [formulaEnvelope]
        exact finiteBoundContext_formulaCodeBound_boundedUniversal
          totalBound resource htotalBound
      have hnegatedCase :
          (binaryFormulaCode
            (∼finiteCaseEqualityFormula
              (iteratedSuccessorTerm 0 bound) (&0))).length <=
            formulaEnvelope := by
        dsimp only [formulaEnvelope]
        exact negatedFiniteCaseEqualityFormula_code_le_boundedUniversal
          bound resource (by omega)
      have hweakContext : FormulaCodeBound
          (insert target
            (insert
              (∼finiteCaseEqualityFormula
                (iteratedSuccessorTerm 0 bound) (&0))
              (finiteBoundContext totalBound))) formulaEnvelope :=
        (hboundContext.insert hnegatedCase).insert htarget
      have hweakCard :
          (insert target
            (insert
              (∼finiteCaseEqualityFormula
                (iteratedSuccessorTerm 0 bound) (&0))
              (finiteBoundContext totalBound))).card <= 8 := by
        have hbase : (finiteBoundContext totalBound).card <= 1 := by
          simp [finiteBoundContext]
        have hfirst := Finset.card_insert_le
          (∼finiteCaseEqualityFormula
            (iteratedSuccessorTerm 0 bound) (&0))
          (finiteBoundContext totalBound)
        have hsecond := Finset.card_insert_le target
          (insert
            (∼finiteCaseEqualityFormula
              (iteratedSuccessorTerm 0 bound) (&0))
            (finiteBoundContext totalBound))
        omega
      have hweakening := weakeningFullAssemblyCost_le_small
        (insert target
          (insert
            (∼finiteCaseEqualityFormula
              (iteratedSuccessorTerm 0 bound) (&0))
            (finiteBoundContext totalBound)))
        formulaEnvelope hweakCard hweakContext
      have hnegatedLeft :
          (binaryFormulaCode
            (∼finiteEqualityCases
              (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0) bound)).length <=
            formulaEnvelope := by
        dsimp only [formulaEnvelope]
        exact negatedFiniteEqualityCases_code_le_boundedUniversal
          bound resource (by omega)
      have hnegatedRight :
          (binaryFormulaCode
            (∼finiteCaseEqualityFormula
              (iteratedSuccessorTerm 0 bound) (&0))).length <=
            formulaEnvelope := hnegatedCase
      have hnegatedDisjunction :
          (binaryFormulaCode
            (∼(finiteEqualityCases (&0) bound ⋎
              finiteCaseEqualityFormula
                (iteratedSuccessorTerm 0 bound) (&0)))).length <=
            formulaEnvelope := by
        have hnext := negatedFiniteEqualityCases_code_le_boundedUniversal
          (bound + 1) resource (by omega)
        simpa only [finiteEqualityCases_succ] using hnext
      have heliminate :=
        eliminateDisjunctionAssumptionFullAssemblyCost_le_small
          (finiteBoundContext totalBound) target
          (finiteEqualityCases (&0) bound)
          (finiteCaseEqualityFormula
            (iteratedSuccessorTerm 0 bound) (&0))
          formulaEnvelope (by simp [finiteBoundContext])
          hboundContext htarget hnegatedLeft hnegatedRight
          hnegatedDisjunction
      have hlocal :
          CheckedUnaryReplacementCertificate.encodedLeafStructuralPayloadBound
                last +
              FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
                (insert target
                  (insert
                    (∼finiteCaseEqualityFormula
                      (iteratedSuccessorTerm 0 bound) (&0))
                    (finiteBoundContext totalBound))) +
            CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
              (finiteBoundContext totalBound) target
              (finiteEqualityCases (&0) bound)
              (finiteCaseEqualityFormula
                (iteratedSuccessorTerm 0 bound) (&0)) <= localEnvelope := by
        dsimp only [formulaEnvelope] at hweakening heliminate
        dsimp only [localEnvelope, termEnvelope] at hlast ⊢
        unfold boundedUniversalBranchLocalPayloadEnvelope
        omega
      simp only [encodedLeafStructuralPayloadBound]
      dsimp only [target, formulaEnvelope, localEnvelope] at hinitial hlocal ⊢
      have hcombined := Nat.add_le_add hinitial hlocal
      calc
        _ <=
            (bound + 1) * boundedUniversalBranchLocalPayloadEnvelope resource +
              boundedUniversalBranchLocalPayloadEnvelope resource := by
          simpa only [Nat.add_assoc] using hcombined
        _ = (bound + 2) *
            boundedUniversalBranchLocalPayloadEnvelope resource := by
          ring

theorem encodedLeafStructuralPayloadBound_le_polynomial
    (totalBound resource : Nat)
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    {caseCount : Nat}
    (branches : CheckedFiniteUniversalBranches body caseCount)
    (hbody : (binaryFormulaCode body).length <= resource)
    (htotalBound : totalBound <= resource)
    (hcaseCount : caseCount <= totalBound)
    (hcode :
      (FoundationCompactPABoundedUniversalCertificateCode.CheckedFiniteUniversalBranches.proofFreeCode
        branches).length <= resource) :
    encodedLeafStructuralPayloadBound totalBound branches <=
      boundedUniversalBranchPayloadPolynomial resource := by
  have hscaled := encodedLeafStructuralPayloadBound_le_caseCount_mul_local
    totalBound resource branches hbody htotalBound hcaseCount hcode
  have hcoefficient : caseCount + 1 <= resource + 1 := by omega
  have hmul := Nat.mul_le_mul_right
    (boundedUniversalBranchLocalPayloadEnvelope resource) hcoefficient
  exact hscaled.trans (by
    unfold boundedUniversalBranchPayloadPolynomial
    exact hmul)

end CheckedFiniteUniversalBranches

/-! ## Fixed input-size bounds for the outer compiler assembly -/

def cumulativeFiniteExhaustionPayloadPolynomial (resource : Nat) : Nat :=
  ∑ bound ∈ Finset.range (resource + 1),
    finiteExhaustionPayloadPolynomial bound

theorem finiteExhaustionPayloadPolynomial_le_cumulative
    (bound resource : Nat) (hbound : bound <= resource) :
    finiteExhaustionPayloadPolynomial bound <=
      cumulativeFiniteExhaustionPayloadPolynomial resource := by
  have hmem : bound ∈ Finset.range (resource + 1) := by
    simp
    omega
  unfold cumulativeFiniteExhaustionPayloadPolynomial
  exact Finset.single_le_sum
    (f := finiteExhaustionPayloadPolynomial)
    (s := Finset.range (resource + 1))
    (fun candidate _ => Nat.zero_le
      (finiteExhaustionPayloadPolynomial candidate))
    hmem

def boundedUniversalFiniteExhaustionSpecializationEnvelope
    (resource : Nat) : Nat :=
  let formulaBound := finiteExhaustionFormulaCodePolynomial
    (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) resource
  let scale := formulaBound +
    (binaryTermCode
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)).length + 1
  192 + 2048 * scale * scale * scale

theorem finiteExhaustionSpecializationCost_le_boundedUniversal
    (bound resource : Nat) (hbound : bound <= resource) :
    specializationCost (finiteExhaustionBody bound) (&0) <=
      boundedUniversalFiniteExhaustionSpecializationEnvelope resource := by
  let formulaBound := finiteExhaustionFormulaCodePolynomial
    (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) resource
  let scale := formulaBound +
    (binaryTermCode
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)).length + 1
  have hformulaRaw := finiteExhaustionBody_code_length_le_polynomial bound
  have hformulaMono := finiteExhaustionFormulaCodePolynomial_mono
    (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) hbound
  have hformula :
      (binaryFormulaCode (finiteExhaustionBody bound)).length <=
        formulaBound := hformulaRaw.trans hformulaMono
  have hscale : specializationScale (finiteExhaustionBody bound) (&0) <=
      scale := by
    unfold specializationScale
    dsimp only [scale]
    omega
  unfold specializationCost
    boundedUniversalFiniteExhaustionSpecializationEnvelope
  dsimp only [formulaBound, scale]
  gcongr

theorem finiteExhaustionAtEigenvariableStructuralPayloadBound_le_polynomial
    (bound resource : Nat) (hbound : bound <= resource) :
    finiteExhaustionAtEigenvariableStructuralPayloadBound bound <=
      cumulativeFiniteExhaustionPayloadPolynomial resource +
        boundedUniversalFiniteExhaustionSpecializationEnvelope resource := by
  have hfinite := finiteExhaustionStructuralPayloadBound_le_polynomial bound
  have hcumulative := finiteExhaustionPayloadPolynomial_le_cumulative
    bound resource hbound
  have hspecialization :=
    finiteExhaustionSpecializationCost_le_boundedUniversal
      bound resource hbound
  unfold finiteExhaustionAtEigenvariableStructuralPayloadBound
  omega

theorem lowerBoundContradictionFullPayloadCost_le_boundedUniversal
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (resource : Nat)
    (hbound : bound <= resource)
    (hbody : (binaryFormulaCode body).length <= resource) :
    lowerBoundContradictionFullPayloadCost bound (body/[&0]) <=
      smallContextAssemblyEnvelope
        (boundedUniversalClosedFormulaEnvelope resource) := by
  let target := body/[(&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)]
  let formulaEnvelope := boundedUniversalClosedFormulaEnvelope resource
  let Gamma := insert target
    (insert (∼finiteLowerBoundFormula bound (&0))
      (finiteBoundContext bound))
  have htarget : (binaryFormulaCode target).length <= formulaEnvelope := by
    dsimp only [target, formulaEnvelope]
    exact closedBodyInstance_code_le_boundedUniversal body resource hbody
  have hdouble :
      (binaryFormulaCode (∼finiteLowerBoundFormula bound (&0))).length <=
        formulaEnvelope := by
    dsimp only [formulaEnvelope]
    exact doubleNegatedFiniteBoundFormula_code_le_boundedUniversal
      bound resource hbound
  have hboundContext : FormulaCodeBound
      (finiteBoundContext bound) formulaEnvelope := by
    dsimp only [formulaEnvelope]
    exact finiteBoundContext_formulaCodeBound_boundedUniversal
      bound resource hbound
  have hGamma : FormulaCodeBound Gamma formulaEnvelope :=
    (hboundContext.insert hdouble).insert htarget
  have hcard : Gamma.card <= 8 := by
    have hbase : (finiteBoundContext bound).card <= 1 := by
      simp [finiteBoundContext]
    have hfirst := Finset.card_insert_le
      (∼finiteLowerBoundFormula bound (&0)) (finiteBoundContext bound)
    have hsecond := Finset.card_insert_le target
      (insert (∼finiteLowerBoundFormula bound (&0))
        (finiteBoundContext bound))
    dsimp only [Gamma]
    omega
  have hsequent := binarySequentCode_length_le_small
    Gamma formulaEnvelope hcard hGamma
  have hboundFormula := finiteBoundFormula_code_le_boundedUniversal
    bound resource hbound
  have htag : (binaryNatCode 0).length <= 32 := by decide
  unfold lowerBoundContradictionFullPayloadCost
    smallContextAssemblyEnvelope
  dsimp only [target, formulaEnvelope, Gamma] at hsequent hboundFormula ⊢
  omega

theorem underExhaustionEliminationCost_le_boundedUniversal
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (resource : Nat)
    (hbound : bound <= resource)
    (hbody : (binaryFormulaCode body).length <= resource) :
    CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
        (finiteBoundContext bound) (body/[&0])
        (finiteEqualityCases (&0) bound)
        (finiteLowerBoundFormula bound (&0)) <=
      smallContextAssemblyEnvelope
        (boundedUniversalClosedFormulaEnvelope resource) := by
  let target := body/[(&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)]
  let formulaEnvelope := boundedUniversalClosedFormulaEnvelope resource
  have hcontext := finiteBoundContext_formulaCodeBound_boundedUniversal
    bound resource hbound
  have htarget := closedBodyInstance_code_le_boundedUniversal
    body resource hbody
  have hnegatedLeft := negatedFiniteEqualityCases_code_le_boundedUniversal
    bound resource (by omega)
  have hnegatedRight :=
    doubleNegatedFiniteBoundFormula_code_le_boundedUniversal
      bound resource hbound
  have hnegatedDisjunction :
      (binaryFormulaCode
        (∼(finiteEqualityCases (&0) bound ⋎
          finiteLowerBoundFormula bound (&0)))).length <=
        formulaEnvelope := by
    have hexhaustion :=
      negatedFiniteExhaustionFormula_code_le_boundedUniversal
        bound resource hbound
    simpa only [finiteExhaustionFormula, finiteLowerBoundFormula] using
      hexhaustion
  simpa only [target, formulaEnvelope] using
    eliminateDisjunctionAssumptionFullAssemblyCost_le_small
      (finiteBoundContext bound) target
      (finiteEqualityCases (&0) bound)
      (finiteLowerBoundFormula bound (&0))
      formulaEnvelope (by simp [finiteBoundContext]) hcontext
      htarget hnegatedLeft hnegatedRight hnegatedDisjunction

theorem cutFiniteExhaustionFullAssemblyCost_le_boundedUniversal
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (resource : Nat)
    (hbound : bound <= resource)
    (hbody : (binaryFormulaCode body).length <= resource) :
    cutClosedAssumptionFullAssemblyCost
        (finiteBoundContext bound)
        (finiteExhaustionFormula bound (&0)) (body/[&0]) <=
      smallContextAssemblyEnvelope
        (boundedUniversalClosedFormulaEnvelope resource) := by
  let target := body/[(&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)]
  let caseFormula := finiteExhaustionFormula bound
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
  let formulaEnvelope := boundedUniversalClosedFormulaEnvelope resource
  let Gamma := finiteBoundContext bound
  let rootContext := insert target Gamma
  let caseContext := insert caseFormula rootContext
  let negatedCaseContext := insert (∼caseFormula) rootContext
  have htarget := closedBodyInstance_code_le_boundedUniversal
    body resource hbody
  have hcase := finiteExhaustionFormula_code_le_boundedUniversal
    bound resource hbound
  have hnegatedCase :=
    negatedFiniteExhaustionFormula_code_le_boundedUniversal
      bound resource hbound
  have hGamma := finiteBoundContext_formulaCodeBound_boundedUniversal
    bound resource hbound
  have hrootBound : FormulaCodeBound rootContext formulaEnvelope :=
    hGamma.insert htarget
  have hcaseBound : FormulaCodeBound caseContext formulaEnvelope :=
    hrootBound.insert hcase
  have hnegatedCaseBound :
      FormulaCodeBound negatedCaseContext formulaEnvelope :=
    hrootBound.insert hnegatedCase
  have hGammaCard : Gamma.card <= 1 := by
    dsimp only [Gamma]
    simp [finiteBoundContext]
  have hrootCardTight : rootContext.card <= 2 := by
    have hstep := Finset.card_insert_le target Gamma
    dsimp only [rootContext]
    omega
  have hrootCard : rootContext.card <= 8 := hrootCardTight.trans (by omega)
  have hcaseCard : caseContext.card <= 8 := by
    have hstep := Finset.card_insert_le caseFormula rootContext
    dsimp only [caseContext]
    omega
  have hnegatedCaseCard : negatedCaseContext.card <= 8 := by
    have hstep := Finset.card_insert_le (∼caseFormula) rootContext
    dsimp only [negatedCaseContext]
    omega
  have hrootSequent := binarySequentCode_length_le_small
    rootContext formulaEnvelope hrootCard hrootBound
  have hcaseSequent := binarySequentCode_length_le_small
    caseContext formulaEnvelope hcaseCard hcaseBound
  have hnegatedCaseSequent := binarySequentCode_length_le_small
    negatedCaseContext formulaEnvelope hnegatedCaseCard
    hnegatedCaseBound
  have htag7 : (binaryNatCode 7).length <= 32 := by decide
  have htag9 : (binaryNatCode 9).length <= 32 := by decide
  unfold cutClosedAssumptionFullAssemblyCost
    cutClosedAssumptionDerivationCost smallContextAssemblyEnvelope
  dsimp only [target, caseFormula, formulaEnvelope, Gamma,
    rootContext, caseContext, negatedCaseContext] at *
  omega

theorem dischargeBoundedImplicationCost_le_boundedUniversal
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (resource : Nat)
    (hbound : bound <= resource)
    (hbody : (binaryFormulaCode body).length <= resource) :
    CertifiedPAContextProof.dischargeFullAssemblyCost
        (finiteBoundFormula bound) (body/[&0]) <=
      smallContextAssemblyEnvelope
        (boundedUniversalClosedFormulaEnvelope resource) := by
  have hantecedent := finiteBoundFormula_code_le_boundedUniversal
    bound resource hbound
  have hconsequent := closedBodyInstance_code_le_boundedUniversal
    body resource hbody
  have himplication := boundedImplication_code_le_boundedUniversal
    bound body resource hbound hbody
  have hnegated := negatedFiniteBoundFormula_code_le_boundedUniversal
    bound resource hbound
  exact dischargeFullAssemblyCost_le_small
    (finiteBoundFormula bound) (body/[&0])
    (boundedUniversalClosedFormulaEnvelope resource)
    hantecedent hconsequent himplication hnegated

theorem universalIntroductionPayloadPolynomial_mono_local
    {small large : Nat} (h : small <= large) :
    universalIntroductionPayloadPolynomial small <=
      universalIntroductionPayloadPolynomial large := by
  unfold universalIntroductionPayloadPolynomial
    universalIntroductionSequentCodeEnvelope
    universalIntroductionFormulaCodeEnvelope
  omega

theorem universalIntroductionCost_le_boundedUniversal
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (resource : Nat)
    (hbound : bound <= resource)
    (hbody : (binaryFormulaCode body).length <= resource) :
    universalIntroductionFullAssemblyCost
        (finiteBoundedUniversalBody bound body) <=
      universalIntroductionPayloadPolynomial
        (boundedUniversalOpenBodyCodeEnvelope resource) := by
  have hraw := universalIntroductionFullAssemblyCost_le_polynomial
    (finiteBoundedUniversalBody bound body)
  have hbodyCode := finiteBoundedUniversalBody_code_le_envelope
    bound body resource hbound hbody
  exact hraw.trans
    (universalIntroductionPayloadPolynomial_mono_local hbodyCode)

namespace CheckedFiniteBoundedUniversalCertificate

open FoundationCompactPABoundedUniversalCompilerBounds.CheckedFiniteBoundedUniversalCertificate

def encodedLeafStructuralPayloadBound
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) : Nat :=
  let branchBound :=
    CheckedFiniteUniversalBranches.encodedLeafStructuralPayloadBound
      bound certificate.branches
  let underExhaustionBound :=
    branchBound +
      lowerBoundContradictionFullPayloadCost bound (body/[&0]) +
      CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
        (finiteBoundContext bound) (body/[&0])
        (finiteEqualityCases (&0) bound)
        (finiteLowerBoundFormula bound (&0))
  let underBound :=
    finiteExhaustionAtEigenvariableStructuralPayloadBound bound +
      underExhaustionBound +
      cutClosedAssumptionFullAssemblyCost
        (finiteBoundContext bound)
        (finiteExhaustionFormula bound (&0)) (body/[&0])
  let openBound := underBound +
    CertifiedPAContextProof.dischargeFullAssemblyCost
      (finiteBoundFormula bound) (body/[&0])
  openBound + universalIntroductionFullAssemblyCost
    (finiteBoundedUniversalBody bound body)

theorem structuralPayloadBound_le_encodedLeaf
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    compileStructuralPayloadBound certificate <=
      encodedLeafStructuralPayloadBound certificate := by
  have hbranches :=
    CheckedFiniteUniversalBranches.structuralPayloadBound_le_encodedLeaf
      bound certificate.branches
  unfold compileStructuralPayloadBound
    compileOpenImplicationStructuralPayloadBound
    compileUnderBoundAssumptionStructuralPayloadBound
    underExhaustionStructuralPayloadBound
    encodedLeafStructuralPayloadBound
  dsimp only
  omega

theorem compile_payloadLength_le_encodedLeaf
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    certificate.compile.payloadLength <=
      encodedLeafStructuralPayloadBound certificate := by
  have hstructural :=
    compile_payloadLength_le_structural certificate
  exact hstructural.trans (structuralPayloadBound_le_encodedLeaf certificate)

theorem compile_checked_encodedLeaf
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    listedCompactCertifiedPAProofVerifier certificate.compile.code
        (compactFormulaCode (∀⁰ finiteBoundedUniversalBody bound body)) = true ∧
      certificate.compile.payloadLength <=
        encodedLeafStructuralPayloadBound certificate :=
  ⟨certificate.compile_verifier_eq_true,
    compile_payloadLength_le_encodedLeaf certificate⟩

def boundedUniversalPayloadPolynomial (resource : Nat) : Nat :=
  CheckedFiniteUniversalBranches.boundedUniversalBranchPayloadPolynomial
      resource +
    cumulativeFiniteExhaustionPayloadPolynomial resource +
    boundedUniversalFiniteExhaustionSpecializationEnvelope resource +
    4 * smallContextAssemblyEnvelope
      (boundedUniversalClosedFormulaEnvelope resource) +
    universalIntroductionPayloadPolynomial
      (boundedUniversalOpenBodyCodeEnvelope resource)

theorem encodedLeafStructuralPayloadBound_le_polynomial
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    encodedLeafStructuralPayloadBound certificate <=
      boundedUniversalPayloadPolynomial
        (FoundationCompactPABoundedUniversalCertificateCode.CheckedFiniteBoundedUniversalCertificate.encodedSize
          certificate) := by
  let resource :=
    FoundationCompactPABoundedUniversalCertificateCode.CheckedFiniteBoundedUniversalCertificate.encodedSize
      certificate
  let formulaEnvelope := boundedUniversalClosedFormulaEnvelope resource
  have hbound :=
    FoundationCompactPABoundedUniversalCertificateCode.CheckedFiniteBoundedUniversalCertificate.bound_le_encodedSize
      certificate
  have hbody :=
    FoundationCompactPABoundedUniversalCertificateCode.CheckedFiniteBoundedUniversalCertificate.body_code_length_le_encodedSize
      certificate
  have hbranchCode :=
    FoundationCompactPABoundedUniversalCertificateCode.CheckedFiniteBoundedUniversalCertificate.branches_code_length_le_encodedSize
      certificate
  have hbranches :=
    CheckedFiniteUniversalBranches.encodedLeafStructuralPayloadBound_le_polynomial
      bound resource certificate.branches hbody hbound le_rfl hbranchCode
  have hlower := lowerBoundContradictionFullPayloadCost_le_boundedUniversal
    bound body resource hbound hbody
  have heliminate := underExhaustionEliminationCost_le_boundedUniversal
    bound body resource hbound hbody
  have hexhaustion :=
    finiteExhaustionAtEigenvariableStructuralPayloadBound_le_polynomial
      bound resource hbound
  have hcut := cutFiniteExhaustionFullAssemblyCost_le_boundedUniversal
    bound body resource hbound hbody
  have hdischarge := dischargeBoundedImplicationCost_le_boundedUniversal
    bound body resource hbound hbody
  have huniversal := universalIntroductionCost_le_boundedUniversal
    bound body resource hbound hbody
  unfold encodedLeafStructuralPayloadBound
    boundedUniversalPayloadPolynomial
  dsimp only [resource, formulaEnvelope] at *
  omega

theorem compile_payloadLength_le_polynomial
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    certificate.compile.payloadLength <=
      boundedUniversalPayloadPolynomial
        (FoundationCompactPABoundedUniversalCertificateCode.CheckedFiniteBoundedUniversalCertificate.encodedSize
          certificate) := by
  exact (compile_payloadLength_le_encodedLeaf certificate).trans
    (encodedLeafStructuralPayloadBound_le_polynomial certificate)

theorem compile_checked_polynomial
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    listedCompactCertifiedPAProofVerifier certificate.compile.code
        (compactFormulaCode (∀⁰ finiteBoundedUniversalBody bound body)) = true ∧
      certificate.compile.payloadLength <=
        boundedUniversalPayloadPolynomial
          (FoundationCompactPABoundedUniversalCertificateCode.CheckedFiniteBoundedUniversalCertificate.encodedSize
            certificate) :=
  ⟨certificate.compile_verifier_eq_true,
    compile_payloadLength_le_polynomial certificate⟩

end CheckedFiniteBoundedUniversalCertificate

#print axioms atomicPrimitiveEnvelope_le_cumulative
#print axioms ClosedPAAtomicLiteralBounds.payloadPolynomial_le_uniform
#print axioms ClosedPAAtomicLiteralBounds.payloadPolynomial_le_encoded
#print axioms CheckedUnaryReplacementCertificate.compileUnderAssumption_payloadLength_le_encodedLeaf
#print axioms CheckedUnaryReplacementCertificate.encodedLeafStructuralPayloadBound_le_polynomial
#print axioms CheckedUnaryReplacementCertificate.compileUnderAssumption_payloadLength_le_polynomial

namespace CheckedFiniteUniversalBranches
#print axioms compileCasesUnderBoundAssumption_payloadLength_le_encodedLeaf
#print axioms encodedLeafStructuralPayloadBound_le_polynomial
end CheckedFiniteUniversalBranches

namespace CheckedFiniteBoundedUniversalCertificate
#print axioms compile_checked_encodedLeaf
#print axioms compile_checked_polynomial
end CheckedFiniteBoundedUniversalCertificate

end FoundationCompactPABoundedUniversalPolynomialBounds
