import integration.FoundationCompactPAClosedAtomicCompiler
import integration.FoundationCompactPAQuantitativeOrderBounds
import integration.FoundationCompactListedLocalCostPrimitives
import integration.FoundationCompactPANegativeEqualityBounds
import integration.FoundationCompactPANegativeOrderBounds

/-!
# Quantitative bounds for the closed arithmetic compiler

The bounds depend only on an explicit syntax-node budget and a leaf-numeral
bit-weight budget.  No proof length or compiler-bound premise is accepted.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAClosedAtomicCompilerBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeEqualityTransitivity
open FoundationCompactPAQuantitativeFunctionCongruence
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABinaryNumeralMultiplication
open FoundationCompactPABinaryNumeralMultiplicationBounds
open FoundationCompactPAQuantitativeOrder
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactCertifiedDisjunction
open FoundationCompactCertifiedConjunction
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactPANegativeEquality
open FoundationCompactPANegativeEqualityBounds
open FoundationCompactPANegativeOrder
open FoundationCompactPANegativeOrderBounds
open FoundationCompactCertifiedModusTollens
open FoundationCompactPAClosedAtomicCompiler
open FoundationCompactPAClosedAtomicCompiler.ClosedPATerm

namespace ClosedPATerm

/-! ## Shared code and local-cost envelopes -/

def compilerTermCodeEnvelope (nodeBudget bitWidth : Nat) : Nat :=
  (nodeBudget + 4) * paGeneratedTermAtomEnvelope bitWidth

def compilerLocalCostEnvelope (nodeBudget bitWidth : Nat) : Nat :=
  16 *
    (paPrimitiveCostEnvelope
        (compilerTermCodeEnvelope nodeBudget bitWidth) +
      binaryNumeralAdditionPayloadPolynomial bitWidth +
      binaryNumeralMultiplicationPayloadPolynomial bitWidth + 1)

theorem primitiveCost_le_compilerLocal (nodeBudget bitWidth : Nat) :
    paPrimitiveCostEnvelope
        (compilerTermCodeEnvelope nodeBudget bitWidth) <=
      compilerLocalCostEnvelope nodeBudget bitWidth := by
  unfold compilerLocalCostEnvelope
  omega

theorem additionCost_le_compilerLocal (nodeBudget bitWidth : Nat) :
    binaryNumeralAdditionPayloadPolynomial bitWidth <=
      compilerLocalCostEnvelope nodeBudget bitWidth := by
  unfold compilerLocalCostEnvelope
  omega

theorem multiplicationCost_le_compilerLocal (nodeBudget bitWidth : Nat) :
    binaryNumeralMultiplicationPayloadPolynomial bitWidth <=
      compilerLocalCostEnvelope nodeBudget bitWidth := by
  unfold compilerLocalCostEnvelope
  omega

theorem generatedTerm_of_leafBitWeight
    (expression : ClosedPATerm) (bitWidth : Nat)
    (hweight : expression.leafBitWeight <= bitWidth) :
    PACompilerGeneratedTerm bitWidth expression.nodeCount expression.term := by
  induction expression with
  | numeral value =>
      apply PACompilerGeneratedTerm.numeral
      have hvalue := value_size_le_leafBitWeight (.numeral value)
      simp only [ClosedPATerm.value, leafBitWeight] at hvalue hweight
      omega
  | add left right ihLeft ihRight =>
      have hleftWeight : left.leafBitWeight <= bitWidth := by
        simp only [leafBitWeight] at hweight
        omega
      have hrightWeight : right.leafBitWeight <= bitWidth := by
        simp only [leafBitWeight] at hweight
        omega
      simpa [ClosedPATerm.nodeCount, ClosedPATerm.term] using
        (PACompilerGeneratedTerm.add
          (ihLeft hleftWeight) (ihRight hrightWeight))
  | mul left right ihLeft ihRight =>
      have hleftWeight : left.leafBitWeight <= bitWidth := by
        simp only [leafBitWeight] at hweight
        omega
      have hrightWeight : right.leafBitWeight <= bitWidth := by
        simp only [leafBitWeight] at hweight
        omega
      simpa [ClosedPATerm.nodeCount, ClosedPATerm.term] using
        (PACompilerGeneratedTerm.mul
          (ihLeft hleftWeight) (ihRight hrightWeight))

theorem generatedTerm_code_length_le_compiler
    {expression : ClosedPATerm} {nodeBudget bitWidth : Nat}
    (hnodes : expression.nodeCount <= nodeBudget)
    (hweight : expression.leafBitWeight <= bitWidth) :
    (binaryTermCode expression.term).length <=
      compilerTermCodeEnvelope nodeBudget bitWidth := by
  have hgenerated := generatedTerm_of_leafBitWeight
    expression bitWidth hweight
  have hcode := PACompilerGeneratedTerm_code_length_le hgenerated
  unfold compilerTermCodeEnvelope
  exact hcode.trans (Nat.mul_le_mul_right
    (paGeneratedTermAtomEnvelope bitWidth) (by omega))

theorem generatedAuxTerm_code_length_le_compiler
    {term : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {budget nodeBudget bitWidth : Nat}
    (hterm : PACompilerGeneratedTerm bitWidth budget term)
    (hbudget : budget <= nodeBudget + 4) :
    (binaryTermCode term).length <=
      compilerTermCodeEnvelope nodeBudget bitWidth := by
  have hcode := PACompilerGeneratedTerm_code_length_le hterm
  unfold compilerTermCodeEnvelope
  exact hcode.trans (Nat.mul_le_mul_right
    (paGeneratedTermAtomEnvelope bitWidth) hbudget)

theorem proveBinaryNumeralAddition_payloadLength_le_width
    (left right bitWidth : Nat)
    (hwidth : Nat.size left + Nat.size right <= bitWidth) :
    (proveBinaryNumeralAddition left right).payloadLength <=
      binaryNumeralAdditionPayloadPolynomial bitWidth := by
  have hproof := proveBinaryNumeralAddition_payloadLength_le_external
    left right bitWidth hwidth
  unfold binaryNumeralAdditionPayloadPolynomial
  exact hproof.trans (Nat.mul_le_mul_right
    (paAdditionLocalCostEnvelope bitWidth)
    (Nat.add_le_add_right
      ((Nat.le_add_right (Nat.size left) (Nat.size right)).trans hwidth) 1))

theorem proveBinaryNumeralMultiplication_payloadLength_le_width
    (left right bitWidth : Nat)
    (hwidth : Nat.size left + Nat.size right <= bitWidth) :
    (proveBinaryNumeralMultiplication left right).payloadLength <=
      binaryNumeralMultiplicationPayloadPolynomial bitWidth := by
  have hproof := proveBinaryNumeralMultiplication_payloadLength_le_external
    left right bitWidth hwidth
  unfold binaryNumeralMultiplicationPayloadPolynomial
  exact hproof.trans (Nat.mul_le_mul_right
    (paMultiplicationStepCostEnvelope bitWidth)
    (Nat.add_le_add_right
      ((Nat.le_add_left (Nat.size right) (Nat.size left)).trans hwidth) 1))

/-! ## Recursive normalization bound -/

theorem proveNormalization_payloadLength_le_external
    (expression : ClosedPATerm) (nodeBudget bitWidth : Nat)
    (hnodes : expression.nodeCount <= nodeBudget)
    (hweight : expression.leafBitWeight <= bitWidth) :
    (proveNormalization expression).payloadLength <=
      (4 * expression.nodeCount) *
        compilerLocalCostEnvelope nodeBudget bitWidth := by
  induction expression with
  | numeral value =>
      have hgenerated := generatedTerm_of_leafBitWeight
        (.numeral value) bitWidth hweight
      have hcode := generatedAuxTerm_code_length_le_compiler
        (nodeBudget := nodeBudget) hgenerated (by
          simp [ClosedPATerm.nodeCount])
      have hproof := proveEqualityReflexivityAtTerm_payloadLength_le_primitive
        (shortBinaryNumeralTerm value)
        (compilerTermCodeEnvelope nodeBudget bitWidth) hcode
      change
        (proveEqualityReflexivityAtTerm
          (shortBinaryNumeralTerm value)).payloadLength <= _
      have hlocal := primitiveCost_le_compilerLocal nodeBudget bitWidth
      simp only [ClosedPATerm.nodeCount]
      exact hproof.trans (hlocal.trans (by omega))
  | add left right ihLeft ihRight =>
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
      let result := shortBinaryNumeralTerm (left.value + right.value)
      let through := proveEqualityTransitivity source middle result
        congruence arithmetic
      have hleftNodes : left.nodeCount <= nodeBudget := by
        simp only [ClosedPATerm.nodeCount] at hnodes
        omega
      have hrightNodes : right.nodeCount <= nodeBudget := by
        simp only [ClosedPATerm.nodeCount] at hnodes
        omega
      have hnodeSum : left.nodeCount + right.nodeCount + 1 <= nodeBudget := by
        simpa [ClosedPATerm.nodeCount] using hnodes
      have hleftWeight : left.leafBitWeight <= bitWidth := by
        simp only [leafBitWeight] at hweight
        omega
      have hrightWeight : right.leafBitWeight <= bitWidth := by
        simp only [leafBitWeight] at hweight
        omega
      have hleftRecursive := ihLeft hleftNodes hleftWeight
      have hrightRecursive := ihRight hrightNodes hrightWeight
      have hleftGenerated := generatedTerm_of_leafBitWeight
        left bitWidth hleftWeight
      have hrightGenerated := generatedTerm_of_leafBitWeight
        right bitWidth hrightWeight
      have hleftValue := value_size_le_leafBitWeight left
      have hrightValue := value_size_le_leafBitWeight right
      have hleftValueSize : Nat.size left.value <= bitWidth := by omega
      have hrightValueSize : Nat.size right.value <= bitWidth := by omega
      have hvalueWidth :
          Nat.size left.value + Nat.size right.value <= bitWidth := by
        simp only [leafBitWeight] at hweight
        omega
      have hnormalizedLeft : PACompilerGeneratedTerm bitWidth 1
          normalizedLeft := .numeral left.value hleftValueSize
      have hnormalizedRight : PACompilerGeneratedTerm bitWidth 1
          normalizedRight := .numeral right.value hrightValueSize
      have hsource : PACompilerGeneratedTerm bitWidth
          (left.nodeCount + right.nodeCount + 1) source :=
        .add hleftGenerated hrightGenerated
      have hmiddle : PACompilerGeneratedTerm bitWidth 3 middle :=
        .add hnormalizedLeft hnormalizedRight
      have hresultSize := value_size_le_leafBitWeight (.add left right)
      have hresult : PACompilerGeneratedTerm bitWidth 1 result :=
        .numeral (left.value + right.value) (by
          simp only [ClosedPATerm.value, leafBitWeight] at hresultSize hweight
          omega)
      have hleftCode := generatedAuxTerm_code_length_le_compiler
        (nodeBudget := nodeBudget) hleftGenerated (by omega)
      have hrightCode := generatedAuxTerm_code_length_le_compiler
        (nodeBudget := nodeBudget) hrightGenerated (by omega)
      have hnormalizedLeftCode := generatedAuxTerm_code_length_le_compiler
        (nodeBudget := nodeBudget) hnormalizedLeft (by omega)
      have hnormalizedRightCode := generatedAuxTerm_code_length_le_compiler
        (nodeBudget := nodeBudget) hnormalizedRight (by omega)
      have hsourceCode := generatedAuxTerm_code_length_le_compiler
        (nodeBudget := nodeBudget) hsource (by omega)
      have hmiddleCode := generatedAuxTerm_code_length_le_compiler
        (nodeBudget := nodeBudget) hmiddle (by omega)
      have hresultCode := generatedAuxTerm_code_length_le_compiler
        (nodeBudget := nodeBudget) hresult (by omega)
      have hcongruenceRaw := proveAddCongruence_payloadLength_le_primitive
        left.term right.term normalizedLeft normalizedRight
        leftProof rightProof
        (compilerTermCodeEnvelope nodeBudget bitWidth)
        hleftCode hrightCode hnormalizedLeftCode hnormalizedRightCode
      have hcongruence : congruence.payloadLength <=
          leftProof.payloadLength + rightProof.payloadLength +
            paPrimitiveCostEnvelope
              (compilerTermCodeEnvelope nodeBudget bitWidth) := by
        have hcast : congruence.payloadLength = congruenceRaw.payloadLength := by
          dsimp only [congruence]
          exact cast_payloadLength _ _
        rw [hcast]
        exact hcongruenceRaw
      have harithmetic := proveBinaryNumeralAddition_payloadLength_le_width
        left.value right.value bitWidth hvalueWidth
      have htrans := proveEqualityTransitivity_payloadLength_le_primitive
        source middle result congruence arithmetic
        (compilerTermCodeEnvelope nodeBudget bitWidth)
        hsourceCode hmiddleCode hresultCode
      have houter : (proveNormalization (.add left right)).payloadLength =
          through.payloadLength := by
        have hformula :
            (“!!source = !!result” : LO.FirstOrder.ArithmeticProposition) =
            (“!!(ClosedPATerm.term (.add left right)) =
              !!(shortBinaryNumeralTerm
                (ClosedPATerm.value (.add left right)))” :
              LO.FirstOrder.ArithmeticProposition) := by
          rfl
        change (CertifiedPAProof.cast hformula through).payloadLength = _
        exact cast_payloadLength _ _
      have hprimitive := primitiveCost_le_compilerLocal nodeBudget bitWidth
      have haddition := additionCost_le_compilerLocal nodeBudget bitWidth
      have hleftLocal : leftProof.payloadLength <=
          (4 * left.nodeCount) *
            compilerLocalCostEnvelope nodeBudget bitWidth := by
        dsimp only [leftProof]
        exact hleftRecursive
      have hrightLocal : rightProof.payloadLength <=
          (4 * right.nodeCount) *
            compilerLocalCostEnvelope nodeBudget bitWidth := by
        dsimp only [rightProof]
        exact hrightRecursive
      have harithmeticLocal : arithmetic.payloadLength <=
          compilerLocalCostEnvelope nodeBudget bitWidth := by
        dsimp only [arithmetic]
        exact harithmetic.trans haddition
      have hcongruenceLocal : congruence.payloadLength <=
          (4 * left.nodeCount + 4 * right.nodeCount + 1) *
            compilerLocalCostEnvelope nodeBudget bitWidth := by
        calc
          congruence.payloadLength <= leftProof.payloadLength +
              rightProof.payloadLength +
              paPrimitiveCostEnvelope
                (compilerTermCodeEnvelope nodeBudget bitWidth) := hcongruence
          _ <= (4 * left.nodeCount) *
                compilerLocalCostEnvelope nodeBudget bitWidth +
              (4 * right.nodeCount) *
                compilerLocalCostEnvelope nodeBudget bitWidth +
              compilerLocalCostEnvelope nodeBudget bitWidth := by omega
          _ = (4 * left.nodeCount + 4 * right.nodeCount + 1) *
              compilerLocalCostEnvelope nodeBudget bitWidth := by ring
      have hthroughRaw : through.payloadLength <=
          congruence.payloadLength + arithmetic.payloadLength +
            paPrimitiveCostEnvelope
              (compilerTermCodeEnvelope nodeBudget bitWidth) := by
        dsimp only [through]
        exact htrans
      have hthroughLocal : through.payloadLength <=
          (4 * (left.nodeCount + right.nodeCount + 1)) *
            compilerLocalCostEnvelope nodeBudget bitWidth := by
        calc
          through.payloadLength <= congruence.payloadLength +
              arithmetic.payloadLength +
              paPrimitiveCostEnvelope
                (compilerTermCodeEnvelope nodeBudget bitWidth) := hthroughRaw
          _ <= (4 * left.nodeCount + 4 * right.nodeCount + 1) *
                compilerLocalCostEnvelope nodeBudget bitWidth +
              compilerLocalCostEnvelope nodeBudget bitWidth +
              compilerLocalCostEnvelope nodeBudget bitWidth := by omega
          _ = (4 * left.nodeCount + 4 * right.nodeCount + 3) *
              compilerLocalCostEnvelope nodeBudget bitWidth := by ring
          _ <= (4 * (left.nodeCount + right.nodeCount + 1)) *
              compilerLocalCostEnvelope nodeBudget bitWidth := by
            apply Nat.mul_le_mul_right
            omega
      rw [houter]
      simpa [ClosedPATerm.nodeCount] using hthroughLocal
  | mul left right ihLeft ihRight =>
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
      let result := shortBinaryNumeralTerm (left.value * right.value)
      let through := proveEqualityTransitivity source middle result
        congruence arithmetic
      have hleftNodes : left.nodeCount <= nodeBudget := by
        simp only [ClosedPATerm.nodeCount] at hnodes
        omega
      have hrightNodes : right.nodeCount <= nodeBudget := by
        simp only [ClosedPATerm.nodeCount] at hnodes
        omega
      have hnodeSum : left.nodeCount + right.nodeCount + 1 <= nodeBudget := by
        simpa [ClosedPATerm.nodeCount] using hnodes
      have hleftWeight : left.leafBitWeight <= bitWidth := by
        simp only [leafBitWeight] at hweight
        omega
      have hrightWeight : right.leafBitWeight <= bitWidth := by
        simp only [leafBitWeight] at hweight
        omega
      have hleftRecursive := ihLeft hleftNodes hleftWeight
      have hrightRecursive := ihRight hrightNodes hrightWeight
      have hleftGenerated := generatedTerm_of_leafBitWeight
        left bitWidth hleftWeight
      have hrightGenerated := generatedTerm_of_leafBitWeight
        right bitWidth hrightWeight
      have hleftValue := value_size_le_leafBitWeight left
      have hrightValue := value_size_le_leafBitWeight right
      have hleftValueSize : Nat.size left.value <= bitWidth := by omega
      have hrightValueSize : Nat.size right.value <= bitWidth := by omega
      have hvalueWidth :
          Nat.size left.value + Nat.size right.value <= bitWidth := by
        simp only [leafBitWeight] at hweight
        omega
      have hnormalizedLeft : PACompilerGeneratedTerm bitWidth 1
          normalizedLeft := .numeral left.value hleftValueSize
      have hnormalizedRight : PACompilerGeneratedTerm bitWidth 1
          normalizedRight := .numeral right.value hrightValueSize
      have hsource : PACompilerGeneratedTerm bitWidth
          (left.nodeCount + right.nodeCount + 1) source :=
        .mul hleftGenerated hrightGenerated
      have hmiddle : PACompilerGeneratedTerm bitWidth 3 middle :=
        .mul hnormalizedLeft hnormalizedRight
      have hresultSize := value_size_le_leafBitWeight (.mul left right)
      have hresult : PACompilerGeneratedTerm bitWidth 1 result :=
        .numeral (left.value * right.value) (by
          simp only [ClosedPATerm.value, leafBitWeight] at hresultSize hweight
          omega)
      have hleftCode := generatedAuxTerm_code_length_le_compiler
        (nodeBudget := nodeBudget) hleftGenerated (by omega)
      have hrightCode := generatedAuxTerm_code_length_le_compiler
        (nodeBudget := nodeBudget) hrightGenerated (by omega)
      have hnormalizedLeftCode := generatedAuxTerm_code_length_le_compiler
        (nodeBudget := nodeBudget) hnormalizedLeft (by omega)
      have hnormalizedRightCode := generatedAuxTerm_code_length_le_compiler
        (nodeBudget := nodeBudget) hnormalizedRight (by omega)
      have hsourceCode := generatedAuxTerm_code_length_le_compiler
        (nodeBudget := nodeBudget) hsource (by omega)
      have hmiddleCode := generatedAuxTerm_code_length_le_compiler
        (nodeBudget := nodeBudget) hmiddle (by omega)
      have hresultCode := generatedAuxTerm_code_length_le_compiler
        (nodeBudget := nodeBudget) hresult (by omega)
      have hcongruenceRaw := proveMulCongruence_payloadLength_le_primitive
        left.term right.term normalizedLeft normalizedRight
        leftProof rightProof
        (compilerTermCodeEnvelope nodeBudget bitWidth)
        hleftCode hrightCode hnormalizedLeftCode hnormalizedRightCode
      have hcongruence : congruence.payloadLength <=
          leftProof.payloadLength + rightProof.payloadLength +
            paPrimitiveCostEnvelope
              (compilerTermCodeEnvelope nodeBudget bitWidth) := by
        have hcast : congruence.payloadLength = congruenceRaw.payloadLength := by
          dsimp only [congruence]
          exact cast_payloadLength _ _
        rw [hcast]
        exact hcongruenceRaw
      have harithmetic :=
        proveBinaryNumeralMultiplication_payloadLength_le_width
          left.value right.value bitWidth hvalueWidth
      have htrans := proveEqualityTransitivity_payloadLength_le_primitive
        source middle result congruence arithmetic
        (compilerTermCodeEnvelope nodeBudget bitWidth)
        hsourceCode hmiddleCode hresultCode
      have houter : (proveNormalization (.mul left right)).payloadLength =
          through.payloadLength := by
        have hformula :
            (“!!source = !!result” : LO.FirstOrder.ArithmeticProposition) =
            (“!!(ClosedPATerm.term (.mul left right)) =
              !!(shortBinaryNumeralTerm
                (ClosedPATerm.value (.mul left right)))” :
              LO.FirstOrder.ArithmeticProposition) := by
          rfl
        change (CertifiedPAProof.cast hformula through).payloadLength = _
        exact cast_payloadLength _ _
      have hprimitive := primitiveCost_le_compilerLocal nodeBudget bitWidth
      have hmultiplication :=
        multiplicationCost_le_compilerLocal nodeBudget bitWidth
      have hleftLocal : leftProof.payloadLength <=
          (4 * left.nodeCount) *
            compilerLocalCostEnvelope nodeBudget bitWidth := by
        dsimp only [leftProof]
        exact hleftRecursive
      have hrightLocal : rightProof.payloadLength <=
          (4 * right.nodeCount) *
            compilerLocalCostEnvelope nodeBudget bitWidth := by
        dsimp only [rightProof]
        exact hrightRecursive
      have harithmeticLocal : arithmetic.payloadLength <=
          compilerLocalCostEnvelope nodeBudget bitWidth := by
        dsimp only [arithmetic]
        exact harithmetic.trans hmultiplication
      have hcongruenceLocal : congruence.payloadLength <=
          (4 * left.nodeCount + 4 * right.nodeCount + 1) *
            compilerLocalCostEnvelope nodeBudget bitWidth := by
        calc
          congruence.payloadLength <= leftProof.payloadLength +
              rightProof.payloadLength +
              paPrimitiveCostEnvelope
                (compilerTermCodeEnvelope nodeBudget bitWidth) := hcongruence
          _ <= (4 * left.nodeCount) *
                compilerLocalCostEnvelope nodeBudget bitWidth +
              (4 * right.nodeCount) *
                compilerLocalCostEnvelope nodeBudget bitWidth +
              compilerLocalCostEnvelope nodeBudget bitWidth := by omega
          _ = (4 * left.nodeCount + 4 * right.nodeCount + 1) *
              compilerLocalCostEnvelope nodeBudget bitWidth := by ring
      have hthroughRaw : through.payloadLength <=
          congruence.payloadLength + arithmetic.payloadLength +
            paPrimitiveCostEnvelope
              (compilerTermCodeEnvelope nodeBudget bitWidth) := by
        dsimp only [through]
        exact htrans
      have hthroughLocal : through.payloadLength <=
          (4 * (left.nodeCount + right.nodeCount + 1)) *
            compilerLocalCostEnvelope nodeBudget bitWidth := by
        calc
          through.payloadLength <= congruence.payloadLength +
              arithmetic.payloadLength +
              paPrimitiveCostEnvelope
                (compilerTermCodeEnvelope nodeBudget bitWidth) := hthroughRaw
          _ <= (4 * left.nodeCount + 4 * right.nodeCount + 1) *
                compilerLocalCostEnvelope nodeBudget bitWidth +
              compilerLocalCostEnvelope nodeBudget bitWidth +
              compilerLocalCostEnvelope nodeBudget bitWidth := by omega
          _ = (4 * left.nodeCount + 4 * right.nodeCount + 3) *
              compilerLocalCostEnvelope nodeBudget bitWidth := by ring
          _ <= (4 * (left.nodeCount + right.nodeCount + 1)) *
              compilerLocalCostEnvelope nodeBudget bitWidth := by
            apply Nat.mul_le_mul_right
            omega
      rw [houter]
      simpa [ClosedPATerm.nodeCount] using hthroughLocal

def normalizationPayloadPolynomial (expression : ClosedPATerm) : Nat :=
  (4 * expression.nodeCount) *
    compilerLocalCostEnvelope expression.nodeCount expression.leafBitWeight

theorem proveNormalization_payloadLength_le_polynomial
    (expression : ClosedPATerm) :
    (proveNormalization expression).payloadLength <=
      normalizationPayloadPolynomial expression := by
  exact proveNormalization_payloadLength_le_external expression
    expression.nodeCount expression.leafBitWeight le_rfl le_rfl

/-! ## Positive equality atom bound -/

def positiveEqualityNodeBudget
    (left right : ClosedPATerm) : Nat :=
  left.nodeCount + right.nodeCount + 1

def positiveEqualityBitWidth
    (left right : ClosedPATerm) : Nat :=
  left.leafBitWeight + right.leafBitWeight

def positiveEqualityPayloadPolynomial
    (left right : ClosedPATerm) : Nat :=
  (4 * positiveEqualityNodeBudget left right) *
    compilerLocalCostEnvelope
      (positiveEqualityNodeBudget left right)
      (positiveEqualityBitWidth left right)

theorem provePositiveEquality_payloadLength_le_polynomial
    (left right : ClosedPATerm)
    (hvalue : PositiveEqualityCertificate left right) :
    (provePositiveEquality left right hvalue).payloadLength <=
      positiveEqualityPayloadPolynomial left right := by
  let nodeBudget := positiveEqualityNodeBudget left right
  let bitWidth := positiveEqualityBitWidth left right
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
  let through := proveEqualityTransitivity left.term middle right.term
    leftProof rightBackward
  have hleftNodes : left.nodeCount <= nodeBudget := by
    unfold nodeBudget positiveEqualityNodeBudget
    omega
  have hrightNodes : right.nodeCount <= nodeBudget := by
    unfold nodeBudget positiveEqualityNodeBudget
    omega
  have hleftWeight : left.leafBitWeight <= bitWidth := by
    unfold bitWidth positiveEqualityBitWidth
    omega
  have hrightWeight : right.leafBitWeight <= bitWidth := by
    unfold bitWidth positiveEqualityBitWidth
    omega
  have hleftGenerated := generatedTerm_of_leafBitWeight
    left bitWidth hleftWeight
  have hrightGenerated := generatedTerm_of_leafBitWeight
    right bitWidth hrightWeight
  have hleftValue := value_size_le_leafBitWeight left
  have hmiddleGenerated : PACompilerGeneratedTerm bitWidth 1 middle :=
    .numeral left.value (by omega)
  have hleftCode := generatedAuxTerm_code_length_le_compiler
    (nodeBudget := nodeBudget) hleftGenerated (by omega)
  have hrightCode := generatedAuxTerm_code_length_le_compiler
    (nodeBudget := nodeBudget) hrightGenerated (by omega)
  have hmiddleCode := generatedAuxTerm_code_length_le_compiler
    (nodeBudget := nodeBudget) hmiddleGenerated (by omega)
  have hleftNormalize := proveNormalization_payloadLength_le_external
    left nodeBudget bitWidth hleftNodes hleftWeight
  have hrightNormalize := proveNormalization_payloadLength_le_external
    right nodeBudget bitWidth hrightNodes hrightWeight
  have hleftLocal : leftProof.payloadLength <=
      (4 * left.nodeCount) * compilerLocalCostEnvelope nodeBudget bitWidth := by
    dsimp only [leftProof]
    exact hleftNormalize
  have hrightForwardRawLocal : rightForwardRaw.payloadLength <=
      (4 * right.nodeCount) *
        compilerLocalCostEnvelope nodeBudget bitWidth := by
    dsimp only [rightForwardRaw]
    exact hrightNormalize
  have hrightForwardLocal : rightForward.payloadLength <=
      (4 * right.nodeCount) *
        compilerLocalCostEnvelope nodeBudget bitWidth := by
    have hcast : rightForward.payloadLength = rightForwardRaw.payloadLength := by
      dsimp only [rightForward]
      exact cast_payloadLength _ _
    rw [hcast]
    exact hrightForwardRawLocal
  have hsymmetry := proveEqualitySymmetry_payloadLength_le_primitive
    right.term middle rightForward
    (compilerTermCodeEnvelope nodeBudget bitWidth)
    hrightCode hmiddleCode
  have hrightBackwardLocal : rightBackward.payloadLength <=
      (4 * right.nodeCount + 1) *
        compilerLocalCostEnvelope nodeBudget bitWidth := by
    dsimp only [rightBackward]
    have hprimitive := primitiveCost_le_compilerLocal nodeBudget bitWidth
    calc
      (proveEqualitySymmetry right.term middle rightForward).payloadLength <=
          rightForward.payloadLength +
            paPrimitiveCostEnvelope
              (compilerTermCodeEnvelope nodeBudget bitWidth) := hsymmetry
      _ <= (4 * right.nodeCount) *
            compilerLocalCostEnvelope nodeBudget bitWidth +
          compilerLocalCostEnvelope nodeBudget bitWidth := by omega
      _ = (4 * right.nodeCount + 1) *
          compilerLocalCostEnvelope nodeBudget bitWidth := by ring
  have htrans := proveEqualityTransitivity_payloadLength_le_primitive
    left.term middle right.term leftProof rightBackward
    (compilerTermCodeEnvelope nodeBudget bitWidth)
    hleftCode hmiddleCode hrightCode
  have hthrough : through.payloadLength <=
      (4 * left.nodeCount + 4 * right.nodeCount + 2) *
        compilerLocalCostEnvelope nodeBudget bitWidth := by
    dsimp only [through]
    have hprimitive := primitiveCost_le_compilerLocal nodeBudget bitWidth
    calc
      (proveEqualityTransitivity left.term middle right.term
          leftProof rightBackward).payloadLength <=
          leftProof.payloadLength + rightBackward.payloadLength +
            paPrimitiveCostEnvelope
              (compilerTermCodeEnvelope nodeBudget bitWidth) := htrans
      _ <= (4 * left.nodeCount) *
            compilerLocalCostEnvelope nodeBudget bitWidth +
          (4 * right.nodeCount + 1) *
            compilerLocalCostEnvelope nodeBudget bitWidth +
          compilerLocalCostEnvelope nodeBudget bitWidth := by omega
      _ = (4 * left.nodeCount + 4 * right.nodeCount + 2) *
          compilerLocalCostEnvelope nodeBudget bitWidth := by ring
  have houter : (provePositiveEquality left right hvalue).payloadLength =
      through.payloadLength := by
    rfl
  rw [houter]
  unfold positiveEqualityPayloadPolynomial
  exact hthrough.trans (by
    apply Nat.mul_le_mul_right
    unfold positiveEqualityNodeBudget
    omega)

theorem provePositiveEquality_checked_polynomial
    (left right : ClosedPATerm)
    (hvalue : PositiveEqualityCertificate left right) :
    listedCompactCertifiedPAProofVerifier
        (provePositiveEquality left right hvalue).code
        (compactFormulaCode
          (“!!left.term = !!right.term” :
            LO.FirstOrder.ArithmeticProposition)) = true ∧
      (provePositiveEquality left right hvalue).payloadLength <=
        positiveEqualityPayloadPolynomial left right := by
  exact ⟨provePositiveEquality_verifier_eq_true left right hvalue,
    provePositiveEquality_payloadLength_le_polynomial left right hvalue⟩

/-! ## Positive strict-order atom bound -/

def positiveLessThanNodeBudget
    (left right : ClosedPATerm) : Nat :=
  left.nodeCount + right.nodeCount + 1

def positiveLessThanBitWidth
    (left right : ClosedPATerm) : Nat :=
  left.leafBitWeight + right.leafBitWeight

def positiveLessThanPayloadPolynomial
    (left right : ClosedPATerm) : Nat :=
  let nodeBudget := positiveLessThanNodeBudget left right
  let bitWidth := positiveLessThanBitWidth left right
  let termBound := compilerTermCodeEnvelope nodeBudget bitWidth
  (4 * left.nodeCount) *
      compilerLocalCostEnvelope nodeBudget bitWidth +
    (4 * right.nodeCount) *
      compilerLocalCostEnvelope nodeBudget bitWidth +
    positiveBinaryNumeralPayloadPolynomial bitWidth +
    orderStepCostEnvelope bitWidth +
    2 * paPrimitiveCostEnvelope termBound +
    2 * orderPrimitiveCostEnvelope termBound

theorem provePositiveLessThan_payloadLength_le_polynomial
    (left right : ClosedPATerm)
    (hvalue : PositiveLessThanCertificate left right) :
    (provePositiveLessThan left right hvalue).payloadLength <=
      positiveLessThanPayloadPolynomial left right := by
  let nodeBudget := positiveLessThanNodeBudget left right
  let bitWidth := positiveLessThanBitWidth left right
  let termBound := compilerTermCodeEnvelope nodeBudget bitWidth
  let gap := right.value - left.value
  have hgapPositive : 0 < gap := by
    exact Nat.sub_pos_of_lt hvalue
  let gapProof := provePositiveBinaryNumeral gap hgapPositive
  let shiftedRaw :=
    proveBinaryNumeralAddLtAdd 0 gap left.value gapProof
  let numeralProof := CertifiedPAProof.cast
    (shiftedGapLessThan_formula left.value right.value hvalue)
    shiftedRaw
  let leftProof := proveNormalization left
  let rightProof := proveNormalization right
  let leftNumeral := shortBinaryNumeralTerm left.value
  let rightNumeral := shortBinaryNumeralTerm right.value
  let leftBackward := proveEqualitySymmetry left.term leftNumeral leftProof
  let rightBackward := proveEqualitySymmetry right.term rightNumeral rightProof
  let through := proveLtTransport leftNumeral rightNumeral
    left.term right.term leftBackward rightBackward numeralProof
  have hleftNodes : left.nodeCount <= nodeBudget := by
    unfold nodeBudget positiveLessThanNodeBudget
    omega
  have hrightNodes : right.nodeCount <= nodeBudget := by
    unfold nodeBudget positiveLessThanNodeBudget
    omega
  have hleftWeight : left.leafBitWeight <= bitWidth := by
    unfold bitWidth positiveLessThanBitWidth
    omega
  have hrightWeight : right.leafBitWeight <= bitWidth := by
    unfold bitWidth positiveLessThanBitWidth
    omega
  have hleftValueRaw := value_size_le_leafBitWeight left
  have hrightValueRaw := value_size_le_leafBitWeight right
  have hleftValueSize : Nat.size left.value <= bitWidth := by
    omega
  have hrightValueSize : Nat.size right.value <= bitWidth := by
    omega
  have hgapLeRight : gap <= right.value := by
    dsimp only [gap]
    exact Nat.sub_le _ _
  have hgapSize : Nat.size gap <= bitWidth := by
    exact (Nat.size_le_size hgapLeRight).trans hrightValueSize
  have hleftGenerated := generatedTerm_of_leafBitWeight
    left bitWidth hleftWeight
  have hrightGenerated := generatedTerm_of_leafBitWeight
    right bitWidth hrightWeight
  have hleftNumeralGenerated : PACompilerGeneratedTerm bitWidth 1 leftNumeral :=
    .numeral left.value hleftValueSize
  have hrightNumeralGenerated : PACompilerGeneratedTerm bitWidth 1 rightNumeral :=
    .numeral right.value hrightValueSize
  have hleftCode : (binaryTermCode left.term).length <= termBound := by
    dsimp only [termBound]
    exact generatedAuxTerm_code_length_le_compiler
      (nodeBudget := nodeBudget) hleftGenerated (by omega)
  have hrightCode : (binaryTermCode right.term).length <= termBound := by
    dsimp only [termBound]
    exact generatedAuxTerm_code_length_le_compiler
      (nodeBudget := nodeBudget) hrightGenerated (by omega)
  have hleftNumeralCode : (binaryTermCode leftNumeral).length <= termBound := by
    dsimp only [termBound]
    exact generatedAuxTerm_code_length_le_compiler
      (nodeBudget := nodeBudget) hleftNumeralGenerated (by omega)
  have hrightNumeralCode :
      (binaryTermCode rightNumeral).length <= termBound := by
    dsimp only [termBound]
    exact generatedAuxTerm_code_length_le_compiler
      (nodeBudget := nodeBudget) hrightNumeralGenerated (by omega)
  have hleftNormalize := proveNormalization_payloadLength_le_external
    left nodeBudget bitWidth hleftNodes hleftWeight
  have hrightNormalize := proveNormalization_payloadLength_le_external
    right nodeBudget bitWidth hrightNodes hrightWeight
  have hleftNormalizeLocal : leftProof.payloadLength <=
      (4 * left.nodeCount) *
        compilerLocalCostEnvelope nodeBudget bitWidth := by
    dsimp only [leftProof]
    exact hleftNormalize
  have hrightNormalizeLocal : rightProof.payloadLength <=
      (4 * right.nodeCount) *
        compilerLocalCostEnvelope nodeBudget bitWidth := by
    dsimp only [rightProof]
    exact hrightNormalize
  have hgapProof : gapProof.payloadLength <=
      positiveBinaryNumeralPayloadPolynomial bitWidth := by
    dsimp only [gapProof]
    exact provePositiveBinaryNumeral_payloadLength_le_width
      gap bitWidth hgapPositive hgapSize
  have hshiftedBound := proveBinaryNumeralAddLtAdd_payloadLength_le
    0 gap left.value gapProof
  have hshiftedEnvelope := binaryNumeralAddLtAddPayloadBound_le_orderStep
    0 gap left.value gapProof.payloadLength bitWidth
    (by simp) hgapSize hleftValueSize
  have hshifted : shiftedRaw.payloadLength <=
      gapProof.payloadLength + orderStepCostEnvelope bitWidth := by
    dsimp only [shiftedRaw]
    exact hshiftedBound.trans hshiftedEnvelope
  have hnumeralPayload : numeralProof.payloadLength =
      shiftedRaw.payloadLength := by
    dsimp only [numeralProof]
    exact cast_payloadLength _ _
  have hleftBackward : leftBackward.payloadLength <=
      leftProof.payloadLength + paPrimitiveCostEnvelope termBound := by
    dsimp only [leftBackward]
    exact proveEqualitySymmetry_payloadLength_le_primitive
      left.term leftNumeral leftProof termBound hleftCode hleftNumeralCode
  have hrightBackward : rightBackward.payloadLength <=
      rightProof.payloadLength + paPrimitiveCostEnvelope termBound := by
    dsimp only [rightBackward]
    exact proveEqualitySymmetry_payloadLength_le_primitive
      right.term rightNumeral rightProof termBound hrightCode hrightNumeralCode
  have hthroughRaw : through.payloadLength <=
      leftBackward.payloadLength + rightBackward.payloadLength +
        numeralProof.payloadLength +
        2 * orderPrimitiveCostEnvelope termBound := by
    dsimp only [through]
    exact proveLtTransport_payloadLength_le_primitive
      leftNumeral rightNumeral left.term right.term
      leftBackward rightBackward numeralProof termBound
      hleftNumeralCode hrightNumeralCode hleftCode hrightCode
  have hthrough : through.payloadLength <=
      positiveLessThanPayloadPolynomial left right := by
    calc
      through.payloadLength <=
          leftBackward.payloadLength + rightBackward.payloadLength +
            numeralProof.payloadLength +
            2 * orderPrimitiveCostEnvelope termBound := hthroughRaw
      _ <= (leftProof.payloadLength + paPrimitiveCostEnvelope termBound) +
          (rightProof.payloadLength + paPrimitiveCostEnvelope termBound) +
          (gapProof.payloadLength + orderStepCostEnvelope bitWidth) +
          2 * orderPrimitiveCostEnvelope termBound := by
        rw [hnumeralPayload]
        omega
      _ <= ((4 * left.nodeCount) *
              compilerLocalCostEnvelope nodeBudget bitWidth +
            paPrimitiveCostEnvelope termBound) +
          ((4 * right.nodeCount) *
              compilerLocalCostEnvelope nodeBudget bitWidth +
            paPrimitiveCostEnvelope termBound) +
          (positiveBinaryNumeralPayloadPolynomial bitWidth +
            orderStepCostEnvelope bitWidth) +
          2 * orderPrimitiveCostEnvelope termBound := by
        omega
      _ = positiveLessThanPayloadPolynomial left right := by
        simp only [positiveLessThanPayloadPolynomial, nodeBudget, bitWidth,
          termBound]
        ring
  have houter :
      (provePositiveLessThan left right hvalue).payloadLength =
        through.payloadLength := by
    rfl
  rw [houter]
  exact hthrough

theorem provePositiveLessThan_checked_polynomial
    (left right : ClosedPATerm)
    (hvalue : PositiveLessThanCertificate left right) :
    listedCompactCertifiedPAProofVerifier
        (provePositiveLessThan left right hvalue).code
        (compactFormulaCode
          (“!!left.term < !!right.term” :
            LO.FirstOrder.ArithmeticProposition)) = true ∧
      (provePositiveLessThan left right hvalue).payloadLength <=
        positiveLessThanPayloadPolynomial left right := by
  exact ⟨provePositiveLessThan_verifier_eq_true left right hvalue,
    provePositiveLessThan_payloadLength_le_polynomial left right hvalue⟩

/-! ## Positive non-strict-order atom bound -/

theorem equalityLessDisjunctionSyntaxBudget_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    disjunctionSyntaxBudget
        (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)
        (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition) <=
      4 * orderAtomicFormulaCodeEnvelope termBound + 8 := by
  have hequality := equalityFormula_code_le_orderAtomic
    left right termBound hleft hright
  have hless := lessThanFormula_code_le_orderAtomic
    left right termBound hleft hright
  have hor := binaryFormulaCode_or_length_le
    (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)
    (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)
  unfold disjunctionSyntaxBudget
  omega

def closedOrderDisjunctionPayloadCostEnvelope (termBound : Nat) : Nat :=
  96 + 8 * (4 * orderAtomicFormulaCodeEnvelope termBound + 8)

theorem equalityLessDisjunctionPayloadCost_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    96 + 8 * disjunctionSyntaxBudget
        (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)
        (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition) <=
      closedOrderDisjunctionPayloadCostEnvelope termBound := by
  have hsyntax := equalityLessDisjunctionSyntaxBudget_le
    left right termBound hleft hright
  unfold closedOrderDisjunctionPayloadCostEnvelope
  omega

def positiveLessEqualPayloadPolynomial
    (left right : ClosedPATerm) : Nat :=
  let nodeBudget := positiveLessThanNodeBudget left right
  let bitWidth := positiveLessThanBitWidth left right
  let termBound := compilerTermCodeEnvelope nodeBudget bitWidth
  positiveEqualityPayloadPolynomial left right +
    positiveLessThanPayloadPolynomial left right +
    closedOrderDisjunctionPayloadCostEnvelope termBound

theorem provePositiveLessEqual_payloadLength_le_polynomial
    (left right : ClosedPATerm)
    (hvalue : PositiveLessEqualCertificate left right) :
    (provePositiveLessEqual left right hvalue).payloadLength <=
      positiveLessEqualPayloadPolynomial left right := by
  let nodeBudget := positiveLessThanNodeBudget left right
  let bitWidth := positiveLessThanBitWidth left right
  let termBound := compilerTermCodeEnvelope nodeBudget bitWidth
  have hleftNodes : left.nodeCount <= nodeBudget := by
    unfold nodeBudget positiveLessThanNodeBudget
    omega
  have hrightNodes : right.nodeCount <= nodeBudget := by
    unfold nodeBudget positiveLessThanNodeBudget
    omega
  have hleftWeight : left.leafBitWeight <= bitWidth := by
    unfold bitWidth positiveLessThanBitWidth
    omega
  have hrightWeight : right.leafBitWeight <= bitWidth := by
    unfold bitWidth positiveLessThanBitWidth
    omega
  have hleftGenerated := generatedTerm_of_leafBitWeight
    left bitWidth hleftWeight
  have hrightGenerated := generatedTerm_of_leafBitWeight
    right bitWidth hrightWeight
  have hleftCode : (binaryTermCode left.term).length <= termBound := by
    dsimp only [termBound]
    exact generatedAuxTerm_code_length_le_compiler
      (nodeBudget := nodeBudget) hleftGenerated (by omega)
  have hrightCode : (binaryTermCode right.term).length <= termBound := by
    dsimp only [termBound]
    exact generatedAuxTerm_code_length_le_compiler
      (nodeBudget := nodeBudget) hrightGenerated (by omega)
  have hdisjunctionCost := equalityLessDisjunctionPayloadCost_le
    left.term right.term termBound hleftCode hrightCode
  by_cases hequal : left.value = right.value
  · let equalityProof := provePositiveEquality left right hequal
    let disjunction := disjunctionLeft
      (right := (“!!left.term < !!right.term” :
        LO.FirstOrder.ArithmeticProposition)) equalityProof
    let through := CertifiedPAProof.cast
      (lessEqualAsEqualityOrLessThan_formula left.term right.term)
      disjunction
    have hequality := provePositiveEquality_payloadLength_le_polynomial
      left right hequal
    have hequalityLocal : equalityProof.payloadLength <=
        positiveEqualityPayloadPolynomial left right := by
      dsimp only [equalityProof]
      exact hequality
    have hdisjunction := disjunctionLeft_payloadLength_le
      (right := (“!!left.term < !!right.term” :
        LO.FirstOrder.ArithmeticProposition)) equalityProof
    have hcast : through.payloadLength = disjunction.payloadLength := by
      dsimp only [through]
      exact cast_payloadLength _ _
    have houter :
        (provePositiveLessEqual left right hvalue).payloadLength =
          through.payloadLength := by
      simp only [provePositiveLessEqual, hequal]
      rfl
    rw [houter, hcast]
    calc
      disjunction.payloadLength <= equalityProof.payloadLength + 96 +
          8 * disjunctionSyntaxBudget
            (“!!left.term = !!right.term” :
              LO.FirstOrder.ArithmeticProposition)
            (“!!left.term < !!right.term” :
              LO.FirstOrder.ArithmeticProposition) := hdisjunction
      _ <= positiveEqualityPayloadPolynomial left right +
          closedOrderDisjunctionPayloadCostEnvelope termBound := by
        omega
      _ <= positiveLessEqualPayloadPolynomial left right := by
        simp only [positiveLessEqualPayloadPolynomial, nodeBudget, bitWidth,
          termBound]
        omega
  · have hstrict : left.value < right.value :=
      Nat.lt_of_le_of_ne hvalue hequal
    let strictProof := provePositiveLessThan left right hstrict
    let disjunction := disjunctionRight
      (left := (“!!left.term = !!right.term” :
        LO.FirstOrder.ArithmeticProposition)) strictProof
    let through := CertifiedPAProof.cast
      (lessEqualAsEqualityOrLessThan_formula left.term right.term)
      disjunction
    have hstrictBound :=
      provePositiveLessThan_payloadLength_le_polynomial
        left right hstrict
    have hstrictBoundLocal : strictProof.payloadLength <=
        positiveLessThanPayloadPolynomial left right := by
      dsimp only [strictProof]
      exact hstrictBound
    have hdisjunction := disjunctionRight_payloadLength_le
      (left := (“!!left.term = !!right.term” :
        LO.FirstOrder.ArithmeticProposition)) strictProof
    have hcast : through.payloadLength = disjunction.payloadLength := by
      dsimp only [through]
      exact cast_payloadLength _ _
    have houter :
        (provePositiveLessEqual left right hvalue).payloadLength =
          through.payloadLength := by
      simp only [provePositiveLessEqual, hequal]
      rfl
    rw [houter, hcast]
    calc
      disjunction.payloadLength <= strictProof.payloadLength + 96 +
          8 * disjunctionSyntaxBudget
            (“!!left.term = !!right.term” :
              LO.FirstOrder.ArithmeticProposition)
            (“!!left.term < !!right.term” :
              LO.FirstOrder.ArithmeticProposition) := hdisjunction
      _ <= positiveLessThanPayloadPolynomial left right +
          closedOrderDisjunctionPayloadCostEnvelope termBound := by
        omega
      _ <= positiveLessEqualPayloadPolynomial left right := by
        simp only [positiveLessEqualPayloadPolynomial, nodeBudget, bitWidth,
          termBound]
        omega

theorem provePositiveLessEqual_checked_polynomial
    (left right : ClosedPATerm)
    (hvalue : PositiveLessEqualCertificate left right) :
    listedCompactCertifiedPAProofVerifier
        (provePositiveLessEqual left right hvalue).code
        (compactFormulaCode
          (“!!left.term ≤ !!right.term” :
            LO.FirstOrder.ArithmeticProposition)) = true ∧
      (provePositiveLessEqual left right hvalue).payloadLength <=
        positiveLessEqualPayloadPolynomial left right := by
  exact ⟨provePositiveLessEqual_verifier_eq_true left right hvalue,
    provePositiveLessEqual_payloadLength_le_polynomial left right hvalue⟩

/-! ## Negative equality atom bound -/

def negativeEqualityNodeBudget
    (left right : ClosedPATerm) : Nat :=
  left.nodeCount + right.nodeCount + 1

def negativeEqualityBitWidth
    (left right : ClosedPATerm) : Nat :=
  left.leafBitWeight + right.leafBitWeight + 2

def negativeEqualityPayloadPolynomial
    (left right : ClosedPATerm) : Nat :=
  let nodeBudget := negativeEqualityNodeBudget left right
  let bitWidth := negativeEqualityBitWidth left right
  let termBound := compilerTermCodeEnvelope nodeBudget bitWidth
  positiveLessThanPayloadPolynomial left right +
    positiveLessThanPayloadPolynomial right left +
    2 * negativeEqualityPrimitiveCostEnvelope termBound +
    negativeEqualityModusTollensCostEnvelope termBound

theorem proveNegativeEquality_payloadLength_le_polynomial
    (left right : ClosedPATerm)
    (hvalue : NegativeEqualityCertificate left right) :
    (proveNegativeEquality left right hvalue).payloadLength <=
      negativeEqualityPayloadPolynomial left right := by
  let nodeBudget := negativeEqualityNodeBudget left right
  let bitWidth := negativeEqualityBitWidth left right
  let termBound := compilerTermCodeEnvelope nodeBudget bitWidth
  have hleftNodes : left.nodeCount <= nodeBudget := by
    unfold nodeBudget negativeEqualityNodeBudget
    omega
  have hrightNodes : right.nodeCount <= nodeBudget := by
    unfold nodeBudget negativeEqualityNodeBudget
    omega
  have hleftWeight : left.leafBitWeight <= bitWidth := by
    unfold bitWidth negativeEqualityBitWidth
    omega
  have hrightWeight : right.leafBitWeight <= bitWidth := by
    unfold bitWidth negativeEqualityBitWidth
    omega
  have hleftGenerated := generatedTerm_of_leafBitWeight
    left bitWidth hleftWeight
  have hrightGenerated := generatedTerm_of_leafBitWeight
    right bitWidth hrightWeight
  have hleftCode : (binaryTermCode left.term).length <= termBound := by
    dsimp only [termBound]
    exact generatedAuxTerm_code_length_le_compiler
      (nodeBudget := nodeBudget) hleftGenerated (by omega)
  have hrightCode : (binaryTermCode right.term).length <= termBound := by
    dsimp only [termBound]
    exact generatedAuxTerm_code_length_le_compiler
      (nodeBudget := nodeBudget) hrightGenerated (by omega)
  by_cases hforward : left.value < right.value
  · let strictProof := provePositiveLessThan left right hforward
    let through := proveNotEqualityOfLessThan
      left.term right.term strictProof
    have hstrict := provePositiveLessThan_payloadLength_le_polynomial
      left right hforward
    have hcore := proveNotEqualityOfLessThan_payloadLength_le_primitive
      left.term right.term strictProof termBound hleftCode hrightCode
    have hstrictLocal : strictProof.payloadLength <=
        positiveLessThanPayloadPolynomial left right := by
      dsimp only [strictProof]
      exact hstrict
    have hcoreLocal :
        (proveNotEqualityOfLessThan
          left.term right.term strictProof).payloadLength <=
          strictProof.payloadLength +
            negativeEqualityPrimitiveCostEnvelope
              (compilerTermCodeEnvelope nodeBudget bitWidth) := by
      dsimp only [termBound] at hcore
      exact hcore
    dsimp only [nodeBudget, bitWidth] at hcoreLocal
    have houter :
        (proveNegativeEquality left right hvalue).payloadLength =
          through.payloadLength := by
      simp only [proveNegativeEquality, hforward]
      rfl
    rw [houter]
    change (proveNotEqualityOfLessThan
      left.term right.term strictProof).payloadLength <= _
    unfold negativeEqualityPayloadPolynomial
    dsimp only [nodeBudget, bitWidth, termBound]
    omega
  · have hreverse : right.value < left.value := by
      unfold NegativeEqualityCertificate at hvalue
      omega
    let reverseStrictProof := provePositiveLessThan right left hreverse
    let reverseNegative := proveNotEqualityOfLessThan
      right.term left.term reverseStrictProof
    let through := modusTollens
      (equalitySymmetryImplication left.term right.term)
      reverseNegative
    have hstrict := provePositiveLessThan_payloadLength_le_polynomial
      right left hreverse
    have hcore := proveNotEqualityOfLessThan_payloadLength_le_primitive
      right.term left.term reverseStrictProof termBound hrightCode hleftCode
    have hmt := equalitySymmetryModusTollens_payloadLength_le_primitive
      left.term right.term reverseNegative termBound hleftCode hrightCode
    have hstrictLocal : reverseStrictProof.payloadLength <=
        positiveLessThanPayloadPolynomial right left := by
      dsimp only [reverseStrictProof]
      exact hstrict
    have hcoreLocal :
        (proveNotEqualityOfLessThan
          right.term left.term reverseStrictProof).payloadLength <=
          reverseStrictProof.payloadLength +
            negativeEqualityPrimitiveCostEnvelope
              (compilerTermCodeEnvelope nodeBudget bitWidth) := by
      dsimp only [termBound] at hcore
      exact hcore
    have hmtLocal :
        (modusTollens
          (equalitySymmetryImplication left.term right.term)
          reverseNegative).payloadLength <=
          reverseNegative.payloadLength +
            negativeEqualityModusTollensCostEnvelope
              (compilerTermCodeEnvelope nodeBudget bitWidth) := by
      dsimp only [termBound] at hmt
      exact hmt
    dsimp only [nodeBudget, bitWidth] at hcoreLocal hmtLocal
    dsimp only [reverseNegative] at hmtLocal
    have houter :
        (proveNegativeEquality left right hvalue).payloadLength =
          through.payloadLength := by
      simp only [proveNegativeEquality, hforward]
      rfl
    rw [houter]
    change (modusTollens
      (equalitySymmetryImplication left.term right.term)
      (proveNotEqualityOfLessThan
        right.term left.term reverseStrictProof)).payloadLength <= _
    unfold negativeEqualityPayloadPolynomial
    dsimp only [nodeBudget, bitWidth, termBound]
    omega

theorem proveNegativeEquality_checked_polynomial
    (left right : ClosedPATerm)
    (hvalue : NegativeEqualityCertificate left right) :
    listedCompactCertifiedPAProofVerifier
        (proveNegativeEquality left right hvalue).code
        (compactFormulaCode
          (∼(“!!left.term = !!right.term” :
            LO.FirstOrder.ArithmeticProposition))) = true ∧
      (proveNegativeEquality left right hvalue).payloadLength <=
        negativeEqualityPayloadPolynomial left right := by
  exact ⟨proveNegativeEquality_verifier_eq_true left right hvalue,
    proveNegativeEquality_payloadLength_le_polynomial left right hvalue⟩

/-! ## Negative strict-order atom bound -/

def negativeLessThanNodeBudget
    (left right : ClosedPATerm) : Nat :=
  left.nodeCount + right.nodeCount + 1

def negativeLessThanBitWidth
    (left right : ClosedPATerm) : Nat :=
  left.leafBitWeight + right.leafBitWeight + 2

def negativeLessThanPayloadPolynomial
    (left right : ClosedPATerm) : Nat :=
  let nodeBudget := negativeLessThanNodeBudget left right
  let bitWidth := negativeLessThanBitWidth left right
  let termBound := compilerTermCodeEnvelope nodeBudget bitWidth
  positiveEqualityPayloadPolynomial left right +
    positiveLessThanPayloadPolynomial right left +
    negativeOrderEqualityPrimitiveCostEnvelope termBound +
    negativeOrderReversePrimitiveCostEnvelope termBound

theorem proveNegativeLessThan_payloadLength_le_polynomial
    (left right : ClosedPATerm)
    (hvalue : NegativeLessThanCertificate left right) :
    (proveNegativeLessThan left right hvalue).payloadLength <=
      negativeLessThanPayloadPolynomial left right := by
  let nodeBudget := negativeLessThanNodeBudget left right
  let bitWidth := negativeLessThanBitWidth left right
  let termBound := compilerTermCodeEnvelope nodeBudget bitWidth
  have hleftNodes : left.nodeCount <= nodeBudget := by
    unfold nodeBudget negativeLessThanNodeBudget
    omega
  have hrightNodes : right.nodeCount <= nodeBudget := by
    unfold nodeBudget negativeLessThanNodeBudget
    omega
  have hleftWeight : left.leafBitWeight <= bitWidth := by
    unfold bitWidth negativeLessThanBitWidth
    omega
  have hrightWeight : right.leafBitWeight <= bitWidth := by
    unfold bitWidth negativeLessThanBitWidth
    omega
  have hleftGenerated := generatedTerm_of_leafBitWeight
    left bitWidth hleftWeight
  have hrightGenerated := generatedTerm_of_leafBitWeight
    right bitWidth hrightWeight
  have hleftCode : (binaryTermCode left.term).length <= termBound := by
    dsimp only [termBound]
    exact generatedAuxTerm_code_length_le_compiler
      (nodeBudget := nodeBudget) hleftGenerated (by omega)
  have hrightCode : (binaryTermCode right.term).length <= termBound := by
    dsimp only [termBound]
    exact generatedAuxTerm_code_length_le_compiler
      (nodeBudget := nodeBudget) hrightGenerated (by omega)
  by_cases hequal : left.value = right.value
  · let equalityProof := provePositiveEquality left right hequal
    let through := proveNotLessThanOfEquality
      left.term right.term equalityProof
    have hequality := provePositiveEquality_payloadLength_le_polynomial
      left right hequal
    have hcore := proveNotLessThanOfEquality_payloadLength_le_primitive
      left.term right.term equalityProof termBound hleftCode hrightCode
    have hequalityLocal : equalityProof.payloadLength <=
        positiveEqualityPayloadPolynomial left right := by
      dsimp only [equalityProof]
      exact hequality
    have hcoreLocal :
        (proveNotLessThanOfEquality
          left.term right.term equalityProof).payloadLength <=
          equalityProof.payloadLength +
            negativeOrderEqualityPrimitiveCostEnvelope
              (compilerTermCodeEnvelope nodeBudget bitWidth) := by
      dsimp only [termBound] at hcore
      exact hcore
    dsimp only [nodeBudget, bitWidth] at hcoreLocal
    have houter :
        (proveNegativeLessThan left right hvalue).payloadLength =
          through.payloadLength := by
      simp only [proveNegativeLessThan, hequal]
      rfl
    rw [houter]
    change (proveNotLessThanOfEquality
      left.term right.term equalityProof).payloadLength <= _
    unfold negativeLessThanPayloadPolynomial
    dsimp only [nodeBudget, bitWidth, termBound]
    omega
  · have hreverse : right.value < left.value := by
      unfold NegativeLessThanCertificate at hvalue
      omega
    let reverseProof := provePositiveLessThan right left hreverse
    let through := proveNotLessThanOfReverseLessThan
      left.term right.term reverseProof
    have hstrict := provePositiveLessThan_payloadLength_le_polynomial
      right left hreverse
    have hcore :=
      proveNotLessThanOfReverseLessThan_payloadLength_le_primitive
        left.term right.term reverseProof termBound hleftCode hrightCode
    have hstrictLocal : reverseProof.payloadLength <=
        positiveLessThanPayloadPolynomial right left := by
      dsimp only [reverseProof]
      exact hstrict
    have hcoreLocal :
        (proveNotLessThanOfReverseLessThan
          left.term right.term reverseProof).payloadLength <=
          reverseProof.payloadLength +
            negativeOrderReversePrimitiveCostEnvelope
              (compilerTermCodeEnvelope nodeBudget bitWidth) := by
      dsimp only [termBound] at hcore
      exact hcore
    dsimp only [nodeBudget, bitWidth] at hcoreLocal
    have houter :
        (proveNegativeLessThan left right hvalue).payloadLength =
          through.payloadLength := by
      simp only [proveNegativeLessThan, hequal]
      rfl
    rw [houter]
    change (proveNotLessThanOfReverseLessThan
      left.term right.term reverseProof).payloadLength <= _
    unfold negativeLessThanPayloadPolynomial
    dsimp only [nodeBudget, bitWidth, termBound]
    omega

theorem proveNegativeLessThan_checked_polynomial
    (left right : ClosedPATerm)
    (hvalue : NegativeLessThanCertificate left right) :
    listedCompactCertifiedPAProofVerifier
        (proveNegativeLessThan left right hvalue).code
        (compactFormulaCode
          (∼(“!!left.term < !!right.term” :
            LO.FirstOrder.ArithmeticProposition))) = true ∧
      (proveNegativeLessThan left right hvalue).payloadLength <=
        negativeLessThanPayloadPolynomial left right := by
  exact ⟨proveNegativeLessThan_verifier_eq_true left right hvalue,
    proveNegativeLessThan_payloadLength_le_polynomial left right hvalue⟩

/-! ## Negative non-strict-order atom bound -/

theorem negativeEqualityLessConjunctionSyntaxBudget_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    conjunctionSyntaxBudget
        (∼(“!!left = !!right” : LO.FirstOrder.ArithmeticProposition))
        (∼(“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)) <=
      8 * orderAtomicFormulaCodeEnvelope termBound + 8 := by
  let equalityAtom :=
    (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)
  let lessAtom :=
    (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)
  have hequality : (binaryFormulaCode equalityAtom).length <=
      orderAtomicFormulaCodeEnvelope termBound := by
    dsimp only [equalityAtom]
    exact equalityFormula_code_le_orderAtomic
      left right termBound hleft hright
  have hless : (binaryFormulaCode lessAtom).length <=
      orderAtomicFormulaCodeEnvelope termBound := by
    dsimp only [lessAtom]
    exact lessThanFormula_code_le_orderAtomic
      left right termBound hleft hright
  have hnegEquality := binaryFormulaCode_neg_length_le equalityAtom
  have hnegLess := binaryFormulaCode_neg_length_le lessAtom
  have hconjunction := binaryFormulaCode_and_length_le
    (∼equalityAtom) (∼lessAtom)
  unfold conjunctionSyntaxBudget
  dsimp only [equalityAtom, lessAtom] at *
  omega

def closedNegativeOrderConjunctionPayloadCostEnvelope
    (termBound : Nat) : Nat :=
  144 + 11 * (8 * orderAtomicFormulaCodeEnvelope termBound + 8)

theorem negativeEqualityLessConjunctionPayloadCost_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    144 + 11 * conjunctionSyntaxBudget
        (∼(“!!left = !!right” : LO.FirstOrder.ArithmeticProposition))
        (∼(“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)) <=
      closedNegativeOrderConjunctionPayloadCostEnvelope termBound := by
  have hsyntax := negativeEqualityLessConjunctionSyntaxBudget_le
    left right termBound hleft hright
  unfold closedNegativeOrderConjunctionPayloadCostEnvelope
  omega

def negativeLessEqualNodeBudget
    (left right : ClosedPATerm) : Nat :=
  left.nodeCount + right.nodeCount + 1

def negativeLessEqualBitWidth
    (left right : ClosedPATerm) : Nat :=
  left.leafBitWeight + right.leafBitWeight + 2

def negativeLessEqualPayloadPolynomial
    (left right : ClosedPATerm) : Nat :=
  let nodeBudget := negativeLessEqualNodeBudget left right
  let bitWidth := negativeLessEqualBitWidth left right
  let termBound := compilerTermCodeEnvelope nodeBudget bitWidth
  negativeEqualityPayloadPolynomial left right +
    negativeLessThanPayloadPolynomial left right +
    closedNegativeOrderConjunctionPayloadCostEnvelope termBound

theorem proveNegativeLessEqual_payloadLength_le_polynomial
    (left right : ClosedPATerm)
    (hvalue : NegativeLessEqualCertificate left right) :
    (proveNegativeLessEqual left right hvalue).payloadLength <=
      negativeLessEqualPayloadPolynomial left right := by
  let nodeBudget := negativeLessEqualNodeBudget left right
  let bitWidth := negativeLessEqualBitWidth left right
  let termBound := compilerTermCodeEnvelope nodeBudget bitWidth
  have hleftNodes : left.nodeCount <= nodeBudget := by
    unfold nodeBudget negativeLessEqualNodeBudget
    omega
  have hrightNodes : right.nodeCount <= nodeBudget := by
    unfold nodeBudget negativeLessEqualNodeBudget
    omega
  have hleftWeight : left.leafBitWeight <= bitWidth := by
    unfold bitWidth negativeLessEqualBitWidth
    omega
  have hrightWeight : right.leafBitWeight <= bitWidth := by
    unfold bitWidth negativeLessEqualBitWidth
    omega
  have hleftGenerated := generatedTerm_of_leafBitWeight
    left bitWidth hleftWeight
  have hrightGenerated := generatedTerm_of_leafBitWeight
    right bitWidth hrightWeight
  have hleftCode : (binaryTermCode left.term).length <= termBound := by
    dsimp only [termBound]
    exact generatedAuxTerm_code_length_le_compiler
      (nodeBudget := nodeBudget) hleftGenerated (by omega)
  have hrightCode : (binaryTermCode right.term).length <= termBound := by
    dsimp only [termBound]
    exact generatedAuxTerm_code_length_le_compiler
      (nodeBudget := nodeBudget) hrightGenerated (by omega)
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
  let through := CertifiedPAProof.cast
    (negativeLessEqualAsNegativeConjunction_formula left.term right.term)
    conjunctionProof
  have hequality := proveNegativeEquality_payloadLength_le_polynomial
    left right hnotEqual
  have hless := proveNegativeLessThan_payloadLength_le_polynomial
    left right hnotLess
  have hequalityLocal : negativeEquality.payloadLength <=
      negativeEqualityPayloadPolynomial left right := by
    dsimp only [negativeEquality]
    exact hequality
  have hlessLocal : negativeLessThan.payloadLength <=
      negativeLessThanPayloadPolynomial left right := by
    dsimp only [negativeLessThan]
    exact hless
  have hconjunction := conjunction_payloadLength_le
    negativeEquality negativeLessThan
  have hconjunctionCost :=
    negativeEqualityLessConjunctionPayloadCost_le
      left.term right.term termBound hleftCode hrightCode
  have hcast : through.payloadLength = conjunctionProof.payloadLength := by
    dsimp only [through]
    exact cast_payloadLength _ _
  have houter :
      (proveNegativeLessEqual left right hvalue).payloadLength =
        through.payloadLength := by
    rfl
  rw [houter, hcast]
  calc
    conjunctionProof.payloadLength <=
        negativeEquality.payloadLength + negativeLessThan.payloadLength +
          144 + 11 * conjunctionSyntaxBudget
            (∼(“!!left.term = !!right.term” :
              LO.FirstOrder.ArithmeticProposition))
            (∼(“!!left.term < !!right.term” :
              LO.FirstOrder.ArithmeticProposition)) := hconjunction
    _ <= negativeEqualityPayloadPolynomial left right +
        negativeLessThanPayloadPolynomial left right +
        closedNegativeOrderConjunctionPayloadCostEnvelope termBound := by
      omega
    _ = negativeLessEqualPayloadPolynomial left right := by
      simp only [negativeLessEqualPayloadPolynomial, nodeBudget, bitWidth,
        termBound]

theorem proveNegativeLessEqual_checked_polynomial
    (left right : ClosedPATerm)
    (hvalue : NegativeLessEqualCertificate left right) :
    listedCompactCertifiedPAProofVerifier
        (proveNegativeLessEqual left right hvalue).code
        (compactFormulaCode
          (∼(“!!left.term ≤ !!right.term” :
            LO.FirstOrder.ArithmeticProposition))) = true ∧
      (proveNegativeLessEqual left right hvalue).payloadLength <=
        negativeLessEqualPayloadPolynomial left right := by
  exact ⟨proveNegativeLessEqual_verifier_eq_true left right hvalue,
    proveNegativeLessEqual_payloadLength_le_polynomial left right hvalue⟩

/-! ## Unified closed atomic-literal bound -/

namespace ClosedPAAtomicLiteralBounds

def payloadPolynomial : ClosedPAAtomicLiteral → Nat
  | .equality left right =>
      positiveEqualityPayloadPolynomial left right
  | .disequality left right =>
      negativeEqualityPayloadPolynomial left right
  | .lessThan left right =>
      positiveLessThanPayloadPolynomial left right
  | .notLessThan left right =>
      negativeLessThanPayloadPolynomial left right
  | .lessEqual left right =>
      positiveLessEqualPayloadPolynomial left right
  | .notLessEqual left right =>
      negativeLessEqualPayloadPolynomial left right

theorem compile_payloadLength_le_polynomial
    (literal : ClosedPAAtomicLiteral)
    (hvalue : literal.Truth) :
    (literal.compile hvalue).payloadLength <=
      payloadPolynomial literal := by
  cases literal with
  | equality left right =>
      exact provePositiveEquality_payloadLength_le_polynomial
        left right hvalue
  | disequality left right =>
      exact proveNegativeEquality_payloadLength_le_polynomial
        left right hvalue
  | lessThan left right =>
      exact provePositiveLessThan_payloadLength_le_polynomial
        left right hvalue
  | notLessThan left right =>
      exact proveNegativeLessThan_payloadLength_le_polynomial
        left right hvalue
  | lessEqual left right =>
      exact provePositiveLessEqual_payloadLength_le_polynomial
        left right hvalue
  | notLessEqual left right =>
      exact proveNegativeLessEqual_payloadLength_le_polynomial
        left right hvalue

theorem compile_checked_polynomial
    (literal : ClosedPAAtomicLiteral)
    (hvalue : literal.Truth) :
    listedCompactCertifiedPAProofVerifier
        (literal.compile hvalue).code
        (compactFormulaCode literal.formula) = true ∧
      (literal.compile hvalue).payloadLength <=
        payloadPolynomial literal := by
  exact ⟨ClosedPAAtomicLiteral.compile_verifier_eq_true literal hvalue,
    compile_payloadLength_le_polynomial literal hvalue⟩

end ClosedPAAtomicLiteralBounds

#print axioms generatedTerm_code_length_le_compiler
#print axioms proveNormalization_payloadLength_le_polynomial
#print axioms provePositiveEquality_payloadLength_le_polynomial
#print axioms provePositiveEquality_checked_polynomial
#print axioms provePositiveLessThan_payloadLength_le_polynomial
#print axioms provePositiveLessThan_checked_polynomial
#print axioms provePositiveLessEqual_payloadLength_le_polynomial
#print axioms provePositiveLessEqual_checked_polynomial
#print axioms proveNegativeEquality_payloadLength_le_polynomial
#print axioms proveNegativeEquality_checked_polynomial
#print axioms proveNegativeLessThan_payloadLength_le_polynomial
#print axioms proveNegativeLessThan_checked_polynomial
#print axioms proveNegativeLessEqual_payloadLength_le_polynomial
#print axioms proveNegativeLessEqual_checked_polynomial
#print axioms ClosedPAAtomicLiteralBounds.compile_payloadLength_le_polynomial
#print axioms ClosedPAAtomicLiteralBounds.compile_checked_polynomial

end ClosedPATerm

end FoundationCompactPAClosedAtomicCompilerBounds
