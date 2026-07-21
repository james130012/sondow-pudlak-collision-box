import integration.FoundationCompactPABoundedFormulaCompiler
import integration.FoundationCompactPAClosedAtomicCompilerBounds
import integration.FoundationCompactPABoundedUniversalPolynomialBounds

/-!
# Structural payload bounds for the checked bounded-formula compiler

Every constructor is charged by the exact public payload theorem of the proof
constructor it invokes.  This file first establishes an auditable recursive
bound.  The bounded-universal branch reuses the independently checked
finite-exhaustion compiler and its honest input-size polynomial.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABoundedFormulaCompilerBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactCertifiedConjunction
open FoundationCompactCertifiedDisjunction
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAClosedAtomicCompiler
open FoundationCompactPAClosedAtomicCompiler.ClosedPATerm
open FoundationCompactPAClosedAtomicCompiler.ClosedPATerm.ClosedPAAtomicLiteral
open FoundationCompactPAClosedAtomicCompilerBounds
open FoundationCompactPAClosedAtomicCompilerBounds.ClosedPATerm
open FoundationCompactPAClosedAtomicCompilerBounds.ClosedPATerm.ClosedPAAtomicLiteralBounds
open FoundationCompactPABoundedFormulaCompiler
open FoundationCompactPABoundedUniversalCompiler
open FoundationCompactPABoundedUniversalCompiler.CheckedFiniteBoundedUniversalCertificate
open FoundationCompactPABoundedUniversalCertificateCode
open FoundationCompactPABoundedUniversalPolynomialBounds

namespace CheckedClosedBoundedFormulaCertificate

open FoundationCompactPABoundedFormulaCompiler.CheckedClosedBoundedFormulaCertificate

/-- Formula-specific structural payload bound obtained by adding the exact
cost theorem for every constructor in the certificate tree. -/
def structuralPayloadBound :
    {formula : LO.FirstOrder.ArithmeticProposition} →
    CheckedClosedBoundedFormulaCertificate formula → Nat
  | _, .verum => 48 + 9 * verumSyntaxBudget
  | _, .atomic literal _ =>
      ClosedPAAtomicLiteralBounds.payloadPolynomial literal
  | _, .conjunction (left := left) (right := right)
      leftCertificate rightCertificate =>
      structuralPayloadBound leftCertificate +
        structuralPayloadBound rightCertificate + 144 +
        11 * conjunctionSyntaxBudget left right
  | _, .disjunctionLeft (left := left) (right := right)
      leftCertificate =>
      structuralPayloadBound leftCertificate + 96 +
        8 * disjunctionSyntaxBudget left right
  | _, .disjunctionRight (left := left) (right := right)
      rightCertificate =>
      structuralPayloadBound rightCertificate + 96 +
        8 * disjunctionSyntaxBudget left right
  | _, .existsWitness body witness bodyCertificate =>
      structuralPayloadBound bodyCertificate + 96 +
        14 * existsIntroSyntaxBudget body witness.term
  | _, .boundedUniversal certificate =>
      FoundationCompactPABoundedUniversalPolynomialBounds.CheckedFiniteBoundedUniversalCertificate.boundedUniversalPayloadPolynomial
        (FoundationCompactPABoundedUniversalCertificateCode.CheckedFiniteBoundedUniversalCertificate.encodedSize
          certificate)

theorem compile_payloadLength_le_structuralPayloadBound
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedClosedBoundedFormulaCertificate formula) :
    certificate.compile.payloadLength <=
      structuralPayloadBound certificate := by
  induction certificate with
  | verum =>
      exact verumProof_payloadLength_le
  | atomic literal hvalue =>
      exact ClosedPAAtomicLiteralBounds.compile_payloadLength_le_polynomial
        literal hvalue
  | conjunction leftCertificate rightCertificate ihLeft ihRight =>
      have hconstructor := conjunction_payloadLength_le
        leftCertificate.compile rightCertificate.compile
      simp only [FoundationCompactPABoundedFormulaCompiler.CheckedClosedBoundedFormulaCertificate.compile,
        structuralPayloadBound]
      omega
  | disjunctionLeft leftCertificate ihLeft =>
      simp only [FoundationCompactPABoundedFormulaCompiler.CheckedClosedBoundedFormulaCertificate.compile,
        structuralPayloadBound]
      apply le_trans
        (FoundationCompactCertifiedDisjunction.disjunctionLeft_payloadLength_le
          leftCertificate.compile)
      omega
  | disjunctionRight rightCertificate ihRight =>
      simp only [FoundationCompactPABoundedFormulaCompiler.CheckedClosedBoundedFormulaCertificate.compile,
        structuralPayloadBound]
      apply le_trans
        (FoundationCompactCertifiedDisjunction.disjunctionRight_payloadLength_le
          rightCertificate.compile)
      omega
  | existsWitness body witness bodyCertificate ihBody =>
      have hconstructor := existsIntro_payloadLength_le
        witness.term bodyCertificate.compile
      simp only [FoundationCompactPABoundedFormulaCompiler.CheckedClosedBoundedFormulaCertificate.compile,
        structuralPayloadBound]
      omega
  | boundedUniversal certificate =>
      simpa only [
        FoundationCompactPABoundedFormulaCompiler.CheckedClosedBoundedFormulaCertificate.compile,
        structuralPayloadBound] using
        FoundationCompactPABoundedUniversalPolynomialBounds.CheckedFiniteBoundedUniversalCertificate.compile_payloadLength_le_polynomial
          certificate

/-! ## Honest proof-free serialization of the complete certificate tree -/

def proofFreeCode :
    {formula : LO.FirstOrder.ArithmeticProposition} →
      CheckedClosedBoundedFormulaCertificate formula → List Bool
  | _, .verum =>
      binaryNatCode 0 ++
        binaryFormulaCode (⊤ : LO.FirstOrder.ArithmeticProposition)
  | _, .atomic literal _ =>
      binaryNatCode 1 ++ binaryFormulaCode literal.formula ++
        FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.proofFreeCode
          literal
  | _, .conjunction (left := left) (right := right)
      leftCertificate rightCertificate =>
      binaryNatCode 2 ++ binaryFormulaCode (left ⋏ right) ++
        proofFreeCode leftCertificate ++ proofFreeCode rightCertificate
  | _, .disjunctionLeft (left := left) (right := right)
      leftCertificate =>
      binaryNatCode 3 ++ binaryFormulaCode (left ⋎ right) ++
        proofFreeCode leftCertificate
  | _, .disjunctionRight (left := left) (right := right)
      rightCertificate =>
      binaryNatCode 4 ++ binaryFormulaCode (left ⋎ right) ++
        proofFreeCode rightCertificate
  | _, .existsWitness body witness bodyCertificate =>
      binaryNatCode 5 ++ binaryFormulaCode (∃⁰ body) ++
        FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.proofFreeCode
          witness ++ proofFreeCode bodyCertificate
  | _, .boundedUniversal (bound := bound) (body := body) certificate =>
      binaryNatCode 6 ++
        binaryFormulaCode (∀⁰ finiteBoundedUniversalBody bound body) ++
        FoundationCompactPABoundedUniversalCertificateCode.CheckedFiniteBoundedUniversalCertificate.proofFreeCode
          certificate

def nodeCount :
    {formula : LO.FirstOrder.ArithmeticProposition} →
      CheckedClosedBoundedFormulaCertificate formula → Nat
  | _, .verum => 1
  | _, .atomic _ _ => 1
  | _, .conjunction leftCertificate rightCertificate =>
      1 + nodeCount leftCertificate + nodeCount rightCertificate
  | _, .disjunctionLeft leftCertificate =>
      1 + nodeCount leftCertificate
  | _, .disjunctionRight rightCertificate =>
      1 + nodeCount rightCertificate
  | _, .existsWitness _ _ bodyCertificate =>
      1 + nodeCount bodyCertificate
  | _, .boundedUniversal _ => 1

theorem targetFormulaCodeLength_le_proofFreeCode_length
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedClosedBoundedFormulaCertificate formula) :
    (binaryFormulaCode formula).length <=
      (proofFreeCode certificate).length := by
  cases certificate with
  | verum =>
      simp only [proofFreeCode, List.length_append]
      omega
  | atomic literal hvalue =>
      simp only [proofFreeCode, List.length_append]
      omega
  | conjunction leftCertificate rightCertificate =>
      simp only [proofFreeCode, List.length_append]
      omega
  | disjunctionLeft leftCertificate =>
      simp only [proofFreeCode, List.length_append]
      omega
  | disjunctionRight rightCertificate =>
      simp only [proofFreeCode, List.length_append]
      omega
  | existsWitness body witness bodyCertificate =>
      simp only [proofFreeCode, List.length_append]
      omega
  | boundedUniversal certificate =>
      simp only [proofFreeCode, List.length_append]
      omega

theorem nodeCount_le_proofFreeCode_length
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedClosedBoundedFormulaCertificate formula) :
    nodeCount certificate <= (proofFreeCode certificate).length := by
  induction certificate with
  | verum =>
      have htag := two_le_binaryNatCode_length 0
      simp only [nodeCount, proofFreeCode, List.length_append]
      omega
  | atomic literal hvalue =>
      have htag := two_le_binaryNatCode_length 1
      simp only [nodeCount, proofFreeCode, List.length_append]
      omega
  | conjunction leftCertificate rightCertificate ihLeft ihRight =>
      have htag := two_le_binaryNatCode_length 2
      simp only [nodeCount, proofFreeCode, List.length_append]
      omega
  | disjunctionLeft leftCertificate ihLeft =>
      have htag := two_le_binaryNatCode_length 3
      simp only [nodeCount, proofFreeCode, List.length_append]
      omega
  | disjunctionRight rightCertificate ihRight =>
      have htag := two_le_binaryNatCode_length 4
      simp only [nodeCount, proofFreeCode, List.length_append]
      omega
  | existsWitness body witness bodyCertificate ihBody =>
      have htag := two_le_binaryNatCode_length 5
      simp only [nodeCount, proofFreeCode, List.length_append]
      omega
  | boundedUniversal certificate =>
      have htag := two_le_binaryNatCode_length 6
      simp only [nodeCount, proofFreeCode, List.length_append]
      omega

/-! ## Uniform leaf and connector costs -/

def cumulativeBoundedUniversalPayloadEnvelope (resource : Nat) : Nat :=
  ∑ inputSize ∈ Finset.range (resource + 1),
    FoundationCompactPABoundedUniversalPolynomialBounds.CheckedFiniteBoundedUniversalCertificate.boundedUniversalPayloadPolynomial
      inputSize

theorem boundedUniversalPayloadPolynomial_le_cumulative
    (inputSize resource : Nat) (hinput : inputSize <= resource) :
    FoundationCompactPABoundedUniversalPolynomialBounds.CheckedFiniteBoundedUniversalCertificate.boundedUniversalPayloadPolynomial
        inputSize <=
      cumulativeBoundedUniversalPayloadEnvelope resource := by
  have hmem : inputSize ∈ Finset.range (resource + 1) := by
    simp
    omega
  unfold cumulativeBoundedUniversalPayloadEnvelope
  exact Finset.single_le_sum
    (f := fun candidate =>
      FoundationCompactPABoundedUniversalPolynomialBounds.CheckedFiniteBoundedUniversalCertificate.boundedUniversalPayloadPolynomial
        candidate)
    (s := Finset.range (resource + 1))
    (fun candidate _ => Nat.zero_le
      (FoundationCompactPABoundedUniversalPolynomialBounds.CheckedFiniteBoundedUniversalCertificate.boundedUniversalPayloadPolynomial
        candidate))
    hmem

def boundedFormulaLeafPayloadEnvelope (resource : Nat) : Nat :=
  (48 + 9 * verumSyntaxBudget) +
    ClosedPAAtomicLiteralBounds.encodedPayloadPolynomial resource +
    cumulativeBoundedUniversalPayloadEnvelope resource + 1

def boundedFormulaTermCodeEnvelope (resource : Nat) : Nat :=
  FoundationCompactPAClosedAtomicCompilerBounds.ClosedPATerm.compilerTermCodeEnvelope
    resource resource

def boundedFormulaConnectorPayloadEnvelope (resource : Nat) : Nat :=
  1024 + 256 *
    (resource + boundedFormulaTermCodeEnvelope resource + 1)

def localLeafPayload :
    {formula : LO.FirstOrder.ArithmeticProposition} →
      CheckedClosedBoundedFormulaCertificate formula → Nat
  | _, .verum => 48 + 9 * verumSyntaxBudget
  | _, .atomic literal _ =>
      ClosedPAAtomicLiteralBounds.payloadPolynomial literal
  | _, .conjunction _ _ => 0
  | _, .disjunctionLeft _ => 0
  | _, .disjunctionRight _ => 0
  | _, .existsWitness _ _ _ => 0
  | _, .boundedUniversal certificate =>
      FoundationCompactPABoundedUniversalPolynomialBounds.CheckedFiniteBoundedUniversalCertificate.boundedUniversalPayloadPolynomial
        (FoundationCompactPABoundedUniversalCertificateCode.CheckedFiniteBoundedUniversalCertificate.encodedSize
          certificate)

def localConnectorPayload :
    {formula : LO.FirstOrder.ArithmeticProposition} →
      CheckedClosedBoundedFormulaCertificate formula → Nat
  | _, .verum => 0
  | _, .atomic _ _ => 0
  | _, .conjunction (left := left) (right := right) _ _ =>
      144 + 11 * conjunctionSyntaxBudget left right
  | _, .disjunctionLeft (left := left) (right := right) _ =>
      96 + 8 * disjunctionSyntaxBudget left right
  | _, .disjunctionRight (left := left) (right := right) _ =>
      96 + 8 * disjunctionSyntaxBudget left right
  | _, .existsWitness body witness _ =>
      96 + 14 * existsIntroSyntaxBudget body witness.term
  | _, .boundedUniversal _ => 0

theorem localLeafPayload_le_envelope
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedClosedBoundedFormulaCertificate formula)
    (resource : Nat)
    (hcode : (proofFreeCode certificate).length <= resource) :
    localLeafPayload certificate <=
      boundedFormulaLeafPayloadEnvelope resource := by
  cases certificate with
  | verum =>
      simp only [localLeafPayload]
      unfold boundedFormulaLeafPayloadEnvelope
      omega
  | atomic literal hvalue =>
      have hliteralCode :
          (FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.proofFreeCode
            literal).length <= resource := by
        apply le_trans ?_ hcode
        simp only [proofFreeCode, List.length_append]
        omega
      have hencoded := ClosedPAAtomicLiteralBounds.payloadPolynomial_le_encoded
        literal
      have hmono := ClosedPAAtomicLiteralBounds.encodedPayloadPolynomial_mono
        hliteralCode
      simp only [localLeafPayload]
      unfold boundedFormulaLeafPayloadEnvelope
      omega
  | conjunction leftCertificate rightCertificate =>
      simp [localLeafPayload]
  | disjunctionLeft leftCertificate =>
      simp [localLeafPayload]
  | disjunctionRight rightCertificate =>
      simp [localLeafPayload]
  | existsWitness body witness bodyCertificate =>
      simp [localLeafPayload]
  | boundedUniversal certificate =>
      have hinput :
          FoundationCompactPABoundedUniversalCertificateCode.CheckedFiniteBoundedUniversalCertificate.encodedSize
              certificate <= resource := by
        unfold FoundationCompactPABoundedUniversalCertificateCode.CheckedFiniteBoundedUniversalCertificate.encodedSize
        apply le_trans ?_ hcode
        simp only [proofFreeCode, List.length_append]
        omega
      have hcumulative := boundedUniversalPayloadPolynomial_le_cumulative
        _ resource hinput
      simp only [localLeafPayload]
      unfold boundedFormulaLeafPayloadEnvelope
      omega

theorem localConnectorPayload_le_envelope
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedClosedBoundedFormulaCertificate formula)
    (resource : Nat)
    (hcode : (proofFreeCode certificate).length <= resource) :
    localConnectorPayload certificate <=
      boundedFormulaConnectorPayloadEnvelope resource := by
  cases certificate with
  | verum => simp [localConnectorPayload]
  | atomic literal hvalue => simp [localConnectorPayload]
  | @conjunction left right leftCertificate rightCertificate =>
      have hroot := targetFormulaCodeLength_le_proofFreeCode_length
        (CheckedClosedBoundedFormulaCertificate.conjunction
          leftCertificate rightCertificate)
      have hrootBound := hroot.trans hcode
      have hleft : (binaryFormulaCode left).length <= resource := by
        apply le_trans ?_ hrootBound
        simp [binaryFormulaCode]
        omega
      have hright : (binaryFormulaCode right).length <= resource := by
        apply le_trans ?_ hrootBound
        simp [binaryFormulaCode]
        omega
      simp only [localConnectorPayload]
      unfold conjunctionSyntaxBudget boundedFormulaConnectorPayloadEnvelope
      omega
  | @disjunctionLeft left right leftCertificate =>
      have hroot := targetFormulaCodeLength_le_proofFreeCode_length
        (CheckedClosedBoundedFormulaCertificate.disjunctionLeft
          (right := right) leftCertificate)
      have hrootBound := hroot.trans hcode
      have hleft : (binaryFormulaCode left).length <= resource := by
        apply le_trans ?_ hrootBound
        simp [binaryFormulaCode]
        omega
      have hright : (binaryFormulaCode right).length <= resource := by
        apply le_trans ?_ hrootBound
        simp [binaryFormulaCode]
        omega
      simp only [localConnectorPayload]
      unfold disjunctionSyntaxBudget boundedFormulaConnectorPayloadEnvelope
      omega
  | @disjunctionRight left right rightCertificate =>
      have hroot := targetFormulaCodeLength_le_proofFreeCode_length
        (CheckedClosedBoundedFormulaCertificate.disjunctionRight
          (left := left) rightCertificate)
      have hrootBound := hroot.trans hcode
      have hleft : (binaryFormulaCode left).length <= resource := by
        apply le_trans ?_ hrootBound
        simp [binaryFormulaCode]
        omega
      have hright : (binaryFormulaCode right).length <= resource := by
        apply le_trans ?_ hrootBound
        simp [binaryFormulaCode]
        omega
      simp only [localConnectorPayload]
      unfold disjunctionSyntaxBudget boundedFormulaConnectorPayloadEnvelope
      omega
  | existsWitness body witness bodyCertificate =>
      have hroot := targetFormulaCodeLength_le_proofFreeCode_length
        (CheckedClosedBoundedFormulaCertificate.existsWitness
          body witness bodyCertificate)
      have hrootBound := hroot.trans hcode
      have hbody : (binaryFormulaCode body).length <= resource := by
        apply le_trans ?_ hrootBound
        simp [binaryFormulaCode]
      have hbodyCertificateCode :
          (proofFreeCode bodyCertificate).length <= resource := by
        apply le_trans ?_ hcode
        simp only [proofFreeCode, List.length_append]
        omega
      have hinstance :=
        (targetFormulaCodeLength_le_proofFreeCode_length
          bodyCertificate).trans hbodyCertificateCode
      have hwitnessCode :
          (FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.proofFreeCode
            witness).length <= resource := by
        apply le_trans ?_ hcode
        simp only [proofFreeCode, List.length_append]
        omega
      have htermRaw :=
        FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.termCode_length_le_compilerCode
          witness
      have htermMono :=
        FoundationCompactPABoundedUniversalPolynomialBounds.compilerTermCodeEnvelope_diagonal_mono
          hwitnessCode
      have hterm : (binaryTermCode witness.term).length <=
          boundedFormulaTermCodeEnvelope resource := by
        unfold boundedFormulaTermCodeEnvelope
        exact htermRaw.trans htermMono
      simp only [localConnectorPayload]
      unfold existsIntroSyntaxBudget boundedFormulaConnectorPayloadEnvelope
      omega
  | boundedUniversal certificate => simp [localConnectorPayload]

def boundedFormulaNodePayloadEnvelope (resource : Nat) : Nat :=
  boundedFormulaLeafPayloadEnvelope resource +
    boundedFormulaConnectorPayloadEnvelope resource + 1

theorem structuralPayloadBound_le_nodeCount_mul_envelope
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedClosedBoundedFormulaCertificate formula)
    (resource : Nat)
    (hcode : (proofFreeCode certificate).length <= resource) :
    structuralPayloadBound certificate <=
      nodeCount certificate * boundedFormulaNodePayloadEnvelope resource := by
  induction certificate generalizing resource with
  | verum =>
      have hleaf := localLeafPayload_le_envelope
        (CheckedClosedBoundedFormulaCertificate.verum) resource hcode
      simp only [structuralPayloadBound, nodeCount, localLeafPayload] at hleaf ⊢
      unfold boundedFormulaNodePayloadEnvelope
      omega
  | atomic literal hvalue =>
      have hleaf := localLeafPayload_le_envelope
        (CheckedClosedBoundedFormulaCertificate.atomic literal hvalue)
        resource hcode
      simp only [structuralPayloadBound, nodeCount, localLeafPayload] at hleaf ⊢
      unfold boundedFormulaNodePayloadEnvelope
      omega
  | conjunction leftCertificate rightCertificate ihLeft ihRight =>
      let total := boundedFormulaNodePayloadEnvelope resource
      have hleftCode : (proofFreeCode leftCertificate).length <= resource := by
        apply le_trans ?_ hcode
        simp only [proofFreeCode, List.length_append]
        omega
      have hrightCode : (proofFreeCode rightCertificate).length <= resource := by
        apply le_trans ?_ hcode
        simp only [proofFreeCode, List.length_append]
        omega
      have hleft := ihLeft resource hleftCode
      have hright := ihRight resource hrightCode
      have hlocal := localConnectorPayload_le_envelope
        (CheckedClosedBoundedFormulaCertificate.conjunction
          leftCertificate rightCertificate) resource hcode
      have hlocalTotal :
          localConnectorPayload
              (CheckedClosedBoundedFormulaCertificate.conjunction
                leftCertificate rightCertificate) <= total := by
        exact hlocal.trans (by
          dsimp only [total]
          unfold boundedFormulaNodePayloadEnvelope
          omega)
      simp only [localConnectorPayload] at hlocalTotal
      simp only [structuralPayloadBound, nodeCount]
      dsimp only [total] at hleft hright hlocalTotal ⊢
      calc
        _ <= nodeCount leftCertificate *
                boundedFormulaNodePayloadEnvelope resource +
              nodeCount rightCertificate *
                boundedFormulaNodePayloadEnvelope resource +
              boundedFormulaNodePayloadEnvelope resource := by
          omega
        _ = (1 + nodeCount leftCertificate + nodeCount rightCertificate) *
            boundedFormulaNodePayloadEnvelope resource := by
          ring
  | @disjunctionLeft left right leftCertificate ihLeft =>
      let total := boundedFormulaNodePayloadEnvelope resource
      have hleftCode : (proofFreeCode leftCertificate).length <= resource := by
        apply le_trans ?_ hcode
        simp only [proofFreeCode, List.length_append]
        omega
      have hleftBound := ihLeft resource hleftCode
      have hlocal := localConnectorPayload_le_envelope
        (CheckedClosedBoundedFormulaCertificate.disjunctionLeft
          (right := right) leftCertificate) resource hcode
      have hlocalTotal :
          localConnectorPayload
              (CheckedClosedBoundedFormulaCertificate.disjunctionLeft
                (right := right) leftCertificate) <= total := by
        exact hlocal.trans (by
          dsimp only [total]
          unfold boundedFormulaNodePayloadEnvelope
          omega)
      simp only [localConnectorPayload] at hlocalTotal
      simp only [structuralPayloadBound, nodeCount]
      dsimp only [total] at hleftBound hlocalTotal ⊢
      calc
        _ <= nodeCount leftCertificate *
                boundedFormulaNodePayloadEnvelope resource +
              boundedFormulaNodePayloadEnvelope resource := by
          omega
        _ = (1 + nodeCount leftCertificate) *
            boundedFormulaNodePayloadEnvelope resource := by
          ring
  | @disjunctionRight left right rightCertificate ihRight =>
      let total := boundedFormulaNodePayloadEnvelope resource
      have hrightCode : (proofFreeCode rightCertificate).length <= resource := by
        apply le_trans ?_ hcode
        simp only [proofFreeCode, List.length_append]
        omega
      have hrightBound := ihRight resource hrightCode
      have hlocal := localConnectorPayload_le_envelope
        (CheckedClosedBoundedFormulaCertificate.disjunctionRight
          (left := left) rightCertificate) resource hcode
      have hlocalTotal :
          localConnectorPayload
              (CheckedClosedBoundedFormulaCertificate.disjunctionRight
                (left := left) rightCertificate) <= total := by
        exact hlocal.trans (by
          dsimp only [total]
          unfold boundedFormulaNodePayloadEnvelope
          omega)
      simp only [localConnectorPayload] at hlocalTotal
      simp only [structuralPayloadBound, nodeCount]
      dsimp only [total] at hrightBound hlocalTotal ⊢
      calc
        _ <= nodeCount rightCertificate *
                boundedFormulaNodePayloadEnvelope resource +
              boundedFormulaNodePayloadEnvelope resource := by
          omega
        _ = (1 + nodeCount rightCertificate) *
            boundedFormulaNodePayloadEnvelope resource := by
          ring
  | existsWitness body witness bodyCertificate ihBody =>
      let total := boundedFormulaNodePayloadEnvelope resource
      have hbodyCode : (proofFreeCode bodyCertificate).length <= resource := by
        apply le_trans ?_ hcode
        simp only [proofFreeCode, List.length_append]
        omega
      have hbodyBound := ihBody resource hbodyCode
      have hlocal := localConnectorPayload_le_envelope
        (CheckedClosedBoundedFormulaCertificate.existsWitness
          body witness bodyCertificate) resource hcode
      have hlocalTotal :
          localConnectorPayload
              (CheckedClosedBoundedFormulaCertificate.existsWitness
                body witness bodyCertificate) <= total := by
        exact hlocal.trans (by
          dsimp only [total]
          unfold boundedFormulaNodePayloadEnvelope
          omega)
      simp only [localConnectorPayload] at hlocalTotal
      simp only [structuralPayloadBound, nodeCount]
      dsimp only [total] at hbodyBound hlocalTotal ⊢
      calc
        _ <= nodeCount bodyCertificate *
                boundedFormulaNodePayloadEnvelope resource +
              boundedFormulaNodePayloadEnvelope resource := by
          omega
        _ = (1 + nodeCount bodyCertificate) *
            boundedFormulaNodePayloadEnvelope resource := by
          ring
  | boundedUniversal certificate =>
      have hleaf := localLeafPayload_le_envelope
        (CheckedClosedBoundedFormulaCertificate.boundedUniversal certificate)
        resource hcode
      simp only [structuralPayloadBound, nodeCount, localLeafPayload] at hleaf ⊢
      unfold boundedFormulaNodePayloadEnvelope
      omega

def encodedSize
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedClosedBoundedFormulaCertificate formula) : Nat :=
  (proofFreeCode certificate).length

def boundedFormulaPayloadPolynomial (resource : Nat) : Nat :=
  resource * boundedFormulaNodePayloadEnvelope resource

theorem structuralPayloadBound_le_polynomial
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedClosedBoundedFormulaCertificate formula) :
    structuralPayloadBound certificate <=
      boundedFormulaPayloadPolynomial (encodedSize certificate) := by
  have hstructural := structuralPayloadBound_le_nodeCount_mul_envelope
    certificate (encodedSize certificate) le_rfl
  have hnodes := nodeCount_le_proofFreeCode_length certificate
  exact hstructural.trans (by
    unfold boundedFormulaPayloadPolynomial encodedSize
    exact Nat.mul_le_mul_right _ hnodes)

theorem compile_payloadLength_le_polynomial
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedClosedBoundedFormulaCertificate formula) :
    certificate.compile.payloadLength <=
      boundedFormulaPayloadPolynomial (encodedSize certificate) := by
  exact (compile_payloadLength_le_structuralPayloadBound certificate).trans
    (structuralPayloadBound_le_polynomial certificate)

theorem compile_checked_polynomial
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedClosedBoundedFormulaCertificate formula) :
    listedCompactCertifiedPAProofVerifier
        certificate.compile.code (compactFormulaCode formula) = true ∧
      certificate.compile.payloadLength <=
        boundedFormulaPayloadPolynomial (encodedSize certificate) :=
  ⟨compile_verifier_eq_true certificate,
    compile_payloadLength_le_polynomial certificate⟩

theorem compile_checked_structuralPayloadBound
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedClosedBoundedFormulaCertificate formula) :
    listedCompactCertifiedPAProofVerifier
        certificate.compile.code (compactFormulaCode formula) = true ∧
      certificate.compile.payloadLength <=
        structuralPayloadBound certificate := by
  exact ⟨compile_verifier_eq_true certificate,
    compile_payloadLength_le_structuralPayloadBound certificate⟩

#print axioms compile_payloadLength_le_structuralPayloadBound
#print axioms compile_checked_structuralPayloadBound
#print axioms nodeCount_le_proofFreeCode_length
#print axioms compile_checked_polynomial

end CheckedClosedBoundedFormulaCertificate

end FoundationCompactPABoundedFormulaCompilerBounds
