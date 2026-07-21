import integration.FoundationCompactCertifiedContextualModusPonens
import integration.FoundationCompactPAQuantitativeOrderBounds
import integration.FoundationCompactCertifiedModusTollens

/-!
# Proof-producing strict-order asymmetry

From a checked PA proof of `right < left`, this module emits a checked proof of
`not (left < right)`.  The construction applies the explicit transitivity
proof under the one-formula context `not (left < right)` and closes the result
against the explicit irreflexivity proof of `left < left`.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPANegativeOrder

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAQuantitativeOrder
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactCertifiedModusTollens

def negativeOrderForwardAtom
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)

def negativeOrderReverseAtom
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  (“!!right < !!left” : LO.FirstOrder.ArithmeticProposition)

def negativeOrderSelfAtom
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  (“!!left < !!left” : LO.FirstOrder.ArithmeticProposition)

def negativeOrderAntecedent
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  negativeOrderForwardAtom left right ⋏
    negativeOrderReverseAtom left right

def negativeOrderContext
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    Finset LO.FirstOrder.ArithmeticProposition :=
  {∼negativeOrderForwardAtom left right}

theorem negativeOrderTransImplication_formula
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (((“!!left < !!right” : LO.FirstOrder.ArithmeticProposition) ⋏
        (“!!right < !!left” : LO.FirstOrder.ArithmeticProposition)) 🡒
      (“!!left < !!left” : LO.FirstOrder.ArithmeticProposition)) =
      (negativeOrderAntecedent left right 🡒
        negativeOrderSelfAtom left) := by
  rfl

def negativeOrderTransImplication
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (negativeOrderAntecedent left right 🡒
        negativeOrderSelfAtom left) :=
  CertifiedPAProof.cast
    (negativeOrderTransImplication_formula left right)
    (ltTransImplication left right left)

def negativeOrderAntecedentDerivation
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (reverseProof : LO.FirstOrder.Derivation2 PA
      {negativeOrderReverseAtom left right}) :
    LO.FirstOrder.Derivation2 PA
      (insert (negativeOrderAntecedent left right)
        (negativeOrderContext left right)) :=
  LO.FirstOrder.Derivation2.and
    (φ := negativeOrderForwardAtom left right)
    (ψ := negativeOrderReverseAtom left right)
    (by simp [negativeOrderAntecedent])
    (LO.FirstOrder.Derivation2.closed _
      (negativeOrderForwardAtom left right) (by simp)
      (by simp [negativeOrderContext]))
    (LO.FirstOrder.Derivation2.wk reverseProof
      (by simp [negativeOrderContext]))

def negativeOrderAntecedentCertificate
    (reverseCertificate : StructuralValidityCertificate) :
    StructuralValidityCertificate :=
  .binary .leaf (.unary reverseCertificate)

theorem negativeOrderAntecedentCertificate_valid
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (reverseProof : LO.FirstOrder.Derivation2 PA
      {negativeOrderReverseAtom left right})
    (reverseCertificate : StructuralValidityCertificate)
    (hvalid : certificateValid
      (CheckedPAProofTree.ofDerivation reverseProof)
      reverseCertificate) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (negativeOrderAntecedentDerivation left right reverseProof))
      (negativeOrderAntecedentCertificate reverseCertificate) := by
  have hconclusion :=
    CheckedPAProofTree.conclusion_ofDerivation reverseProof
  simp [negativeOrderAntecedentDerivation,
    negativeOrderAntecedentCertificate, negativeOrderAntecedent,
    negativeOrderContext, CheckedPAProofTree.ofDerivation,
    CheckedPAProofTree.conclusion, certificateValid]
  constructor
  · change (CheckedPAProofTree.ofDerivation reverseProof).conclusion ⊆ _
    rw [hconclusion]
    simp [negativeOrderReverseAtom]
  · exact hvalid

def negativeOrderAntecedentDerivationCost
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  let context := negativeOrderContext left right
  let forward := negativeOrderForwardAtom left right
  let reverse := negativeOrderReverseAtom left right
  let antecedent := negativeOrderAntecedent left right
  (binaryNatCode 3).length +
      (binarySequentCode (insert antecedent context)).length +
      (binaryFormulaCode forward).length +
      (binaryFormulaCode reverse).length +
    (binaryNatCode 0).length +
      (binarySequentCode
        (insert forward (insert antecedent context))).length +
      (binaryFormulaCode forward).length +
    (binaryNatCode 7).length +
      (binarySequentCode
        (insert reverse (insert antecedent context))).length

def negativeOrderAntecedentFullAssemblyCost
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  negativeOrderAntecedentDerivationCost left right + 48

theorem negativeOrderAntecedentDerivation_binaryProofLength_eq
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (reverseProof : LO.FirstOrder.Derivation2 PA
      {negativeOrderReverseAtom left right}) :
    binaryProofLength
        (negativeOrderAntecedentDerivation left right reverseProof) =
      binaryProofLength reverseProof +
        negativeOrderAntecedentDerivationCost left right := by
  simp only [negativeOrderAntecedentDerivation,
    negativeOrderAntecedentDerivationCost, binaryProofLength,
    binaryDerivationCode, List.length_append]
  omega

theorem negativeOrderAntecedentCertificate_code_length_le
    (certificate : StructuralValidityCertificate) :
    (binaryStructuralValidityCertificateCode
      (negativeOrderAntecedentCertificate certificate)).length <=
      (binaryStructuralValidityCertificateCode certificate).length + 48 := by
  have htag0 : (binaryNatCode 0).length <= 16 := by decide
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  simp only [negativeOrderAntecedentCertificate,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

theorem negativeOrderAntecedent_full_payload_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (reverseProof : CertifiedPAProof
      (negativeOrderReverseAtom left right)) :
    binaryProofLength
        (negativeOrderAntecedentDerivation left right
          reverseProof.derivation) +
        (binaryStructuralValidityCertificateCode
          (negativeOrderAntecedentCertificate
            reverseProof.certificate)).length <=
      reverseProof.payloadLength +
        negativeOrderAntecedentFullAssemblyCost left right := by
  have hproof := negativeOrderAntecedentDerivation_binaryProofLength_eq
    left right reverseProof.derivation
  have hcertificate :=
    negativeOrderAntecedentCertificate_code_length_le
      reverseProof.certificate
  rw [CertifiedPAProof.payloadLength_eq]
  unfold negativeOrderAntecedentFullAssemblyCost
  omega

def proveNotLessThanOfReverseLessThanDerivation
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (reverseProof : CertifiedPAProof
      (negativeOrderReverseAtom left right)) :
    LO.FirstOrder.Derivation2 PA
      {∼negativeOrderForwardAtom left right} := by
  let context := negativeOrderContext left right
  let antecedent := negativeOrderAntecedent left right
  let selfAtom := negativeOrderSelfAtom left
  let implication := negativeOrderTransImplication left right
  let irreflexivity := proveLtIrrefl left
  let implicationInContext : LO.FirstOrder.Derivation2 PA
      (insert (antecedent 🡒 selfAtom) context) :=
    LO.FirstOrder.Derivation2.wk implication.derivation (by
      simp [antecedent, selfAtom, context, negativeOrderContext])
  let antecedentInContext := negativeOrderAntecedentDerivation
    left right reverseProof.derivation
  let selfInContext := contextualModusPonensDerivation
    implicationInContext antecedentInContext
  let irreflexivityInContext : LO.FirstOrder.Derivation2 PA
      (insert (∼selfAtom) context) :=
    LO.FirstOrder.Derivation2.wk irreflexivity.derivation (by
      simp [selfAtom, negativeOrderSelfAtom, context,
        negativeOrderContext])
  exact LO.FirstOrder.Derivation2.cut
    (φ := selfAtom) selfInContext irreflexivityInContext

def proveNotLessThanOfReverseLessThanCertificate
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (reverseProof : CertifiedPAProof
      (negativeOrderReverseAtom left right)) :
    StructuralValidityCertificate :=
  let implication := negativeOrderTransImplication left right
  let irreflexivity := proveLtIrrefl left
  let implicationCertificate : StructuralValidityCertificate :=
    .unary implication.certificate
  let antecedentCertificate : StructuralValidityCertificate :=
    negativeOrderAntecedentCertificate reverseProof.certificate
  let selfCertificate : StructuralValidityCertificate :=
    contextualModusPonensCertificate
      implicationCertificate antecedentCertificate
  let irreflexivityCertificate : StructuralValidityCertificate :=
    .unary irreflexivity.certificate
  .binary selfCertificate irreflexivityCertificate

theorem proveNotLessThanOfReverseLessThanCertificate_valid
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (reverseProof : CertifiedPAProof
      (negativeOrderReverseAtom left right)) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (proveNotLessThanOfReverseLessThanDerivation
          left right reverseProof))
      (proveNotLessThanOfReverseLessThanCertificate
        left right reverseProof) := by
  let context := negativeOrderContext left right
  let antecedent := negativeOrderAntecedent left right
  let selfAtom := negativeOrderSelfAtom left
  let implication := negativeOrderTransImplication left right
  let irreflexivity := proveLtIrrefl left
  let implicationInContext : LO.FirstOrder.Derivation2 PA
      (insert (antecedent 🡒 selfAtom) context) :=
    LO.FirstOrder.Derivation2.wk implication.derivation (by
      simp [antecedent, selfAtom, context, negativeOrderContext])
  let antecedentInContext := negativeOrderAntecedentDerivation
    left right reverseProof.derivation
  let selfInContext := contextualModusPonensDerivation
    implicationInContext antecedentInContext
  let irreflexivityInContext : LO.FirstOrder.Derivation2 PA
      (insert (∼selfAtom) context) :=
    LO.FirstOrder.Derivation2.wk irreflexivity.derivation (by
      simp [selfAtom, negativeOrderSelfAtom, context,
        negativeOrderContext])
  let implicationCertificate : StructuralValidityCertificate :=
    .unary implication.certificate
  let antecedentCertificate : StructuralValidityCertificate :=
    negativeOrderAntecedentCertificate reverseProof.certificate
  let selfCertificate : StructuralValidityCertificate :=
    contextualModusPonensCertificate
      implicationCertificate antecedentCertificate
  let irreflexivityCertificate : StructuralValidityCertificate :=
    .unary irreflexivity.certificate
  have himplication : certificateValid
      (CheckedPAProofTree.ofDerivation implicationInContext)
      implicationCertificate := by
    dsimp only [implicationInContext, implicationCertificate]
    exact weakeningCertificate_valid implication.derivation
      implication.certificate
      (by simp [antecedent, selfAtom, context, negativeOrderContext])
      implication.certificate_valid
  have hantecedent := negativeOrderAntecedentCertificate_valid
    left right reverseProof.derivation reverseProof.certificate
      reverseProof.certificate_valid
  have hself := contextualModusPonensCertificate_valid
    implicationInContext antecedentInContext
    implicationCertificate antecedentCertificate
    himplication hantecedent
  have hirreflexivity : certificateValid
      (CheckedPAProofTree.ofDerivation irreflexivityInContext)
      irreflexivityCertificate := by
    dsimp only [irreflexivityInContext, irreflexivityCertificate]
    exact weakeningCertificate_valid irreflexivity.derivation
      irreflexivity.certificate
      (by simp [selfAtom, negativeOrderSelfAtom, context,
        negativeOrderContext])
      irreflexivity.certificate_valid
  have hselfConclusion :=
    CheckedPAProofTree.conclusion_ofDerivation selfInContext
  have hirreflexivityConclusion :=
    CheckedPAProofTree.conclusion_ofDerivation irreflexivityInContext
  change certificateValid
    (CheckedPAProofTree.ofDerivation
      (LO.FirstOrder.Derivation2.cut
        (φ := selfAtom) selfInContext irreflexivityInContext))
    (.binary selfCertificate irreflexivityCertificate)
  simp only [CheckedPAProofTree.ofDerivation, certificateValid]
  exact ⟨hselfConclusion, hirreflexivityConclusion,
    hself, hirreflexivity⟩

def proveNotLessThanOfReverseLessThan
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (reverseProof : CertifiedPAProof
      (negativeOrderReverseAtom left right)) :
    CertifiedPAProof (∼negativeOrderForwardAtom left right) where
  derivation := proveNotLessThanOfReverseLessThanDerivation
    left right reverseProof
  certificate := proveNotLessThanOfReverseLessThanCertificate
    left right reverseProof
  certificate_valid :=
    proveNotLessThanOfReverseLessThanCertificate_valid
      left right reverseProof

def negativeOrderFinalCutFullAssemblyCost
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  (binaryNatCode 9).length +
    (binarySequentCode (negativeOrderContext left right)).length +
    (binaryFormulaCode (negativeOrderSelfAtom left)).length + 16

def proveNotLessThanOfReverseLessThanPayloadBound
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (reversePayloadLength : Nat) : Nat :=
  let context := negativeOrderContext left right
  let antecedent := negativeOrderAntecedent left right
  let selfAtom := negativeOrderSelfAtom left
  (negativeOrderTransImplication left right).payloadLength +
    weakeningFullAssemblyCost (insert (antecedent 🡒 selfAtom) context) +
    reversePayloadLength +
    negativeOrderAntecedentFullAssemblyCost left right +
    contextualModusPonensFullAssemblyCost context antecedent selfAtom +
    (proveLtIrrefl left).payloadLength +
    weakeningFullAssemblyCost (insert (∼selfAtom) context) +
    negativeOrderFinalCutFullAssemblyCost left right

theorem proveNotLessThanOfReverseLessThan_payloadLength_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (reverseProof : CertifiedPAProof
      (negativeOrderReverseAtom left right)) :
    (proveNotLessThanOfReverseLessThan
      left right reverseProof).payloadLength <=
      proveNotLessThanOfReverseLessThanPayloadBound
        left right reverseProof.payloadLength := by
  let context := negativeOrderContext left right
  let antecedent := negativeOrderAntecedent left right
  let selfAtom := negativeOrderSelfAtom left
  let implication := negativeOrderTransImplication left right
  let irreflexivity := proveLtIrrefl left
  let implicationInContext : LO.FirstOrder.Derivation2 PA
      (insert (antecedent 🡒 selfAtom) context) :=
    LO.FirstOrder.Derivation2.wk implication.derivation (by
      simp [antecedent, selfAtom, context, negativeOrderContext])
  let antecedentInContext := negativeOrderAntecedentDerivation
    left right reverseProof.derivation
  let selfInContext := contextualModusPonensDerivation
    implicationInContext antecedentInContext
  let irreflexivityInContext : LO.FirstOrder.Derivation2 PA
      (insert (∼selfAtom) context) :=
    LO.FirstOrder.Derivation2.wk irreflexivity.derivation (by
      simp [selfAtom, negativeOrderSelfAtom, context,
        negativeOrderContext])
  let implicationCertificate : StructuralValidityCertificate :=
    .unary implication.certificate
  let antecedentCertificate : StructuralValidityCertificate :=
    negativeOrderAntecedentCertificate reverseProof.certificate
  let selfCertificate : StructuralValidityCertificate :=
    contextualModusPonensCertificate
      implicationCertificate antecedentCertificate
  let irreflexivityCertificate : StructuralValidityCertificate :=
    .unary irreflexivity.certificate
  have himplicationWeakRaw := weakening_full_payload_le
    (Gamma := insert (antecedent 🡒 selfAtom) context)
    implication.derivation implication.certificate
    (by simp [antecedent, selfAtom, context, negativeOrderContext])
  have himplicationWeak :
      binaryProofLength implicationInContext +
          (binaryStructuralValidityCertificateCode
            implicationCertificate).length <=
        implication.payloadLength +
          weakeningFullAssemblyCost
            (insert (antecedent 🡒 selfAtom) context) := by
    dsimp only [implicationInContext, implicationCertificate]
    simpa [CertifiedPAProof.payloadLength_eq] using himplicationWeakRaw
  have hantecedent := negativeOrderAntecedent_full_payload_le
    left right reverseProof
  have hantecedentLocal :
      binaryProofLength antecedentInContext +
          (binaryStructuralValidityCertificateCode
            antecedentCertificate).length <=
        reverseProof.payloadLength +
          negativeOrderAntecedentFullAssemblyCost left right := by
    dsimp only [antecedentInContext, antecedentCertificate]
    exact hantecedent
  have hselfRaw := contextualModusPonens_full_payload_le
    implicationInContext antecedentInContext
    implicationCertificate antecedentCertificate
  have hself :
      binaryProofLength selfInContext +
          (binaryStructuralValidityCertificateCode selfCertificate).length <=
        (implication.payloadLength +
          weakeningFullAssemblyCost
            (insert (antecedent 🡒 selfAtom) context)) +
        (reverseProof.payloadLength +
          negativeOrderAntecedentFullAssemblyCost left right) +
        contextualModusPonensFullAssemblyCost
          context antecedent selfAtom := by
    dsimp only [selfInContext, selfCertificate]
    calc
      _ <= (binaryProofLength implicationInContext +
            (binaryStructuralValidityCertificateCode
              implicationCertificate).length) +
          (binaryProofLength antecedentInContext +
            (binaryStructuralValidityCertificateCode
              antecedentCertificate).length) +
          contextualModusPonensFullAssemblyCost
            context antecedent selfAtom := hselfRaw
      _ <= _ := by omega
  have hirreflexivityWeakRaw := weakening_full_payload_le
    (Gamma := insert (∼selfAtom) context)
    irreflexivity.derivation irreflexivity.certificate
    (by simp [selfAtom, negativeOrderSelfAtom, context,
      negativeOrderContext])
  have hirreflexivityWeak :
      binaryProofLength irreflexivityInContext +
          (binaryStructuralValidityCertificateCode
            irreflexivityCertificate).length <=
        irreflexivity.payloadLength +
          weakeningFullAssemblyCost (insert (∼selfAtom) context) := by
    dsimp only [irreflexivityInContext, irreflexivityCertificate]
    simpa [CertifiedPAProof.payloadLength_eq] using hirreflexivityWeakRaw
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  have hfinal :
      binaryProofLength
          (LO.FirstOrder.Derivation2.cut
            (φ := selfAtom) selfInContext irreflexivityInContext) +
          (binaryStructuralValidityCertificateCode
            (.binary selfCertificate irreflexivityCertificate)).length <=
        (binaryProofLength selfInContext +
          (binaryStructuralValidityCertificateCode selfCertificate).length) +
        (binaryProofLength irreflexivityInContext +
          (binaryStructuralValidityCertificateCode
            irreflexivityCertificate).length) +
        negativeOrderFinalCutFullAssemblyCost left right := by
    simp only [binaryProofLength, binaryDerivationCode,
      binaryStructuralValidityCertificateCode, List.length_append]
    unfold negativeOrderFinalCutFullAssemblyCost
    dsimp only [context, selfAtom]
    omega
  rw [CertifiedPAProof.payloadLength_eq]
  change binaryProofLength
      (proveNotLessThanOfReverseLessThanDerivation
        left right reverseProof) +
      (binaryStructuralValidityCertificateCode
        (proveNotLessThanOfReverseLessThanCertificate
          left right reverseProof)).length <= _
  have houterDerivation :
      proveNotLessThanOfReverseLessThanDerivation
          left right reverseProof =
        LO.FirstOrder.Derivation2.cut
          (φ := selfAtom) selfInContext irreflexivityInContext := by
    rfl
  have houterCertificate :
      proveNotLessThanOfReverseLessThanCertificate
          left right reverseProof =
        .binary selfCertificate irreflexivityCertificate := by
    rfl
  rw [houterDerivation, houterCertificate]
  calc
    binaryProofLength
          (LO.FirstOrder.Derivation2.cut
            (φ := selfAtom) selfInContext irreflexivityInContext) +
        (binaryStructuralValidityCertificateCode
          (.binary selfCertificate irreflexivityCertificate)).length <=
        (binaryProofLength selfInContext +
          (binaryStructuralValidityCertificateCode selfCertificate).length) +
        (binaryProofLength irreflexivityInContext +
          (binaryStructuralValidityCertificateCode
            irreflexivityCertificate).length) +
        negativeOrderFinalCutFullAssemblyCost left right := hfinal
    _ <= ((implication.payloadLength +
            weakeningFullAssemblyCost
              (insert (antecedent 🡒 selfAtom) context)) +
          (reverseProof.payloadLength +
            negativeOrderAntecedentFullAssemblyCost left right) +
          contextualModusPonensFullAssemblyCost
            context antecedent selfAtom) +
        (irreflexivity.payloadLength +
          weakeningFullAssemblyCost (insert (∼selfAtom) context)) +
        negativeOrderFinalCutFullAssemblyCost left right := by
      omega
    _ = proveNotLessThanOfReverseLessThanPayloadBound
        left right reverseProof.payloadLength := by
      unfold proveNotLessThanOfReverseLessThanPayloadBound
      dsimp only [context, antecedent, selfAtom, implication, irreflexivity]
      ring

theorem proveNotLessThanOfReverseLessThan_verifier_eq_true
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (reverseProof : CertifiedPAProof
      (negativeOrderReverseAtom left right)) :
    listedCompactCertifiedPAProofVerifier
      (proveNotLessThanOfReverseLessThan left right reverseProof).code
      (compactFormulaCode
        (∼negativeOrderForwardAtom left right)) = true :=
  (proveNotLessThanOfReverseLessThan left right
    reverseProof).verifier_eq_true

theorem negativeOrderTransportConclusion_formula
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryRelationCongruenceConclusion Language.ORing.Rel.lt
        left right right right =
      (negativeOrderForwardAtom left right 🡒
        negativeOrderSelfAtom right) := by
  simpa [negativeOrderForwardAtom, negativeOrderSelfAtom] using
    binaryRelationCongruenceConclusion_lt_formula
      left right right right

def proveNotLessThanOfEquality
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (equalityProof : CertifiedPAProof
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof (∼negativeOrderForwardAtom left right) := by
  let reflexivity := proveEqualityReflexivityAtTerm right
  let transportRaw := proveBinaryRelationTransportImplication
    Language.ORing.Rel.lt left right right right
    equalityProof reflexivity
  let transport : CertifiedPAProof
      (negativeOrderForwardAtom left right 🡒
        negativeOrderSelfAtom right) :=
    CertifiedPAProof.cast
      (negativeOrderTransportConclusion_formula left right)
      transportRaw
  let irreflexivity := proveLtIrrefl right
  exact modusTollens transport irreflexivity

theorem proveNotLessThanOfEquality_verifier_eq_true
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (equalityProof : CertifiedPAProof
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)) :
    listedCompactCertifiedPAProofVerifier
      (proveNotLessThanOfEquality left right equalityProof).code
      (compactFormulaCode
        (∼negativeOrderForwardAtom left right)) = true :=
  (proveNotLessThanOfEquality left right equalityProof).verifier_eq_true

#print axioms negativeOrderAntecedentCertificate_valid
#print axioms proveNotLessThanOfReverseLessThanCertificate_valid
#print axioms proveNotLessThanOfReverseLessThan_payloadLength_le
#print axioms proveNotLessThanOfReverseLessThan_verifier_eq_true
#print axioms proveNotLessThanOfEquality_verifier_eq_true

end FoundationCompactPANegativeOrder
