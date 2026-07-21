import integration.FoundationCompactCertifiedContextualModusPonens
import integration.FoundationCompactPAQuantitativeOrderBounds

/-!
# Proof-producing negative equality from strict order

For arbitrary closed PA terms, a checked proof of `left < right` is converted
to a checked proof of `not (left = right)`.  The construction specializes
relation extensionality, derives `right < right` under the equality context,
and closes against the explicit `ltIrrefl` proof.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPANegativeEquality

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPAQuantitativeOrder
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextualModusPonens

def negativeEqualityAtom
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)

def negativeEqualityStrictAtom
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)

def negativeEqualitySelfStrictAtom
    (right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  (“!!right < !!right” : LO.FirstOrder.ArithmeticProposition)

def negativeEqualityAntecedent
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  binaryRelationCongruenceAntecedent left right right right

def negativeEqualityTransportConclusion
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  negativeEqualityStrictAtom left right 🡒
    negativeEqualitySelfStrictAtom right

theorem negativeEqualityTransportConclusion_formula
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryRelationCongruenceConclusion Language.ORing.Rel.lt
        left right right right =
      negativeEqualityTransportConclusion left right := by
  simpa [negativeEqualityStrictAtom, negativeEqualitySelfStrictAtom,
    negativeEqualityTransportConclusion] using
    binaryRelationCongruenceConclusion_lt_formula left right right right

theorem negativeEqualityTransportImplication_formula
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (negativeEqualityAntecedent left right 🡒
        binaryRelationCongruenceConclusion Language.ORing.Rel.lt
          left right right right) =
      (negativeEqualityAntecedent left right 🡒
        negativeEqualityTransportConclusion left right) := by
  rw [negativeEqualityTransportConclusion_formula]

def negativeEqualityTransportImplication
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (negativeEqualityAntecedent left right 🡒
        negativeEqualityTransportConclusion left right) :=
  CertifiedPAProof.cast
    (negativeEqualityTransportImplication_formula left right)
    (binaryRelationExtImplication Language.ORing.Rel.lt
      left right right right)

def negativeEqualityContext
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    Finset LO.FirstOrder.ArithmeticProposition :=
  {∼negativeEqualityAtom left right}

def negativeEqualityAntecedentDerivation
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (rightReflexivity : LO.FirstOrder.Derivation2 PA
      {negativeEqualityAtom right right}) :
    LO.FirstOrder.Derivation2 PA
      (insert (negativeEqualityAntecedent left right)
        (negativeEqualityContext left right)) :=
  LO.FirstOrder.Derivation2.and
    (φ := negativeEqualityAtom left right)
    (ψ := negativeEqualityAtom right right ⋏
      (⊤ : LO.FirstOrder.ArithmeticProposition))
    (by
      simp [negativeEqualityAntecedent, negativeEqualityAtom,
        binaryRelationCongruenceAntecedent])
    (LO.FirstOrder.Derivation2.closed _
      (negativeEqualityAtom left right) (by simp)
      (by simp [negativeEqualityContext]))
    (LO.FirstOrder.Derivation2.and
      (φ := negativeEqualityAtom right right)
      (ψ := (⊤ : LO.FirstOrder.ArithmeticProposition))
      (by simp)
      (LO.FirstOrder.Derivation2.wk rightReflexivity (by simp))
      (LO.FirstOrder.Derivation2.verum (by simp)))

def negativeEqualityAntecedentCertificate
    (rightReflexivityCertificate : StructuralValidityCertificate) :
    StructuralValidityCertificate :=
  .binary .leaf
    (.binary (.unary rightReflexivityCertificate) .leaf)

theorem negativeEqualityAntecedentCertificate_valid
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (rightReflexivity : LO.FirstOrder.Derivation2 PA
      {negativeEqualityAtom right right})
    (rightReflexivityCertificate : StructuralValidityCertificate)
    (hvalid : certificateValid
      (CheckedPAProofTree.ofDerivation rightReflexivity)
      rightReflexivityCertificate) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (negativeEqualityAntecedentDerivation left right rightReflexivity))
      (negativeEqualityAntecedentCertificate
        rightReflexivityCertificate) := by
  have hconclusion :=
    CheckedPAProofTree.conclusion_ofDerivation rightReflexivity
  simp [negativeEqualityAntecedentDerivation,
    negativeEqualityAntecedentCertificate,
    negativeEqualityAntecedent, negativeEqualityAtom,
    negativeEqualityContext, binaryRelationCongruenceAntecedent,
    CheckedPAProofTree.ofDerivation, CheckedPAProofTree.conclusion,
    certificateValid]
  constructor
  · change (CheckedPAProofTree.ofDerivation rightReflexivity).conclusion ⊆ _
    rw [hconclusion]
    simp [negativeEqualityAtom]
  · exact hvalid

def negativeEqualityAntecedentDerivationCost
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  let context := negativeEqualityContext left right
  let equality := negativeEqualityAtom left right
  let reflexivity := negativeEqualityAtom right right
  let truth := (⊤ : LO.FirstOrder.ArithmeticProposition)
  let inner := reflexivity ⋏ truth
  let antecedent := negativeEqualityAntecedent left right
  (binaryNatCode 3).length +
      (binarySequentCode (insert antecedent context)).length +
      (binaryFormulaCode equality).length +
      (binaryFormulaCode inner).length +
    (binaryNatCode 0).length +
      (binarySequentCode
        (insert equality (insert antecedent context))).length +
      (binaryFormulaCode equality).length +
    (binaryNatCode 3).length +
      (binarySequentCode
        (insert inner (insert antecedent context))).length +
      (binaryFormulaCode reflexivity).length +
      (binaryFormulaCode truth).length +
    (binaryNatCode 7).length +
      (binarySequentCode
        (insert reflexivity (insert inner
          (insert antecedent context)))).length +
    (binaryNatCode 2).length +
      (binarySequentCode
        (insert truth (insert inner
          (insert antecedent context)))).length

def negativeEqualityAntecedentFullAssemblyCost
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  negativeEqualityAntecedentDerivationCost left right + 80

theorem negativeEqualityAntecedentDerivation_binaryProofLength_eq
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (rightReflexivity : LO.FirstOrder.Derivation2 PA
      {negativeEqualityAtom right right}) :
    binaryProofLength
        (negativeEqualityAntecedentDerivation left right rightReflexivity) =
      binaryProofLength rightReflexivity +
        negativeEqualityAntecedentDerivationCost left right := by
  simp only [negativeEqualityAntecedentDerivation,
    negativeEqualityAntecedentDerivationCost, binaryProofLength,
    binaryDerivationCode, List.length_append]
  omega

theorem negativeEqualityAntecedentCertificate_code_length_le
    (certificate : StructuralValidityCertificate) :
    (binaryStructuralValidityCertificateCode
      (negativeEqualityAntecedentCertificate certificate)).length <=
      (binaryStructuralValidityCertificateCode certificate).length + 80 := by
  have htag0 : (binaryNatCode 0).length <= 16 := by decide
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  simp only [negativeEqualityAntecedentCertificate,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

theorem negativeEqualityAntecedent_full_payload_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (rightReflexivity : CertifiedPAProof
      (negativeEqualityAtom right right)) :
    binaryProofLength
        (negativeEqualityAntecedentDerivation left right
          rightReflexivity.derivation) +
        (binaryStructuralValidityCertificateCode
          (negativeEqualityAntecedentCertificate
            rightReflexivity.certificate)).length <=
      rightReflexivity.payloadLength +
        negativeEqualityAntecedentFullAssemblyCost left right := by
  have hproof := negativeEqualityAntecedentDerivation_binaryProofLength_eq
    left right rightReflexivity.derivation
  have hcertificate :=
    negativeEqualityAntecedentCertificate_code_length_le
      rightReflexivity.certificate
  rw [CertifiedPAProof.payloadLength_eq]
  unfold negativeEqualityAntecedentFullAssemblyCost
  omega

def proveNotEqualityOfLessThanDerivation
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (strictProof : CertifiedPAProof
      (negativeEqualityStrictAtom left right)) :
    LO.FirstOrder.Derivation2 PA
      {∼negativeEqualityAtom left right} := by
  let context := negativeEqualityContext left right
  let antecedent := negativeEqualityAntecedent left right
  let strictAtom := negativeEqualityStrictAtom left right
  let selfStrict := negativeEqualitySelfStrictAtom right
  let transportConclusion := negativeEqualityTransportConclusion left right
  let transport := negativeEqualityTransportImplication left right
  let rightReflexivity := proveEqualityReflexivityAtTerm right
  let irreflexivity := proveLtIrrefl right
  let transportInContext : LO.FirstOrder.Derivation2 PA
      (insert (antecedent 🡒 transportConclusion) context) :=
    LO.FirstOrder.Derivation2.wk transport.derivation (by
      simp [antecedent, transportConclusion, context,
        negativeEqualityContext])
  let antecedentInContext :=
    negativeEqualityAntecedentDerivation left right
      rightReflexivity.derivation
  let transportConclusionInContext :=
    contextualModusPonensDerivation transportInContext antecedentInContext
  let strictInContext : LO.FirstOrder.Derivation2 PA
      (insert strictAtom context) :=
    LO.FirstOrder.Derivation2.wk strictProof.derivation (by
      simp [strictAtom, context, negativeEqualityContext])
  let selfStrictInContext :=
    contextualModusPonensDerivation
      transportConclusionInContext strictInContext
  let irreflexivityInContext : LO.FirstOrder.Derivation2 PA
      (insert (∼selfStrict) context) :=
    LO.FirstOrder.Derivation2.wk irreflexivity.derivation (by
      simp [selfStrict, negativeEqualitySelfStrictAtom, context,
        negativeEqualityContext])
  exact LO.FirstOrder.Derivation2.cut
    (φ := selfStrict) selfStrictInContext irreflexivityInContext

def proveNotEqualityOfLessThanCertificate
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (strictProof : CertifiedPAProof
      (negativeEqualityStrictAtom left right)) :
    StructuralValidityCertificate :=
  let transport := negativeEqualityTransportImplication left right
  let rightReflexivity := proveEqualityReflexivityAtTerm right
  let irreflexivity := proveLtIrrefl right
  let transportCertificate : StructuralValidityCertificate :=
    .unary transport.certificate
  let antecedentCertificate : StructuralValidityCertificate :=
    negativeEqualityAntecedentCertificate
    rightReflexivity.certificate
  let transportConclusionCertificate : StructuralValidityCertificate :=
    contextualModusPonensCertificate transportCertificate
      antecedentCertificate
  let strictCertificate : StructuralValidityCertificate :=
    .unary strictProof.certificate
  let selfStrictCertificate : StructuralValidityCertificate :=
    contextualModusPonensCertificate
    transportConclusionCertificate strictCertificate
  let irreflexivityCertificate : StructuralValidityCertificate :=
    .unary irreflexivity.certificate
  .binary selfStrictCertificate irreflexivityCertificate

theorem proveNotEqualityOfLessThanCertificate_valid
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (strictProof : CertifiedPAProof
      (negativeEqualityStrictAtom left right)) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (proveNotEqualityOfLessThanDerivation left right strictProof))
      (proveNotEqualityOfLessThanCertificate left right strictProof) := by
  let context := negativeEqualityContext left right
  let antecedent := negativeEqualityAntecedent left right
  let strictAtom := negativeEqualityStrictAtom left right
  let selfStrict := negativeEqualitySelfStrictAtom right
  let transportConclusion := negativeEqualityTransportConclusion left right
  let transport := negativeEqualityTransportImplication left right
  let rightReflexivity := proveEqualityReflexivityAtTerm right
  let irreflexivity := proveLtIrrefl right
  let transportInContext : LO.FirstOrder.Derivation2 PA
      (insert (antecedent 🡒 transportConclusion) context) :=
    LO.FirstOrder.Derivation2.wk transport.derivation (by
      simp [antecedent, transportConclusion, context,
        negativeEqualityContext])
  let antecedentInContext :=
    negativeEqualityAntecedentDerivation left right
      rightReflexivity.derivation
  let transportConclusionInContext :=
    contextualModusPonensDerivation transportInContext antecedentInContext
  let strictInContext : LO.FirstOrder.Derivation2 PA
      (insert strictAtom context) :=
    LO.FirstOrder.Derivation2.wk strictProof.derivation (by
      simp [strictAtom, context, negativeEqualityContext])
  let selfStrictInContext := contextualModusPonensDerivation
    transportConclusionInContext strictInContext
  let irreflexivityInContext : LO.FirstOrder.Derivation2 PA
      (insert (∼selfStrict) context) :=
    LO.FirstOrder.Derivation2.wk irreflexivity.derivation (by
      simp [selfStrict, negativeEqualitySelfStrictAtom, context,
        negativeEqualityContext])
  let transportCertificate : StructuralValidityCertificate :=
    .unary transport.certificate
  let antecedentCertificate : StructuralValidityCertificate :=
    negativeEqualityAntecedentCertificate
    rightReflexivity.certificate
  let transportConclusionCertificate : StructuralValidityCertificate :=
    contextualModusPonensCertificate transportCertificate
      antecedentCertificate
  let strictCertificate : StructuralValidityCertificate :=
    .unary strictProof.certificate
  let selfStrictCertificate : StructuralValidityCertificate :=
    contextualModusPonensCertificate
    transportConclusionCertificate strictCertificate
  let irreflexivityCertificate : StructuralValidityCertificate :=
    .unary irreflexivity.certificate
  have htransport : certificateValid
      (CheckedPAProofTree.ofDerivation transportInContext)
      transportCertificate := by
    dsimp only [transportInContext, transportCertificate]
    exact weakeningCertificate_valid transport.derivation
      transport.certificate
      (by simp [antecedent, transportConclusion, context,
        negativeEqualityContext])
      transport.certificate_valid
  have hantecedent := negativeEqualityAntecedentCertificate_valid
    left right rightReflexivity.derivation rightReflexivity.certificate
    rightReflexivity.certificate_valid
  have htransportConclusion := contextualModusPonensCertificate_valid
    transportInContext antecedentInContext
    transportCertificate antecedentCertificate htransport hantecedent
  have hstrict : certificateValid
      (CheckedPAProofTree.ofDerivation strictInContext)
      strictCertificate := by
    dsimp only [strictInContext, strictCertificate]
    exact weakeningCertificate_valid strictProof.derivation
      strictProof.certificate
      (by simp [strictAtom, context, negativeEqualityContext])
      strictProof.certificate_valid
  have hselfStrict := contextualModusPonensCertificate_valid
    transportConclusionInContext strictInContext
    transportConclusionCertificate strictCertificate
    htransportConclusion hstrict
  have hirreflexivity : certificateValid
      (CheckedPAProofTree.ofDerivation irreflexivityInContext)
      irreflexivityCertificate := by
    dsimp only [irreflexivityInContext, irreflexivityCertificate]
    exact weakeningCertificate_valid irreflexivity.derivation
      irreflexivity.certificate
      (by simp [selfStrict, negativeEqualitySelfStrictAtom, context,
        negativeEqualityContext])
      irreflexivity.certificate_valid
  have hselfConclusion :=
    CheckedPAProofTree.conclusion_ofDerivation selfStrictInContext
  have hirreflexivityConclusion :=
    CheckedPAProofTree.conclusion_ofDerivation irreflexivityInContext
  change certificateValid
    (CheckedPAProofTree.ofDerivation
      (LO.FirstOrder.Derivation2.cut
        (φ := selfStrict) selfStrictInContext irreflexivityInContext))
    (.binary selfStrictCertificate irreflexivityCertificate)
  simp only [CheckedPAProofTree.ofDerivation, certificateValid]
  exact ⟨hselfConclusion, hirreflexivityConclusion,
    hselfStrict, hirreflexivity⟩

def proveNotEqualityOfLessThan
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (strictProof : CertifiedPAProof
      (negativeEqualityStrictAtom left right)) :
    CertifiedPAProof (∼negativeEqualityAtom left right) where
  derivation := proveNotEqualityOfLessThanDerivation left right strictProof
  certificate := proveNotEqualityOfLessThanCertificate left right strictProof
  certificate_valid :=
    proveNotEqualityOfLessThanCertificate_valid left right strictProof

def negativeEqualityFinalCutFullAssemblyCost
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  (binaryNatCode 9).length +
    (binarySequentCode (negativeEqualityContext left right)).length +
    (binaryFormulaCode
      (negativeEqualitySelfStrictAtom right)).length + 16

def proveNotEqualityOfLessThanPayloadBound
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (strictPayloadLength : Nat) : Nat :=
  let context := negativeEqualityContext left right
  let antecedent := negativeEqualityAntecedent left right
  let strictAtom := negativeEqualityStrictAtom left right
  let selfStrict := negativeEqualitySelfStrictAtom right
  let transportConclusion := negativeEqualityTransportConclusion left right
  (negativeEqualityTransportImplication left right).payloadLength +
    weakeningFullAssemblyCost
      (insert (antecedent 🡒 transportConclusion) context) +
    (proveEqualityReflexivityAtTerm right).payloadLength +
    negativeEqualityAntecedentFullAssemblyCost left right +
    contextualModusPonensFullAssemblyCost context
      antecedent transportConclusion +
    strictPayloadLength +
    weakeningFullAssemblyCost (insert strictAtom context) +
    contextualModusPonensFullAssemblyCost context strictAtom selfStrict +
    (proveLtIrrefl right).payloadLength +
    weakeningFullAssemblyCost (insert (∼selfStrict) context) +
    negativeEqualityFinalCutFullAssemblyCost left right

theorem proveNotEqualityOfLessThan_payloadLength_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (strictProof : CertifiedPAProof
      (negativeEqualityStrictAtom left right)) :
    (proveNotEqualityOfLessThan left right strictProof).payloadLength <=
      proveNotEqualityOfLessThanPayloadBound
        left right strictProof.payloadLength := by
  let context := negativeEqualityContext left right
  let antecedent := negativeEqualityAntecedent left right
  let strictAtom := negativeEqualityStrictAtom left right
  let selfStrict := negativeEqualitySelfStrictAtom right
  let transportConclusion := negativeEqualityTransportConclusion left right
  let transport := negativeEqualityTransportImplication left right
  let rightReflexivity := proveEqualityReflexivityAtTerm right
  let irreflexivity := proveLtIrrefl right
  let transportInContext : LO.FirstOrder.Derivation2 PA
      (insert (antecedent 🡒 transportConclusion) context) :=
    LO.FirstOrder.Derivation2.wk transport.derivation (by
      simp [antecedent, transportConclusion, context,
        negativeEqualityContext])
  let antecedentInContext :=
    negativeEqualityAntecedentDerivation left right
      rightReflexivity.derivation
  let transportConclusionInContext :=
    contextualModusPonensDerivation transportInContext antecedentInContext
  let strictInContext : LO.FirstOrder.Derivation2 PA
      (insert strictAtom context) :=
    LO.FirstOrder.Derivation2.wk strictProof.derivation (by
      simp [strictAtom, context, negativeEqualityContext])
  let selfStrictInContext := contextualModusPonensDerivation
    transportConclusionInContext strictInContext
  let irreflexivityInContext : LO.FirstOrder.Derivation2 PA
      (insert (∼selfStrict) context) :=
    LO.FirstOrder.Derivation2.wk irreflexivity.derivation (by
      simp [selfStrict, negativeEqualitySelfStrictAtom, context,
        negativeEqualityContext])
  let transportCertificate : StructuralValidityCertificate :=
    .unary transport.certificate
  let antecedentCertificate : StructuralValidityCertificate :=
    negativeEqualityAntecedentCertificate rightReflexivity.certificate
  let transportConclusionCertificate : StructuralValidityCertificate :=
    contextualModusPonensCertificate transportCertificate
      antecedentCertificate
  let strictCertificate : StructuralValidityCertificate :=
    .unary strictProof.certificate
  let selfStrictCertificate : StructuralValidityCertificate :=
    contextualModusPonensCertificate
      transportConclusionCertificate strictCertificate
  let irreflexivityCertificate : StructuralValidityCertificate :=
    .unary irreflexivity.certificate
  have htransportWeakRaw := weakening_full_payload_le
    (Gamma := insert (antecedent 🡒 transportConclusion) context)
    transport.derivation transport.certificate
    (by simp [antecedent, transportConclusion, context,
      negativeEqualityContext])
  have htransportWeak :
      binaryProofLength transportInContext +
          (binaryStructuralValidityCertificateCode
            transportCertificate).length <=
        transport.payloadLength +
          weakeningFullAssemblyCost
            (insert (antecedent 🡒 transportConclusion) context) := by
    dsimp only [transportInContext, transportCertificate, transport]
    simpa [CertifiedPAProof.payloadLength_eq] using htransportWeakRaw
  have hantecedentRaw := negativeEqualityAntecedent_full_payload_le
    left right rightReflexivity
  have hantecedent :
      binaryProofLength antecedentInContext +
          (binaryStructuralValidityCertificateCode
            antecedentCertificate).length <=
        rightReflexivity.payloadLength +
          negativeEqualityAntecedentFullAssemblyCost left right := by
    dsimp only [antecedentInContext, antecedentCertificate]
    exact hantecedentRaw
  have htransportConclusionRaw :=
    contextualModusPonens_full_payload_le
      transportInContext antecedentInContext
      transportCertificate antecedentCertificate
  have htransportConclusion :
      binaryProofLength transportConclusionInContext +
          (binaryStructuralValidityCertificateCode
            transportConclusionCertificate).length <=
        (transport.payloadLength +
          weakeningFullAssemblyCost
            (insert (antecedent 🡒 transportConclusion) context)) +
        (rightReflexivity.payloadLength +
          negativeEqualityAntecedentFullAssemblyCost left right) +
        contextualModusPonensFullAssemblyCost context
          antecedent transportConclusion := by
    dsimp only [transportConclusionInContext,
      transportConclusionCertificate]
    omega
  have hstrictWeakRaw := weakening_full_payload_le
    (Gamma := insert strictAtom context)
    strictProof.derivation strictProof.certificate
    (by simp [strictAtom, context, negativeEqualityContext])
  have hstrictWeak :
      binaryProofLength strictInContext +
          (binaryStructuralValidityCertificateCode strictCertificate).length <=
        strictProof.payloadLength +
          weakeningFullAssemblyCost (insert strictAtom context) := by
    dsimp only [strictInContext, strictCertificate]
    simpa [CertifiedPAProof.payloadLength_eq] using hstrictWeakRaw
  have hselfStrictRaw := contextualModusPonens_full_payload_le
    transportConclusionInContext strictInContext
    transportConclusionCertificate strictCertificate
  have hsecondCost :
      contextualModusPonensFullAssemblyCost context
          (negativeEqualityStrictAtom left right)
          (negativeEqualitySelfStrictAtom right) =
        contextualModusPonensFullAssemblyCost context
          strictAtom selfStrict := by
    rfl
  rw [hsecondCost] at hselfStrictRaw
  let selfPayloadBound :=
    (transport.payloadLength +
      weakeningFullAssemblyCost
        (insert (antecedent 🡒 transportConclusion) context)) +
    (rightReflexivity.payloadLength +
      negativeEqualityAntecedentFullAssemblyCost left right) +
    contextualModusPonensFullAssemblyCost context
      antecedent transportConclusion +
    (strictProof.payloadLength +
      weakeningFullAssemblyCost (insert strictAtom context)) +
    contextualModusPonensFullAssemblyCost context strictAtom selfStrict
  have hselfStrict :
      binaryProofLength selfStrictInContext +
          (binaryStructuralValidityCertificateCode
            selfStrictCertificate).length <=
        selfPayloadBound := by
    dsimp only [selfPayloadBound]
    change
      binaryProofLength
          (contextualModusPonensDerivation
            transportConclusionInContext strictInContext) +
        (binaryStructuralValidityCertificateCode
          (contextualModusPonensCertificate
            transportConclusionCertificate strictCertificate)).length <= _
    calc
      _ <= (binaryProofLength transportConclusionInContext +
            (binaryStructuralValidityCertificateCode
              transportConclusionCertificate).length) +
          (binaryProofLength strictInContext +
            (binaryStructuralValidityCertificateCode
              strictCertificate).length) +
          contextualModusPonensFullAssemblyCost context
            strictAtom selfStrict := hselfStrictRaw
      _ <= _ := by omega
  have hirreflexivityWeakRaw := weakening_full_payload_le
    (Gamma := insert (∼selfStrict) context)
    irreflexivity.derivation irreflexivity.certificate
    (by simp [selfStrict, negativeEqualitySelfStrictAtom, context,
      negativeEqualityContext])
  have hirreflexivityWeak :
      binaryProofLength irreflexivityInContext +
          (binaryStructuralValidityCertificateCode
            irreflexivityCertificate).length <=
        irreflexivity.payloadLength +
          weakeningFullAssemblyCost (insert (∼selfStrict) context) := by
    dsimp only [irreflexivityInContext, irreflexivityCertificate,
      irreflexivity]
    simpa [CertifiedPAProof.payloadLength_eq] using hirreflexivityWeakRaw
  let irreflexivityPayloadBound :=
    irreflexivity.payloadLength +
      weakeningFullAssemblyCost (insert (∼selfStrict) context)
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  have hfinal :
      binaryProofLength
          (LO.FirstOrder.Derivation2.cut
            (φ := selfStrict) selfStrictInContext
            irreflexivityInContext) +
          (binaryStructuralValidityCertificateCode
            (.binary selfStrictCertificate
              irreflexivityCertificate)).length <=
        (binaryProofLength selfStrictInContext +
          (binaryStructuralValidityCertificateCode
            selfStrictCertificate).length) +
        (binaryProofLength irreflexivityInContext +
          (binaryStructuralValidityCertificateCode
            irreflexivityCertificate).length) +
        negativeEqualityFinalCutFullAssemblyCost left right := by
    simp only [binaryProofLength, binaryDerivationCode,
      binaryStructuralValidityCertificateCode, List.length_append]
    unfold negativeEqualityFinalCutFullAssemblyCost
    dsimp only [context, selfStrict]
    omega
  rw [CertifiedPAProof.payloadLength_eq]
  change
    binaryProofLength
        (proveNotEqualityOfLessThanDerivation left right strictProof) +
      (binaryStructuralValidityCertificateCode
        (proveNotEqualityOfLessThanCertificate
          left right strictProof)).length <= _
  have houterDerivation :
      proveNotEqualityOfLessThanDerivation left right strictProof =
        LO.FirstOrder.Derivation2.cut
          (φ := selfStrict) selfStrictInContext
          irreflexivityInContext := by
    rfl
  have houterCertificate :
      proveNotEqualityOfLessThanCertificate left right strictProof =
        .binary selfStrictCertificate irreflexivityCertificate := by
    rfl
  rw [houterDerivation, houterCertificate]
  calc
    binaryProofLength
          (LO.FirstOrder.Derivation2.cut
            (φ := selfStrict) selfStrictInContext
            irreflexivityInContext) +
        (binaryStructuralValidityCertificateCode
          (.binary selfStrictCertificate
            irreflexivityCertificate)).length <=
        (binaryProofLength selfStrictInContext +
          (binaryStructuralValidityCertificateCode
            selfStrictCertificate).length) +
        (binaryProofLength irreflexivityInContext +
          (binaryStructuralValidityCertificateCode
            irreflexivityCertificate).length) +
        negativeEqualityFinalCutFullAssemblyCost left right := hfinal
    _ <= selfPayloadBound + irreflexivityPayloadBound +
        negativeEqualityFinalCutFullAssemblyCost left right := by
      dsimp only [irreflexivityPayloadBound]
      omega
    _ = proveNotEqualityOfLessThanPayloadBound
        left right strictProof.payloadLength := by
      unfold proveNotEqualityOfLessThanPayloadBound
      dsimp only [selfPayloadBound, irreflexivityPayloadBound,
        context, antecedent, strictAtom, selfStrict,
        transportConclusion, transport, rightReflexivity, irreflexivity]
      ring

theorem proveNotEqualityOfLessThan_verifier_eq_true
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (strictProof : CertifiedPAProof
      (negativeEqualityStrictAtom left right)) :
    listedCompactCertifiedPAProofVerifier
      (proveNotEqualityOfLessThan left right strictProof).code
      (compactFormulaCode (∼negativeEqualityAtom left right)) = true :=
  (proveNotEqualityOfLessThan left right strictProof).verifier_eq_true

#print axioms negativeEqualityAntecedentCertificate_valid
#print axioms proveNotEqualityOfLessThanCertificate_valid
#print axioms proveNotEqualityOfLessThan_payloadLength_le
#print axioms proveNotEqualityOfLessThan_verifier_eq_true

end FoundationCompactPANegativeEquality
