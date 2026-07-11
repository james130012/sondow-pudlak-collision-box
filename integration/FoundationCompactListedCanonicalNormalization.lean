import integration.FoundationCompactListedMinProofLength
import integration.FoundationCompactCertificateCanonicalDecodeLength
import integration.FoundationCompactListedFiniteConsistencyTarget

/-!
# Canonical normalization of listed compact certified PA proofs

Every code accepted by the list-preserving verifier decodes to a checked proof
tree and a complete structural certificate.  Re-encoding those same decoded
objects canonically preserves acceptance and never increases the honest payload
length.  Consequently the minimum accepted payload length is attained by a
canonical code; malformed or redundant encodings cannot create an artificially
short minimum.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedCanonicalNormalization

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAProofVerifier
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationCompactCertificateCanonicalDecodeLength
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactListedCertifiedVerifier
open FoundationComputableCompactPAProofEncoder
open FoundationCompactListedProofEncoder
open FoundationCompactListedCertifiedEncoder
open FoundationCompactListedMinProofLength
open FoundationCompactListedFiniteConsistencyTarget

/-- A canonical code is the explicit canonical packing of a checked proof tree
and its complete certificate, with the displayed conclusion fixed exactly. -/
def CanonicalListedCertifiedPAProofOf
    (code : Nat)
    (formula : LO.FirstOrder.ArithmeticProposition) : Prop :=
  exists (tree : CheckedPAProofTree)
      (certificate : StructuralValidityCertificate),
    code = canonicalPackedCertifiedPAProofCode tree certificate ∧
      certificateValid tree certificate ∧
      tree.conclusion = {formula}

/-- The fully numeric-coordinate canonical proof relation.  Both public
arguments are natural numbers; the existential formula is uniquely determined
by its injective compact code. -/
def CanonicalListedCertifiedCodedPAProofOf
    (code formulaCode : Nat) : Prop :=
  exists formula : LO.FirstOrder.ArithmeticProposition,
    CanonicalListedCertifiedPAProofOf code formula ∧
      compactFormulaCode formula = formulaCode

/-- Deterministic Boolean checker for the canonical numeric relation.  It
first decodes the complete listed payload, checks that the input is exactly the
canonical re-encoding of its checked projection, and then invokes the same
public proof verifier. -/
def canonicalListedCertifiedCodedPAProofVerifier
    (code formulaCode : Nat) : Bool :=
  match decodeCompactPackedListedCertifiedPAProof code with
  | some (listedTree, certificate) =>
      decide (code = canonicalPackedCertifiedPAProofCode
        listedTree.toChecked certificate) &&
        listedCompactCertifiedPAProofVerifier code formulaCode
  | none => false

theorem canonicalListedCertifiedPAProofOf_accepts
    {code : Nat}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hcanonical : CanonicalListedCertifiedPAProofOf code formula) :
    ListedCertifiedPAProofOf code formula := by
  rcases hcanonical with
    ⟨tree, certificate, rfl, hcertificate, hconclusion⟩
  exact listedCompactCertifiedPAProofVerifier_eq_true_of_certifiedTree
    tree certificate formula hcertificate hconclusion

theorem canonicalListedCertifiedCodedPAProofOf_accepts
    {code formulaCode : Nat}
    (hcanonical :
      CanonicalListedCertifiedCodedPAProofOf code formulaCode) :
    listedCompactCertifiedPAProofVerifier code formulaCode = true := by
  rcases hcanonical with ⟨formula, hproof, hformulaCode⟩
  have haccept := canonicalListedCertifiedPAProofOf_accepts hproof
  simpa [ListedCertifiedPAProofOf, hformulaCode] using haccept

theorem canonicalListedCertifiedCodedPAProofVerifier_eq_true_iff
    (code formulaCode : Nat) :
    canonicalListedCertifiedCodedPAProofVerifier code formulaCode = true ↔
      CanonicalListedCertifiedCodedPAProofOf code formulaCode := by
  constructor
  · intro haccept
    cases hdecode : decodeCompactPackedListedCertifiedPAProof code with
    | none =>
        simp [canonicalListedCertifiedCodedPAProofVerifier, hdecode]
          at haccept
    | some decoded =>
        rcases decoded with ⟨listedTree, certificate⟩
        have hparts :
            decide (code = canonicalPackedCertifiedPAProofCode
                listedTree.toChecked certificate) = true ∧
              listedCompactCertifiedPAProofVerifier
                code formulaCode = true := by
          simpa [canonicalListedCertifiedCodedPAProofVerifier,
            hdecode] using haccept
        have hcanonicalCode :
            code = canonicalPackedCertifiedPAProofCode
              listedTree.toChecked certificate := by
          simpa using of_decide_eq_true hparts.1
        rcases
            (listedCompactCertifiedPAProofVerifier_eq_true_iff _ _).mp
              hparts.2 with
          ⟨checkedTree, checkedCertificate, formula,
            hcheckedDecode, hcertificate, hconclusion, hformulaCode⟩
        have hdecodedObjects :
            (checkedTree, checkedCertificate) =
              (listedTree, certificate) := by
          exact Option.some.inj (hcheckedDecode.symm.trans hdecode)
        have htree : checkedTree = listedTree :=
          congrArg Prod.fst hdecodedObjects
        have hcertificateEq : checkedCertificate = certificate :=
          congrArg Prod.snd hdecodedObjects
        subst checkedTree
        subst checkedCertificate
        have hcheckedCertificate :
            certificateValid listedTree.toChecked certificate :=
          (listedCertificateValid_toChecked_iff
            listedTree certificate).mp hcertificate
        have hcheckedConclusion :
            listedTree.toChecked.conclusion = {formula} := by
          simpa using hconclusion
        exact ⟨formula,
          ⟨listedTree.toChecked, certificate, hcanonicalCode,
            hcheckedCertificate, hcheckedConclusion⟩,
          hformulaCode⟩
  · rintro ⟨formula, hcanonical, hformulaCode⟩
    rcases hcanonical with
      ⟨tree, certificate, hcode, hcertificate, hconclusion⟩
    subst code
    have hdecode :=
      decodeCompactPackedListedCertifiedPAProof_canonicalPackedCode
        tree certificate
    have hpublic :=
      listedCompactCertifiedPAProofVerifier_eq_true_of_certifiedTree
        tree certificate formula hcertificate hconclusion
    simpa [canonicalListedCertifiedCodedPAProofVerifier,
      hdecode, toListed_toChecked, hformulaCode] using hpublic

/-- Canonically re-encoding the objects decoded from an accepted listed code
does not increase its complete proof-plus-certificate payload length. -/
theorem acceptedCode_has_noLongerCanonicalCode
    {code : Nat}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (haccept : ListedCertifiedPAProofOf code formula) :
    exists normalizedCode : Nat,
      CanonicalListedCertifiedPAProofOf normalizedCode formula ∧
        packedPayloadLength normalizedCode <= packedPayloadLength code := by
  have hchecks :=
    (listedCompactCertifiedPAProofVerifier_eq_true_iff _ _).mp haccept
  rcases hchecks with
    ⟨listedTree, certificate, decodedFormula, hdecode,
      hcertificate, hconclusion, hformulaCode⟩
  have hformula : decodedFormula = formula :=
    compactFormulaCode_injective hformulaCode
  subst decodedFormula
  let tree := listedTree.toChecked
  let normalizedCode :=
    canonicalPackedCertifiedPAProofCode tree certificate
  have hcheckedDecode :
      decodeCompactPackedCertifiedPAProof code =
        some (tree, certificate) := by
    exact decodeCompactPackedListedCertifiedPAProof_toChecked hdecode
  have hlength :
      (binaryCertifiedPAProofCode tree certificate).length <=
        packedPayloadLength code :=
    decodeCompactPackedCertifiedPAProof_binaryLength_le hcheckedDecode
  have hcheckedCertificate : certificateValid tree certificate := by
    exact (listedCertificateValid_toChecked_iff
      listedTree certificate).mp hcertificate
  have hcheckedConclusion : tree.conclusion = {formula} := by
    simpa [tree] using hconclusion
  refine ⟨normalizedCode, ?_, ?_⟩
  · exact ⟨tree, certificate, rfl,
      hcheckedCertificate, hcheckedConclusion⟩
  · simpa [normalizedCode,
      canonicalBinaryCertifiedPAProofCode_length] using hlength

/-- Numeric-coordinate form of canonical normalization: an arbitrary public
acceptance at `(code, formulaCode)` has a no-longer canonical representative
at exactly the same formula number. -/
theorem acceptedCodedProof_has_noLongerCanonicalCode
    {code formulaCode : Nat}
    (haccept :
      listedCompactCertifiedPAProofVerifier code formulaCode = true) :
    exists normalizedCode : Nat,
      CanonicalListedCertifiedCodedPAProofOf
          normalizedCode formulaCode ∧
        packedPayloadLength normalizedCode <= packedPayloadLength code := by
  rcases (listedCompactCertifiedPAProofVerifier_eq_true_iff _ _).mp haccept with
    ⟨tree, certificate, formula, hdecode, hcertificate,
      hconclusion, hformulaCode⟩
  have htypedAccept : ListedCertifiedPAProofOf code formula := by
    simpa [ListedCertifiedPAProofOf, hformulaCode] using haccept
  rcases acceptedCode_has_noLongerCanonicalCode htypedAccept with
    ⟨normalizedCode, hcanonical, hlength⟩
  exact ⟨normalizedCode,
    ⟨formula, hcanonical, hformulaCode⟩, hlength⟩

/-- The concrete minimum accepted payload length is attained by a canonical
proof-plus-certificate code. -/
theorem minListedCertifiedPAProofPayloadLength_realized_canonically
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (derivation : LO.FirstOrder.Derivation2 PA Gamma)
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hconclusion : Gamma = {formula}) :
    exists code : Nat,
      CanonicalListedCertifiedPAProofOf code formula ∧
        packedPayloadLength code =
          minListedCertifiedPAProofPayloadLength formula := by
  rcases minListedCertifiedPAProofPayloadLength_spec_of_derivation
      derivation hconclusion with
    ⟨minimumCode, hminimumAccepts, hminimumLength⟩
  rcases acceptedCode_has_noLongerCanonicalCode hminimumAccepts with
    ⟨canonicalCode, hcanonical, hcanonicalLength⟩
  have hcanonicalAccepts :
      ListedCertifiedPAProofOf canonicalCode formula :=
    canonicalListedCertifiedPAProofOf_accepts hcanonical
  have hminimumLeCanonical :
      minListedCertifiedPAProofPayloadLength formula <=
        packedPayloadLength canonicalCode :=
    minListedCertifiedPAProofPayloadLength_le_of_accept hcanonicalAccepts
  have hcanonicalLeMinimum :
      packedPayloadLength canonicalCode <=
        minListedCertifiedPAProofPayloadLength formula := by
    simpa [hminimumLength] using hcanonicalLength
  exact ⟨canonicalCode, hcanonical,
    Nat.le_antisymm hcanonicalLeMinimum hminimumLeCanonical⟩

/-- Finite consistency restricted to canonical complete proof-plus-certificate
codes.  The normalization theorem below proves that this restriction changes
neither the cutoff nor the standard-model proposition. -/
def CanonicalListedCertifiedFiniteConsistencyAt (cutoff : Nat) : Prop :=
  Not (exists code : Nat,
    packedPayloadLength code <= cutoff ∧
      CanonicalListedCertifiedPAProofOf code
        (⊥ : LO.FirstOrder.ArithmeticProposition))

/-- The same canonical finite-consistency target written only with numeric
proof and formula coordinates. -/
def CanonicalCodedFiniteConsistencyAt (cutoff : Nat) : Prop :=
  Not (exists code : Nat,
    packedPayloadLength code <= cutoff ∧
      CanonicalListedCertifiedCodedPAProofOf code
        (compactFormulaCode
          (⊥ : LO.FirstOrder.ArithmeticProposition)))

theorem canonicalFiniteConsistencyAt_iff_coded
    (cutoff : Nat) :
    CanonicalListedCertifiedFiniteConsistencyAt cutoff ↔
      CanonicalCodedFiniteConsistencyAt cutoff := by
  constructor
  · intro htyped
    rintro ⟨code, hlength, formula, hcanonical, hformulaCode⟩
    have hformula :
        formula = (⊥ : LO.FirstOrder.ArithmeticProposition) :=
      compactFormulaCode_injective hformulaCode
    subst formula
    exact htyped ⟨code, hlength, hcanonical⟩
  · intro hcoded
    rintro ⟨code, hlength, hcanonical⟩
    exact hcoded ⟨code, hlength,
      (⊥ : LO.FirstOrder.ArithmeticProposition), hcanonical, rfl⟩

/-- Pointwise, with the same cutoff, quantifying over all accepted encodings is
equivalent to quantifying only over canonical encodings. -/
theorem listedCertifiedFiniteConsistencyAt_iff_canonical
    (cutoff : Nat) :
    ListedCertifiedFiniteConsistencyAt cutoff ↔
      CanonicalListedCertifiedFiniteConsistencyAt cutoff := by
  constructor
  · intro hall
    rintro ⟨code, hlength, hcanonical⟩
    apply hall
    exact ⟨code, hlength,
      canonicalListedCertifiedPAProofOf_accepts hcanonical⟩
  · intro hcanonical
    rintro ⟨code, hlength, haccept⟩
    rcases acceptedCode_has_noLongerCanonicalCode haccept with
      ⟨normalizedCode, hnormalized, hnormalizedLength⟩
    apply hcanonical
    exact ⟨normalizedCode,
      hnormalizedLength.trans hlength, hnormalized⟩

theorem listedCertifiedFiniteConsistencyAt_iff_canonicalCoded
    (cutoff : Nat) :
    ListedCertifiedFiniteConsistencyAt cutoff ↔
      CanonicalCodedFiniteConsistencyAt cutoff :=
  (listedCertifiedFiniteConsistencyAt_iff_canonical cutoff).trans
    (canonicalFiniteConsistencyAt_iff_coded cutoff)

#print axioms canonicalListedCertifiedPAProofOf_accepts
#print axioms canonicalListedCertifiedCodedPAProofOf_accepts
#print axioms canonicalListedCertifiedCodedPAProofVerifier_eq_true_iff
#print axioms acceptedCode_has_noLongerCanonicalCode
#print axioms acceptedCodedProof_has_noLongerCanonicalCode
#print axioms minListedCertifiedPAProofPayloadLength_realized_canonically
#print axioms listedCertifiedFiniteConsistencyAt_iff_canonical
#print axioms listedCertifiedFiniteConsistencyAt_iff_canonicalCoded

end FoundationCompactListedCanonicalNormalization
