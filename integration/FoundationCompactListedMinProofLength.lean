import integration.FoundationCompactListedCertifiedEncoder

/-!
# Minimum accepted length for the concrete listed compact PA checker

The measured function in the collision route must be induced by an executable
proof predicate, not supplied by a project-level `proof_length` constant.  This
module defines the minimum complete payload length of a code accepted by the
list-preserving certified PA verifier.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedMinProofLength

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactListedCertifiedEncoder

def ListedCertifiedPAProofOf
    (code : Nat)
    (formula : LO.FirstOrder.ArithmeticProposition) : Prop :=
  listedCompactCertifiedPAProofVerifier code
    (compactFormulaCode formula) = true

def ListedCertifiedPayloadLengthWitness
    (formula : LO.FirstOrder.ArithmeticProposition)
    (length : Nat) : Prop :=
  exists code : Nat,
    ListedCertifiedPAProofOf code formula ∧
      packedPayloadLength code = length

noncomputable def minListedCertifiedPAProofPayloadLength
    (formula : LO.FirstOrder.ArithmeticProposition) : Nat := by
  classical
  exact
    if h : exists length : Nat,
        ListedCertifiedPayloadLengthWitness formula length then
      Nat.find h
    else
      0

theorem listedCertifiedPayloadLengthWitness_of_accept
    {code : Nat}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (haccept : ListedCertifiedPAProofOf code formula) :
    ListedCertifiedPayloadLengthWitness formula
      (packedPayloadLength code) := by
  exact ⟨code, haccept, rfl⟩

theorem listedCertifiedPayloadLength_exists_of_derivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (derivation : LO.FirstOrder.Derivation2 PA Gamma)
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hconclusion : Gamma = {formula}) :
    exists length : Nat,
      ListedCertifiedPayloadLengthWitness formula length := by
  rcases derivation_to_listedCompactCertifiedPAProofVerifier
      derivation hconclusion with
    ⟨code, certificate, hlength, haccept⟩
  exact ⟨packedPayloadLength code, code, haccept, rfl⟩

theorem minListedCertifiedPAProofPayloadLength_spec_of_exists
    (formula : LO.FirstOrder.ArithmeticProposition)
    (hexists : exists length : Nat,
      ListedCertifiedPayloadLengthWitness formula length) :
    ListedCertifiedPayloadLengthWitness formula
      (minListedCertifiedPAProofPayloadLength formula) := by
  classical
  rw [minListedCertifiedPAProofPayloadLength, dif_pos hexists]
  exact Nat.find_spec hexists

theorem minListedCertifiedPAProofPayloadLength_spec_of_derivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (derivation : LO.FirstOrder.Derivation2 PA Gamma)
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hconclusion : Gamma = {formula}) :
    exists code : Nat,
      ListedCertifiedPAProofOf code formula ∧
        packedPayloadLength code =
          minListedCertifiedPAProofPayloadLength formula := by
  have hexists := listedCertifiedPayloadLength_exists_of_derivation
    derivation hconclusion
  exact minListedCertifiedPAProofPayloadLength_spec_of_exists
    formula hexists

theorem minListedCertifiedPAProofPayloadLength_le_of_accept
    {code : Nat}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (haccept : ListedCertifiedPAProofOf code formula) :
    minListedCertifiedPAProofPayloadLength formula <=
      packedPayloadLength code := by
  classical
  let witness : ListedCertifiedPayloadLengthWitness formula
      (packedPayloadLength code) :=
    listedCertifiedPayloadLengthWitness_of_accept haccept
  have hexists : exists length : Nat,
      ListedCertifiedPayloadLengthWitness formula length :=
    ⟨packedPayloadLength code, witness⟩
  rw [minListedCertifiedPAProofPayloadLength, dif_pos hexists]
  exact Nat.find_min' hexists witness

theorem listedCertifiedPAProofOf_toDerivation
    {code : Nat}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (haccept : ListedCertifiedPAProofOf code formula) :
    Nonempty (LO.FirstOrder.Derivation2 PA {formula}) := by
  exact listedCompactCertifiedPAProofVerifier_toDerivation haccept

theorem minListedCertifiedPAProofPayloadLength_realized_of_derivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (derivation : LO.FirstOrder.Derivation2 PA Gamma)
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hconclusion : Gamma = {formula}) :
    exists code : Nat,
      packedPayloadLength code =
          minListedCertifiedPAProofPayloadLength formula ∧
        listedCompactCertifiedPAProofVerifier code
          (compactFormulaCode formula) = true := by
  rcases minListedCertifiedPAProofPayloadLength_spec_of_derivation
      derivation hconclusion with
    ⟨code, haccept, hlength⟩
  exact ⟨code, hlength, haccept⟩

#print axioms listedCertifiedPayloadLength_exists_of_derivation
#print axioms minListedCertifiedPAProofPayloadLength_spec_of_derivation
#print axioms minListedCertifiedPAProofPayloadLength_le_of_accept
#print axioms listedCertifiedPAProofOf_toDerivation
#print axioms minListedCertifiedPAProofPayloadLength_realized_of_derivation

end FoundationCompactListedMinProofLength
