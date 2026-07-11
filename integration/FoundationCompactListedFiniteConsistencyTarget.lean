import integration.FoundationCompactListedMinProofLength

/-!
# Finite consistency for the concrete listed compact PA checker

This is the standard-model target that the later arithmetic sentence must
represent exactly.  Both acceptance and length use the list-preserving
certified verifier and its complete packed payload.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedFiniteConsistencyTarget

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedMinProofLength

theorem noListedCertifiedPAProofOfFalsum (code : Nat) :
    Not (ListedCertifiedPAProofOf code
      (⊥ : LO.FirstOrder.ArithmeticProposition)) := by
  intro haccept
  rcases listedCertifiedPAProofOf_toDerivation haccept with
    ⟨derivation⟩
  have hprovable :
      PA ⊢ (⊥ : LO.FirstOrder.ArithmeticSentence) :=
    (LO.FirstOrder.provable_iff_derivable2 (T := PA)).mpr
      (by simpa using Nonempty.intro derivation)
  exact LO.Entailment.Consistent.not_bot
    (𝓢 := PA) inferInstance hprovable

def ListedCertifiedFiniteConsistencyAt (cutoff : Nat) : Prop :=
  Not (exists code : Nat,
    packedPayloadLength code <= cutoff ∧
      ListedCertifiedPAProofOf code
        (⊥ : LO.FirstOrder.ArithmeticProposition))

theorem listedCertifiedFiniteConsistencyAt (cutoff : Nat) :
    ListedCertifiedFiniteConsistencyAt cutoff := by
  rintro ⟨code, _, haccept⟩
  exact noListedCertifiedPAProofOfFalsum code haccept

theorem listedCertifiedFiniteConsistencyAt_iff_forall
    (cutoff : Nat) :
    ListedCertifiedFiniteConsistencyAt cutoff ↔
      forall code : Nat, packedPayloadLength code <= cutoff ->
        Not (ListedCertifiedPAProofOf code
          (⊥ : LO.FirstOrder.ArithmeticProposition)) := by
  simp [ListedCertifiedFiniteConsistencyAt]

def amplifiedListedCertifiedFiniteConsistency
    (amplification n : Nat) : Prop :=
  ListedCertifiedFiniteConsistencyAt (2 ^ (amplification * n))

theorem amplifiedListedCertifiedFiniteConsistency_true
    (amplification n : Nat) :
    amplifiedListedCertifiedFiniteConsistency amplification n :=
  listedCertifiedFiniteConsistencyAt _

#print axioms noListedCertifiedPAProofOfFalsum
#print axioms listedCertifiedFiniteConsistencyAt
#print axioms listedCertifiedFiniteConsistencyAt_iff_forall
#print axioms amplifiedListedCertifiedFiniteConsistency_true

end FoundationCompactListedFiniteConsistencyTarget
