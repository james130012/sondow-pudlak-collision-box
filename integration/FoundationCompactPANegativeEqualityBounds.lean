import integration.FoundationCompactPANegativeEquality
import integration.FoundationCompactListedLocalCostPrimitives
import integration.FoundationCompactCertifiedModusTollens

/-!
# Polynomial bounds for proof-producing negative equality

This module compresses the exact proof-tree and structural-certificate ledger
of `proveNotEqualityOfLessThan` into a fixed polynomial in an honest common
term-code bound.  No proof-length oracle or semantic certificate is used.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPANegativeEqualityBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAQuantitativeOrder
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactCanonicalDecodeLength
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactCertifiedModusTollens
open FoundationCompactPANegativeEquality

theorem binarySequentCode_length_le_uniform
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (cardBound formulaBound : Nat)
    (hcard : Gamma.card <= cardBound)
    (hformula : ∀ formula ∈ Gamma,
      (binaryFormulaCode formula).length <= formulaBound) :
    (binarySequentCode Gamma).length <=
      (binaryNatCode cardBound).length + cardBound * formulaBound := by
  have hheader := binaryNatCode_length_mono hcard
  have hpayload :
      Gamma.sum (fun formula => (binaryFormulaCode formula).length) <=
        Gamma.card * formulaBound := by
    simpa [nsmul_eq_mul] using
      Gamma.sum_le_card_nsmul
        (fun formula => (binaryFormulaCode formula).length)
        formulaBound hformula
  have hpayloadBound :
      Gamma.sum (fun formula => (binaryFormulaCode formula).length) <=
        cardBound * formulaBound :=
    hpayload.trans (Nat.mul_le_mul_right formulaBound hcard)
  have hflat :
      (Gamma.toList.flatMap binaryFormulaCode).length =
        Gamma.sum (fun formula => (binaryFormulaCode formula).length) := by
    rw [List.length_flatMap]
    simp
  simp only [binarySequentCode, List.length_append, hflat]
  omega

def negativeEqualityFormulaCodeEnvelope (termBound : Nat) : Nat :=
  32 * (orderAtomicFormulaCodeEnvelope termBound + 8)

def negativeEqualityFormulaInventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    List LO.FirstOrder.ArithmeticProposition :=
  [ ∼negativeEqualityAtom left right,
    negativeEqualityAtom left right,
    negativeEqualityAtom right right,
    (⊤ : LO.FirstOrder.ArithmeticProposition),
    negativeEqualityAtom right right ⋏
      (⊤ : LO.FirstOrder.ArithmeticProposition),
    negativeEqualityAntecedent left right,
    negativeEqualityStrictAtom left right,
    negativeEqualitySelfStrictAtom right,
    negativeEqualityTransportConclusion left right,
    negativeEqualityAntecedent left right 🡒
      negativeEqualityTransportConclusion left right,
    ∼(negativeEqualityAntecedent left right 🡒
      negativeEqualityTransportConclusion left right),
    ∼negativeEqualityTransportConclusion left right,
    ∼negativeEqualitySelfStrictAtom right ]

theorem negativeEqualityFormulaInventory_length
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (negativeEqualityFormulaInventory left right).length = 13 := by
  rfl

theorem negatedEquality_mem_inventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (∼negativeEqualityAtom left right) ∈
      (negativeEqualityFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeEqualityFormulaInventory, List.mem_cons]
  exact Or.inl True.intro

theorem equality_mem_inventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    negativeEqualityAtom left right ∈
      (negativeEqualityFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeEqualityFormulaInventory, List.mem_cons]
  exact Or.inr (Or.inl True.intro)

theorem reflexivity_mem_inventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    negativeEqualityAtom right right ∈
      (negativeEqualityFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeEqualityFormulaInventory, List.mem_cons]
  exact Or.inr (Or.inr (Or.inl True.intro))

theorem truth_mem_inventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (⊤ : LO.FirstOrder.ArithmeticProposition) ∈
      (negativeEqualityFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeEqualityFormulaInventory, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inl True.intro)))

theorem inner_mem_inventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (negativeEqualityAtom right right ⋏
      (⊤ : LO.FirstOrder.ArithmeticProposition)) ∈
      (negativeEqualityFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeEqualityFormulaInventory, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))

theorem antecedent_mem_inventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    negativeEqualityAntecedent left right ∈
      (negativeEqualityFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeEqualityFormulaInventory, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))

theorem strictAtom_mem_inventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    negativeEqualityStrictAtom left right ∈
      (negativeEqualityFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeEqualityFormulaInventory, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl True.intro))))))

theorem selfStrict_mem_inventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    negativeEqualitySelfStrictAtom right ∈
      (negativeEqualityFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeEqualityFormulaInventory, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inl True.intro)))))))

theorem transport_mem_inventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    negativeEqualityTransportConclusion left right ∈
      (negativeEqualityFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeEqualityFormulaInventory, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))

theorem transportImplication_mem_inventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (negativeEqualityAntecedent left right 🡒
      negativeEqualityTransportConclusion left right) ∈
      (negativeEqualityFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeEqualityFormulaInventory, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))

theorem negatedTransportImplication_mem_inventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (∼(negativeEqualityAntecedent left right 🡒
      negativeEqualityTransportConclusion left right)) ∈
      (negativeEqualityFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeEqualityFormulaInventory, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))

theorem negatedTransport_mem_inventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (∼negativeEqualityTransportConclusion left right) ∈
      (negativeEqualityFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeEqualityFormulaInventory, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl True.intro)))))))))))

theorem negatedSelfStrict_mem_inventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (∼negativeEqualitySelfStrictAtom right) ∈
      (negativeEqualityFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeEqualityFormulaInventory, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl True.intro))))))))))))

theorem negativeEqualityFormulaInventory_code_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (hformula : formula ∈ negativeEqualityFormulaInventory left right) :
    (binaryFormulaCode formula).length <=
      negativeEqualityFormulaCodeEnvelope termBound := by
  let atomicBound := orderAtomicFormulaCodeEnvelope termBound
  let formulaBound := negativeEqualityFormulaCodeEnvelope termBound
  have hequality :
      (binaryFormulaCode (negativeEqualityAtom left right)).length <=
        atomicBound := by
    simpa [negativeEqualityAtom, atomicBound] using
      equalityFormula_code_le_orderAtomic
        left right termBound hleft hright
  have hreflexivity :
      (binaryFormulaCode (negativeEqualityAtom right right)).length <=
        atomicBound := by
    simpa [negativeEqualityAtom, atomicBound] using
      equalityFormula_code_le_orderAtomic
        right right termBound hright hright
  have htruth :
      (binaryFormulaCode
        (⊤ : LO.FirstOrder.ArithmeticProposition)).length <= atomicBound := by
    simpa [atomicBound] using truthFormula_code_le_orderAtomic termBound
  have hstrict :
      (binaryFormulaCode
        (negativeEqualityStrictAtom left right)).length <= atomicBound := by
    simpa [negativeEqualityStrictAtom, atomicBound] using
      lessThanFormula_code_le_orderAtomic
        left right termBound hleft hright
  have hselfStrict :
      (binaryFormulaCode
        (negativeEqualitySelfStrictAtom right)).length <= atomicBound := by
    simpa [negativeEqualitySelfStrictAtom, atomicBound] using
      lessThanFormula_code_le_orderAtomic
        right right termBound hright hright
  have hinnerRaw := binaryFormulaCode_and_length_le
    (negativeEqualityAtom right right)
    (⊤ : LO.FirstOrder.ArithmeticProposition)
  have hinnerTight :
      (binaryFormulaCode
        (negativeEqualityAtom right right ⋏
          (⊤ : LO.FirstOrder.ArithmeticProposition))).length <=
        2 * atomicBound + 8 := by
    omega
  have hinner :
      (binaryFormulaCode
        (negativeEqualityAtom right right ⋏
          (⊤ : LO.FirstOrder.ArithmeticProposition))).length <= formulaBound := by
    exact hinnerTight.trans (by
      dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
      omega)
  have hantecedentRaw := binaryFormulaCode_and_length_le
    (negativeEqualityAtom left right)
    (negativeEqualityAtom right right ⋏
      (⊤ : LO.FirstOrder.ArithmeticProposition))
  have hantecedentTight :
      (binaryFormulaCode
        (negativeEqualityAntecedent left right)).length <=
          3 * atomicBound + 16 := by
    have hformulaEq :
        negativeEqualityAntecedent left right =
          negativeEqualityAtom left right ⋏
            (negativeEqualityAtom right right ⋏
              (⊤ : LO.FirstOrder.ArithmeticProposition)) := by
      simp [negativeEqualityAntecedent, negativeEqualityAtom,
        binaryRelationCongruenceAntecedent]
    rw [hformulaEq]
    omega
  have hantecedent :
      (binaryFormulaCode
        (negativeEqualityAntecedent left right)).length <= formulaBound := by
    exact hantecedentTight.trans (by
      dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
      omega)
  have htransportRaw := binaryFormulaCode_implication_length_le
    (negativeEqualityStrictAtom left right)
    (negativeEqualitySelfStrictAtom right)
  have htransportTight :
      (binaryFormulaCode
        (negativeEqualityTransportConclusion left right)).length <=
          3 * atomicBound + 8 := by
    simp only [negativeEqualityTransportConclusion]
    have htag5 : (binaryNatCode 5).length <= 8 := by decide
    omega
  have htransport :
      (binaryFormulaCode
        (negativeEqualityTransportConclusion left right)).length <=
          formulaBound := by
    exact htransportTight.trans (by
      dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
      omega)
  have himplicationRaw := binaryFormulaCode_implication_length_le
    (negativeEqualityAntecedent left right)
    (negativeEqualityTransportConclusion left right)
  have himplicationTight :
      (binaryFormulaCode
        (negativeEqualityAntecedent left right 🡒
          negativeEqualityTransportConclusion left right)).length <=
            9 * atomicBound + 48 := by
    have htag5 : (binaryNatCode 5).length <= 8 := by decide
    omega
  have himplication :
      (binaryFormulaCode
        (negativeEqualityAntecedent left right 🡒
          negativeEqualityTransportConclusion left right)).length <=
            formulaBound := by
    exact himplicationTight.trans (by
      dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
      omega)
  have hnegEqualityRaw := binaryFormulaCode_neg_length_le
    (negativeEqualityAtom left right)
  have hnegEquality :
      (binaryFormulaCode (∼negativeEqualityAtom left right)).length <=
        formulaBound := by
    dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
    omega
  have hnegImplicationRaw := binaryFormulaCode_neg_length_le
    (negativeEqualityAntecedent left right 🡒
      negativeEqualityTransportConclusion left right)
  have hnegImplication :
      (binaryFormulaCode
        (∼(negativeEqualityAntecedent left right 🡒
          negativeEqualityTransportConclusion left right))).length <=
            formulaBound := by
    dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
    omega
  have hnegTransportRaw := binaryFormulaCode_neg_length_le
    (negativeEqualityTransportConclusion left right)
  have hnegTransport :
      (binaryFormulaCode
        (∼negativeEqualityTransportConclusion left right)).length <=
          formulaBound := by
    dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
    omega
  have hnegSelfStrictRaw := binaryFormulaCode_neg_length_le
    (negativeEqualitySelfStrictAtom right)
  have hnegSelfStrict :
      (binaryFormulaCode
        (∼negativeEqualitySelfStrictAtom right)).length <= formulaBound := by
    dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
    omega
  simp only [negativeEqualityFormulaInventory, List.mem_cons] at hformula
  rcases hformula with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst formula
    exact hnegEquality
  · subst formula
    exact hequality.trans (by
      dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
      omega)
  · subst formula
    exact hreflexivity.trans (by
      dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
      omega)
  · subst formula
    exact htruth.trans (by
      dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
      omega)
  · subst formula
    exact hinner
  · subst formula
    exact hantecedent
  · subst formula
    exact hstrict.trans (by
      dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
      omega)
  · subst formula
    exact hselfStrict.trans (by
      dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
      omega)
  · subst formula
    exact htransport
  · subst formula
    exact himplication
  · subst formula
    exact hnegImplication
  · subst formula
    exact hnegTransport
  · rcases h with h | h
    · subst formula
      exact hnegSelfStrict
    · simp at h

def negativeEqualitySequentCodeEnvelope (termBound : Nat) : Nat :=
  (binaryNatCode 13).length +
    13 * negativeEqualityFormulaCodeEnvelope termBound

theorem negativeEqualitySequentCode_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound)
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (hsubset : Gamma ⊆
      (negativeEqualityFormulaInventory left right).toFinset) :
    (binarySequentCode Gamma).length <=
      negativeEqualitySequentCodeEnvelope termBound := by
  have hcandidates :=
    List.toFinset_card_le
      (l := negativeEqualityFormulaInventory left right)
  have hcard : Gamma.card <= 13 := by
    have hsubcard := Finset.card_le_card hsubset
    rw [negativeEqualityFormulaInventory_length left right] at hcandidates
    omega
  have hformula : ∀ formula ∈ Gamma,
      (binaryFormulaCode formula).length <=
        negativeEqualityFormulaCodeEnvelope termBound := by
    intro formula hmem
    apply negativeEqualityFormulaInventory_code_le
      left right termBound hleft hright formula
    have hinventory := hsubset hmem
    simpa using hinventory
  simpa [negativeEqualitySequentCodeEnvelope] using
    binarySequentCode_length_le_uniform Gamma 13
      (negativeEqualityFormulaCodeEnvelope termBound) hcard hformula

theorem negativeEqualityContext_subset_inventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    negativeEqualityContext left right ⊆
      (negativeEqualityFormulaInventory left right).toFinset := by
  intro formula hformula
  simp only [negativeEqualityContext, Finset.mem_singleton] at hformula
  subst formula
  exact negatedEquality_mem_inventory left right

theorem weakeningFullAssemblyCost_le_negativeEqualityEnvelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound)
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (hsubset : Gamma ⊆
      (negativeEqualityFormulaInventory left right).toFinset) :
    weakeningFullAssemblyCost Gamma <=
      negativeEqualitySequentCodeEnvelope termBound + 32 := by
  have hseq := negativeEqualitySequentCode_le
    left right termBound hleft hright Gamma hsubset
  have htag7 : (binaryNatCode 7).length <= 16 := by decide
  unfold weakeningFullAssemblyCost
  omega

theorem contextualModusPonensFullAssemblyCost_le_negativeEqualityEnvelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound)
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (hGamma : Gamma ⊆
      (negativeEqualityFormulaInventory left right).toFinset)
    (hantecedent : antecedent ∈
      (negativeEqualityFormulaInventory left right).toFinset)
    (hconsequent : consequent ∈
      (negativeEqualityFormulaInventory left right).toFinset)
    (himplication : (antecedent 🡒 consequent) ∈
      (negativeEqualityFormulaInventory left right).toFinset)
    (hnegImplication : (∼(antecedent 🡒 consequent)) ∈
      (negativeEqualityFormulaInventory left right).toFinset)
    (hnegConsequent : (∼consequent) ∈
      (negativeEqualityFormulaInventory left right).toFinset) :
    contextualModusPonensFullAssemblyCost Gamma antecedent consequent <=
      160 + 5 * negativeEqualitySequentCodeEnvelope termBound +
        4 * negativeEqualityFormulaCodeEnvelope termBound := by
  have hseq1 := negativeEqualitySequentCode_le
    left right termBound hleft hright (insert consequent Gamma)
    (Finset.insert_subset hconsequent hGamma)
  have hseq2 := negativeEqualitySequentCode_le
    left right termBound hleft hright
    (insert (antecedent 🡒 consequent) (insert consequent Gamma))
    (Finset.insert_subset himplication
      (Finset.insert_subset hconsequent hGamma))
  have hseq3 := negativeEqualitySequentCode_le
    left right termBound hleft hright
    (insert (∼(antecedent 🡒 consequent)) (insert consequent Gamma))
    (Finset.insert_subset hnegImplication
      (Finset.insert_subset hconsequent hGamma))
  have hseq4 := negativeEqualitySequentCode_le
    left right termBound hleft hright
    (insert antecedent
      (insert (∼(antecedent 🡒 consequent))
        (insert consequent Gamma)))
    (Finset.insert_subset hantecedent
      (Finset.insert_subset hnegImplication
        (Finset.insert_subset hconsequent hGamma)))
  have hseq5 := negativeEqualitySequentCode_le
    left right termBound hleft hright
    (insert (∼consequent)
      (insert (∼(antecedent 🡒 consequent))
        (insert consequent Gamma)))
    (Finset.insert_subset hnegConsequent
      (Finset.insert_subset hnegImplication
        (Finset.insert_subset hconsequent hGamma)))
  have himplicationCode := negativeEqualityFormulaInventory_code_le
    left right termBound hleft hright (antecedent 🡒 consequent)
      (List.mem_toFinset.mp himplication)
  have hantecedentCode := negativeEqualityFormulaInventory_code_le
    left right termBound hleft hright antecedent
      (List.mem_toFinset.mp hantecedent)
  have hnegConsequentCode := negativeEqualityFormulaInventory_code_le
    left right termBound hleft hright (∼consequent)
      (List.mem_toFinset.mp hnegConsequent)
  have hconsequentCode := negativeEqualityFormulaInventory_code_le
    left right termBound hleft hright consequent
      (List.mem_toFinset.mp hconsequent)
  have htag0 : (binaryNatCode 0).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  have htag7 : (binaryNatCode 7).length <= 16 := by decide
  have htag9 : (binaryNatCode 9).length <= 16 := by decide
  unfold contextualModusPonensFullAssemblyCost
  simp only [contextualModusPonensDerivationCost]
  omega

theorem negativeEqualityAntecedentFullAssemblyCost_le_envelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    negativeEqualityAntecedentFullAssemblyCost left right <=
      160 + 5 * negativeEqualitySequentCodeEnvelope termBound +
        5 * negativeEqualityFormulaCodeEnvelope termBound := by
  let inventory :=
    (negativeEqualityFormulaInventory left right).toFinset
  let context := negativeEqualityContext left right
  let equality := negativeEqualityAtom left right
  let reflexivity := negativeEqualityAtom right right
  let truth := (⊤ : LO.FirstOrder.ArithmeticProposition)
  let inner := reflexivity ⋏ truth
  let antecedent := negativeEqualityAntecedent left right
  have hcontext : context ⊆ inventory := by
    dsimp only [context, inventory]
    exact negativeEqualityContext_subset_inventory left right
  have hequality : equality ∈ inventory := by
    dsimp only [equality, inventory]
    exact equality_mem_inventory left right
  have hreflexivity : reflexivity ∈ inventory := by
    dsimp only [reflexivity, inventory]
    exact reflexivity_mem_inventory left right
  have htruth : truth ∈ inventory := by
    dsimp only [truth, inventory]
    exact truth_mem_inventory left right
  have hinner : inner ∈ inventory := by
    dsimp only [inner, reflexivity, truth, inventory]
    exact inner_mem_inventory left right
  have hantecedent : antecedent ∈ inventory := by
    dsimp only [antecedent, inventory]
    exact antecedent_mem_inventory left right
  have hseq1 := negativeEqualitySequentCode_le
    left right termBound hleft hright (insert antecedent context)
    (Finset.insert_subset hantecedent hcontext)
  have hseq2 := negativeEqualitySequentCode_le
    left right termBound hleft hright
    (insert equality (insert antecedent context))
    (Finset.insert_subset hequality
      (Finset.insert_subset hantecedent hcontext))
  have hseq3 := negativeEqualitySequentCode_le
    left right termBound hleft hright
    (insert inner (insert antecedent context))
    (Finset.insert_subset hinner
      (Finset.insert_subset hantecedent hcontext))
  have hseq4 := negativeEqualitySequentCode_le
    left right termBound hleft hright
    (insert reflexivity (insert inner (insert antecedent context)))
    (Finset.insert_subset hreflexivity
      (Finset.insert_subset hinner
        (Finset.insert_subset hantecedent hcontext)))
  have hseq5 := negativeEqualitySequentCode_le
    left right termBound hleft hright
    (insert truth (insert inner (insert antecedent context)))
    (Finset.insert_subset htruth
      (Finset.insert_subset hinner
        (Finset.insert_subset hantecedent hcontext)))
  have hequalityCode := negativeEqualityFormulaInventory_code_le
    left right termBound hleft hright equality
      (List.mem_toFinset.mp hequality)
  have hreflexivityCode := negativeEqualityFormulaInventory_code_le
    left right termBound hleft hright reflexivity
      (List.mem_toFinset.mp hreflexivity)
  have htruthCode := negativeEqualityFormulaInventory_code_le
    left right termBound hleft hright truth
      (List.mem_toFinset.mp htruth)
  have hinnerCode := negativeEqualityFormulaInventory_code_le
    left right termBound hleft hright inner
      (List.mem_toFinset.mp hinner)
  have htag0 : (binaryNatCode 0).length <= 16 := by decide
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  have htag7 : (binaryNatCode 7).length <= 16 := by decide
  dsimp only [context, equality, reflexivity, truth, inner, antecedent] at hseq1
  dsimp only [context, equality, reflexivity, truth, inner, antecedent] at hseq2
  dsimp only [context, equality, reflexivity, truth, inner, antecedent] at hseq3
  dsimp only [context, equality, reflexivity, truth, inner, antecedent] at hseq4
  dsimp only [context, equality, reflexivity, truth, inner, antecedent] at hseq5
  dsimp only [context, equality, reflexivity, truth, inner, antecedent] at hequalityCode
  dsimp only [context, equality, reflexivity, truth, inner, antecedent] at hreflexivityCode
  dsimp only [context, equality, reflexivity, truth, inner, antecedent] at htruthCode
  dsimp only [context, equality, reflexivity, truth, inner, antecedent] at hinnerCode
  unfold negativeEqualityAntecedentFullAssemblyCost
  simp only [negativeEqualityAntecedentDerivationCost]
  omega

theorem negativeEqualityFinalCutFullAssemblyCost_le_envelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    negativeEqualityFinalCutFullAssemblyCost left right <=
      32 + negativeEqualitySequentCodeEnvelope termBound +
        negativeEqualityFormulaCodeEnvelope termBound := by
  have hequality := equalityFormula_code_le_orderAtomic
    left right termBound hleft hright
  have hequalityAtom :
      (binaryFormulaCode (negativeEqualityAtom left right)).length <=
        orderAtomicFormulaCodeEnvelope termBound := by
    simpa only [negativeEqualityAtom] using hequality
  have hnegEqualityRaw := binaryFormulaCode_neg_length_le
    (negativeEqualityAtom left right)
  have hnegEquality :
      (binaryFormulaCode (∼negativeEqualityAtom left right)).length <=
        negativeEqualityFormulaCodeEnvelope termBound := by
    unfold negativeEqualityFormulaCodeEnvelope
    omega
  have hcontextCard : (negativeEqualityContext left right).card <= 1 := by
    simp [negativeEqualityContext]
  have hcontextFormula : ∀ formula ∈ negativeEqualityContext left right,
      (binaryFormulaCode formula).length <=
        negativeEqualityFormulaCodeEnvelope termBound := by
    intro formula hformula
    simp only [negativeEqualityContext, Finset.mem_singleton] at hformula
    subst formula
    exact hnegEquality
  have hseqSmall := binarySequentCode_length_le_uniform
    (negativeEqualityContext left right) 1
      (negativeEqualityFormulaCodeEnvelope termBound)
      hcontextCard hcontextFormula
  have hheader := binaryNatCode_length_mono (show 1 <= 13 by omega)
  have hseq :
      (binarySequentCode (negativeEqualityContext left right)).length <=
        negativeEqualitySequentCodeEnvelope termBound := by
    unfold negativeEqualitySequentCodeEnvelope
    omega
  have hselfAtomic := lessThanFormula_code_le_orderAtomic
    right right termBound hright hright
  have hselfBase :
      (binaryFormulaCode (negativeEqualitySelfStrictAtom right)).length <=
        orderAtomicFormulaCodeEnvelope termBound := by
    simpa only [negativeEqualitySelfStrictAtom] using hselfAtomic
  have hself :
      (binaryFormulaCode (negativeEqualitySelfStrictAtom right)).length <=
        negativeEqualityFormulaCodeEnvelope termBound := by
    unfold negativeEqualityFormulaCodeEnvelope
    omega
  have htag9 : (binaryNatCode 9).length <= 16 := by decide
  unfold negativeEqualityFinalCutFullAssemblyCost
  omega

theorem negativeEqualityTransportImplication_payloadLength_le_primitive
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (negativeEqualityTransportImplication left right).payloadLength <=
      orderPrimitiveCostEnvelope termBound := by
  have himplication := binaryRelationExtImplication_payloadLength_le
    Language.ORing.Rel.lt left right right right
  have haxiom := binaryRelationExtAxiomProof_payloadLength_le
    Language.ORing.Rel.lt
  have houter :=
    (fixedOrderFormulaCode_le_stage0
      (binaryRelationExtOuterBody Language.ORing.Rel.lt)
      (Or.inr (Or.inr (Or.inl rfl)))).trans
      (orderFormulaStage_le_envelope orderFormulaStage0 termBound
        (Or.inl rfl))
  have hstage1 :=
    (relationRightFirstBody_code_le_stage1 right termBound hright).trans
      (orderFormulaStage_le_envelope (orderFormulaStage1 termBound)
        termBound (Or.inr (Or.inl rfl)))
  have hstage2 :=
    (relationLeftSecondBody_code_le_stage2
      right right termBound hright hright).trans
      (orderFormulaStage_le_envelope (orderFormulaStage2 termBound)
        termBound (Or.inr (Or.inr (Or.inl rfl))))
  have hstage3 :=
    (relationAfterLeftSecondMatrix_code_le_stage3
      right right right termBound hright hright hright).trans
      (orderFormulaStage_le_envelope (orderFormulaStage3 termBound)
        termBound (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hfirst := specializationCost_le_orderEnvelope
    (binaryRelationExtOuterBody Language.ORing.Rel.lt)
    right termBound houter hright
  have hsecond := specializationCost_le_orderEnvelope
    (binaryRelationExtRightFirstBody Language.ORing.Rel.lt right)
    right termBound hstage1 hright
  have hthird := specializationCost_le_orderEnvelope
    (binaryRelationExtLeftSecondBody Language.ORing.Rel.lt right right)
    right termBound hstage2 hright
  have hfourth := specializationCost_le_orderEnvelope
    (binaryRelationExtAfterLeftSecondMatrix Language.ORing.Rel.lt
      right right right)
    left termBound hstage3 hleft
  have hfixed :
      32 + 10 * axiomSyntaxBudget
          (.eqRelExt Language.ORing.Rel.lt) <=
        fixedPAOrderPayloadEnvelope := by
    unfold fixedPAOrderPayloadEnvelope
    omega
  have hcast :
      (negativeEqualityTransportImplication left right).payloadLength =
        (binaryRelationExtImplication Language.ORing.Rel.lt
          left right right right).payloadLength := by
    unfold negativeEqualityTransportImplication
    exact cast_payloadLength _ _
  rw [hcast]
  unfold orderPrimitiveCostEnvelope
  omega

def negativeEqualityPrimitiveCostEnvelope (termBound : Nat) : Nat :=
  2 * orderPrimitiveCostEnvelope termBound +
    paPrimitiveCostEnvelope termBound +
    19 * negativeEqualitySequentCodeEnvelope termBound +
    14 * negativeEqualityFormulaCodeEnvelope termBound + 608

theorem proveNotEqualityOfLessThan_payloadLength_le_primitive
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (strictProof : CertifiedPAProof
      (negativeEqualityStrictAtom left right))
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (proveNotEqualityOfLessThan left right strictProof).payloadLength <=
      strictProof.payloadLength +
        negativeEqualityPrimitiveCostEnvelope termBound := by
  let context := negativeEqualityContext left right
  let antecedent := negativeEqualityAntecedent left right
  let strictAtom := negativeEqualityStrictAtom left right
  let selfStrict := negativeEqualitySelfStrictAtom right
  let transportConclusion := negativeEqualityTransportConclusion left right
  let implication := antecedent 🡒 transportConclusion
  let inventory :=
    (negativeEqualityFormulaInventory left right).toFinset
  have hraw := proveNotEqualityOfLessThan_payloadLength_le
    left right strictProof
  have htransport :=
    negativeEqualityTransportImplication_payloadLength_le_primitive
      left right termBound hleft hright
  have hcontext : context ⊆ inventory := by
    dsimp only [context, inventory]
    exact negativeEqualityContext_subset_inventory left right
  have hantecedentMem : antecedent ∈ inventory := by
    dsimp only [antecedent, inventory]
    exact antecedent_mem_inventory left right
  have hstrictMem : strictAtom ∈ inventory := by
    dsimp only [strictAtom, inventory]
    exact strictAtom_mem_inventory left right
  have hselfMem : selfStrict ∈ inventory := by
    dsimp only [selfStrict, inventory]
    exact selfStrict_mem_inventory left right
  have htransportMem : transportConclusion ∈ inventory := by
    dsimp only [transportConclusion, inventory]
    exact transport_mem_inventory left right
  have himplicationMem : implication ∈ inventory := by
    dsimp only [implication, antecedent, transportConclusion, inventory]
    exact transportImplication_mem_inventory left right
  have hnegImplicationMem : (∼implication) ∈ inventory := by
    dsimp only [implication, antecedent, transportConclusion, inventory]
    exact negatedTransportImplication_mem_inventory left right
  have hnegTransportMem : (∼transportConclusion) ∈ inventory := by
    dsimp only [transportConclusion, inventory]
    exact negatedTransport_mem_inventory left right
  have hnegSelfMem : (∼selfStrict) ∈ inventory := by
    dsimp only [selfStrict, inventory]
    exact negatedSelfStrict_mem_inventory left right
  have hweakTransport :=
    weakeningFullAssemblyCost_le_negativeEqualityEnvelope
      left right termBound hleft hright
      (insert implication context)
      (Finset.insert_subset himplicationMem hcontext)
  have hreflexivity :=
    proveEqualityReflexivityAtTerm_payloadLength_le_primitive
      right termBound hright
  have hantecedentCost :=
    negativeEqualityAntecedentFullAssemblyCost_le_envelope
      left right termBound hleft hright
  have hfirstMP :=
    contextualModusPonensFullAssemblyCost_le_negativeEqualityEnvelope
      left right termBound hleft hright context
      antecedent transportConclusion hcontext
      hantecedentMem htransportMem himplicationMem
      hnegImplicationMem hnegTransportMem
  have hweakStrict :=
    weakeningFullAssemblyCost_le_negativeEqualityEnvelope
      left right termBound hleft hright
      (insert strictAtom context)
      (Finset.insert_subset hstrictMem hcontext)
  have hsecondMP :=
    contextualModusPonensFullAssemblyCost_le_negativeEqualityEnvelope
      left right termBound hleft hright context
      strictAtom selfStrict hcontext
      hstrictMem hselfMem htransportMem
      hnegTransportMem hnegSelfMem
  have hirreflexivityRaw := proveLtIrrefl_payloadLength_le right
  have hirreflexivityEnvelope :=
    ltIrreflFullPayloadBound_le_primitive right termBound hright
  have hirreflexivity : (proveLtIrrefl right).payloadLength <=
      orderPrimitiveCostEnvelope termBound :=
    hirreflexivityRaw.trans hirreflexivityEnvelope
  have hweakIrreflexivity :=
    weakeningFullAssemblyCost_le_negativeEqualityEnvelope
      left right termBound hleft hright
      (insert (∼selfStrict) context)
      (Finset.insert_subset hnegSelfMem hcontext)
  have hfinal :=
    negativeEqualityFinalCutFullAssemblyCost_le_envelope
      left right termBound hleft hright
  change weakeningFullAssemblyCost
      (insert
        (negativeEqualityAntecedent left right 🡒
          negativeEqualityTransportConclusion left right)
        (negativeEqualityContext left right)) <=
      negativeEqualitySequentCodeEnvelope termBound + 32 at hweakTransport
  change contextualModusPonensFullAssemblyCost
      (negativeEqualityContext left right)
      (negativeEqualityAntecedent left right)
      (negativeEqualityTransportConclusion left right) <=
      160 + 5 * negativeEqualitySequentCodeEnvelope termBound +
        4 * negativeEqualityFormulaCodeEnvelope termBound at hfirstMP
  change weakeningFullAssemblyCost
      (insert (negativeEqualityStrictAtom left right)
        (negativeEqualityContext left right)) <=
      negativeEqualitySequentCodeEnvelope termBound + 32 at hweakStrict
  change contextualModusPonensFullAssemblyCost
      (negativeEqualityContext left right)
      (negativeEqualityStrictAtom left right)
      (negativeEqualitySelfStrictAtom right) <=
      160 + 5 * negativeEqualitySequentCodeEnvelope termBound +
        4 * negativeEqualityFormulaCodeEnvelope termBound at hsecondMP
  change weakeningFullAssemblyCost
      (insert (∼negativeEqualitySelfStrictAtom right)
        (negativeEqualityContext left right)) <=
      negativeEqualitySequentCodeEnvelope termBound + 32
        at hweakIrreflexivity
  calc
    (proveNotEqualityOfLessThan left right strictProof).payloadLength <=
        proveNotEqualityOfLessThanPayloadBound
          left right strictProof.payloadLength := hraw
    _ <= strictProof.payloadLength +
        negativeEqualityPrimitiveCostEnvelope termBound := by
      dsimp only [proveNotEqualityOfLessThanPayloadBound]
      unfold negativeEqualityPrimitiveCostEnvelope
      omega

theorem equalitySymmetryImplication_payloadLength_le_primitive
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (equalitySymmetryImplication left right).payloadLength <=
      paPrimitiveCostEnvelope termBound := by
  have himplication := equalitySymmetryImplication_payloadLength_le left right
  have haxiom := equalitySymmetryAxiomProof_payloadLength_le_fixed
  have hfirst := specializationCost_fixedFormula_le
    equalitySymmetryOuterBody left termBound (by simp) hleft
  have hsecond := specializationCost_stage1Formula_le
    (equalitySymmetryInnerBody left) right termBound
    (equalitySymmetryInnerBody_code_le_stage1 left termBound hleft) hright
  unfold paPrimitiveCostEnvelope
  omega

theorem equalitySymmetryModusTollensSyntaxBudget_le_envelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    modusTollensSyntaxBudget
        (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)
        (“!!right = !!left” : LO.FirstOrder.ArithmeticProposition) <=
      7 * negativeEqualityFormulaCodeEnvelope termBound := by
  let antecedent :=
    (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)
  let consequent :=
    (“!!right = !!left” : LO.FirstOrder.ArithmeticProposition)
  let atomicBound := orderAtomicFormulaCodeEnvelope termBound
  let formulaBound := negativeEqualityFormulaCodeEnvelope termBound
  have hantecedent : (binaryFormulaCode antecedent).length <= atomicBound := by
    dsimp only [antecedent, atomicBound]
    exact equalityFormula_code_le_orderAtomic
      left right termBound hleft hright
  have hconsequent : (binaryFormulaCode consequent).length <= atomicBound := by
    dsimp only [consequent, atomicBound]
    exact equalityFormula_code_le_orderAtomic
      right left termBound hright hleft
  have himplicationRaw := binaryFormulaCode_implication_length_le
    antecedent consequent
  have himplicationTight :
      (binaryFormulaCode (antecedent 🡒 consequent)).length <=
        3 * atomicBound + 8 := by
    have htag5 : (binaryNatCode 5).length <= 8 := by decide
    omega
  have hnegImplicationRaw := binaryFormulaCode_neg_length_le
    (antecedent 🡒 consequent)
  have hnegConsequentRaw := binaryFormulaCode_neg_length_le consequent
  have hnegAntecedentRaw := binaryFormulaCode_neg_length_le antecedent
  have hconjunctionRaw := binaryFormulaCode_and_length_le
    antecedent (∼consequent)
  have hantecedentEnvelope :
      (binaryFormulaCode antecedent).length <= formulaBound := by
    dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
    omega
  have hconsequentEnvelope :
      (binaryFormulaCode consequent).length <= formulaBound := by
    dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
    omega
  have himplicationEnvelope :
      (binaryFormulaCode (antecedent 🡒 consequent)).length <= formulaBound := by
    exact himplicationTight.trans (by
      dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
      omega)
  have hnegImplicationEnvelope :
      (binaryFormulaCode (∼(antecedent 🡒 consequent))).length <=
        formulaBound := by
    dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
    omega
  have hnegConsequentEnvelope :
      (binaryFormulaCode (∼consequent)).length <= formulaBound := by
    dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
    omega
  have hnegAntecedentEnvelope :
      (binaryFormulaCode (∼antecedent)).length <= formulaBound := by
    dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
    omega
  have hconjunctionEnvelope :
      (binaryFormulaCode (antecedent ⋏ (∼consequent))).length <=
        formulaBound := by
    dsimp only [formulaBound, negativeEqualityFormulaCodeEnvelope]
    omega
  unfold modusTollensSyntaxBudget
  dsimp only [antecedent, consequent] at *
  omega

def negativeEqualityModusTollensCostEnvelope (termBound : Nat) : Nat :=
  paPrimitiveCostEnvelope termBound + 272 +
    336 * negativeEqualityFormulaCodeEnvelope termBound

theorem equalitySymmetryModusTollens_payloadLength_le_primitive
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (negatedReverse : CertifiedPAProof
      (∼(“!!right = !!left” : LO.FirstOrder.ArithmeticProposition)))
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (modusTollens (equalitySymmetryImplication left right)
      negatedReverse).payloadLength <=
      negatedReverse.payloadLength +
        negativeEqualityModusTollensCostEnvelope termBound := by
  have hraw := modusTollens_payloadLength_le
    (equalitySymmetryImplication left right) negatedReverse
  have himplication :=
    equalitySymmetryImplication_payloadLength_le_primitive
      left right termBound hleft hright
  have hsyntax := equalitySymmetryModusTollensSyntaxBudget_le_envelope
    left right termBound hleft hright
  unfold negativeEqualityModusTollensCostEnvelope
  omega

#print axioms negativeEqualityFormulaInventory_code_le
#print axioms negativeEqualitySequentCode_le
#print axioms proveNotEqualityOfLessThan_payloadLength_le_primitive
#print axioms equalitySymmetryModusTollens_payloadLength_le_primitive

end FoundationCompactPANegativeEqualityBounds
