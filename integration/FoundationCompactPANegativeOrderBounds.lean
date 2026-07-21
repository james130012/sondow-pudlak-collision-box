import integration.FoundationCompactPANegativeOrder
import integration.FoundationCompactPANegativeEqualityBounds

/-!
# Polynomial bounds for proof-producing negative order

The strict-order asymmetry tree is compressed into a fixed polynomial in a
common honest term-code bound.  The same envelope also bounds the equality
branch used by the closed atomic compiler.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPANegativeOrderBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAQuantitativeOrder
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactCertifiedModusTollens
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactCanonicalDecodeLength
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactPANegativeEqualityBounds
open FoundationCompactPANegativeOrder

def negativeOrderFormulaCodeEnvelope (termBound : Nat) : Nat :=
  16 * (orderAtomicFormulaCodeEnvelope termBound + 8)

def negativeOrderFormulaInventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    List LO.FirstOrder.ArithmeticProposition :=
  [ ∼negativeOrderForwardAtom left right,
    negativeOrderForwardAtom left right,
    negativeOrderReverseAtom left right,
    negativeOrderAntecedent left right,
    negativeOrderSelfAtom left,
    negativeOrderAntecedent left right 🡒 negativeOrderSelfAtom left,
    ∼(negativeOrderAntecedent left right 🡒 negativeOrderSelfAtom left),
    ∼negativeOrderSelfAtom left ]

theorem negativeOrderFormulaInventory_length
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (negativeOrderFormulaInventory left right).length = 8 := by
  rfl

theorem negatedForward_mem_negativeOrderInventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (∼negativeOrderForwardAtom left right) ∈
      (negativeOrderFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeOrderFormulaInventory, List.mem_cons]
  exact Or.inl True.intro

theorem forward_mem_negativeOrderInventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    negativeOrderForwardAtom left right ∈
      (negativeOrderFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeOrderFormulaInventory, List.mem_cons]
  exact Or.inr (Or.inl True.intro)

theorem reverse_mem_negativeOrderInventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    negativeOrderReverseAtom left right ∈
      (negativeOrderFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeOrderFormulaInventory, List.mem_cons]
  exact Or.inr (Or.inr (Or.inl True.intro))

theorem antecedent_mem_negativeOrderInventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    negativeOrderAntecedent left right ∈
      (negativeOrderFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeOrderFormulaInventory, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inl True.intro)))

theorem self_mem_negativeOrderInventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    negativeOrderSelfAtom left ∈
      (negativeOrderFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeOrderFormulaInventory, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))

theorem implication_mem_negativeOrderInventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (negativeOrderAntecedent left right 🡒 negativeOrderSelfAtom left) ∈
      (negativeOrderFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeOrderFormulaInventory, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl True.intro)))))

theorem negatedImplication_mem_negativeOrderInventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (∼(negativeOrderAntecedent left right 🡒
      negativeOrderSelfAtom left)) ∈
      (negativeOrderFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeOrderFormulaInventory, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl True.intro))))))

theorem negatedSelf_mem_negativeOrderInventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (∼negativeOrderSelfAtom left) ∈
      (negativeOrderFormulaInventory left right).toFinset := by
  apply List.mem_toFinset.mpr
  simp only [negativeOrderFormulaInventory, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inl True.intro)))))))

theorem negativeOrderFormulaInventory_code_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (hformula : formula ∈ negativeOrderFormulaInventory left right) :
    (binaryFormulaCode formula).length <=
      negativeOrderFormulaCodeEnvelope termBound := by
  let atomicBound := orderAtomicFormulaCodeEnvelope termBound
  let formulaBound := negativeOrderFormulaCodeEnvelope termBound
  have hforward :
      (binaryFormulaCode (negativeOrderForwardAtom left right)).length <=
        atomicBound := by
    simpa [negativeOrderForwardAtom, atomicBound] using
      lessThanFormula_code_le_orderAtomic
        left right termBound hleft hright
  have hreverse :
      (binaryFormulaCode (negativeOrderReverseAtom left right)).length <=
        atomicBound := by
    simpa [negativeOrderReverseAtom, atomicBound] using
      lessThanFormula_code_le_orderAtomic
        right left termBound hright hleft
  have hself :
      (binaryFormulaCode (negativeOrderSelfAtom left)).length <=
        atomicBound := by
    simpa [negativeOrderSelfAtom, atomicBound] using
      lessThanFormula_code_le_orderAtomic
        left left termBound hleft hleft
  have hantecedentRaw := binaryFormulaCode_and_length_le
    (negativeOrderForwardAtom left right)
    (negativeOrderReverseAtom left right)
  have hantecedentTight :
      (binaryFormulaCode (negativeOrderAntecedent left right)).length <=
        2 * atomicBound + 8 := by
    simp only [negativeOrderAntecedent]
    omega
  have himplicationRaw := binaryFormulaCode_implication_length_le
    (negativeOrderAntecedent left right)
    (negativeOrderSelfAtom left)
  have himplicationTight :
      (binaryFormulaCode
        (negativeOrderAntecedent left right 🡒
          negativeOrderSelfAtom left)).length <=
        5 * atomicBound + 24 := by
    have htag5 : (binaryNatCode 5).length <= 8 := by decide
    omega
  have hnegForwardRaw := binaryFormulaCode_neg_length_le
    (negativeOrderForwardAtom left right)
  have hnegImplicationRaw := binaryFormulaCode_neg_length_le
    (negativeOrderAntecedent left right 🡒 negativeOrderSelfAtom left)
  have hnegSelfRaw := binaryFormulaCode_neg_length_le
    (negativeOrderSelfAtom left)
  have hforwardEnvelope :
      (binaryFormulaCode (negativeOrderForwardAtom left right)).length <=
        formulaBound := by
    dsimp only [formulaBound, negativeOrderFormulaCodeEnvelope]
    omega
  have hreverseEnvelope :
      (binaryFormulaCode (negativeOrderReverseAtom left right)).length <=
        formulaBound := by
    dsimp only [formulaBound, negativeOrderFormulaCodeEnvelope]
    omega
  have hantecedentEnvelope :
      (binaryFormulaCode (negativeOrderAntecedent left right)).length <=
        formulaBound := by
    exact hantecedentTight.trans (by
      dsimp only [formulaBound, negativeOrderFormulaCodeEnvelope]
      omega)
  have hselfEnvelope :
      (binaryFormulaCode (negativeOrderSelfAtom left)).length <=
        formulaBound := by
    dsimp only [formulaBound, negativeOrderFormulaCodeEnvelope]
    omega
  have himplicationEnvelope :
      (binaryFormulaCode
        (negativeOrderAntecedent left right 🡒
          negativeOrderSelfAtom left)).length <= formulaBound := by
    exact himplicationTight.trans (by
      dsimp only [formulaBound, negativeOrderFormulaCodeEnvelope]
      omega)
  have hnegForwardEnvelope :
      (binaryFormulaCode (∼negativeOrderForwardAtom left right)).length <=
        formulaBound := by
    dsimp only [formulaBound, negativeOrderFormulaCodeEnvelope]
    omega
  have hnegImplicationEnvelope :
      (binaryFormulaCode
        (∼(negativeOrderAntecedent left right 🡒
          negativeOrderSelfAtom left))).length <= formulaBound := by
    dsimp only [formulaBound, negativeOrderFormulaCodeEnvelope]
    omega
  have hnegSelfEnvelope :
      (binaryFormulaCode (∼negativeOrderSelfAtom left)).length <=
        formulaBound := by
    dsimp only [formulaBound, negativeOrderFormulaCodeEnvelope]
    omega
  simp only [negativeOrderFormulaInventory, List.mem_cons] at hformula
  rcases hformula with h | h | h | h | h | h | h | h
  · subst formula
    exact hnegForwardEnvelope
  · subst formula
    exact hforwardEnvelope
  · subst formula
    exact hreverseEnvelope
  · subst formula
    exact hantecedentEnvelope
  · subst formula
    exact hselfEnvelope
  · subst formula
    exact himplicationEnvelope
  · subst formula
    exact hnegImplicationEnvelope
  · rcases h with h | h
    · subst formula
      exact hnegSelfEnvelope
    · simp at h

def negativeOrderSequentCodeEnvelope (termBound : Nat) : Nat :=
  (binaryNatCode 8).length +
    8 * negativeOrderFormulaCodeEnvelope termBound

theorem negativeOrderSequentCode_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound)
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (hsubset : Gamma ⊆
      (negativeOrderFormulaInventory left right).toFinset) :
    (binarySequentCode Gamma).length <=
      negativeOrderSequentCodeEnvelope termBound := by
  have hcandidates :=
    List.toFinset_card_le (l := negativeOrderFormulaInventory left right)
  have hcard : Gamma.card <= 8 := by
    have hsubcard := Finset.card_le_card hsubset
    rw [negativeOrderFormulaInventory_length left right] at hcandidates
    omega
  have hformula : ∀ formula ∈ Gamma,
      (binaryFormulaCode formula).length <=
        negativeOrderFormulaCodeEnvelope termBound := by
    intro formula hmem
    apply negativeOrderFormulaInventory_code_le
      left right termBound hleft hright formula
    exact List.mem_toFinset.mp (hsubset hmem)
  simpa [negativeOrderSequentCodeEnvelope] using
    binarySequentCode_length_le_uniform Gamma 8
      (negativeOrderFormulaCodeEnvelope termBound) hcard hformula

theorem negativeOrderContext_subset_inventory
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    negativeOrderContext left right ⊆
      (negativeOrderFormulaInventory left right).toFinset := by
  intro formula hformula
  simp only [negativeOrderContext, Finset.mem_singleton] at hformula
  subst formula
  exact negatedForward_mem_negativeOrderInventory left right

theorem negativeOrderWeakeningCost_le_envelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound)
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (hsubset : Gamma ⊆
      (negativeOrderFormulaInventory left right).toFinset) :
    weakeningFullAssemblyCost Gamma <=
      negativeOrderSequentCodeEnvelope termBound + 32 := by
  have hseq := negativeOrderSequentCode_le
    left right termBound hleft hright Gamma hsubset
  have htag7 : (binaryNatCode 7).length <= 16 := by decide
  unfold weakeningFullAssemblyCost
  omega

theorem negativeOrderContextualModusPonensCost_le_envelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound)
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (hGamma : Gamma ⊆
      (negativeOrderFormulaInventory left right).toFinset)
    (hantecedent : antecedent ∈
      (negativeOrderFormulaInventory left right).toFinset)
    (hconsequent : consequent ∈
      (negativeOrderFormulaInventory left right).toFinset)
    (himplication : (antecedent 🡒 consequent) ∈
      (negativeOrderFormulaInventory left right).toFinset)
    (hnegImplication : (∼(antecedent 🡒 consequent)) ∈
      (negativeOrderFormulaInventory left right).toFinset)
    (hnegConsequent : (∼consequent) ∈
      (negativeOrderFormulaInventory left right).toFinset) :
    contextualModusPonensFullAssemblyCost Gamma antecedent consequent <=
      160 + 5 * negativeOrderSequentCodeEnvelope termBound +
        4 * negativeOrderFormulaCodeEnvelope termBound := by
  have hseq1 := negativeOrderSequentCode_le
    left right termBound hleft hright (insert consequent Gamma)
    (Finset.insert_subset hconsequent hGamma)
  have hseq2 := negativeOrderSequentCode_le
    left right termBound hleft hright
    (insert (antecedent 🡒 consequent) (insert consequent Gamma))
    (Finset.insert_subset himplication
      (Finset.insert_subset hconsequent hGamma))
  have hseq3 := negativeOrderSequentCode_le
    left right termBound hleft hright
    (insert (∼(antecedent 🡒 consequent)) (insert consequent Gamma))
    (Finset.insert_subset hnegImplication
      (Finset.insert_subset hconsequent hGamma))
  have hseq4 := negativeOrderSequentCode_le
    left right termBound hleft hright
    (insert antecedent
      (insert (∼(antecedent 🡒 consequent))
        (insert consequent Gamma)))
    (Finset.insert_subset hantecedent
      (Finset.insert_subset hnegImplication
        (Finset.insert_subset hconsequent hGamma)))
  have hseq5 := negativeOrderSequentCode_le
    left right termBound hleft hright
    (insert (∼consequent)
      (insert (∼(antecedent 🡒 consequent))
        (insert consequent Gamma)))
    (Finset.insert_subset hnegConsequent
      (Finset.insert_subset hnegImplication
        (Finset.insert_subset hconsequent hGamma)))
  have himplicationCode := negativeOrderFormulaInventory_code_le
    left right termBound hleft hright (antecedent 🡒 consequent)
      (List.mem_toFinset.mp himplication)
  have hantecedentCode := negativeOrderFormulaInventory_code_le
    left right termBound hleft hright antecedent
      (List.mem_toFinset.mp hantecedent)
  have hnegConsequentCode := negativeOrderFormulaInventory_code_le
    left right termBound hleft hright (∼consequent)
      (List.mem_toFinset.mp hnegConsequent)
  have hconsequentCode := negativeOrderFormulaInventory_code_le
    left right termBound hleft hright consequent
      (List.mem_toFinset.mp hconsequent)
  have htag0 : (binaryNatCode 0).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  have htag7 : (binaryNatCode 7).length <= 16 := by decide
  have htag9 : (binaryNatCode 9).length <= 16 := by decide
  unfold contextualModusPonensFullAssemblyCost
  simp only [contextualModusPonensDerivationCost]
  omega

theorem negativeOrderAntecedentFullAssemblyCost_le_envelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    negativeOrderAntecedentFullAssemblyCost left right <=
      96 + 3 * negativeOrderSequentCodeEnvelope termBound +
        3 * negativeOrderFormulaCodeEnvelope termBound := by
  let inventory := (negativeOrderFormulaInventory left right).toFinset
  let context := negativeOrderContext left right
  let forward := negativeOrderForwardAtom left right
  let reverse := negativeOrderReverseAtom left right
  let antecedent := negativeOrderAntecedent left right
  have hcontext : context ⊆ inventory := by
    dsimp only [context, inventory]
    exact negativeOrderContext_subset_inventory left right
  have hforward : forward ∈ inventory := by
    dsimp only [forward, inventory]
    exact forward_mem_negativeOrderInventory left right
  have hreverse : reverse ∈ inventory := by
    dsimp only [reverse, inventory]
    exact reverse_mem_negativeOrderInventory left right
  have hantecedent : antecedent ∈ inventory := by
    dsimp only [antecedent, inventory]
    exact antecedent_mem_negativeOrderInventory left right
  have hseq1 := negativeOrderSequentCode_le
    left right termBound hleft hright (insert antecedent context)
    (Finset.insert_subset hantecedent hcontext)
  have hseq2 := negativeOrderSequentCode_le
    left right termBound hleft hright
    (insert forward (insert antecedent context))
    (Finset.insert_subset hforward
      (Finset.insert_subset hantecedent hcontext))
  have hseq3 := negativeOrderSequentCode_le
    left right termBound hleft hright
    (insert reverse (insert antecedent context))
    (Finset.insert_subset hreverse
      (Finset.insert_subset hantecedent hcontext))
  have hforwardCode := negativeOrderFormulaInventory_code_le
    left right termBound hleft hright forward
      (List.mem_toFinset.mp hforward)
  have hreverseCode := negativeOrderFormulaInventory_code_le
    left right termBound hleft hright reverse
      (List.mem_toFinset.mp hreverse)
  have htag0 : (binaryNatCode 0).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  have htag7 : (binaryNatCode 7).length <= 16 := by decide
  dsimp only [context, forward, reverse, antecedent] at hseq1
  dsimp only [context, forward, reverse, antecedent] at hseq2
  dsimp only [context, forward, reverse, antecedent] at hseq3
  dsimp only [context, forward, reverse, antecedent] at hforwardCode
  dsimp only [context, forward, reverse, antecedent] at hreverseCode
  unfold negativeOrderAntecedentFullAssemblyCost
  simp only [negativeOrderAntecedentDerivationCost]
  omega

theorem negativeOrderFinalCutFullAssemblyCost_le_envelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    negativeOrderFinalCutFullAssemblyCost left right <=
      32 + negativeOrderSequentCodeEnvelope termBound +
        negativeOrderFormulaCodeEnvelope termBound := by
  have hcontext := negativeOrderContext_subset_inventory left right
  have hseq := negativeOrderSequentCode_le
    left right termBound hleft hright
      (negativeOrderContext left right) hcontext
  have hselfMem := self_mem_negativeOrderInventory left right
  have hself := negativeOrderFormulaInventory_code_le
    left right termBound hleft hright
      (negativeOrderSelfAtom left) (List.mem_toFinset.mp hselfMem)
  have htag9 : (binaryNatCode 9).length <= 16 := by decide
  unfold negativeOrderFinalCutFullAssemblyCost
  omega

theorem negativeOrderTransImplication_payloadLength_le_primitive
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (negativeOrderTransImplication left right).payloadLength <=
      orderPrimitiveCostEnvelope termBound := by
  have himplication := ltTransImplication_payloadLength_le left right left
  have haxiom := ltTransAxiomProof_payloadLength_le
  have houter :=
    (fixedOrderFormulaCode_le_stage0 ltTransOuterBody
      (Or.inr (Or.inl rfl))).trans
      (orderFormulaStage_le_envelope orderFormulaStage0 termBound
        (Or.inl rfl))
  have hmiddle :=
    (ltTransMiddleBody_code_le_stage1 left termBound hleft).trans
      (orderFormulaStage_le_envelope (orderFormulaStage1 termBound)
        termBound (Or.inr (Or.inl rfl)))
  have hinner :=
    (ltTransInnerBody_code_le_stage2
      left right termBound hleft hright).trans
      (orderFormulaStage_le_envelope (orderFormulaStage2 termBound)
        termBound (Or.inr (Or.inr (Or.inl rfl))))
  have hfirst := specializationCost_le_orderEnvelope
    ltTransOuterBody left termBound houter hleft
  have hsecond := specializationCost_le_orderEnvelope
    (ltTransMiddleBody left) right termBound hmiddle hright
  have hthird := specializationCost_le_orderEnvelope
    (ltTransInnerBody left right) left termBound hinner hleft
  have hfixed :
      32 + 10 * axiomSyntaxBudget .ltTrans <=
        fixedPAOrderPayloadEnvelope := by
    unfold fixedPAOrderPayloadEnvelope
    omega
  have hcast :
      (negativeOrderTransImplication left right).payloadLength =
        (ltTransImplication left right left).payloadLength := by
    unfold negativeOrderTransImplication
    exact cast_payloadLength _ _
  rw [hcast]
  unfold orderPrimitiveCostEnvelope
  omega

def negativeOrderReversePrimitiveCostEnvelope (termBound : Nat) : Nat :=
  2 * orderPrimitiveCostEnvelope termBound +
    11 * negativeOrderSequentCodeEnvelope termBound +
    8 * negativeOrderFormulaCodeEnvelope termBound + 352

theorem proveNotLessThanOfReverseLessThan_payloadLength_le_primitive
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (reverseProof : CertifiedPAProof
      (negativeOrderReverseAtom left right))
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (proveNotLessThanOfReverseLessThan left right reverseProof).payloadLength <=
      reverseProof.payloadLength +
        negativeOrderReversePrimitiveCostEnvelope termBound := by
  let context := negativeOrderContext left right
  let antecedent := negativeOrderAntecedent left right
  let selfAtom := negativeOrderSelfAtom left
  let implication := antecedent 🡒 selfAtom
  let inventory := (negativeOrderFormulaInventory left right).toFinset
  have hraw := proveNotLessThanOfReverseLessThan_payloadLength_le
    left right reverseProof
  have himplication :=
    negativeOrderTransImplication_payloadLength_le_primitive
      left right termBound hleft hright
  have hcontext : context ⊆ inventory := by
    dsimp only [context, inventory]
    exact negativeOrderContext_subset_inventory left right
  have hantecedentMem : antecedent ∈ inventory := by
    dsimp only [antecedent, inventory]
    exact antecedent_mem_negativeOrderInventory left right
  have hselfMem : selfAtom ∈ inventory := by
    dsimp only [selfAtom, inventory]
    exact self_mem_negativeOrderInventory left right
  have himplicationMem : implication ∈ inventory := by
    dsimp only [implication, antecedent, selfAtom, inventory]
    exact implication_mem_negativeOrderInventory left right
  have hnegImplicationMem : (∼implication) ∈ inventory := by
    dsimp only [implication, antecedent, selfAtom, inventory]
    exact negatedImplication_mem_negativeOrderInventory left right
  have hnegSelfMem : (∼selfAtom) ∈ inventory := by
    dsimp only [selfAtom, inventory]
    exact negatedSelf_mem_negativeOrderInventory left right
  have hweakImplication := negativeOrderWeakeningCost_le_envelope
    left right termBound hleft hright (insert implication context)
    (Finset.insert_subset himplicationMem hcontext)
  have hantecedentCost :=
    negativeOrderAntecedentFullAssemblyCost_le_envelope
      left right termBound hleft hright
  have hmp := negativeOrderContextualModusPonensCost_le_envelope
    left right termBound hleft hright context antecedent selfAtom
    hcontext hantecedentMem hselfMem himplicationMem
    hnegImplicationMem hnegSelfMem
  have hirreflexivityRaw := proveLtIrrefl_payloadLength_le left
  have hirreflexivityEnvelope :=
    ltIrreflFullPayloadBound_le_primitive left termBound hleft
  have hirreflexivity : (proveLtIrrefl left).payloadLength <=
      orderPrimitiveCostEnvelope termBound :=
    hirreflexivityRaw.trans hirreflexivityEnvelope
  have hweakIrreflexivity := negativeOrderWeakeningCost_le_envelope
    left right termBound hleft hright (insert (∼selfAtom) context)
    (Finset.insert_subset hnegSelfMem hcontext)
  have hfinal := negativeOrderFinalCutFullAssemblyCost_le_envelope
    left right termBound hleft hright
  change weakeningFullAssemblyCost
      (insert
        (negativeOrderAntecedent left right 🡒 negativeOrderSelfAtom left)
        (negativeOrderContext left right)) <=
      negativeOrderSequentCodeEnvelope termBound + 32 at hweakImplication
  change contextualModusPonensFullAssemblyCost
      (negativeOrderContext left right)
      (negativeOrderAntecedent left right)
      (negativeOrderSelfAtom left) <=
      160 + 5 * negativeOrderSequentCodeEnvelope termBound +
        4 * negativeOrderFormulaCodeEnvelope termBound at hmp
  change weakeningFullAssemblyCost
      (insert (∼negativeOrderSelfAtom left)
        (negativeOrderContext left right)) <=
      negativeOrderSequentCodeEnvelope termBound + 32 at hweakIrreflexivity
  calc
    (proveNotLessThanOfReverseLessThan left right reverseProof).payloadLength <=
        proveNotLessThanOfReverseLessThanPayloadBound
          left right reverseProof.payloadLength := hraw
    _ <= reverseProof.payloadLength +
        negativeOrderReversePrimitiveCostEnvelope termBound := by
      dsimp only [proveNotLessThanOfReverseLessThanPayloadBound]
      unfold negativeOrderReversePrimitiveCostEnvelope
      omega

theorem negativeOrderEqualityModusTollensSyntaxBudget_le_envelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    modusTollensSyntaxBudget
        (negativeOrderForwardAtom left right)
        (negativeOrderSelfAtom right) <=
      7 * negativeOrderFormulaCodeEnvelope termBound := by
  let antecedent := negativeOrderForwardAtom left right
  let consequent := negativeOrderSelfAtom right
  let atomicBound := orderAtomicFormulaCodeEnvelope termBound
  let formulaBound := negativeOrderFormulaCodeEnvelope termBound
  have hantecedent :
      (binaryFormulaCode antecedent).length <= atomicBound := by
    dsimp only [antecedent, atomicBound, negativeOrderForwardAtom]
    exact lessThanFormula_code_le_orderAtomic
      left right termBound hleft hright
  have hconsequent :
      (binaryFormulaCode consequent).length <= atomicBound := by
    dsimp only [consequent, atomicBound, negativeOrderSelfAtom]
    exact lessThanFormula_code_le_orderAtomic
      right right termBound hright hright
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
    dsimp only [formulaBound, negativeOrderFormulaCodeEnvelope]
    omega
  have hconsequentEnvelope :
      (binaryFormulaCode consequent).length <= formulaBound := by
    dsimp only [formulaBound, negativeOrderFormulaCodeEnvelope]
    omega
  have himplicationEnvelope :
      (binaryFormulaCode (antecedent 🡒 consequent)).length <=
        formulaBound := by
    exact himplicationTight.trans (by
      dsimp only [formulaBound, negativeOrderFormulaCodeEnvelope]
      omega)
  have hnegImplicationEnvelope :
      (binaryFormulaCode (∼(antecedent 🡒 consequent))).length <=
        formulaBound := by
    dsimp only [formulaBound, negativeOrderFormulaCodeEnvelope]
    omega
  have hnegConsequentEnvelope :
      (binaryFormulaCode (∼consequent)).length <= formulaBound := by
    dsimp only [formulaBound, negativeOrderFormulaCodeEnvelope]
    omega
  have hnegAntecedentEnvelope :
      (binaryFormulaCode (∼antecedent)).length <= formulaBound := by
    dsimp only [formulaBound, negativeOrderFormulaCodeEnvelope]
    omega
  have hconjunctionEnvelope :
      (binaryFormulaCode (antecedent ⋏ (∼consequent))).length <=
        formulaBound := by
    dsimp only [formulaBound, negativeOrderFormulaCodeEnvelope]
    omega
  unfold modusTollensSyntaxBudget
  dsimp only [antecedent, consequent] at *
  omega

def negativeOrderEqualityPrimitiveCostEnvelope (termBound : Nat) : Nat :=
  paPrimitiveCostEnvelope termBound +
    2 * orderPrimitiveCostEnvelope termBound + 272 +
    336 * negativeOrderFormulaCodeEnvelope termBound

theorem proveNotLessThanOfEquality_payloadLength_le_primitive
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (equalityProof : CertifiedPAProof
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition))
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (proveNotLessThanOfEquality left right equalityProof).payloadLength <=
      equalityProof.payloadLength +
        negativeOrderEqualityPrimitiveCostEnvelope termBound := by
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
  have hreflexivity :=
    proveEqualityReflexivityAtTerm_payloadLength_le_primitive
      right termBound hright
  change reflexivity.payloadLength <=
    paPrimitiveCostEnvelope termBound at hreflexivity
  have htransportRaw :=
    proveBinaryRelationTransportImplication_full_payloadLength_le
      Language.ORing.Rel.lt left right right right
      equalityProof reflexivity
  change transportRaw.payloadLength <=
    binaryRelationTransportFullPayloadBound Language.ORing.Rel.lt
      left right right right equalityProof.payloadLength
      reflexivity.payloadLength at htransportRaw
  have htransportEnvelope :=
    binaryRelationTransportFullPayloadBound_le_primitive
      left right right right equalityProof.payloadLength
      reflexivity.payloadLength termBound hleft hright hright hright
  have htransportCast :
      transport.payloadLength = transportRaw.payloadLength := by
    dsimp only [transport]
    exact cast_payloadLength _ _
  have htransport : transport.payloadLength <=
      equalityProof.payloadLength + paPrimitiveCostEnvelope termBound +
        orderPrimitiveCostEnvelope termBound := by
    rw [htransportCast]
    calc
      transportRaw.payloadLength <=
          binaryRelationTransportFullPayloadBound
            Language.ORing.Rel.lt left right right right
            equalityProof.payloadLength reflexivity.payloadLength :=
        htransportRaw
      _ <= equalityProof.payloadLength + reflexivity.payloadLength +
          orderPrimitiveCostEnvelope termBound := htransportEnvelope
      _ <= equalityProof.payloadLength +
          paPrimitiveCostEnvelope termBound +
          orderPrimitiveCostEnvelope termBound := by omega
  have hirreflexivityRaw := proveLtIrrefl_payloadLength_le right
  have hirreflexivityEnvelope :=
    ltIrreflFullPayloadBound_le_primitive right termBound hright
  have hirreflexivity : (proveLtIrrefl right).payloadLength <=
      orderPrimitiveCostEnvelope termBound := by
    exact hirreflexivityRaw.trans hirreflexivityEnvelope
  have hsyntax :=
    negativeOrderEqualityModusTollensSyntaxBudget_le_envelope
      left right termBound hleft hright
  have hraw := modusTollens_payloadLength_le transport (proveLtIrrefl right)
  have hfinal :
      (modusTollens transport (proveLtIrrefl right)).payloadLength <=
      equalityProof.payloadLength +
        negativeOrderEqualityPrimitiveCostEnvelope termBound := by
    calc
      (modusTollens transport (proveLtIrrefl right)).payloadLength <=
          transport.payloadLength +
            (proveLtIrrefl right).payloadLength + 272 +
            48 * modusTollensSyntaxBudget
              (negativeOrderForwardAtom left right)
              (negativeOrderSelfAtom right) := hraw
      _ <= transport.payloadLength +
          orderPrimitiveCostEnvelope termBound + 272 +
          48 * modusTollensSyntaxBudget
            (negativeOrderForwardAtom left right)
            (negativeOrderSelfAtom right) := by
        gcongr
      _ <= transport.payloadLength +
          orderPrimitiveCostEnvelope termBound + 272 +
          336 * negativeOrderFormulaCodeEnvelope termBound := by
        omega
      _ <= equalityProof.payloadLength +
          paPrimitiveCostEnvelope termBound +
          2 * orderPrimitiveCostEnvelope termBound + 272 +
          336 * negativeOrderFormulaCodeEnvelope termBound := by
        omega
      _ = equalityProof.payloadLength +
          negativeOrderEqualityPrimitiveCostEnvelope termBound := by
        unfold negativeOrderEqualityPrimitiveCostEnvelope
        ring
  simpa only [proveNotLessThanOfEquality] using hfinal

#print axioms negativeOrderFormulaInventory_code_le
#print axioms negativeOrderSequentCode_le
#print axioms proveNotLessThanOfReverseLessThan_payloadLength_le_primitive
#print axioms proveNotLessThanOfEquality_payloadLength_le_primitive

end FoundationCompactPANegativeOrderBounds
