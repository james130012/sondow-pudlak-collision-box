import integration.FoundationCompactPABoundedUniversalCompilerBounds
import integration.FoundationCompactPANegativeEqualityBounds

/-!
# Uniform bounds for small-context proof constructors

Every constructor used by the bounded-formula compiler has only a fixed
number of local formulas and sequents.  This file charges those constructors
to one honest formula-code coordinate.  It contains no proof object or proof
length as input.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAContextCostPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPANegativeEqualityBounds
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens

def FormulaCodeBound
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (resource : Nat) : Prop :=
  forall formula, formula ∈ Gamma →
    (binaryFormulaCode formula).length <= resource

theorem FormulaCodeBound.insert
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {formula : LO.FirstOrder.ArithmeticProposition}
    {resource : Nat}
    (hformula : (binaryFormulaCode formula).length <= resource)
    (hGamma : FormulaCodeBound Gamma resource) :
    FormulaCodeBound (insert formula Gamma) resource := by
  intro candidate hcandidate
  simp only [Finset.mem_insert] at hcandidate
  rcases hcandidate with hcandidate | hcandidate
  · simpa [hcandidate] using hformula
  · exact hGamma candidate hcandidate

def smallSequentCodeEnvelope (resource : Nat) : Nat :=
  (binaryNatCode 8).length + 8 * resource

theorem binarySequentCode_length_le_small
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (hcard : Gamma.card <= 8)
    (hGamma : FormulaCodeBound Gamma resource) :
    (binarySequentCode Gamma).length <=
      smallSequentCodeEnvelope resource := by
  exact binarySequentCode_length_le_uniform
    Gamma 8 resource hcard hGamma

def smallContextAssemblyEnvelope (resource : Nat) : Nat :=
  2048 + 32 * smallSequentCodeEnvelope resource + 32 * resource

theorem weakeningFullAssemblyCost_le_small
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (hcard : Gamma.card <= 8)
    (hGamma : FormulaCodeBound Gamma resource) :
    weakeningFullAssemblyCost Gamma <=
      smallContextAssemblyEnvelope resource := by
  have hsequent := binarySequentCode_length_le_small
    Gamma resource hcard hGamma
  have htag : (binaryNatCode 7).length <= 32 := by decide
  unfold weakeningFullAssemblyCost smallContextAssemblyEnvelope
  omega

theorem assumptionFullPayloadCost_le_small
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (hcard : Gamma.card <= 4)
    (hGamma : FormulaCodeBound Gamma resource)
    (hformula : (binaryFormulaCode formula).length <= resource) :
    assumptionFullPayloadCost Gamma formula <=
      smallContextAssemblyEnvelope resource := by
  have hinsertBound := hGamma.insert hformula
  have hinsertCard : (insert formula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le formula Gamma
    omega
  have hsequent := binarySequentCode_length_le_small
    _ resource hinsertCard hinsertBound
  have htag : (binaryNatCode 0).length <= 32 := by decide
  unfold assumptionFullPayloadCost smallContextAssemblyEnvelope
  omega

theorem contextualModusPonensFullAssemblyCost_le_small
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (hcard : Gamma.card <= 4)
    (hGamma : FormulaCodeBound Gamma resource)
    (hantecedent : (binaryFormulaCode antecedent).length <= resource)
    (hconsequent : (binaryFormulaCode consequent).length <= resource)
    (himplication :
      (binaryFormulaCode (antecedent 🡒 consequent)).length <= resource)
    (hnegatedImplication :
      (binaryFormulaCode (∼(antecedent 🡒 consequent))).length <= resource)
    (hnegatedConsequent :
      (binaryFormulaCode (∼consequent)).length <= resource) :
    contextualModusPonensFullAssemblyCost Gamma antecedent consequent <=
      smallContextAssemblyEnvelope resource := by
  let implication := antecedent 🡒 consequent
  let negatedImplication := ∼implication
  let negatedConsequent := ∼consequent
  have hconsequentContext := hGamma.insert hconsequent
  have himplicationContext := hconsequentContext.insert himplication
  have hnegatedImplicationContext :=
    hconsequentContext.insert hnegatedImplication
  have hantecedentContext := hnegatedImplicationContext.insert hantecedent
  have hnegatedConsequentContext :=
    hnegatedImplicationContext.insert hnegatedConsequent
  have hcard1 : (insert consequent Gamma).card <= 8 := by
    have := Finset.card_insert_le consequent Gamma
    omega
  have hcard2 : (insert implication (insert consequent Gamma)).card <= 8 := by
    have hfirst := Finset.card_insert_le consequent Gamma
    have hsecond := Finset.card_insert_le implication (insert consequent Gamma)
    omega
  have hcard3 :
      (insert negatedImplication (insert consequent Gamma)).card <= 8 := by
    have hfirst := Finset.card_insert_le consequent Gamma
    have hsecond := Finset.card_insert_le negatedImplication
      (insert consequent Gamma)
    omega
  have hcard4 :
      (insert antecedent
        (insert negatedImplication (insert consequent Gamma))).card <= 8 := by
    have hfirst := Finset.card_insert_le consequent Gamma
    have hsecond := Finset.card_insert_le negatedImplication
      (insert consequent Gamma)
    have hthird := Finset.card_insert_le antecedent
      (insert negatedImplication (insert consequent Gamma))
    omega
  have hcard5 :
      (insert negatedConsequent
        (insert negatedImplication (insert consequent Gamma))).card <= 8 := by
    have hfirst := Finset.card_insert_le consequent Gamma
    have hsecond := Finset.card_insert_le negatedImplication
      (insert consequent Gamma)
    have hthird := Finset.card_insert_le negatedConsequent
      (insert negatedImplication (insert consequent Gamma))
    omega
  have hseq1 := binarySequentCode_length_le_small
    _ resource hcard1 hconsequentContext
  have hseq2 := binarySequentCode_length_le_small
    _ resource hcard2 himplicationContext
  have hseq3 := binarySequentCode_length_le_small
    _ resource hcard3 hnegatedImplicationContext
  have hseq4 := binarySequentCode_length_le_small
    _ resource hcard4 hantecedentContext
  have hseq5 := binarySequentCode_length_le_small
    _ resource hcard5 hnegatedConsequentContext
  have htag0 : (binaryNatCode 0).length <= 32 := by decide
  have htag3 : (binaryNatCode 3).length <= 32 := by decide
  have htag7 : (binaryNatCode 7).length <= 32 := by decide
  have htag9 : (binaryNatCode 9).length <= 32 := by decide
  unfold contextualModusPonensFullAssemblyCost
    contextualModusPonensDerivationCost smallContextAssemblyEnvelope
  dsimp only [implication, negatedImplication, negatedConsequent] at *
  omega

theorem modusTollensFullAssemblyCost_le_small
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (hcard : Gamma.card <= 4)
    (hGamma : FormulaCodeBound Gamma resource)
    (hantecedent : (binaryFormulaCode antecedent).length <= resource)
    (hconsequent : (binaryFormulaCode consequent).length <= resource)
    (himplication :
      (binaryFormulaCode (antecedent 🡒 consequent)).length <= resource)
    (hnegatedImplication :
      (binaryFormulaCode (∼(antecedent 🡒 consequent))).length <= resource)
    (hnegatedAntecedent :
      (binaryFormulaCode (∼antecedent)).length <= resource)
    (hnegatedConsequent :
      (binaryFormulaCode (∼consequent)).length <= resource) :
    modusTollensFullAssemblyCost Gamma antecedent consequent <=
      smallContextAssemblyEnvelope resource := by
  let implication := antecedent 🡒 consequent
  let negatedImplication := ∼implication
  let negatedAntecedent := ∼antecedent
  let negatedConsequent := ∼consequent
  have hroot := hGamma.insert hnegatedAntecedent
  have himplicationContext := hroot.insert himplication
  have hnegatedImplicationContext := hroot.insert hnegatedImplication
  have hantecedentContext := hnegatedImplicationContext.insert hantecedent
  have hnegatedConsequentContext :=
    hnegatedImplicationContext.insert hnegatedConsequent
  have hcard1 : (insert negatedAntecedent Gamma).card <= 8 := by
    have := Finset.card_insert_le negatedAntecedent Gamma
    omega
  have hcard2 :
      (insert implication (insert negatedAntecedent Gamma)).card <= 8 := by
    have hfirst := Finset.card_insert_le negatedAntecedent Gamma
    have hsecond := Finset.card_insert_le implication
      (insert negatedAntecedent Gamma)
    omega
  have hcard3 :
      (insert negatedImplication
        (insert negatedAntecedent Gamma)).card <= 8 := by
    have hfirst := Finset.card_insert_le negatedAntecedent Gamma
    have hsecond := Finset.card_insert_le negatedImplication
      (insert negatedAntecedent Gamma)
    omega
  have hcard4 :
      (insert antecedent
        (insert negatedImplication
          (insert negatedAntecedent Gamma))).card <= 8 := by
    have hfirst := Finset.card_insert_le negatedAntecedent Gamma
    have hsecond := Finset.card_insert_le negatedImplication
      (insert negatedAntecedent Gamma)
    have hthird := Finset.card_insert_le antecedent
      (insert negatedImplication (insert negatedAntecedent Gamma))
    omega
  have hcard5 :
      (insert negatedConsequent
        (insert negatedImplication
          (insert negatedAntecedent Gamma))).card <= 8 := by
    have hfirst := Finset.card_insert_le negatedAntecedent Gamma
    have hsecond := Finset.card_insert_le negatedImplication
      (insert negatedAntecedent Gamma)
    have hthird := Finset.card_insert_le negatedConsequent
      (insert negatedImplication (insert negatedAntecedent Gamma))
    omega
  have hseq1 := binarySequentCode_length_le_small
    _ resource hcard1 hroot
  have hseq2 := binarySequentCode_length_le_small
    _ resource hcard2 himplicationContext
  have hseq3 := binarySequentCode_length_le_small
    _ resource hcard3 hnegatedImplicationContext
  have hseq4 := binarySequentCode_length_le_small
    _ resource hcard4 hantecedentContext
  have hseq5 := binarySequentCode_length_le_small
    _ resource hcard5 hnegatedConsequentContext
  have htag0 : (binaryNatCode 0).length <= 32 := by decide
  have htag3 : (binaryNatCode 3).length <= 32 := by decide
  have htag7 : (binaryNatCode 7).length <= 32 := by decide
  have htag9 : (binaryNatCode 9).length <= 32 := by decide
  unfold modusTollensFullAssemblyCost modusTollensDerivationCost
    smallContextAssemblyEnvelope
  dsimp only [implication, negatedImplication, negatedAntecedent,
    negatedConsequent] at *
  omega

theorem conjunctionFullAssemblyCost_le_small
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (left right : LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (hcard : Gamma.card <= 4)
    (hGamma : FormulaCodeBound Gamma resource)
    (hleft : (binaryFormulaCode left).length <= resource)
    (hright : (binaryFormulaCode right).length <= resource)
    (hconjunction : (binaryFormulaCode (left ⋏ right)).length <= resource) :
    conjunctionFullAssemblyCost Gamma left right <=
      smallContextAssemblyEnvelope resource := by
  have hrootBound := hGamma.insert hconjunction
  have hleftBound := hrootBound.insert hleft
  have hrightBound := hrootBound.insert hright
  have hrootCard : (insert (left ⋏ right) Gamma).card <= 8 := by
    have := Finset.card_insert_le (left ⋏ right) Gamma
    omega
  have hleftCard : (insert left (insert (left ⋏ right) Gamma)).card <= 8 := by
    have hfirst := Finset.card_insert_le (left ⋏ right) Gamma
    have hsecond := Finset.card_insert_le left (insert (left ⋏ right) Gamma)
    omega
  have hrightCard : (insert right (insert (left ⋏ right) Gamma)).card <= 8 := by
    have hfirst := Finset.card_insert_le (left ⋏ right) Gamma
    have hsecond := Finset.card_insert_le right (insert (left ⋏ right) Gamma)
    omega
  have hrootSequent := binarySequentCode_length_le_small
    _ resource hrootCard hrootBound
  have hleftSequent := binarySequentCode_length_le_small
    _ resource hleftCard hleftBound
  have hrightSequent := binarySequentCode_length_le_small
    _ resource hrightCard hrightBound
  have htag3 : (binaryNatCode 3).length <= 32 := by decide
  have htag7 : (binaryNatCode 7).length <= 32 := by decide
  unfold conjunctionFullAssemblyCost conjunctionDerivationCost
    smallContextAssemblyEnvelope
  dsimp only
  omega

theorem disjunctionFullAssemblyCost_le_small
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (left right : LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (hcard : Gamma.card <= 4)
    (hGamma : FormulaCodeBound Gamma resource)
    (hleft : (binaryFormulaCode left).length <= resource)
    (hright : (binaryFormulaCode right).length <= resource)
    (hdisjunction : (binaryFormulaCode (left ⋎ right)).length <= resource) :
    disjunctionFullAssemblyCost Gamma left right <=
      smallContextAssemblyEnvelope resource := by
  have hrootBound := hGamma.insert hdisjunction
  have hbothBound := (hrootBound.insert hright).insert hleft
  have hrootCard : (insert (left ⋎ right) Gamma).card <= 8 := by
    have := Finset.card_insert_le (left ⋎ right) Gamma
    omega
  have hbothCard :
      (insert left (insert right (insert (left ⋎ right) Gamma))).card <= 8 := by
    have hfirst := Finset.card_insert_le (left ⋎ right) Gamma
    have hsecond := Finset.card_insert_le right (insert (left ⋎ right) Gamma)
    have hthird := Finset.card_insert_le left
      (insert right (insert (left ⋎ right) Gamma))
    omega
  have hrootSequent := binarySequentCode_length_le_small
    _ resource hrootCard hrootBound
  have hbothSequent := binarySequentCode_length_le_small
    _ resource hbothCard hbothBound
  have htag4 : (binaryNatCode 4).length <= 32 := by decide
  have htag7 : (binaryNatCode 7).length <= 32 := by decide
  unfold disjunctionFullAssemblyCost disjunctionDerivationCost
    smallContextAssemblyEnvelope
  dsimp only
  omega

theorem existsIntroFullAssemblyCost_le_small
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (resource : Nat)
    (hcard : Gamma.card <= 4)
    (hGamma : FormulaCodeBound Gamma resource)
    (hformula : (binaryFormulaCode formula).length <= resource)
    (hwitness : (binaryTermCode witness).length <= resource)
    (hinstance : (binaryFormulaCode (formula/[witness])).length <= resource)
    (hexistential :
      (binaryFormulaCode
        (∃⁰ formula : LO.FirstOrder.ArithmeticProposition)).length <= resource) :
    existsIntroFullAssemblyCost Gamma formula witness <=
      smallContextAssemblyEnvelope resource := by
  have hrootBound := hGamma.insert hexistential
  have hinstanceBound := hrootBound.insert hinstance
  have hrootCard :
      (insert (∃⁰ formula : LO.FirstOrder.ArithmeticProposition) Gamma).card <= 8 := by
    have := Finset.card_insert_le
      (∃⁰ formula : LO.FirstOrder.ArithmeticProposition) Gamma
    omega
  have hinstanceCard :
      (insert (formula/[witness])
        (insert (∃⁰ formula : LO.FirstOrder.ArithmeticProposition) Gamma)).card <= 8 := by
    have hfirst := Finset.card_insert_le
      (∃⁰ formula : LO.FirstOrder.ArithmeticProposition) Gamma
    have hsecond := Finset.card_insert_le (formula/[witness])
      (insert (∃⁰ formula : LO.FirstOrder.ArithmeticProposition) Gamma)
    omega
  have hrootSequent := binarySequentCode_length_le_small
    _ resource hrootCard hrootBound
  have hinstanceSequent := binarySequentCode_length_le_small
    _ resource hinstanceCard hinstanceBound
  have htag6 : (binaryNatCode 6).length <= 32 := by decide
  have htag7 : (binaryNatCode 7).length <= 32 := by decide
  unfold existsIntroFullAssemblyCost existsIntroDerivationCost
    smallContextAssemblyEnvelope
  dsimp only
  omega

theorem exFalsoAssumptionFullPayloadCost_le_small
    (target : LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (htarget : (binaryFormulaCode target).length <= resource)
    (hfalse :
      (binaryFormulaCode
        (∼(⊥ : LO.FirstOrder.ArithmeticProposition))).length <= resource) :
    CertifiedPAContextProof.exFalsoAssumptionFullPayloadCost target <=
      smallContextAssemblyEnvelope resource := by
  let Gamma : Finset LO.FirstOrder.ArithmeticProposition :=
    insert target {∼(⊥ : LO.FirstOrder.ArithmeticProposition)}
  have hGamma : FormulaCodeBound Gamma resource := by
    intro formula hformula
    simp only [Gamma, Finset.mem_insert, Finset.mem_singleton] at hformula
    rcases hformula with rfl | rfl
    · exact htarget
    · exact hfalse
  have hcard : Gamma.card <= 8 := by
    dsimp only [Gamma]
    have hbase :
        ({∼(⊥ : LO.FirstOrder.ArithmeticProposition)} :
          Finset LO.FirstOrder.ArithmeticProposition).card <= 1 := by
      simp
    have hfirst := Finset.card_insert_le target
      ({∼(⊥ : LO.FirstOrder.ArithmeticProposition)} :
        Finset LO.FirstOrder.ArithmeticProposition)
    omega
  have hsequent := binarySequentCode_length_le_small
    Gamma resource hcard hGamma
  have htagZero : (binaryNatCode 0).length <= 32 := by decide
  have htagTwo : (binaryNatCode 2).length <= 32 := by decide
  unfold CertifiedPAContextProof.exFalsoAssumptionFullPayloadCost
    smallContextAssemblyEnvelope
  dsimp only [Gamma] at hsequent
  omega

theorem eliminateDisjunctionAssumptionFullAssemblyCost_le_small
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (target left right : LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (hcard : Gamma.card <= 4)
    (hGamma : FormulaCodeBound Gamma resource)
    (htarget : (binaryFormulaCode target).length <= resource)
    (hnegatedLeft : (binaryFormulaCode (∼left)).length <= resource)
    (hnegatedRight : (binaryFormulaCode (∼right)).length <= resource)
    (hnegatedDisjunction :
      (binaryFormulaCode (∼(left ⋎ right))).length <= resource) :
    CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
        Gamma target left right <= smallContextAssemblyEnvelope resource := by
  let rootContext := insert target (insert (∼(left ⋎ right)) Gamma)
  let leftContext := insert (∼left) rootContext
  let rightContext := insert (∼right) rootContext
  have hrootBound := (hGamma.insert hnegatedDisjunction).insert htarget
  have hleftBound := hrootBound.insert hnegatedLeft
  have hrightBound := hrootBound.insert hnegatedRight
  have hrootCardTight : rootContext.card <= 6 := by
    have hfirst := Finset.card_insert_le (∼(left ⋎ right)) Gamma
    have hsecond := Finset.card_insert_le target
      (insert (∼(left ⋎ right)) Gamma)
    dsimp only [rootContext]
    omega
  have hrootCard : rootContext.card <= 8 := hrootCardTight.trans (by omega)
  have hleftCard : leftContext.card <= 8 := by
    have hstep := Finset.card_insert_le (∼left) rootContext
    dsimp only [leftContext]
    omega
  have hrightCard : rightContext.card <= 8 := by
    have hstep := Finset.card_insert_le (∼right) rootContext
    dsimp only [rightContext]
    omega
  have hrootSequent := binarySequentCode_length_le_small
    rootContext resource hrootCard hrootBound
  have hleftSequent := binarySequentCode_length_le_small
    leftContext resource hleftCard hleftBound
  have hrightSequent := binarySequentCode_length_le_small
    rightContext resource hrightCard hrightBound
  have htagThree : (binaryNatCode 3).length <= 32 := by decide
  have htagSeven : (binaryNatCode 7).length <= 32 := by decide
  unfold CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
    CertifiedPAContextProof.eliminateDisjunctionAssumptionDerivationCost
    smallContextAssemblyEnvelope
  dsimp only [rootContext, leftContext, rightContext] at *
  omega

theorem dischargeFullAssemblyCost_le_small
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (hantecedent : (binaryFormulaCode antecedent).length <= resource)
    (hconsequent : (binaryFormulaCode consequent).length <= resource)
    (himplication :
      (binaryFormulaCode (antecedent 🡒 consequent)).length <= resource)
    (hnegatedAntecedent :
      (binaryFormulaCode (∼antecedent)).length <= resource) :
    CertifiedPAContextProof.dischargeFullAssemblyCost antecedent consequent <=
      smallContextAssemblyEnvelope resource := by
  let implication := antecedent 🡒 consequent
  let rootContext : Finset LO.FirstOrder.ArithmeticProposition :=
    {implication}
  let premiseContext : Finset LO.FirstOrder.ArithmeticProposition :=
    insert (∼antecedent) (insert consequent rootContext)
  have hrootBound : FormulaCodeBound rootContext resource := by
    intro formula hformula
    simp only [rootContext, Finset.mem_singleton] at hformula
    subst formula
    simpa only [implication] using himplication
  have hpremiseBound : FormulaCodeBound premiseContext resource := by
    exact (hrootBound.insert hconsequent).insert hnegatedAntecedent
  have hrootCardTight : rootContext.card <= 1 := by
    dsimp only [rootContext]
    simp
  have hrootCard : rootContext.card <= 8 := hrootCardTight.trans (by omega)
  have hpremiseCard : premiseContext.card <= 8 := by
    have hfirst := Finset.card_insert_le consequent rootContext
    have hsecond := Finset.card_insert_le (∼antecedent)
      (insert consequent rootContext)
    dsimp only [premiseContext]
    omega
  have hrootSequent := binarySequentCode_length_le_small
    rootContext resource hrootCard hrootBound
  have hpremiseSequent := binarySequentCode_length_le_small
    premiseContext resource hpremiseCard hpremiseBound
  have htag4 : (binaryNatCode 4).length <= 32 := by decide
  have htag7 : (binaryNatCode 7).length <= 32 := by decide
  unfold CertifiedPAContextProof.dischargeFullAssemblyCost
    CertifiedPAContextProof.dischargeDerivationCost
    smallContextAssemblyEnvelope
  dsimp only [implication, rootContext, premiseContext] at hrootSequent hpremiseSequent
  dsimp only
  omega

#print axioms binarySequentCode_length_le_small
#print axioms weakeningFullAssemblyCost_le_small
#print axioms assumptionFullPayloadCost_le_small
#print axioms contextualModusPonensFullAssemblyCost_le_small
#print axioms modusTollensFullAssemblyCost_le_small
#print axioms conjunctionFullAssemblyCost_le_small
#print axioms disjunctionFullAssemblyCost_le_small
#print axioms existsIntroFullAssemblyCost_le_small
#print axioms exFalsoAssumptionFullPayloadCost_le_small
#print axioms eliminateDisjunctionAssumptionFullAssemblyCost_le_small
#print axioms dischargeFullAssemblyCost_le_small

end FoundationCompactPAContextCostPolynomialBounds
