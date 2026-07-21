import integration.FoundationCompactPAQuantitativeOrder

/-!
# Polynomial envelopes for the certified PA order compiler

This file compresses the exact structural bounds from the order compiler into
uniform expressions depending only on a public binary-width budget.  The
envelopes contain syntax-code and rule-assembly costs, never an assumed proof
length or an external order certificate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAQuantitativeOrderBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAAxiomCertificate
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactCertifiedModusPonens
open FoundationCompactCertifiedConjunction
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABinaryNumeralMultiplication
open FoundationCompactPABinaryNumeralMultiplicationBounds
open FoundationCompactPAQuantitativeOrder

/-! ## Fixed order formulas and four-stage specialization envelope -/

def fixedPAOrderFormulaSeed : Nat :=
  fixedPAFormulaSeed +
    (binaryFormulaCode addLtAddOuterBody).length +
    (binaryFormulaCode ltTransOuterBody).length +
    (binaryFormulaCode
      (binaryRelationExtOuterBody Language.ORing.Rel.lt)).length +
    (binaryFormulaCode mulLtMulOuterBody).length +
    (binaryFormulaCode ltIrreflBody).length + 1

def orderFormulaStage0 : Nat := fixedPAOrderFormulaSeed

def orderFormulaStage1 (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope orderFormulaStage0 termBound

def orderFormulaStage2 (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope (orderFormulaStage1 termBound) termBound

def orderFormulaStage3 (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope (orderFormulaStage2 termBound) termBound

def orderFormulaStage4 (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope (orderFormulaStage3 termBound) termBound

def orderFormulaCodeEnvelope (termBound : Nat) : Nat :=
  orderFormulaStage0 + orderFormulaStage1 termBound +
    orderFormulaStage2 termBound + orderFormulaStage3 termBound +
    orderFormulaStage4 termBound + 1

def orderSpecializationScaleEnvelope (termBound : Nat) : Nat :=
  orderFormulaCodeEnvelope termBound + termBound + 1

def orderSpecializationCostEnvelope (termBound : Nat) : Nat :=
  192 + 2048 * orderSpecializationScaleEnvelope termBound *
    orderSpecializationScaleEnvelope termBound *
    orderSpecializationScaleEnvelope termBound

theorem fixedOrderFormulaCode_le_stage0
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hfixed : formula = addLtAddOuterBody ∨
      formula = ltTransOuterBody ∨
      formula = binaryRelationExtOuterBody Language.ORing.Rel.lt ∨
      formula = mulLtMulOuterBody ∨
      formula = ltIrreflBody) :
    (binaryFormulaCode formula).length <= orderFormulaStage0 := by
  rcases hfixed with h | h | h | h | h <;> subst formula <;>
    unfold orderFormulaStage0 fixedPAOrderFormulaSeed <;> omega

theorem orderFormulaStage_le_envelope
    (stage termBound : Nat)
    (hstage : stage = orderFormulaStage0 ∨
      stage = orderFormulaStage1 termBound ∨
      stage = orderFormulaStage2 termBound ∨
      stage = orderFormulaStage3 termBound ∨
      stage = orderFormulaStage4 termBound) :
    stage <= orderFormulaCodeEnvelope termBound := by
  rcases hstage with h | h | h | h | h <;> subst stage <;>
    unfold orderFormulaCodeEnvelope <;> omega

theorem instantiatedUniversalBody_code_le_next
    (outer body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (formulaBound termBound : Nat)
    (houter : (binaryFormulaCode outer).length <= formulaBound)
    (hwitness : (binaryTermCode witness).length <= termBound)
    (hformula : outer/[witness] = ∀⁰ body) :
    (binaryFormulaCode body).length <=
      substitutionFormulaCodeEnvelope formulaBound termBound := by
  have hsub := binaryFormulaCode_substitution_one_length_le_envelope
    outer witness formulaBound termBound houter hwitness
  rw [hformula] at hsub
  exact (binaryFormulaCode_all_body_le body).trans hsub

theorem addLtAddMiddleBody_code_le_stage1
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound) :
    (binaryFormulaCode (addLtAddMiddleBody left)).length <=
      orderFormulaStage1 termBound := by
  exact instantiatedUniversalBody_code_le_next
    addLtAddOuterBody (addLtAddMiddleBody left) left
    orderFormulaStage0 termBound
    (fixedOrderFormulaCode_le_stage0 addLtAddOuterBody (Or.inl rfl))
    hleft (addLtAddAfterFirst_formula left)

theorem addLtAddInnerBody_code_le_stage2
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (binaryFormulaCode (addLtAddInnerBody left right)).length <=
      orderFormulaStage2 termBound := by
  exact instantiatedUniversalBody_code_le_next
    (addLtAddMiddleBody left) (addLtAddInnerBody left right) right
    (orderFormulaStage1 termBound) termBound
    (addLtAddMiddleBody_code_le_stage1 left termBound hleft)
    hright (addLtAddAfterSecond_formula left right)

theorem mulLtMulMiddleBody_code_le_stage1
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound) :
    (binaryFormulaCode (mulLtMulMiddleBody left)).length <=
      orderFormulaStage1 termBound := by
  exact instantiatedUniversalBody_code_le_next
    mulLtMulOuterBody (mulLtMulMiddleBody left) left
    orderFormulaStage0 termBound
    (fixedOrderFormulaCode_le_stage0 mulLtMulOuterBody
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    hleft (mulLtMulAfterFirst_formula left)

theorem mulLtMulInnerBody_code_le_stage2
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (binaryFormulaCode (mulLtMulInnerBody left right)).length <=
      orderFormulaStage2 termBound := by
  exact instantiatedUniversalBody_code_le_next
    (mulLtMulMiddleBody left) (mulLtMulInnerBody left right) right
    (orderFormulaStage1 termBound) termBound
    (mulLtMulMiddleBody_code_le_stage1 left termBound hleft)
    hright (mulLtMulAfterSecond_formula left right)

theorem ltTransMiddleBody_code_le_stage1
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound) :
    (binaryFormulaCode (ltTransMiddleBody left)).length <=
      orderFormulaStage1 termBound := by
  exact instantiatedUniversalBody_code_le_next
    ltTransOuterBody (ltTransMiddleBody left) left
    orderFormulaStage0 termBound
    (fixedOrderFormulaCode_le_stage0 ltTransOuterBody (Or.inr (Or.inl rfl)))
    hleft (ltTransAfterFirst_formula left)

theorem ltTransInnerBody_code_le_stage2
    (left middle : LO.FirstOrder.ArithmeticSemiterm Nat 0) (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hmiddle : (binaryTermCode middle).length <= termBound) :
    (binaryFormulaCode (ltTransInnerBody left middle)).length <=
      orderFormulaStage2 termBound := by
  exact instantiatedUniversalBody_code_le_next
    (ltTransMiddleBody left) (ltTransInnerBody left middle) middle
    (orderFormulaStage1 termBound) termBound
    (ltTransMiddleBody_code_le_stage1 left termBound hleft)
    hmiddle (ltTransAfterSecond_formula left middle)

theorem relationRightFirstBody_code_le_stage1
    (rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (binaryFormulaCode
      (binaryRelationExtRightFirstBody Language.ORing.Rel.lt
        rightSecond)).length <= orderFormulaStage1 termBound := by
  exact instantiatedUniversalBody_code_le_next
    (binaryRelationExtOuterBody Language.ORing.Rel.lt)
    (binaryRelationExtRightFirstBody Language.ORing.Rel.lt rightSecond)
    rightSecond orderFormulaStage0 termBound
    (fixedOrderFormulaCode_le_stage0
      (binaryRelationExtOuterBody Language.ORing.Rel.lt)
      (Or.inr (Or.inr (Or.inl rfl))))
    hrightSecond
    (binaryRelationExtAfterRightSecond_formula
      Language.ORing.Rel.lt rightSecond)

theorem relationLeftSecondBody_code_le_stage2
    (rightFirst rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (binaryFormulaCode
      (binaryRelationExtLeftSecondBody Language.ORing.Rel.lt
        rightFirst rightSecond)).length <= orderFormulaStage2 termBound := by
  exact instantiatedUniversalBody_code_le_next
    (binaryRelationExtRightFirstBody Language.ORing.Rel.lt rightSecond)
    (binaryRelationExtLeftSecondBody Language.ORing.Rel.lt
      rightFirst rightSecond)
    rightFirst (orderFormulaStage1 termBound) termBound
    (relationRightFirstBody_code_le_stage1 rightSecond termBound
      hrightSecond)
    hrightFirst
    (binaryRelationExtAfterRightFirst_formula
      Language.ORing.Rel.lt rightFirst rightSecond)

theorem relationAfterLeftSecondMatrix_code_le_stage3
    (leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (binaryFormulaCode
      (binaryRelationExtAfterLeftSecondMatrix Language.ORing.Rel.lt
        leftSecond rightFirst rightSecond)).length <=
      orderFormulaStage3 termBound := by
  exact instantiatedUniversalBody_code_le_next
    (binaryRelationExtLeftSecondBody Language.ORing.Rel.lt
      rightFirst rightSecond)
    (binaryRelationExtAfterLeftSecondMatrix Language.ORing.Rel.lt
      leftSecond rightFirst rightSecond)
    leftSecond (orderFormulaStage2 termBound) termBound
    (relationLeftSecondBody_code_le_stage2 rightFirst rightSecond termBound
      hrightFirst hrightSecond)
    hleftSecond
    (binaryRelationExtAfterLeftSecond_formula Language.ORing.Rel.lt
      leftSecond rightFirst rightSecond)

theorem specializationCost_le_orderEnvelope
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hformula : (binaryFormulaCode formula).length <=
      orderFormulaCodeEnvelope termBound)
    (hwitness : (binaryTermCode witness).length <= termBound) :
    specializationCost formula witness <=
      orderSpecializationCostEnvelope termBound := by
  have hscale : specializationScale formula witness <=
      orderSpecializationScaleEnvelope termBound := by
    simp [specializationScale, orderSpecializationScaleEnvelope]
    omega
  simp only [specializationCost, orderSpecializationCostEnvelope]
  gcongr

/-! ## Atomic and local proof-assembly syntax envelopes -/

def lessThanFormulaCodeOverhead : Nat :=
    (binaryNatCode 0).length + (binaryNatCode 2).length +
    (binaryNatCode (Encodable.encode
      (Language.LT.lt :
        LO.FirstOrder.Language.Rel ℒₒᵣ 2))).length

theorem lessThanFormula_code_length_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryFormulaCode
      (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        lessThanFormulaCodeOverhead := by
  simp [Semiformula.Operator.operator,
    Semiformula.Operator.LT.sentence_eq, Matrix.fun_eq_vec_two,
    binaryFormulaCode, lessThanFormulaCodeOverhead]
  omega

def orderAtomicFormulaCodeEnvelope (termBound : Nat) : Nat :=
  paFormulaCodeEnvelope termBound +
    2 * termBound + lessThanFormulaCodeOverhead +
    (binaryFormulaCode
      (⊤ : LO.FirstOrder.ArithmeticProposition)).length + 1

def orderDerivedFormulaCodeEnvelope (termBound : Nat) : Nat :=
  paAssemblySyntaxEnvelope (orderAtomicFormulaCodeEnvelope termBound)

def orderLocalFormulaCodeEnvelope (termBound : Nat) : Nat :=
  paAssemblySyntaxEnvelope (orderDerivedFormulaCodeEnvelope termBound)

def orderPrimitiveFormulaCodeEnvelope (termBound : Nat) : Nat :=
  paAssemblySyntaxEnvelope (orderLocalFormulaCodeEnvelope termBound)

theorem equalityFormula_code_le_orderAtomic
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (binaryFormulaCode
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)).length <=
      orderAtomicFormulaCodeEnvelope termBound := by
  have hformula := equalityFormula_code_length_le_paEnvelope
    left right termBound hleft hright
  unfold orderAtomicFormulaCodeEnvelope
  omega

theorem lessThanFormula_code_le_orderAtomic
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (binaryFormulaCode
      (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)).length <=
      orderAtomicFormulaCodeEnvelope termBound := by
  have hformula := lessThanFormula_code_length_le left right
  unfold orderAtomicFormulaCodeEnvelope
  omega

theorem truthFormula_code_le_orderAtomic (termBound : Nat) :
    (binaryFormulaCode
      (⊤ : LO.FirstOrder.ArithmeticProposition)).length <=
      orderAtomicFormulaCodeEnvelope termBound := by
  unfold orderAtomicFormulaCodeEnvelope
  omega

theorem orderAtomic_le_derived (termBound : Nat) :
    orderAtomicFormulaCodeEnvelope termBound <=
      orderDerivedFormulaCodeEnvelope termBound := by
  unfold orderDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
  omega

theorem orderDerived_le_local (termBound : Nat) :
    orderDerivedFormulaCodeEnvelope termBound <=
      orderLocalFormulaCodeEnvelope termBound := by
  unfold orderLocalFormulaCodeEnvelope paAssemblySyntaxEnvelope
  omega

theorem orderLocal_le_primitive (termBound : Nat) :
    orderLocalFormulaCodeEnvelope termBound <=
      orderPrimitiveFormulaCodeEnvelope termBound := by
  unfold orderPrimitiveFormulaCodeEnvelope paAssemblySyntaxEnvelope
  omega

theorem equalityTruthConjunction_code_le_derived
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (binaryFormulaCode
      ((“!!left = !!right” : LO.FirstOrder.ArithmeticProposition) ⋏ ⊤)).length <=
      orderDerivedFormulaCodeEnvelope termBound := by
  have hequality := equalityFormula_code_le_orderAtomic
    left right termBound hleft hright
  have htruth := truthFormula_code_le_orderAtomic termBound
  have hand := binaryFormulaCode_and_length_le_local
    (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)
    (⊤ : LO.FirstOrder.ArithmeticProposition)
  unfold orderDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
  omega

theorem relationCongruenceAntecedent_code_le_local
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (binaryFormulaCode
      (binaryRelationCongruenceAntecedent leftFirst leftSecond
        rightFirst rightSecond)).length <=
      orderLocalFormulaCodeEnvelope termBound := by
  have hfirst := equalityFormula_code_le_orderAtomic
    leftFirst rightFirst termBound hleftFirst hrightFirst
  have hinner := equalityTruthConjunction_code_le_derived
    leftSecond rightSecond termBound hleftSecond hrightSecond
  have hfirstDerived := hfirst.trans (orderAtomic_le_derived termBound)
  have hand := binaryFormulaCode_and_length_le_local
    (“!!leftFirst = !!rightFirst” :
      LO.FirstOrder.ArithmeticProposition)
    ((“!!leftSecond = !!rightSecond” :
      LO.FirstOrder.ArithmeticProposition) ⋏ ⊤)
  simp only [binaryRelationCongruenceAntecedent]
  unfold orderLocalFormulaCodeEnvelope paAssemblySyntaxEnvelope
  omega

theorem relationCongruenceConclusion_code_le_derived
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (binaryFormulaCode
      (binaryRelationCongruenceConclusion Language.ORing.Rel.lt
        leftFirst leftSecond rightFirst rightSecond)).length <=
      orderDerivedFormulaCodeEnvelope termBound := by
  have hleft := lessThanFormula_code_le_orderAtomic
    leftFirst leftSecond termBound hleftFirst hleftSecond
  have hright := lessThanFormula_code_le_orderAtomic
    rightFirst rightSecond termBound hrightFirst hrightSecond
  have himplication := binaryFormulaCode_implication_length_le
    (“!!leftFirst < !!leftSecond” :
      LO.FirstOrder.ArithmeticProposition)
    (“!!rightFirst < !!rightSecond” :
      LO.FirstOrder.ArithmeticProposition)
  rw [binaryRelationCongruenceConclusion_lt_formula]
  unfold orderDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
  omega

def fixedPAOrderPayloadEnvelope : Nat :=
  fixedPAPayloadEnvelope +
    (32 + 10 * axiomSyntaxBudget
      (.eqRelExt Language.ORing.Rel.lt)) +
    (32 + 10 * axiomSyntaxBudget .zeroLtOne) +
    (32 + 10 * axiomSyntaxBudget .addLtAdd) +
    (32 + 10 * axiomSyntaxBudget .ltTrans) +
    (32 + 10 * axiomSyntaxBudget .mulLtMul) +
    (32 + 10 * axiomSyntaxBudget .ltIrrefl) +
    (48 + 9 * verumSyntaxBudget) + 1

def orderPrimitiveCostEnvelope (termBound : Nat) : Nat :=
  32 * fixedPAOrderPayloadEnvelope +
    32 * orderSpecializationCostEnvelope termBound + 4096 +
    2048 * orderPrimitiveFormulaCodeEnvelope termBound

theorem ltIrreflFullPayloadBound_le_primitive
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hterm : (binaryTermCode term).length <= termBound) :
    ltIrreflFullPayloadBound term <=
      orderPrimitiveCostEnvelope termBound := by
  have hbody := (fixedOrderFormulaCode_le_stage0 ltIrreflBody
    (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).trans
      (orderFormulaStage_le_envelope orderFormulaStage0 termBound
        (Or.inl rfl))
  have hspecialization := specializationCost_le_orderEnvelope
    ltIrreflBody term termBound hbody hterm
  have haxiom : 10 * axiomSyntaxBudget .ltIrrefl <=
      fixedPAOrderPayloadEnvelope := by
    unfold fixedPAOrderPayloadEnvelope
    omega
  unfold ltIrreflFullPayloadBound orderPrimitiveCostEnvelope
  omega

theorem relationInnerConjunctionSyntaxBudget_le_derived
    (leftSecond rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    binaryRelationCongruenceInnerConjunctionSyntaxBudget
        leftSecond rightSecond <=
      orderDerivedFormulaCodeEnvelope termBound := by
  have hraw := conjunctionSyntaxBudget_le_paAssemblyEnvelope
    (“!!leftSecond = !!rightSecond” :
      LO.FirstOrder.ArithmeticProposition)
    (⊤ : LO.FirstOrder.ArithmeticProposition)
    (orderAtomicFormulaCodeEnvelope termBound)
    (equalityFormula_code_le_orderAtomic leftSecond rightSecond
      termBound hleftSecond hrightSecond)
    (truthFormula_code_le_orderAtomic termBound)
  simpa [binaryRelationCongruenceInnerConjunctionSyntaxBudget,
    orderDerivedFormulaCodeEnvelope] using hraw

theorem relationOuterConjunctionSyntaxBudget_le_local
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    binaryRelationCongruenceOuterConjunctionSyntaxBudget
        leftFirst leftSecond rightFirst rightSecond <=
      orderLocalFormulaCodeEnvelope termBound := by
  have hfirst := (equalityFormula_code_le_orderAtomic
    leftFirst rightFirst termBound hleftFirst hrightFirst).trans
      (orderAtomic_le_derived termBound)
  have hinner := equalityTruthConjunction_code_le_derived
    leftSecond rightSecond termBound hleftSecond hrightSecond
  have hraw := conjunctionSyntaxBudget_le_paAssemblyEnvelope
    (“!!leftFirst = !!rightFirst” :
      LO.FirstOrder.ArithmeticProposition)
    ((“!!leftSecond = !!rightSecond” :
      LO.FirstOrder.ArithmeticProposition) ⋏ ⊤)
    (orderDerivedFormulaCodeEnvelope termBound) hfirst hinner
  simpa [binaryRelationCongruenceOuterConjunctionSyntaxBudget,
    orderLocalFormulaCodeEnvelope] using hraw

theorem relationCongruenceMPSyntaxBudget_le_primitive
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    binaryRelationCongruenceMPSyntaxBudget Language.ORing.Rel.lt
        leftFirst leftSecond rightFirst rightSecond <=
      orderPrimitiveFormulaCodeEnvelope termBound := by
  have hantecedent := relationCongruenceAntecedent_code_le_local
    leftFirst leftSecond rightFirst rightSecond termBound
    hleftFirst hleftSecond hrightFirst hrightSecond
  have hconclusion := (relationCongruenceConclusion_code_le_derived
    leftFirst leftSecond rightFirst rightSecond termBound
    hleftFirst hleftSecond hrightFirst hrightSecond).trans
      (orderDerived_le_local termBound)
  have hraw := modusPonensSyntaxBudget_le_paAssemblyEnvelope
    (binaryRelationCongruenceAntecedent leftFirst leftSecond
      rightFirst rightSecond)
    (binaryRelationCongruenceConclusion Language.ORing.Rel.lt
      leftFirst leftSecond rightFirst rightSecond)
    (orderLocalFormulaCodeEnvelope termBound) hantecedent hconclusion
  simpa [binaryRelationCongruenceMPSyntaxBudget,
    orderPrimitiveFormulaCodeEnvelope] using hraw

theorem lessThanMPSyntaxBudget_le_derived
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    modusPonensSyntaxBudget
        (“!!leftFirst < !!leftSecond” :
          LO.FirstOrder.ArithmeticProposition)
        (“!!rightFirst < !!rightSecond” :
          LO.FirstOrder.ArithmeticProposition) <=
      orderDerivedFormulaCodeEnvelope termBound := by
  have hleft := lessThanFormula_code_le_orderAtomic
    leftFirst leftSecond termBound hleftFirst hleftSecond
  have hright := lessThanFormula_code_le_orderAtomic
    rightFirst rightSecond termBound hrightFirst hrightSecond
  have hraw := modusPonensSyntaxBudget_le_paAssemblyEnvelope
    (“!!leftFirst < !!leftSecond” :
      LO.FirstOrder.ArithmeticProposition)
    (“!!rightFirst < !!rightSecond” :
      LO.FirstOrder.ArithmeticProposition)
    (orderAtomicFormulaCodeEnvelope termBound) hleft hright
  simpa [orderDerivedFormulaCodeEnvelope] using hraw

theorem addLtAddImplicationFullPayloadBound_le_primitive
    (left right shift : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound)
    (hshift : (binaryTermCode shift).length <= termBound) :
    addLtAddImplicationFullPayloadBound left right shift <=
      orderPrimitiveCostEnvelope termBound := by
  have houter := (fixedOrderFormulaCode_le_stage0
    addLtAddOuterBody (Or.inl rfl)).trans
      (orderFormulaStage_le_envelope orderFormulaStage0 termBound
        (Or.inl rfl))
  have hmiddle := (addLtAddMiddleBody_code_le_stage1
    left termBound hleft).trans
      (orderFormulaStage_le_envelope (orderFormulaStage1 termBound)
        termBound (Or.inr (Or.inl rfl)))
  have hinner := (addLtAddInnerBody_code_le_stage2
    left right termBound hleft hright).trans
      (orderFormulaStage_le_envelope (orderFormulaStage2 termBound)
        termBound (Or.inr (Or.inr (Or.inl rfl))))
  have hfirst := specializationCost_le_orderEnvelope
    addLtAddOuterBody left termBound houter hleft
  have hsecond := specializationCost_le_orderEnvelope
    (addLtAddMiddleBody left) right termBound hmiddle hright
  have hthird := specializationCost_le_orderEnvelope
    (addLtAddInnerBody left right) shift termBound hinner hshift
  have haxiom : 10 * axiomSyntaxBudget .addLtAdd <=
      fixedPAOrderPayloadEnvelope := by
    unfold fixedPAOrderPayloadEnvelope
    omega
  unfold addLtAddImplicationFullPayloadBound orderPrimitiveCostEnvelope
  omega

theorem mulLtMulImplicationFullPayloadBound_le_primitive
    (left right factor : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound)
    (hfactor : (binaryTermCode factor).length <= termBound) :
    mulLtMulImplicationFullPayloadBound left right factor <=
      orderPrimitiveCostEnvelope termBound := by
  have houter := (fixedOrderFormulaCode_le_stage0
    mulLtMulOuterBody (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).trans
      (orderFormulaStage_le_envelope orderFormulaStage0 termBound
        (Or.inl rfl))
  have hmiddle := (mulLtMulMiddleBody_code_le_stage1
    left termBound hleft).trans
      (orderFormulaStage_le_envelope (orderFormulaStage1 termBound)
        termBound (Or.inr (Or.inl rfl)))
  have hinner := (mulLtMulInnerBody_code_le_stage2
    left right termBound hleft hright).trans
      (orderFormulaStage_le_envelope (orderFormulaStage2 termBound)
        termBound (Or.inr (Or.inr (Or.inl rfl))))
  have hfirst := specializationCost_le_orderEnvelope
    mulLtMulOuterBody left termBound houter hleft
  have hsecond := specializationCost_le_orderEnvelope
    (mulLtMulMiddleBody left) right termBound hmiddle hright
  have hthird := specializationCost_le_orderEnvelope
    (mulLtMulInnerBody left right) factor termBound hinner hfactor
  have haxiom : 10 * axiomSyntaxBudget .mulLtMul <=
      fixedPAOrderPayloadEnvelope := by
    unfold fixedPAOrderPayloadEnvelope
    omega
  unfold mulLtMulImplicationFullPayloadBound orderPrimitiveCostEnvelope
  omega

theorem ltTransitivityFullPayloadBound_le_primitive
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (leftLength rightLength termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hmiddle : (binaryTermCode middle).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    ltTransitivityFullPayloadBound left middle right
        leftLength rightLength <=
      leftLength + rightLength + orderPrimitiveCostEnvelope termBound := by
  have houter := (fixedOrderFormulaCode_le_stage0
    ltTransOuterBody (Or.inr (Or.inl rfl))).trans
      (orderFormulaStage_le_envelope orderFormulaStage0 termBound
        (Or.inl rfl))
  have hmiddleFormula := (ltTransMiddleBody_code_le_stage1
    left termBound hleft).trans
      (orderFormulaStage_le_envelope (orderFormulaStage1 termBound)
        termBound (Or.inr (Or.inl rfl)))
  have hinner := (ltTransInnerBody_code_le_stage2
    left middle termBound hleft hmiddle).trans
      (orderFormulaStage_le_envelope (orderFormulaStage2 termBound)
        termBound (Or.inr (Or.inr (Or.inl rfl))))
  have hfirst := specializationCost_le_orderEnvelope
    ltTransOuterBody left termBound houter hleft
  have hsecond := specializationCost_le_orderEnvelope
    (ltTransMiddleBody left) middle termBound hmiddleFormula hmiddle
  have hthird := specializationCost_le_orderEnvelope
    (ltTransInnerBody left middle) right termBound hinner hright
  have hleftLt := lessThanFormula_code_le_orderAtomic
    left middle termBound hleft hmiddle
  have hrightLt := lessThanFormula_code_le_orderAtomic
    middle right termBound hmiddle hright
  have hconjunction := conjunctionSyntaxBudget_le_paAssemblyEnvelope
    (“!!left < !!middle” : LO.FirstOrder.ArithmeticProposition)
    (“!!middle < !!right” : LO.FirstOrder.ArithmeticProposition)
    (orderAtomicFormulaCodeEnvelope termBound) hleftLt hrightLt
  have hconjunctionCode := binaryFormulaCode_and_length_le_local
    (“!!left < !!middle” : LO.FirstOrder.ArithmeticProposition)
    (“!!middle < !!right” : LO.FirstOrder.ArithmeticProposition)
  have hantecedent :
      (binaryFormulaCode
        ((“!!left < !!middle” : LO.FirstOrder.ArithmeticProposition) ⋏
          (“!!middle < !!right” :
            LO.FirstOrder.ArithmeticProposition))).length <=
        orderDerivedFormulaCodeEnvelope termBound := by
    unfold orderDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
    omega
  have hconsequent := (lessThanFormula_code_le_orderAtomic
    left right termBound hleft hright).trans
      (orderAtomic_le_derived termBound)
  have hmp := modusPonensSyntaxBudget_le_paAssemblyEnvelope
    ((“!!left < !!middle” : LO.FirstOrder.ArithmeticProposition) ⋏
      (“!!middle < !!right” : LO.FirstOrder.ArithmeticProposition))
    (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)
    (orderDerivedFormulaCodeEnvelope termBound) hantecedent hconsequent
  have haxiom : 10 * axiomSyntaxBudget .ltTrans <=
      fixedPAOrderPayloadEnvelope := by
    unfold fixedPAOrderPayloadEnvelope
    omega
  have hconjunctionPrimitive :
      conjunctionSyntaxBudget
          (“!!left < !!middle” : LO.FirstOrder.ArithmeticProposition)
          (“!!middle < !!right” : LO.FirstOrder.ArithmeticProposition) <=
        orderPrimitiveFormulaCodeEnvelope termBound := by
    have hderived : conjunctionSyntaxBudget
        (“!!left < !!middle” : LO.FirstOrder.ArithmeticProposition)
        (“!!middle < !!right” : LO.FirstOrder.ArithmeticProposition) <=
        orderDerivedFormulaCodeEnvelope termBound := by
      simpa [orderDerivedFormulaCodeEnvelope] using hconjunction
    exact (hderived.trans (orderDerived_le_local termBound)).trans
      (orderLocal_le_primitive termBound)
  have hmpPrimitive :
      modusPonensSyntaxBudget
          ((“!!left < !!middle” : LO.FirstOrder.ArithmeticProposition) ⋏
            (“!!middle < !!right” :
              LO.FirstOrder.ArithmeticProposition))
          (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition) <=
        orderPrimitiveFormulaCodeEnvelope termBound := by
    have hlocal : modusPonensSyntaxBudget
        ((“!!left < !!middle” : LO.FirstOrder.ArithmeticProposition) ⋏
          (“!!middle < !!right” : LO.FirstOrder.ArithmeticProposition))
        (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition) <=
        orderLocalFormulaCodeEnvelope termBound := by
      simpa [orderLocalFormulaCodeEnvelope] using hmp
    exact hlocal.trans (orderLocal_le_primitive termBound)
  unfold ltTransitivityFullPayloadBound orderPrimitiveCostEnvelope
  omega

theorem binaryRelationTransportFullPayloadBound_le_primitive
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstLength secondLength termBound : Nat)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    binaryRelationTransportFullPayloadBound Language.ORing.Rel.lt
        leftFirst leftSecond rightFirst rightSecond
        firstLength secondLength <=
      firstLength + secondLength + orderPrimitiveCostEnvelope termBound := by
  have houter := (fixedOrderFormulaCode_le_stage0
    (binaryRelationExtOuterBody Language.ORing.Rel.lt)
    (Or.inr (Or.inr (Or.inl rfl)))).trans
      (orderFormulaStage_le_envelope orderFormulaStage0 termBound
        (Or.inl rfl))
  have hstage1 := (relationRightFirstBody_code_le_stage1
    rightSecond termBound hrightSecond).trans
      (orderFormulaStage_le_envelope (orderFormulaStage1 termBound)
        termBound (Or.inr (Or.inl rfl)))
  have hstage2 := (relationLeftSecondBody_code_le_stage2
    rightFirst rightSecond termBound hrightFirst hrightSecond).trans
      (orderFormulaStage_le_envelope (orderFormulaStage2 termBound)
        termBound (Or.inr (Or.inr (Or.inl rfl))))
  have hstage3 := (relationAfterLeftSecondMatrix_code_le_stage3
    leftSecond rightFirst rightSecond termBound
    hleftSecond hrightFirst hrightSecond).trans
      (orderFormulaStage_le_envelope (orderFormulaStage3 termBound)
        termBound (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hfirst := specializationCost_le_orderEnvelope
    (binaryRelationExtOuterBody Language.ORing.Rel.lt)
    rightSecond termBound houter hrightSecond
  have hsecond := specializationCost_le_orderEnvelope
    (binaryRelationExtRightFirstBody Language.ORing.Rel.lt rightSecond)
    rightFirst termBound hstage1 hrightFirst
  have hthird := specializationCost_le_orderEnvelope
    (binaryRelationExtLeftSecondBody Language.ORing.Rel.lt
      rightFirst rightSecond)
    leftSecond termBound hstage2 hleftSecond
  have hfourth := specializationCost_le_orderEnvelope
    (binaryRelationExtAfterLeftSecondMatrix Language.ORing.Rel.lt
      leftSecond rightFirst rightSecond)
    leftFirst termBound hstage3 hleftFirst
  have hinner := relationInnerConjunctionSyntaxBudget_le_derived
    leftSecond rightSecond termBound hleftSecond hrightSecond
  have hinnerPrimitive :=
    (hinner.trans (orderDerived_le_local termBound)).trans
      (orderLocal_le_primitive termBound)
  have houterConjunction := relationOuterConjunctionSyntaxBudget_le_local
    leftFirst leftSecond rightFirst rightSecond termBound
    hleftFirst hleftSecond hrightFirst hrightSecond
  have houterPrimitive := houterConjunction.trans
    (orderLocal_le_primitive termBound)
  have hmp := relationCongruenceMPSyntaxBudget_le_primitive
    leftFirst leftSecond rightFirst rightSecond termBound
    hleftFirst hleftSecond hrightFirst hrightSecond
  have haxiom :
      10 * axiomSyntaxBudget (.eqRelExt Language.ORing.Rel.lt) <=
        fixedPAOrderPayloadEnvelope := by
    unfold fixedPAOrderPayloadEnvelope
    omega
  have hverum : 9 * verumSyntaxBudget <=
      fixedPAOrderPayloadEnvelope := by
    unfold fixedPAOrderPayloadEnvelope
    omega
  unfold binaryRelationTransportFullPayloadBound orderPrimitiveCostEnvelope
  omega

theorem proveLtTransport_payloadLength_le_primitive
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstEquality : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondEquality : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition))
    (relationProof : CertifiedPAProof
      (“!!leftFirst < !!leftSecond” :
        LO.FirstOrder.ArithmeticProposition))
    (termBound : Nat)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (proveLtTransport leftFirst leftSecond rightFirst rightSecond
      firstEquality secondEquality relationProof).payloadLength <=
      firstEquality.payloadLength + secondEquality.payloadLength +
        relationProof.payloadLength +
        2 * orderPrimitiveCostEnvelope termBound := by
  have hproof := proveLtTransport_payloadLength_le
    leftFirst leftSecond rightFirst rightSecond
    firstEquality secondEquality relationProof
  have hrelation := binaryRelationTransportFullPayloadBound_le_primitive
    leftFirst leftSecond rightFirst rightSecond
    firstEquality.payloadLength secondEquality.payloadLength termBound
    hleftFirst hleftSecond hrightFirst hrightSecond
  have hmp := lessThanMPSyntaxBudget_le_derived
    leftFirst leftSecond rightFirst rightSecond termBound
    hleftFirst hleftSecond hrightFirst hrightSecond
  have hmpPrimitive := (hmp.trans (orderDerived_le_local termBound)).trans
    (orderLocal_le_primitive termBound)
  have hfinalCost : 240 +
      34 * modusPonensSyntaxBudget
        (“!!leftFirst < !!leftSecond” :
          LO.FirstOrder.ArithmeticProposition)
        (“!!rightFirst < !!rightSecond” :
          LO.FirstOrder.ArithmeticProposition) <=
      orderPrimitiveCostEnvelope termBound := by
    unfold orderPrimitiveCostEnvelope
    omega
  omega

def cumulativeBinaryAdditionPayloadPolynomial (width : Nat) : Nat :=
  ∑ candidate ∈ Finset.range (width + 1),
    binaryNumeralAdditionPayloadPolynomial candidate

theorem binaryAdditionPolynomial_le_cumulative
    {candidate width : Nat} (hwidth : candidate <= width) :
    binaryNumeralAdditionPayloadPolynomial candidate <=
      cumulativeBinaryAdditionPayloadPolynomial width := by
  have hmem : candidate ∈ Finset.range (width + 1) := by
    simp
    omega
  unfold cumulativeBinaryAdditionPayloadPolynomial
  exact Finset.single_le_sum
    (f := fun index => binaryNumeralAdditionPayloadPolynomial index)
    (s := Finset.range (width + 1))
    (fun index _ => Nat.zero_le
      (binaryNumeralAdditionPayloadPolynomial index))
    hmem

def cumulativeBinaryMultiplicationPayloadPolynomial (width : Nat) : Nat :=
  ∑ candidate ∈ Finset.range (width + 1),
    binaryNumeralMultiplicationPayloadPolynomial candidate

theorem binaryMultiplicationPolynomial_le_cumulative
    {candidate width : Nat} (hwidth : candidate <= width) :
    binaryNumeralMultiplicationPayloadPolynomial candidate <=
      cumulativeBinaryMultiplicationPayloadPolynomial width := by
  have hmem : candidate ∈ Finset.range (width + 1) := by
    simp
    omega
  unfold cumulativeBinaryMultiplicationPayloadPolynomial
  exact Finset.single_le_sum
    (f := fun index => binaryNumeralMultiplicationPayloadPolynomial index)
    (s := Finset.range (width + 1))
    (fun index _ => Nat.zero_le
      (binaryNumeralMultiplicationPayloadPolynomial index))
    hmem

/-! ## One binary positivity step under a public width budget -/

def orderTermWorkWidth (inputWidth : Nat) : Nat :=
  2 * inputWidth + 2

def orderTermCodeEnvelope (inputWidth : Nat) : Nat :=
  paGeneratedTermCodeEnvelope (orderTermWorkWidth inputWidth)

def orderStepCostEnvelope (inputWidth : Nat) : Nat :=
  16 *
    (orderPrimitiveCostEnvelope (orderTermCodeEnvelope inputWidth) +
      cumulativeBinaryAdditionPayloadPolynomial (2 * inputWidth) + 1)

theorem binaryNumeralAddLtAddPayloadBound_le_orderStep
    (left right shift relationLength inputWidth : Nat)
    (hleft : Nat.size left <= inputWidth)
    (hright : Nat.size right <= inputWidth)
    (hshift : Nat.size shift <= inputWidth) :
    binaryNumeralAddLtAddPayloadBound
        left right shift relationLength <=
      relationLength + orderStepCostEnvelope inputWidth := by
  let workWidth := orderTermWorkWidth inputWidth
  let termBound := orderTermCodeEnvelope inputWidth
  let leftTerm := shortBinaryNumeralTerm left
  let rightTerm := shortBinaryNumeralTerm right
  let shiftTerm := shortBinaryNumeralTerm shift
  let leftSum := paAddTerm leftTerm shiftTerm
  let rightSum := paAddTerm rightTerm shiftTerm
  let leftResult := shortBinaryNumeralTerm (left + shift)
  let rightResult := shortBinaryNumeralTerm (right + shift)
  have hleftSize : Nat.size left <= workWidth := by
    unfold workWidth orderTermWorkWidth
    omega
  have hrightSize : Nat.size right <= workWidth := by
    unfold workWidth orderTermWorkWidth
    omega
  have hshiftSize : Nat.size shift <= workWidth := by
    unfold workWidth orderTermWorkWidth
    omega
  have hleftResultRaw := natSize_add_le left shift
  have hrightResultRaw := natSize_add_le right shift
  have hleftResultSize : Nat.size (left + shift) <= workWidth := by
    unfold workWidth orderTermWorkWidth
    omega
  have hrightResultSize : Nat.size (right + shift) <= workWidth := by
    unfold workWidth orderTermWorkWidth
    omega
  have hleftGenerated : PACompilerGeneratedTerm workWidth 1 leftTerm :=
    .numeral left hleftSize
  have hrightGenerated : PACompilerGeneratedTerm workWidth 1 rightTerm :=
    .numeral right hrightSize
  have hshiftGenerated : PACompilerGeneratedTerm workWidth 1 shiftTerm :=
    .numeral shift hshiftSize
  have hleftSumGenerated : PACompilerGeneratedTerm workWidth 3 leftSum :=
    .add hleftGenerated hshiftGenerated
  have hrightSumGenerated : PACompilerGeneratedTerm workWidth 3 rightSum :=
    .add hrightGenerated hshiftGenerated
  have hleftResultGenerated : PACompilerGeneratedTerm workWidth 1 leftResult :=
    .numeral (left + shift) hleftResultSize
  have hrightResultGenerated :
      PACompilerGeneratedTerm workWidth 1 rightResult :=
    .numeral (right + shift) hrightResultSize
  have hleftCode : (binaryTermCode leftTerm).length <= termBound := by
    exact generatedTerm_code_length_le_compiler hleftGenerated (by omega)
  have hrightCode : (binaryTermCode rightTerm).length <= termBound := by
    exact generatedTerm_code_length_le_compiler hrightGenerated (by omega)
  have hshiftCode : (binaryTermCode shiftTerm).length <= termBound := by
    exact generatedTerm_code_length_le_compiler hshiftGenerated (by omega)
  have hleftSumCode : (binaryTermCode leftSum).length <= termBound := by
    exact generatedTerm_code_length_le_compiler hleftSumGenerated (by omega)
  have hrightSumCode : (binaryTermCode rightSum).length <= termBound := by
    exact generatedTerm_code_length_le_compiler hrightSumGenerated (by omega)
  have hleftResultCode :
      (binaryTermCode leftResult).length <= termBound := by
    exact generatedTerm_code_length_le_compiler hleftResultGenerated (by omega)
  have hrightResultCode :
      (binaryTermCode rightResult).length <= termBound := by
    exact generatedTerm_code_length_le_compiler hrightResultGenerated (by omega)
  have hleftAddition := binaryAdditionPolynomial_le_cumulative
    (candidate := Nat.size left + Nat.size shift)
    (width := 2 * inputWidth) (by omega)
  have hrightAddition := binaryAdditionPolynomial_le_cumulative
    (candidate := Nat.size right + Nat.size shift)
    (width := 2 * inputWidth) (by omega)
  have hrelation := binaryRelationTransportFullPayloadBound_le_primitive
    leftSum rightSum leftResult rightResult
    (binaryNumeralAdditionPayloadPolynomial
      (Nat.size left + Nat.size shift))
    (binaryNumeralAdditionPayloadPolynomial
      (Nat.size right + Nat.size shift))
    termBound hleftSumCode hrightSumCode
    hleftResultCode hrightResultCode
  have himplication := addLtAddImplicationFullPayloadBound_le_primitive
    leftTerm rightTerm shiftTerm termBound
    hleftCode hrightCode hshiftCode
  have hshiftMP := lessThanMPSyntaxBudget_le_derived
    leftTerm rightTerm leftSum rightSum termBound
    hleftCode hrightCode hleftSumCode hrightSumCode
  have hshiftMPPrimitive :=
    (hshiftMP.trans (orderDerived_le_local termBound)).trans
      (orderLocal_le_primitive termBound)
  have hfinalMP := lessThanMPSyntaxBudget_le_derived
    leftSum rightSum leftResult rightResult termBound
    hleftSumCode hrightSumCode hleftResultCode hrightResultCode
  have hfinalMPPrimitive :=
    (hfinalMP.trans (orderDerived_le_local termBound)).trans
      (orderLocal_le_primitive termBound)
  have hshiftCost :
      addLtAddImplicationFullPayloadBound leftTerm rightTerm shiftTerm +
          relationLength + 240 +
          34 * modusPonensSyntaxBudget
            (“!!leftTerm < !!rightTerm” :
              LO.FirstOrder.ArithmeticProposition)
            (“!!leftTerm + !!shiftTerm < !!rightTerm + !!shiftTerm” :
              LO.FirstOrder.ArithmeticProposition) <=
        relationLength + 2 * orderPrimitiveCostEnvelope termBound := by
    have hformula :
        (“!!leftTerm + !!shiftTerm < !!rightTerm + !!shiftTerm” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!leftSum < !!rightSum” :
          LO.FirstOrder.ArithmeticProposition) := by
      simp [leftSum, rightSum, paAddTerm]
    rw [hformula]
    have hlocalCost : 240 +
        34 * modusPonensSyntaxBudget
          (“!!leftTerm < !!rightTerm” :
            LO.FirstOrder.ArithmeticProposition)
          (“!!leftSum < !!rightSum” :
            LO.FirstOrder.ArithmeticProposition) <=
        orderPrimitiveCostEnvelope termBound := by
      unfold orderPrimitiveCostEnvelope
      omega
    omega
  have hfinalCost : 240 +
      34 * modusPonensSyntaxBudget
        (“!!leftSum < !!rightSum” :
          LO.FirstOrder.ArithmeticProposition)
        (“!!leftResult < !!rightResult” :
          LO.FirstOrder.ArithmeticProposition) <=
      orderPrimitiveCostEnvelope termBound := by
    unfold orderPrimitiveCostEnvelope
    omega
  change
    binaryRelationTransportFullPayloadBound Language.ORing.Rel.lt
        leftSum rightSum leftResult rightResult
        (binaryNumeralAdditionPayloadPolynomial
          (Nat.size left + Nat.size shift))
        (binaryNumeralAdditionPayloadPolynomial
          (Nat.size right + Nat.size shift)) +
      (addLtAddImplicationFullPayloadBound leftTerm rightTerm shiftTerm +
        relationLength + 240 +
        34 * modusPonensSyntaxBudget
          (“!!leftTerm < !!rightTerm” :
            LO.FirstOrder.ArithmeticProposition)
          (“!!leftTerm + !!shiftTerm < !!rightTerm + !!shiftTerm” :
            LO.FirstOrder.ArithmeticProposition)) + 240 +
      34 * modusPonensSyntaxBudget
        (“!!leftSum < !!rightSum” :
          LO.FirstOrder.ArithmeticProposition)
        (“!!leftResult < !!rightResult” :
          LO.FirstOrder.ArithmeticProposition) <=
      relationLength + orderStepCostEnvelope inputWidth
  dsimp only [termBound] at hrelation himplication hshiftCost hfinalCost
  unfold orderStepCostEnvelope
  omega

def orderDoubleTermWorkWidth (inputWidth : Nat) : Nat :=
  inputWidth + 3

def orderDoubleTermCodeEnvelope (inputWidth : Nat) : Nat :=
  paGeneratedTermCodeEnvelope (orderDoubleTermWorkWidth inputWidth)

def orderDoubleStepCostEnvelope (inputWidth : Nat) : Nat :=
  32 *
    (orderPrimitiveCostEnvelope (orderDoubleTermCodeEnvelope inputWidth) +
      cumulativeBinaryMultiplicationPayloadPolynomial (inputWidth + 2) +
      zeroLtBinaryTwoPayloadBound + 1)

theorem positiveBinaryDoublePayloadBound_le_orderStep
    (high relationLength inputWidth : Nat)
    (hhigh : Nat.size high <= inputWidth) :
    positiveBinaryDoublePayloadBound high relationLength <=
      relationLength + orderDoubleStepCostEnvelope inputWidth := by
  let workWidth := orderDoubleTermWorkWidth inputWidth
  let termBound := orderDoubleTermCodeEnvelope inputWidth
  let zeroTerm := shortBinaryNumeralTerm 0
  let highTerm := shortBinaryNumeralTerm high
  let twoTerm := shortBinaryNumeralTerm 2
  let leftProduct := paMulTerm zeroTerm twoTerm
  let rightProduct := paMulTerm highTerm twoTerm
  let leftResult := shortBinaryNumeralTerm (0 * 2)
  let rightResult := shortBinaryNumeralTerm (high * 2)
  have hsizeZero : Nat.size 0 = 0 := by decide
  have hsizeTwo : Nat.size 2 = 2 := by decide
  have hzeroSize : Nat.size 0 <= workWidth := by
    unfold workWidth orderDoubleTermWorkWidth
    rw [hsizeZero]
    omega
  have hhighSize : Nat.size high <= workWidth := by
    unfold workWidth orderDoubleTermWorkWidth
    omega
  have htwoSize : Nat.size 2 <= workWidth := by
    unfold workWidth orderDoubleTermWorkWidth
    rw [hsizeTwo]
    omega
  have hleftResultRaw := natSize_mul_le 0 2
  have hrightResultRaw := natSize_mul_le high 2
  have hleftResultSize : Nat.size (0 * 2) <= workWidth := by
    unfold workWidth orderDoubleTermWorkWidth
    simp
  have hrightResultSize : Nat.size (high * 2) <= workWidth := by
    unfold workWidth orderDoubleTermWorkWidth
    rw [hsizeTwo] at hrightResultRaw
    omega
  have hzeroGenerated : PACompilerGeneratedTerm workWidth 1 zeroTerm :=
    .numeral 0 hzeroSize
  have hhighGenerated : PACompilerGeneratedTerm workWidth 1 highTerm :=
    .numeral high hhighSize
  have htwoGenerated : PACompilerGeneratedTerm workWidth 1 twoTerm :=
    .numeral 2 htwoSize
  have hpaZeroGenerated : PACompilerGeneratedTerm workWidth 1 paZeroTerm :=
    .zero
  have hleftProductGenerated :
      PACompilerGeneratedTerm workWidth 3 leftProduct :=
    .mul hzeroGenerated htwoGenerated
  have hrightProductGenerated :
      PACompilerGeneratedTerm workWidth 3 rightProduct :=
    .mul hhighGenerated htwoGenerated
  have hleftResultGenerated :
      PACompilerGeneratedTerm workWidth 1 leftResult :=
    .numeral (0 * 2) hleftResultSize
  have hrightResultGenerated :
      PACompilerGeneratedTerm workWidth 1 rightResult :=
    .numeral (high * 2) hrightResultSize
  have hzeroCode : (binaryTermCode zeroTerm).length <= termBound :=
    generatedTerm_code_length_le_compiler hzeroGenerated (by omega)
  have hhighCode : (binaryTermCode highTerm).length <= termBound :=
    generatedTerm_code_length_le_compiler hhighGenerated (by omega)
  have htwoCode : (binaryTermCode twoTerm).length <= termBound :=
    generatedTerm_code_length_le_compiler htwoGenerated (by omega)
  have hpaZeroCode : (binaryTermCode paZeroTerm).length <= termBound :=
    generatedTerm_code_length_le_compiler hpaZeroGenerated (by omega)
  have hleftProductCode :
      (binaryTermCode leftProduct).length <= termBound :=
    generatedTerm_code_length_le_compiler hleftProductGenerated (by omega)
  have hrightProductCode :
      (binaryTermCode rightProduct).length <= termBound :=
    generatedTerm_code_length_le_compiler hrightProductGenerated (by omega)
  have hleftResultCode :
      (binaryTermCode leftResult).length <= termBound :=
    generatedTerm_code_length_le_compiler hleftResultGenerated (by omega)
  have hrightResultCode :
      (binaryTermCode rightResult).length <= termBound :=
    generatedTerm_code_length_le_compiler hrightResultGenerated (by omega)
  have hleftMultiplication := binaryMultiplicationPolynomial_le_cumulative
    (candidate := Nat.size 0 + Nat.size 2)
    (width := inputWidth + 2) (by simp [hsizeZero, hsizeTwo])
  have hrightMultiplication := binaryMultiplicationPolynomial_le_cumulative
    (candidate := Nat.size high + Nat.size 2)
    (width := inputWidth + 2) (by rw [hsizeTwo]; omega)
  have himplication := mulLtMulImplicationFullPayloadBound_le_primitive
    zeroTerm highTerm twoTerm termBound hzeroCode hhighCode htwoCode
  have hsourceLt := lessThanFormula_code_le_orderAtomic
    zeroTerm highTerm termBound hzeroCode hhighCode
  have hfactorLt := lessThanFormula_code_le_orderAtomic
    paZeroTerm twoTerm termBound hpaZeroCode htwoCode
  have hconjunction := conjunctionSyntaxBudget_le_paAssemblyEnvelope
    (“!!zeroTerm < !!highTerm” : LO.FirstOrder.ArithmeticProposition)
    (“!!paZeroTerm < !!twoTerm” : LO.FirstOrder.ArithmeticProposition)
    (orderAtomicFormulaCodeEnvelope termBound) hsourceLt hfactorLt
  have hantecedentCodeRaw := binaryFormulaCode_and_length_le_local
    (“!!zeroTerm < !!highTerm” : LO.FirstOrder.ArithmeticProposition)
    (“!!paZeroTerm < !!twoTerm” : LO.FirstOrder.ArithmeticProposition)
  have hantecedentCode :
      (binaryFormulaCode
        ((“!!zeroTerm < !!highTerm” :
            LO.FirstOrder.ArithmeticProposition) ⋏
          (“!!paZeroTerm < !!twoTerm” :
            LO.FirstOrder.ArithmeticProposition))).length <=
        orderDerivedFormulaCodeEnvelope termBound := by
    unfold orderDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
    omega
  have hconsequentCode := lessThanFormula_code_le_orderAtomic
    leftProduct rightProduct termBound hleftProductCode hrightProductCode
  have hmpRaw := modusPonensSyntaxBudget_le_paAssemblyEnvelope
    ((“!!zeroTerm < !!highTerm” :
        LO.FirstOrder.ArithmeticProposition) ⋏
      (“!!paZeroTerm < !!twoTerm” :
        LO.FirstOrder.ArithmeticProposition))
    (“!!leftProduct < !!rightProduct” :
      LO.FirstOrder.ArithmeticProposition)
    (orderDerivedFormulaCodeEnvelope termBound)
    hantecedentCode
    (hconsequentCode.trans (orderAtomic_le_derived termBound))
  have hmp :
      modusPonensSyntaxBudget
          ((“!!zeroTerm < !!highTerm” :
              LO.FirstOrder.ArithmeticProposition) ⋏
            (“!!paZeroTerm < !!twoTerm” :
              LO.FirstOrder.ArithmeticProposition))
          (“!!zeroTerm * !!twoTerm < !!highTerm * !!twoTerm” :
            LO.FirstOrder.ArithmeticProposition) <=
        orderLocalFormulaCodeEnvelope termBound := by
    rw [mulLtMulAsTerms_formula zeroTerm highTerm twoTerm]
    simpa [orderLocalFormulaCodeEnvelope] using hmpRaw
  have hrelation := binaryRelationTransportFullPayloadBound_le_primitive
    leftProduct rightProduct leftResult rightResult
    (binaryNumeralMultiplicationPayloadPolynomial
      (Nat.size 0 + Nat.size 2))
    (binaryNumeralMultiplicationPayloadPolynomial
      (Nat.size high + Nat.size 2))
    termBound hleftProductCode hrightProductCode
    hleftResultCode hrightResultCode
  have hfinalMP := lessThanMPSyntaxBudget_le_derived
    leftProduct rightProduct leftResult rightResult termBound
    hleftProductCode hrightProductCode hleftResultCode hrightResultCode
  have hconjunctionPrimitive :
      conjunctionSyntaxBudget
          (“!!zeroTerm < !!highTerm” :
            LO.FirstOrder.ArithmeticProposition)
          (“!!paZeroTerm < !!twoTerm” :
            LO.FirstOrder.ArithmeticProposition) <=
        orderPrimitiveFormulaCodeEnvelope termBound := by
    have hderived : conjunctionSyntaxBudget
        (“!!zeroTerm < !!highTerm” :
          LO.FirstOrder.ArithmeticProposition)
        (“!!paZeroTerm < !!twoTerm” :
          LO.FirstOrder.ArithmeticProposition) <=
        orderDerivedFormulaCodeEnvelope termBound := by
      simpa [orderDerivedFormulaCodeEnvelope] using hconjunction
    exact (hderived.trans (orderDerived_le_local termBound)).trans
      (orderLocal_le_primitive termBound)
  have hmpPrimitive := hmp.trans (orderLocal_le_primitive termBound)
  have hfinalMPPrimitive :=
    (hfinalMP.trans (orderDerived_le_local termBound)).trans
      (orderLocal_le_primitive termBound)
  have hmultipliedCost :
      mulLtMulImplicationFullPayloadBound zeroTerm highTerm twoTerm +
          relationLength + zeroLtBinaryTwoPayloadBound + 384 +
          11 * conjunctionSyntaxBudget
            (“!!zeroTerm < !!highTerm” :
              LO.FirstOrder.ArithmeticProposition)
            (“!!paZeroTerm < !!twoTerm” :
              LO.FirstOrder.ArithmeticProposition) +
          34 * modusPonensSyntaxBudget
            ((“!!zeroTerm < !!highTerm” :
                LO.FirstOrder.ArithmeticProposition) ⋏
              (“!!paZeroTerm < !!twoTerm” :
                LO.FirstOrder.ArithmeticProposition))
            (“!!zeroTerm * !!twoTerm < !!highTerm * !!twoTerm” :
              LO.FirstOrder.ArithmeticProposition) <=
        relationLength + zeroLtBinaryTwoPayloadBound +
          3 * orderPrimitiveCostEnvelope termBound := by
    have hlocalCost : 384 +
        11 * conjunctionSyntaxBudget
          (“!!zeroTerm < !!highTerm” :
            LO.FirstOrder.ArithmeticProposition)
          (“!!paZeroTerm < !!twoTerm” :
            LO.FirstOrder.ArithmeticProposition) +
        34 * modusPonensSyntaxBudget
          ((“!!zeroTerm < !!highTerm” :
              LO.FirstOrder.ArithmeticProposition) ⋏
            (“!!paZeroTerm < !!twoTerm” :
              LO.FirstOrder.ArithmeticProposition))
          (“!!zeroTerm * !!twoTerm < !!highTerm * !!twoTerm” :
            LO.FirstOrder.ArithmeticProposition) <=
        2 * orderPrimitiveCostEnvelope termBound := by
      unfold orderPrimitiveCostEnvelope
      omega
    omega
  have hfinalCost : 240 +
      34 * modusPonensSyntaxBudget
        (“!!leftProduct < !!rightProduct” :
          LO.FirstOrder.ArithmeticProposition)
        (“!!leftResult < !!rightResult” :
          LO.FirstOrder.ArithmeticProposition) <=
      orderPrimitiveCostEnvelope termBound := by
    unfold orderPrimitiveCostEnvelope
    omega
  change
    binaryRelationTransportFullPayloadBound Language.ORing.Rel.lt
        leftProduct rightProduct leftResult rightResult
        (binaryNumeralMultiplicationPayloadPolynomial
          (Nat.size 0 + Nat.size 2))
        (binaryNumeralMultiplicationPayloadPolynomial
          (Nat.size high + Nat.size 2)) +
      (mulLtMulImplicationFullPayloadBound zeroTerm highTerm twoTerm +
        relationLength + zeroLtBinaryTwoPayloadBound + 384 +
        11 * conjunctionSyntaxBudget
          (“!!zeroTerm < !!highTerm” :
            LO.FirstOrder.ArithmeticProposition)
          (“!!paZeroTerm < !!twoTerm” :
            LO.FirstOrder.ArithmeticProposition) +
        34 * modusPonensSyntaxBudget
          ((“!!zeroTerm < !!highTerm” :
              LO.FirstOrder.ArithmeticProposition) ⋏
            (“!!paZeroTerm < !!twoTerm” :
              LO.FirstOrder.ArithmeticProposition))
          (“!!zeroTerm * !!twoTerm < !!highTerm * !!twoTerm” :
            LO.FirstOrder.ArithmeticProposition)) + 240 +
      34 * modusPonensSyntaxBudget
        (“!!leftProduct < !!rightProduct” :
          LO.FirstOrder.ArithmeticProposition)
        (“!!leftResult < !!rightResult” :
          LO.FirstOrder.ArithmeticProposition) <=
      relationLength + orderDoubleStepCostEnvelope inputWidth
  dsimp only [termBound] at himplication hrelation hmultipliedCost hfinalCost
  have hsum :
      binaryRelationTransportFullPayloadBound Language.ORing.Rel.lt
          leftProduct rightProduct leftResult rightResult
          (binaryNumeralMultiplicationPayloadPolynomial
            (Nat.size 0 + Nat.size 2))
          (binaryNumeralMultiplicationPayloadPolynomial
            (Nat.size high + Nat.size 2)) +
        (mulLtMulImplicationFullPayloadBound zeroTerm highTerm twoTerm +
          relationLength + zeroLtBinaryTwoPayloadBound + 384 +
          11 * conjunctionSyntaxBudget
            (“!!zeroTerm < !!highTerm” :
              LO.FirstOrder.ArithmeticProposition)
            (“!!paZeroTerm < !!twoTerm” :
              LO.FirstOrder.ArithmeticProposition) +
          34 * modusPonensSyntaxBudget
            ((“!!zeroTerm < !!highTerm” :
                LO.FirstOrder.ArithmeticProposition) ⋏
              (“!!paZeroTerm < !!twoTerm” :
                LO.FirstOrder.ArithmeticProposition))
            (“!!zeroTerm * !!twoTerm < !!highTerm * !!twoTerm” :
              LO.FirstOrder.ArithmeticProposition)) + 240 +
        34 * modusPonensSyntaxBudget
          (“!!leftProduct < !!rightProduct” :
            LO.FirstOrder.ArithmeticProposition)
          (“!!leftResult < !!rightResult” :
            LO.FirstOrder.ArithmeticProposition) <=
        relationLength + zeroLtBinaryTwoPayloadBound +
          2 * cumulativeBinaryMultiplicationPayloadPolynomial
            (inputWidth + 2) +
          8 * orderPrimitiveCostEnvelope
            (orderDoubleTermCodeEnvelope inputWidth) := by
    omega
  exact hsum.trans (by
    unfold orderDoubleStepCostEnvelope
    omega)

/-! ## Linear binary recursion and the public polynomial -/

def positiveBinaryLocalCostEnvelope (inputWidth : Nat) : Nat :=
  orderDoubleStepCostEnvelope inputWidth +
    zeroLtBinaryOnePayloadBound +
    4 * orderStepCostEnvelope (2 * inputWidth + 1) + 1

theorem positiveBinaryNumeralPayloadBound_bit_le_local
    (bit : Bool) (high inputWidth : Nat)
    (hcanonical : high = 0 → bit = true)
    (hhighNonzero : high ≠ 0)
    (hhighSize : Nat.size high <= inputWidth) :
    positiveBinaryNumeralPayloadBound (Nat.bit bit high) <=
      positiveBinaryNumeralPayloadBound high +
        positiveBinaryLocalCostEnvelope inputWidth := by
  let localWidth := 2 * inputWidth + 1
  let doubleBound := positiveBinaryDoublePayloadBound high
    (positiveBinaryNumeralPayloadBound high)
  have hdouble := positiveBinaryDoublePayloadBound_le_orderStep
    high (positiveBinaryNumeralPayloadBound high) inputWidth hhighSize
  rw [positiveBinaryNumeralPayloadBound_bit bit high hcanonical]
  rw [if_neg hhighNonzero]
  cases bit with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      unfold positiveBinaryLocalCostEnvelope
      omega
  | true =>
      simp only [if_true]
      have hsizeOne : Nat.size 1 = 1 := by decide
      have hsumSizeRaw := natSize_add_le high high
      have hsumSize : Nat.size (high + high) <= localWidth := by
        unfold localWidth
        omega
      have hadd := binaryNumeralAddLtAddPayloadBound_le_orderStep
        0 1 (high + high) zeroLtBinaryOnePayloadBound localWidth
        (by simp)
        (by rw [hsizeOne]; unfold localWidth; omega)
        hsumSize
      let workWidth := orderTermWorkWidth localWidth
      let termBound := orderTermCodeEnvelope localWidth
      let zeroTerm := shortBinaryNumeralTerm 0
      let doubleTerm := shortBinaryNumeralTerm (high + high)
      let oddTerm := shortBinaryNumeralTerm (1 + (high + high))
      have hzeroSize : Nat.size 0 <= workWidth := by
        simp [workWidth, orderTermWorkWidth]
      have hdoubleSize : Nat.size (high + high) <= workWidth := by
        unfold workWidth orderTermWorkWidth
        omega
      have hoddSizeRaw := natSize_add_le 1 (high + high)
      have hoddSize : Nat.size (1 + (high + high)) <= workWidth := by
        rw [hsizeOne] at hoddSizeRaw
        unfold workWidth orderTermWorkWidth localWidth
        omega
      have hzeroGenerated : PACompilerGeneratedTerm workWidth 1 zeroTerm :=
        .numeral 0 hzeroSize
      have hdoubleGenerated :
          PACompilerGeneratedTerm workWidth 1 doubleTerm :=
        .numeral (high + high) hdoubleSize
      have hoddGenerated : PACompilerGeneratedTerm workWidth 1 oddTerm :=
        .numeral (1 + (high + high)) hoddSize
      have hzeroCode : (binaryTermCode zeroTerm).length <= termBound :=
        generatedTerm_code_length_le_compiler hzeroGenerated (by omega)
      have hdoubleCode : (binaryTermCode doubleTerm).length <= termBound :=
        generatedTerm_code_length_le_compiler hdoubleGenerated (by omega)
      have hoddCode : (binaryTermCode oddTerm).length <= termBound :=
        generatedTerm_code_length_le_compiler hoddGenerated (by omega)
      have htrans := ltTransitivityFullPayloadBound_le_primitive
        zeroTerm doubleTerm oddTerm
        doubleBound
        (binaryNumeralAddLtAddPayloadBound
          0 1 (high + high) zeroLtBinaryOnePayloadBound)
        termBound hzeroCode hdoubleCode hoddCode
      have hprimitive : orderPrimitiveCostEnvelope termBound <=
          orderStepCostEnvelope localWidth := by
        dsimp only [termBound]
        unfold orderStepCostEnvelope
        omega
      have haddPublic :
          binaryNumeralAddLtAddPayloadBound
              0 1 (high + high) zeroLtBinaryOnePayloadBound <=
            zeroLtBinaryOnePayloadBound +
              orderStepCostEnvelope (2 * inputWidth + 1) := by
        simpa [localWidth] using hadd
      have hprimitivePublic :
          orderPrimitiveCostEnvelope termBound <=
            orderStepCostEnvelope (2 * inputWidth + 1) := by
        simpa [localWidth] using hprimitive
      have htransPublic :
          ltTransitivityFullPayloadBound
              (shortBinaryNumeralTerm 0)
              (shortBinaryNumeralTerm (high + high))
              (shortBinaryNumeralTerm (1 + (high + high)))
              (positiveBinaryDoublePayloadBound high
                (positiveBinaryNumeralPayloadBound high))
              (binaryNumeralAddLtAddPayloadBound
                0 1 (high + high) zeroLtBinaryOnePayloadBound) <=
            positiveBinaryDoublePayloadBound high
                (positiveBinaryNumeralPayloadBound high) +
              binaryNumeralAddLtAddPayloadBound
                0 1 (high + high) zeroLtBinaryOnePayloadBound +
              orderPrimitiveCostEnvelope termBound := by
        simpa [zeroTerm, doubleTerm, oddTerm, doubleBound] using htrans
      unfold positiveBinaryLocalCostEnvelope
      omega

def positiveBinaryNumeralPayloadPolynomial (inputWidth : Nat) : Nat :=
  zeroLtBinaryOnePayloadBound +
    inputWidth * positiveBinaryLocalCostEnvelope inputWidth

theorem positiveBinaryNumeralPayloadBound_le_external
    (value inputWidth : Nat)
    (hsize : Nat.size value <= inputWidth) :
    positiveBinaryNumeralPayloadBound value <=
      zeroLtBinaryOnePayloadBound +
        Nat.size value * positiveBinaryLocalCostEnvelope inputWidth := by
  induction value using Nat.binaryRec' with
  | zero =>
      simp [positiveBinaryNumeralPayloadBound]
  | bit bit high hcanonical ih =>
      have hvalueNonzero : Nat.bit bit high ≠ 0 :=
        Nat.bit_ne_zero_iff.mpr hcanonical
      have hsizeEq : Nat.size (Nat.bit bit high) = Nat.size high + 1 :=
        Nat.size_bit hvalueNonzero
      by_cases hhigh : high = 0
      · rw [positiveBinaryNumeralPayloadBound_bit bit high hcanonical]
        rw [if_pos hhigh]
        omega
      · have hhighSize : Nat.size high <= inputWidth := by omega
        have hrecursive := ih hhighSize
        have hstep := positiveBinaryNumeralPayloadBound_bit_le_local
          bit high inputWidth hcanonical hhigh hhighSize
        rw [hsizeEq]
        calc
          positiveBinaryNumeralPayloadBound (Nat.bit bit high) <=
              positiveBinaryNumeralPayloadBound high +
                positiveBinaryLocalCostEnvelope inputWidth := hstep
          _ <= (zeroLtBinaryOnePayloadBound +
                Nat.size high * positiveBinaryLocalCostEnvelope inputWidth) +
              positiveBinaryLocalCostEnvelope inputWidth :=
            Nat.add_le_add_right hrecursive _
          _ = zeroLtBinaryOnePayloadBound +
              (Nat.size high + 1) *
                positiveBinaryLocalCostEnvelope inputWidth := by ring

theorem positiveBinaryNumeralPayloadBound_le_polynomial
    (value : Nat) :
    positiveBinaryNumeralPayloadBound value <=
      positiveBinaryNumeralPayloadPolynomial (Nat.size value) := by
  simpa [positiveBinaryNumeralPayloadPolynomial] using
    positiveBinaryNumeralPayloadBound_le_external
      value (Nat.size value) le_rfl

theorem provePositiveBinaryNumeral_payloadLength_le_polynomial
    (value : Nat) (hpositive : 0 < value) :
    (provePositiveBinaryNumeral value hpositive).payloadLength <=
      positiveBinaryNumeralPayloadPolynomial (Nat.size value) :=
  (provePositiveBinaryNumeral_payloadLength_le value hpositive).trans
    (positiveBinaryNumeralPayloadBound_le_polynomial value)

theorem provePositiveBinaryNumeral_payloadLength_le_width
    (value inputWidth : Nat) (hpositive : 0 < value)
    (hsize : Nat.size value <= inputWidth) :
    (provePositiveBinaryNumeral value hpositive).payloadLength <=
      positiveBinaryNumeralPayloadPolynomial inputWidth := by
  calc
    (provePositiveBinaryNumeral value hpositive).payloadLength <=
        positiveBinaryNumeralPayloadBound value :=
      provePositiveBinaryNumeral_payloadLength_le value hpositive
    _ <= zeroLtBinaryOnePayloadBound +
          Nat.size value * positiveBinaryLocalCostEnvelope inputWidth :=
      positiveBinaryNumeralPayloadBound_le_external value inputWidth hsize
    _ <= zeroLtBinaryOnePayloadBound +
          inputWidth * positiveBinaryLocalCostEnvelope inputWidth := by
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_right (positiveBinaryLocalCostEnvelope inputWidth) hsize)
        zeroLtBinaryOnePayloadBound
    _ = positiveBinaryNumeralPayloadPolynomial inputWidth := by
      rfl

#print axioms instantiatedUniversalBody_code_le_next
#print axioms relationAfterLeftSecondMatrix_code_le_stage3
#print axioms specializationCost_le_orderEnvelope
#print axioms lessThanFormula_code_length_le
#print axioms relationCongruenceConclusion_code_le_derived
#print axioms positiveBinaryNumeralPayloadBound_le_polynomial
#print axioms provePositiveBinaryNumeral_payloadLength_le_polynomial
#print axioms provePositiveBinaryNumeral_payloadLength_le_width

end FoundationCompactPAQuantitativeOrderBounds
