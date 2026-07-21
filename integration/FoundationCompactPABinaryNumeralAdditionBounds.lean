import integration.FoundationCompactPABinaryNumeralAddition

/-!
# Polynomial payload bound for the binary-numeral addition compiler

This module is the quantitative half of the proof-producing addition
compiler.  It derives a closed polynomial bound from the concrete syntax
encoders and the checked payload inequalities of the PA proof constructors.
No proof-length oracle or assumed compiler bound is used.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABinaryNumeralAdditionBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAAxiomCertificate
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeEqualityTransitivity
open FoundationCompactPAQuantitativeFunctionCongruence
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactCertifiedModusPonens
open FoundationCompactCertifiedConjunction

def binaryFunctionTermCodeOverhead
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2) : Nat :=
  2 * (binaryNatCode 2).length +
    (binaryNatCode (Encodable.encode functionSymbol)).length

theorem paAddTerm_code_length_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryTermCode (paAddTerm left right)).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        binaryFunctionTermCodeOverhead Language.Add.add := by
  simp [paAddTerm, Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Matrix.fun_eq_vec_two, binaryTermCode,
    binaryFunctionTermCodeOverhead]
  omega

theorem paMulTerm_code_length_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryTermCode (paMulTerm left right)).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        binaryFunctionTermCodeOverhead Language.Mul.mul := by
  simp [paMulTerm, Semiterm.Operator.operator,
    Semiterm.Operator.Mul.term_eq, Matrix.fun_eq_vec_two, binaryTermCode,
    binaryFunctionTermCodeOverhead]
  omega

def equalityFormulaCodeOverhead : Nat :=
  (binaryNatCode 0).length + (binaryNatCode 2).length +
    (binaryNatCode (Encodable.encode
      (Language.Eq.eq : LO.FirstOrder.Language.Rel ℒₒᵣ 2))).length

theorem equalityFormula_code_length_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryFormulaCode
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        equalityFormulaCodeOverhead := by
  simp [Semiformula.Operator.operator, Semiformula.Operator.Eq.sentence_eq,
    Matrix.fun_eq_vec_two, binaryFormulaCode, equalityFormulaCodeOverhead]
  omega

theorem binaryFormulaCode_or_length_le_local
    (left right : LO.FirstOrder.ArithmeticProposition) :
    (binaryFormulaCode (left ⋎ right)).length <=
      (binaryFormulaCode left).length +
        (binaryFormulaCode right).length + (binaryNatCode 5).length := by
  simp [binaryFormulaCode]
  omega

theorem binaryFormulaCode_and_length_le_local
    (left right : LO.FirstOrder.ArithmeticProposition) :
    (binaryFormulaCode (left ⋏ right)).length <=
      (binaryFormulaCode left).length +
        (binaryFormulaCode right).length + (binaryNatCode 4).length := by
  simp [binaryFormulaCode]
  omega

theorem binaryFormulaCode_all_body_le
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaCode body).length <=
      (binaryFormulaCode (∀⁰ body)).length := by
  simp [binaryFormulaCode]

theorem binaryFormulaCode_implication_length_le
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition) :
    (binaryFormulaCode (antecedent 🡒 consequent)).length <=
      2 * (binaryFormulaCode antecedent).length +
        (binaryFormulaCode consequent).length + (binaryNatCode 5).length := by
  have hneg := binaryFormulaCode_neg_length_le antecedent
  have hor := binaryFormulaCode_or_length_le_local
    (∼antecedent) consequent
  have hformula : antecedent 🡒 consequent = (∼antecedent) ⋎ consequent := by
    simp [DeMorgan.imply]
  rw [hformula]
  omega

/-- Closed code budget for every universal axiom matrix used by the addition
compiler.  It is a computable constant, not an input proof length. -/
def fixedPAFormulaSeed : Nat :=
  (binaryFormulaCode
      (⊤ : LO.FirstOrder.ArithmeticProposition)).length +
  binaryFunctionTermCodeOverhead Language.Add.add +
  binaryFunctionTermCodeOverhead Language.Mul.mul +
  (binaryFormulaCode equalityReflexivityBody).length +
  (binaryFormulaCode equalitySymmetryOuterBody).length +
  (binaryFormulaCode equalityTransitivityOuterBody).length +
  (binaryFormulaCode
    (binaryFunctionExtOuterBody Language.Add.add)).length +
  (binaryFormulaCode
    (binaryFunctionExtOuterBody Language.Mul.mul)).length +
  (binaryFormulaCode addZeroBody).length +
  (binaryFormulaCode mulZeroBody).length +
  (binaryFormulaCode mulOneBody).length +
  (binaryFormulaCode addCommutativityOuterBody).length +
  (binaryFormulaCode addAssociativityOuterBody).length +
  (binaryFormulaCode leftDistributivityOuterBody).length + 1

def substitutionFormulaCodeEnvelope
    (formulaBound witnessBound : Nat) : Nat :=
  3 * (formulaBound + 1) * (witnessBound + 1) * formulaBound

def instantiatedFormulaStage0 : Nat := fixedPAFormulaSeed

def instantiatedFormulaStage1 (witnessBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope instantiatedFormulaStage0 witnessBound

def instantiatedFormulaStage2 (witnessBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope
    (instantiatedFormulaStage1 witnessBound) witnessBound

def instantiatedFormulaStage3 (witnessBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope
    (instantiatedFormulaStage2 witnessBound) witnessBound

def instantiatedFormulaStage4 (witnessBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope
    (instantiatedFormulaStage3 witnessBound) witnessBound

/-- A single nonrecursive polynomial expression dominating all formula codes
encountered during at most four universal instantiations. -/
def instantiatedFormulaCodeEnvelope (witnessBound : Nat) : Nat :=
  instantiatedFormulaStage0 + instantiatedFormulaStage1 witnessBound +
    instantiatedFormulaStage2 witnessBound +
    instantiatedFormulaStage3 witnessBound +
    instantiatedFormulaStage4 witnessBound + 1

theorem binaryFormulaCode_substitution_one_length_le_envelope
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (formulaBound witnessBound : Nat)
    (hformula : (binaryFormulaCode formula).length <= formulaBound)
    (hwitness : (binaryTermCode witness).length <= witnessBound) :
    (binaryFormulaCode (formula/[witness])).length <=
      substitutionFormulaCodeEnvelope formulaBound witnessBound := by
  have hraw := binaryFormulaCode_substitution_one_length_le formula witness
  calc
    (binaryFormulaCode (formula/[witness])).length <=
        3 * ((binaryFormulaCode formula).length + 1) *
          ((binaryTermCode witness).length + 1) *
          (binaryFormulaCode formula).length := hraw
    _ <= 3 * (formulaBound + 1) * (witnessBound + 1) *
        formulaBound := by
      gcongr
    _ = substitutionFormulaCodeEnvelope formulaBound witnessBound := by
      rfl

theorem instantiatedBodyCode_le_nextStage
    (formula body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (formulaBound witnessBound : Nat)
    (hformula : (binaryFormulaCode formula).length <= formulaBound)
    (hwitness : (binaryTermCode witness).length <= witnessBound)
    (hresult : formula/[witness] = ∀⁰ body) :
    (binaryFormulaCode body).length <=
      substitutionFormulaCodeEnvelope formulaBound witnessBound := by
  have hsubstitution :=
    binaryFormulaCode_substitution_one_length_le_envelope
      formula witness formulaBound witnessBound hformula hwitness
  rw [hresult] at hsubstitution
  exact (binaryFormulaCode_all_body_le body).trans hsubstitution

theorem fixedFormulaCode_le_seed
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hformula :
      formula = equalityReflexivityBody ∨
      formula = equalitySymmetryOuterBody ∨
      formula = equalityTransitivityOuterBody ∨
      formula = binaryFunctionExtOuterBody Language.Add.add ∨
      formula = binaryFunctionExtOuterBody Language.Mul.mul ∨
      formula = addZeroBody ∨ formula = mulZeroBody ∨
      formula = mulOneBody ∨ formula = addCommutativityOuterBody ∨
      formula = addAssociativityOuterBody ∨
      formula = leftDistributivityOuterBody) :
    (binaryFormulaCode formula).length <= fixedPAFormulaSeed := by
  rcases hformula with h | h | h | h | h | h | h | h | h | h | h <;>
    subst formula <;> simp [fixedPAFormulaSeed] <;> omega

theorem instantiatedFormulaStage0_le_envelope (witnessBound : Nat) :
    instantiatedFormulaStage0 <=
      instantiatedFormulaCodeEnvelope witnessBound := by
  simp [instantiatedFormulaCodeEnvelope]
  omega

theorem instantiatedFormulaStage1_le_envelope (witnessBound : Nat) :
    instantiatedFormulaStage1 witnessBound <=
      instantiatedFormulaCodeEnvelope witnessBound := by
  simp [instantiatedFormulaCodeEnvelope]
  omega

theorem instantiatedFormulaStage2_le_envelope (witnessBound : Nat) :
    instantiatedFormulaStage2 witnessBound <=
      instantiatedFormulaCodeEnvelope witnessBound := by
  simp [instantiatedFormulaCodeEnvelope]
  omega

theorem instantiatedFormulaStage3_le_envelope (witnessBound : Nat) :
    instantiatedFormulaStage3 witnessBound <=
      instantiatedFormulaCodeEnvelope witnessBound := by
  simp [instantiatedFormulaCodeEnvelope]
  omega

theorem instantiatedFormulaStage4_le_envelope (witnessBound : Nat) :
    instantiatedFormulaStage4 witnessBound <=
      instantiatedFormulaCodeEnvelope witnessBound := by
  simp [instantiatedFormulaCodeEnvelope]
  omega

theorem equalitySymmetryInnerBody_code_le_stage1
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) (witnessBound : Nat)
    (hleft : (binaryTermCode left).length <= witnessBound) :
    (binaryFormulaCode (equalitySymmetryInnerBody left)).length <=
      instantiatedFormulaStage1 witnessBound := by
  exact instantiatedBodyCode_le_nextStage
    equalitySymmetryOuterBody (equalitySymmetryInnerBody left) left
    instantiatedFormulaStage0 witnessBound
    (fixedFormulaCode_le_seed equalitySymmetryOuterBody (by simp))
    hleft (equalitySymmetryAfterFirst_formula left)

theorem equalityTransitivityMiddleBody_code_le_stage1
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) (witnessBound : Nat)
    (hleft : (binaryTermCode left).length <= witnessBound) :
    (binaryFormulaCode (equalityTransitivityMiddleBody left)).length <=
      instantiatedFormulaStage1 witnessBound := by
  exact instantiatedBodyCode_le_nextStage
    equalityTransitivityOuterBody (equalityTransitivityMiddleBody left) left
    instantiatedFormulaStage0 witnessBound
    (fixedFormulaCode_le_seed equalityTransitivityOuterBody (by simp))
    hleft (equalityTransitivityAfterFirst_formula left)

theorem equalityTransitivityInnerBody_code_le_stage2
    (left middle : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (witnessBound : Nat)
    (hleft : (binaryTermCode left).length <= witnessBound)
    (hmiddle : (binaryTermCode middle).length <= witnessBound) :
    (binaryFormulaCode
      (equalityTransitivityInnerBody left middle)).length <=
      instantiatedFormulaStage2 witnessBound := by
  exact instantiatedBodyCode_le_nextStage
    (equalityTransitivityMiddleBody left)
    (equalityTransitivityInnerBody left middle) middle
    (instantiatedFormulaStage1 witnessBound) witnessBound
    (equalityTransitivityMiddleBody_code_le_stage1 left witnessBound hleft)
    hmiddle (equalityTransitivityAfterSecond_formula left middle)

theorem addCommutativityInnerBody_code_le_stage1
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) (witnessBound : Nat)
    (hleft : (binaryTermCode left).length <= witnessBound) :
    (binaryFormulaCode (addCommutativityInnerBody left)).length <=
      instantiatedFormulaStage1 witnessBound := by
  exact instantiatedBodyCode_le_nextStage
    addCommutativityOuterBody (addCommutativityInnerBody left) left
    instantiatedFormulaStage0 witnessBound
    (fixedFormulaCode_le_seed addCommutativityOuterBody (by simp))
    hleft (addCommutativityAfterFirst_formula left)

theorem addAssociativityMiddleBody_code_le_stage1
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) (witnessBound : Nat)
    (hleft : (binaryTermCode left).length <= witnessBound) :
    (binaryFormulaCode (addAssociativityMiddleBody left)).length <=
      instantiatedFormulaStage1 witnessBound := by
  exact instantiatedBodyCode_le_nextStage
    addAssociativityOuterBody (addAssociativityMiddleBody left) left
    instantiatedFormulaStage0 witnessBound
    (fixedFormulaCode_le_seed addAssociativityOuterBody (by simp))
    hleft (addAssociativityAfterFirst_formula left)

theorem addAssociativityInnerBody_code_le_stage2
    (left middle : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (witnessBound : Nat)
    (hleft : (binaryTermCode left).length <= witnessBound)
    (hmiddle : (binaryTermCode middle).length <= witnessBound) :
    (binaryFormulaCode (addAssociativityInnerBody left middle)).length <=
      instantiatedFormulaStage2 witnessBound := by
  exact instantiatedBodyCode_le_nextStage
    (addAssociativityMiddleBody left)
    (addAssociativityInnerBody left middle) middle
    (instantiatedFormulaStage1 witnessBound) witnessBound
    (addAssociativityMiddleBody_code_le_stage1 left witnessBound hleft)
    hmiddle (addAssociativityAfterSecond_formula left middle)

theorem leftDistributivityMiddleBody_code_le_stage1
    (factor : LO.FirstOrder.ArithmeticSemiterm Nat 0) (witnessBound : Nat)
    (hfactor : (binaryTermCode factor).length <= witnessBound) :
    (binaryFormulaCode (leftDistributivityMiddleBody factor)).length <=
      instantiatedFormulaStage1 witnessBound := by
  exact instantiatedBodyCode_le_nextStage
    leftDistributivityOuterBody (leftDistributivityMiddleBody factor) factor
    instantiatedFormulaStage0 witnessBound
    (fixedFormulaCode_le_seed leftDistributivityOuterBody (by simp))
    hfactor (leftDistributivityAfterFirst_formula factor)

theorem leftDistributivityInnerBody_code_le_stage2
    (factor left : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (witnessBound : Nat)
    (hfactor : (binaryTermCode factor).length <= witnessBound)
    (hleft : (binaryTermCode left).length <= witnessBound) :
    (binaryFormulaCode (leftDistributivityInnerBody factor left)).length <=
      instantiatedFormulaStage2 witnessBound := by
  exact instantiatedBodyCode_le_nextStage
    (leftDistributivityMiddleBody factor)
    (leftDistributivityInnerBody factor left) left
    (instantiatedFormulaStage1 witnessBound) witnessBound
    (leftDistributivityMiddleBody_code_le_stage1 factor witnessBound hfactor)
    hleft (leftDistributivityAfterSecond_formula factor left)

theorem binaryFunctionExtRightFirstBody_code_le_stage1
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (witnessBound : Nat)
    (hfunction : functionSymbol = Language.Add.add ∨
      functionSymbol = Language.Mul.mul)
    (hrightSecond : (binaryTermCode rightSecond).length <= witnessBound) :
    (binaryFormulaCode
      (binaryFunctionExtRightFirstBody functionSymbol rightSecond)).length <=
      instantiatedFormulaStage1 witnessBound := by
  have hseed :
      (binaryFormulaCode
        (binaryFunctionExtOuterBody functionSymbol)).length <=
        instantiatedFormulaStage0 := by
    rcases hfunction with h | h <;> subst functionSymbol
    · exact fixedFormulaCode_le_seed
        (binaryFunctionExtOuterBody Language.Add.add) (by simp)
    · exact fixedFormulaCode_le_seed
        (binaryFunctionExtOuterBody Language.Mul.mul) (by simp)
  exact instantiatedBodyCode_le_nextStage
    (binaryFunctionExtOuterBody functionSymbol)
    (binaryFunctionExtRightFirstBody functionSymbol rightSecond)
    rightSecond instantiatedFormulaStage0 witnessBound hseed hrightSecond
    (binaryFunctionExtAfterRightSecond_formula functionSymbol rightSecond)

theorem binaryFunctionExtLeftSecondBody_code_le_stage2
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (rightFirst rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (witnessBound : Nat)
    (hfunction : functionSymbol = Language.Add.add ∨
      functionSymbol = Language.Mul.mul)
    (hrightFirst : (binaryTermCode rightFirst).length <= witnessBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= witnessBound) :
    (binaryFormulaCode
      (binaryFunctionExtLeftSecondBody functionSymbol
        rightFirst rightSecond)).length <=
      instantiatedFormulaStage2 witnessBound := by
  exact instantiatedBodyCode_le_nextStage
    (binaryFunctionExtRightFirstBody functionSymbol rightSecond)
    (binaryFunctionExtLeftSecondBody functionSymbol rightFirst rightSecond)
    rightFirst (instantiatedFormulaStage1 witnessBound) witnessBound
    (binaryFunctionExtRightFirstBody_code_le_stage1 functionSymbol
      rightSecond witnessBound hfunction hrightSecond)
    hrightFirst
    (binaryFunctionExtAfterRightFirst_formula functionSymbol
      rightFirst rightSecond)

theorem binaryFunctionExtAfterLeftSecondMatrix_code_le_stage3
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (witnessBound : Nat)
    (hfunction : functionSymbol = Language.Add.add ∨
      functionSymbol = Language.Mul.mul)
    (hleftSecond : (binaryTermCode leftSecond).length <= witnessBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= witnessBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= witnessBound) :
    (binaryFormulaCode
      (binaryFunctionExtAfterLeftSecondMatrix functionSymbol
        leftSecond rightFirst rightSecond)).length <=
      instantiatedFormulaStage3 witnessBound := by
  exact instantiatedBodyCode_le_nextStage
    (binaryFunctionExtLeftSecondBody functionSymbol rightFirst rightSecond)
    (binaryFunctionExtAfterLeftSecondMatrix functionSymbol
      leftSecond rightFirst rightSecond)
    leftSecond (instantiatedFormulaStage2 witnessBound) witnessBound
    (binaryFunctionExtLeftSecondBody_code_le_stage2 functionSymbol
      rightFirst rightSecond witnessBound hfunction
      hrightFirst hrightSecond)
    hleftSecond
    (binaryFunctionExtAfterLeftSecond_formula functionSymbol
      leftSecond rightFirst rightSecond)

def paSpecializationScaleEnvelope (witnessBound : Nat) : Nat :=
  instantiatedFormulaCodeEnvelope witnessBound + witnessBound + 1

def paSpecializationCostEnvelope (witnessBound : Nat) : Nat :=
  192 + 2048 * paSpecializationScaleEnvelope witnessBound *
    paSpecializationScaleEnvelope witnessBound *
    paSpecializationScaleEnvelope witnessBound

theorem specializationCost_le_paEnvelope
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (witnessBound : Nat)
    (hformula : (binaryFormulaCode formula).length <=
      instantiatedFormulaCodeEnvelope witnessBound)
    (hwitness : (binaryTermCode witness).length <= witnessBound) :
    specializationCost formula witness <=
      paSpecializationCostEnvelope witnessBound := by
  have hscale : specializationScale formula witness <=
      paSpecializationScaleEnvelope witnessBound := by
    simp [specializationScale, paSpecializationScaleEnvelope]
    omega
  simp only [specializationCost, paSpecializationCostEnvelope]
  gcongr

def paEqualityFormulaCodeEnvelope (termBound : Nat) : Nat :=
  2 * termBound + equalityFormulaCodeOverhead

def paFormulaCodeEnvelope (termBound : Nat) : Nat :=
  instantiatedFormulaCodeEnvelope termBound +
    paEqualityFormulaCodeEnvelope termBound + 1

theorem equalityFormula_code_length_le_paEnvelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (binaryFormulaCode
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)).length <=
      paFormulaCodeEnvelope termBound := by
  have heq := equalityFormula_code_length_le left right
  simp [paFormulaCodeEnvelope, paEqualityFormulaCodeEnvelope]
  omega

def paAssemblySyntaxEnvelope (formulaBound : Nat) : Nat :=
  64 * (formulaBound + (binaryNatCode 4).length +
    (binaryNatCode 5).length + 1)

theorem conjunctionSyntaxBudget_le_paAssemblyEnvelope
    (left right : LO.FirstOrder.ArithmeticProposition)
    (formulaBound : Nat)
    (hleft : (binaryFormulaCode left).length <= formulaBound)
    (hright : (binaryFormulaCode right).length <= formulaBound) :
    conjunctionSyntaxBudget left right <=
      paAssemblySyntaxEnvelope formulaBound := by
  have hand := binaryFormulaCode_and_length_le_local left right
  simp only [conjunctionSyntaxBudget, paAssemblySyntaxEnvelope]
  omega

theorem modusPonensSyntaxBudget_le_paAssemblyEnvelope
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (formulaBound : Nat)
    (hantecedent : (binaryFormulaCode antecedent).length <= formulaBound)
    (hconsequent : (binaryFormulaCode consequent).length <= formulaBound) :
    modusPonensSyntaxBudget antecedent consequent <=
      paAssemblySyntaxEnvelope formulaBound := by
  let implication := antecedent 🡒 consequent
  have himplication :=
    binaryFormulaCode_implication_length_le antecedent consequent
  have hnegImplication := binaryFormulaCode_neg_length_le implication
  have hnegConsequent := binaryFormulaCode_neg_length_le consequent
  have hand := binaryFormulaCode_and_length_le_local
    antecedent (∼consequent)
  simp only [modusPonensSyntaxBudget, paAssemblySyntaxEnvelope]
  dsimp only [implication] at hnegImplication
  omega

theorem transportedCertifiedPAProof_payloadLength
    {source target : LO.FirstOrder.ArithmeticProposition}
    (formulaEq : source = target)
    (typeEq : CertifiedPAProof source = CertifiedPAProof target)
    (proof : CertifiedPAProof source) :
    ((_root_.cast typeEq proof : CertifiedPAProof target).payloadLength) =
      proof.payloadLength := by
  subst target
  have hproofIrrelevance : typeEq = rfl := Subsingleton.elim _ _
  rw [hproofIrrelevance]
  rfl

theorem equalityReflexivityAxiomProof_payloadLength_le_explicit :
    equalityReflexivityAxiomProof.payloadLength <=
      32 + 10 * axiomSyntaxBudget .eqRefl := by
  have heq : equalityReflexivityAxiomProof.payloadLength =
      (ofAxiom PAAxiomCertificate.eqRefl).payloadLength := by
    unfold equalityReflexivityAxiomProof
    apply transportedCertifiedPAProof_payloadLength
      (by simp [equalityReflexivityBody, PAAxiomCertificate.sentence])
  rw [heq]
  exact ofAxiom_payloadLength_le PAAxiomCertificate.eqRefl

theorem equalitySymmetryAxiomProof_payloadLength_le_explicit :
    equalitySymmetryAxiomProof.payloadLength <=
      32 + 10 * axiomSyntaxBudget .eqSymm := by
  have heq : equalitySymmetryAxiomProof.payloadLength =
      (ofAxiom PAAxiomCertificate.eqSymm).payloadLength := by
    unfold equalitySymmetryAxiomProof
    apply transportedCertifiedPAProof_payloadLength
      (by simp [equalitySymmetryOuterBody, PAAxiomCertificate.sentence])
  rw [heq]
  exact ofAxiom_payloadLength_le PAAxiomCertificate.eqSymm

theorem equalityTransitivityAxiomProof_payloadLength_le_explicit :
    equalityTransitivityAxiomProof.payloadLength <=
      32 + 10 * axiomSyntaxBudget .eqTrans := by
  have heq : equalityTransitivityAxiomProof.payloadLength =
      (ofAxiom PAAxiomCertificate.eqTrans).payloadLength := by
    unfold equalityTransitivityAxiomProof
    apply transportedCertifiedPAProof_payloadLength
      (by simp [equalityTransitivityOuterBody,
        PAAxiomCertificate.sentence])
  rw [heq]
  exact ofAxiom_payloadLength_le PAAxiomCertificate.eqTrans

theorem addZeroAxiomProof_payloadLength_le_explicit :
    addZeroAxiomProof.payloadLength <=
      32 + 10 * axiomSyntaxBudget .addZero := by
  have heq : addZeroAxiomProof.payloadLength =
      (ofAxiom PAAxiomCertificate.addZero).payloadLength := by
    unfold addZeroAxiomProof
    apply transportedCertifiedPAProof_payloadLength
      (by simp [addZeroBody, PAAxiomCertificate.sentence])
  rw [heq]
  exact ofAxiom_payloadLength_le PAAxiomCertificate.addZero

theorem mulZeroAxiomProof_payloadLength_le_explicit :
    mulZeroAxiomProof.payloadLength <=
      32 + 10 * axiomSyntaxBudget .mulZero := by
  have heq : mulZeroAxiomProof.payloadLength =
      (ofAxiom PAAxiomCertificate.mulZero).payloadLength := by
    unfold mulZeroAxiomProof
    apply transportedCertifiedPAProof_payloadLength
      (by simp [mulZeroBody, PAAxiomCertificate.sentence])
  rw [heq]
  exact ofAxiom_payloadLength_le PAAxiomCertificate.mulZero

theorem mulOneAxiomProof_payloadLength_le_explicit :
    mulOneAxiomProof.payloadLength <=
      32 + 10 * axiomSyntaxBudget .mulOne := by
  have heq : mulOneAxiomProof.payloadLength =
      (ofAxiom PAAxiomCertificate.mulOne).payloadLength := by
    unfold mulOneAxiomProof
    apply transportedCertifiedPAProof_payloadLength
      (by simp [mulOneBody, PAAxiomCertificate.sentence])
  rw [heq]
  exact ofAxiom_payloadLength_le PAAxiomCertificate.mulOne

/-- Sum of explicit one-node axiom and truth-proof bounds.  This is a closed,
executable natural-number constant. -/
def fixedPAPayloadEnvelope : Nat :=
  (32 + 10 * axiomSyntaxBudget .eqRefl) +
  (32 + 10 * axiomSyntaxBudget .eqSymm) +
  (32 + 10 * axiomSyntaxBudget .eqTrans) +
  (32 + 10 * axiomSyntaxBudget (.eqFuncExt Language.Add.add)) +
  (32 + 10 * axiomSyntaxBudget (.eqFuncExt Language.Mul.mul)) +
  (32 + 10 * axiomSyntaxBudget .addZero) +
  (32 + 10 * axiomSyntaxBudget .mulZero) +
  (32 + 10 * axiomSyntaxBudget .mulOne) +
  (32 + 10 * axiomSyntaxBudget .addComm) +
  (32 + 10 * axiomSyntaxBudget .addAssoc) +
  (32 + 10 * axiomSyntaxBudget .distr) +
  (48 + 9 * verumSyntaxBudget) + 1

def paDerivedFormulaCodeEnvelope (termBound : Nat) : Nat :=
  paAssemblySyntaxEnvelope (paFormulaCodeEnvelope termBound)

def paLocalAssemblyCostEnvelope (termBound : Nat) : Nat :=
  paAssemblySyntaxEnvelope (paDerivedFormulaCodeEnvelope termBound)

def paPrimitiveAssemblyCostEnvelope (termBound : Nat) : Nat :=
  paAssemblySyntaxEnvelope (paLocalAssemblyCostEnvelope termBound)

/-- Uniform local cost of one algebraic PA compiler primitive.  Every
component is a fixed polynomial expression in the honest term-code bound. -/
def paPrimitiveCostEnvelope (termBound : Nat) : Nat :=
  4 * fixedPAPayloadEnvelope +
    8 * paSpecializationCostEnvelope termBound + 1024 +
    256 * paLocalAssemblyCostEnvelope termBound +
    256 * paPrimitiveAssemblyCostEnvelope termBound

theorem equalityReflexivityAxiomProof_payloadLength_le_fixed :
    equalityReflexivityAxiomProof.payloadLength <=
      fixedPAPayloadEnvelope := by
  calc
    equalityReflexivityAxiomProof.payloadLength <=
        32 + 10 * axiomSyntaxBudget .eqRefl :=
      equalityReflexivityAxiomProof_payloadLength_le_explicit
    _ <= fixedPAPayloadEnvelope := by
      unfold fixedPAPayloadEnvelope
      omega

theorem equalitySymmetryAxiomProof_payloadLength_le_fixed :
    equalitySymmetryAxiomProof.payloadLength <=
      fixedPAPayloadEnvelope := by
  calc
    equalitySymmetryAxiomProof.payloadLength <=
        32 + 10 * axiomSyntaxBudget .eqSymm :=
      equalitySymmetryAxiomProof_payloadLength_le_explicit
    _ <= fixedPAPayloadEnvelope := by
      unfold fixedPAPayloadEnvelope
      omega

theorem equalityTransitivityAxiomProof_payloadLength_le_fixed :
    equalityTransitivityAxiomProof.payloadLength <=
      fixedPAPayloadEnvelope := by
  calc
    equalityTransitivityAxiomProof.payloadLength <=
        32 + 10 * axiomSyntaxBudget .eqTrans :=
      equalityTransitivityAxiomProof_payloadLength_le_explicit
    _ <= fixedPAPayloadEnvelope := by
      unfold fixedPAPayloadEnvelope
      omega

theorem binaryFunctionExtAxiomProof_payloadLength_le_fixed
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (hfunction : functionSymbol = Language.Add.add ∨
      functionSymbol = Language.Mul.mul) :
    (binaryFunctionExtAxiomProof functionSymbol).payloadLength <=
      fixedPAPayloadEnvelope := by
  rcases hfunction with hAdd | hMul
  · subst functionSymbol
    calc
      (binaryFunctionExtAxiomProof Language.Add.add).payloadLength <=
          32 + 10 * axiomSyntaxBudget
            (.eqFuncExt Language.Add.add) :=
        binaryFunctionExtAxiomProof_payloadLength_le Language.Add.add
      _ <= fixedPAPayloadEnvelope := by
        unfold fixedPAPayloadEnvelope
        omega
  · subst functionSymbol
    calc
      (binaryFunctionExtAxiomProof Language.Mul.mul).payloadLength <=
          32 + 10 * axiomSyntaxBudget
            (.eqFuncExt Language.Mul.mul) :=
        binaryFunctionExtAxiomProof_payloadLength_le Language.Mul.mul
      _ <= fixedPAPayloadEnvelope := by
        unfold fixedPAPayloadEnvelope
        omega

theorem addCommutativityAxiomProof_payloadLength_le_fixed :
    addCommutativityAxiomProof.payloadLength <= fixedPAPayloadEnvelope := by
  calc
    addCommutativityAxiomProof.payloadLength <=
        32 + 10 * axiomSyntaxBudget .addComm :=
      addCommutativityAxiomProof_payloadLength_le
    _ <= fixedPAPayloadEnvelope := by
      unfold fixedPAPayloadEnvelope
      omega

theorem addAssociativityAxiomProof_payloadLength_le_fixed :
    addAssociativityAxiomProof.payloadLength <= fixedPAPayloadEnvelope := by
  calc
    addAssociativityAxiomProof.payloadLength <=
        32 + 10 * axiomSyntaxBudget .addAssoc :=
      addAssociativityAxiomProof_payloadLength_le
    _ <= fixedPAPayloadEnvelope := by
      unfold fixedPAPayloadEnvelope
      omega

theorem leftDistributivityAxiomProof_payloadLength_le_fixed :
    leftDistributivityAxiomProof.payloadLength <= fixedPAPayloadEnvelope := by
  calc
    leftDistributivityAxiomProof.payloadLength <=
        32 + 10 * axiomSyntaxBudget .distr :=
      leftDistributivityAxiomProof_payloadLength_le
    _ <= fixedPAPayloadEnvelope := by
      unfold fixedPAPayloadEnvelope
      omega

theorem addZeroAxiomProof_payloadLength_le_fixed :
    addZeroAxiomProof.payloadLength <= fixedPAPayloadEnvelope := by
  calc
    addZeroAxiomProof.payloadLength <=
        32 + 10 * axiomSyntaxBudget .addZero :=
      addZeroAxiomProof_payloadLength_le_explicit
    _ <= fixedPAPayloadEnvelope := by
      unfold fixedPAPayloadEnvelope
      omega

theorem mulZeroAxiomProof_payloadLength_le_fixed :
    mulZeroAxiomProof.payloadLength <= fixedPAPayloadEnvelope := by
  calc
    mulZeroAxiomProof.payloadLength <=
        32 + 10 * axiomSyntaxBudget .mulZero :=
      mulZeroAxiomProof_payloadLength_le_explicit
    _ <= fixedPAPayloadEnvelope := by
      unfold fixedPAPayloadEnvelope
      omega

theorem mulOneAxiomProof_payloadLength_le_fixed :
    mulOneAxiomProof.payloadLength <= fixedPAPayloadEnvelope := by
  calc
    mulOneAxiomProof.payloadLength <=
        32 + 10 * axiomSyntaxBudget .mulOne :=
      mulOneAxiomProof_payloadLength_le_explicit
    _ <= fixedPAPayloadEnvelope := by
      unfold fixedPAPayloadEnvelope
      omega

theorem verumProof_payloadLength_le_fixed :
    verumProof.payloadLength <= fixedPAPayloadEnvelope := by
  calc
    verumProof.payloadLength <= 48 + 9 * verumSyntaxBudget :=
      verumProof_payloadLength_le
    _ <= fixedPAPayloadEnvelope := by
      unfold fixedPAPayloadEnvelope
      omega

theorem specializationCost_fixedFormula_le
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hfixed :
      formula = equalityReflexivityBody ∨
      formula = equalitySymmetryOuterBody ∨
      formula = equalityTransitivityOuterBody ∨
      formula = binaryFunctionExtOuterBody Language.Add.add ∨
      formula = binaryFunctionExtOuterBody Language.Mul.mul ∨
      formula = addZeroBody ∨ formula = mulZeroBody ∨
      formula = mulOneBody ∨ formula = addCommutativityOuterBody ∨
      formula = addAssociativityOuterBody ∨
      formula = leftDistributivityOuterBody)
    (hwitness : (binaryTermCode witness).length <= termBound) :
    specializationCost formula witness <=
      paSpecializationCostEnvelope termBound := by
  apply specializationCost_le_paEnvelope formula witness termBound
  · exact (fixedFormulaCode_le_seed formula hfixed).trans
      (instantiatedFormulaStage0_le_envelope termBound)
  · exact hwitness

theorem specializationCost_stage1Formula_le
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hformula : (binaryFormulaCode formula).length <=
      instantiatedFormulaStage1 termBound)
    (hwitness : (binaryTermCode witness).length <= termBound) :
    specializationCost formula witness <=
      paSpecializationCostEnvelope termBound := by
  apply specializationCost_le_paEnvelope formula witness termBound
  · exact hformula.trans (instantiatedFormulaStage1_le_envelope termBound)
  · exact hwitness

theorem specializationCost_stage2Formula_le
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hformula : (binaryFormulaCode formula).length <=
      instantiatedFormulaStage2 termBound)
    (hwitness : (binaryTermCode witness).length <= termBound) :
    specializationCost formula witness <=
      paSpecializationCostEnvelope termBound := by
  apply specializationCost_le_paEnvelope formula witness termBound
  · exact hformula.trans (instantiatedFormulaStage2_le_envelope termBound)
  · exact hwitness

theorem specializationCost_stage3Formula_le
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hformula : (binaryFormulaCode formula).length <=
      instantiatedFormulaStage3 termBound)
    (hwitness : (binaryTermCode witness).length <= termBound) :
    specializationCost formula witness <=
      paSpecializationCostEnvelope termBound := by
  apply specializationCost_le_paEnvelope formula witness termBound
  · exact hformula.trans (instantiatedFormulaStage3_le_envelope termBound)
  · exact hwitness

theorem paFormulaCodeEnvelope_le_derived (termBound : Nat) :
    paFormulaCodeEnvelope termBound <=
      paDerivedFormulaCodeEnvelope termBound := by
  unfold paDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
  omega

theorem paDerivedFormulaCodeEnvelope_le_localAssembly (termBound : Nat) :
    paDerivedFormulaCodeEnvelope termBound <=
      paLocalAssemblyCostEnvelope termBound := by
  unfold paLocalAssemblyCostEnvelope paAssemblySyntaxEnvelope
  omega

theorem paLocalAssemblyCostEnvelope_le_primitiveAssembly (termBound : Nat) :
    paLocalAssemblyCostEnvelope termBound <=
      paPrimitiveAssemblyCostEnvelope termBound := by
  unfold paPrimitiveAssemblyCostEnvelope paAssemblySyntaxEnvelope
  omega

theorem proveEqualityReflexivityAtTerm_payloadLength_le_primitive
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) (termBound : Nat)
    (hterm : (binaryTermCode term).length <= termBound) :
    (proveEqualityReflexivityAtTerm term).payloadLength <=
      paPrimitiveCostEnvelope termBound := by
  have hproof :
      (proveEqualityReflexivity term).payloadLength <=
        equalityReflexivityAxiomProof.payloadLength +
          specializationCost equalityReflexivityBody term := by
    simpa [specializationCost, Nat.add_assoc] using
      (proveEqualityReflexivity_payloadLength_le term)
  have haxiom := equalityReflexivityAxiomProof_payloadLength_le_fixed
  have hcost := specializationCost_fixedFormula_le
    equalityReflexivityBody term termBound (by simp) hterm
  have hcast : (proveEqualityReflexivityAtTerm term).payloadLength =
      (proveEqualityReflexivity term).payloadLength := by
    change (cast (equalityReflexivityAtTerm_formula term)
      (proveEqualityReflexivity term)).payloadLength = _
    exact cast_payloadLength _ _
  rw [hcast]
  unfold paPrimitiveCostEnvelope
  omega

theorem proveAddCommutativity_payloadLength_le_primitive
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (proveAddCommutativity left right).payloadLength <=
      paPrimitiveCostEnvelope termBound := by
  have hproof := proveAddCommutativity_payloadLength_le left right
  have haxiom := addCommutativityAxiomProof_payloadLength_le_fixed
  have hfirst := specializationCost_fixedFormula_le
    addCommutativityOuterBody left termBound (by simp) hleft
  have hsecond := specializationCost_stage1Formula_le
    (addCommutativityInnerBody left) right termBound
    (addCommutativityInnerBody_code_le_stage1 left termBound hleft) hright
  unfold paPrimitiveCostEnvelope
  omega

theorem proveAddAssociativity_payloadLength_le_primitive
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hmiddle : (binaryTermCode middle).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (proveAddAssociativity left middle right).payloadLength <=
      paPrimitiveCostEnvelope termBound := by
  have hproof := proveAddAssociativity_payloadLength_le left middle right
  have haxiom := addAssociativityAxiomProof_payloadLength_le_fixed
  have hfirst := specializationCost_fixedFormula_le
    addAssociativityOuterBody left termBound (by simp) hleft
  have hsecond := specializationCost_stage1Formula_le
    (addAssociativityMiddleBody left) middle termBound
    (addAssociativityMiddleBody_code_le_stage1 left termBound hleft) hmiddle
  have hthird := specializationCost_stage2Formula_le
    (addAssociativityInnerBody left middle) right termBound
    (addAssociativityInnerBody_code_le_stage2 left middle termBound
      hleft hmiddle) hright
  unfold paPrimitiveCostEnvelope
  omega

theorem proveLeftDistributivity_payloadLength_le_primitive
    (factor left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hfactor : (binaryTermCode factor).length <= termBound)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (proveLeftDistributivity factor left right).payloadLength <=
      paPrimitiveCostEnvelope termBound := by
  have hproof := proveLeftDistributivity_payloadLength_le factor left right
  have haxiom := leftDistributivityAxiomProof_payloadLength_le_fixed
  have hfirst := specializationCost_fixedFormula_le
    leftDistributivityOuterBody factor termBound (by simp) hfactor
  have hsecond := specializationCost_stage1Formula_le
    (leftDistributivityMiddleBody factor) left termBound
    (leftDistributivityMiddleBody_code_le_stage1 factor termBound hfactor)
    hleft
  have hthird := specializationCost_stage2Formula_le
    (leftDistributivityInnerBody factor left) right termBound
    (leftDistributivityInnerBody_code_le_stage2 factor left termBound
      hfactor hleft) hright
  unfold paPrimitiveCostEnvelope
  omega

theorem proveAddZeroAtPaZero_payloadLength_le_primitive
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) (termBound : Nat)
    (hterm : (binaryTermCode term).length <= termBound) :
    (proveAddZeroAtPaZero term).payloadLength <=
      paPrimitiveCostEnvelope termBound := by
  have hproof : (proveAddZeroAtPaZero term).payloadLength <=
      addZeroAxiomProof.payloadLength + specializationCost addZeroBody term := by
    simpa [specializationCost, Nat.add_assoc] using
      (proveAddZeroAtPaZero_payloadLength_le term)
  have haxiom := addZeroAxiomProof_payloadLength_le_fixed
  have hcost := specializationCost_fixedFormula_le
    addZeroBody term termBound (by simp) hterm
  unfold paPrimitiveCostEnvelope
  omega

theorem proveMulZeroAtPaZero_payloadLength_le_primitive
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) (termBound : Nat)
    (hterm : (binaryTermCode term).length <= termBound) :
    (proveMulZeroAtPaZero term).payloadLength <=
      paPrimitiveCostEnvelope termBound := by
  have hproof : (proveMulZero term).payloadLength <=
      mulZeroAxiomProof.payloadLength + specializationCost mulZeroBody term := by
    simpa [specializationCost, Nat.add_assoc] using
      (proveMulZero_payloadLength_le term)
  have haxiom := mulZeroAxiomProof_payloadLength_le_fixed
  have hcost := specializationCost_fixedFormula_le
    mulZeroBody term termBound (by simp) hterm
  have hcast : (proveMulZeroAtPaZero term).payloadLength =
      (proveMulZero term).payloadLength := by
    change (cast (mulZeroAtPaZero_formula term)
      (proveMulZero term)).payloadLength = _
    exact cast_payloadLength _ _
  rw [hcast]
  unfold paPrimitiveCostEnvelope
  omega

theorem proveMulOneAtPaOne_payloadLength_le_primitive
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) (termBound : Nat)
    (hterm : (binaryTermCode term).length <= termBound) :
    (proveMulOneAtPaOne term).payloadLength <=
      paPrimitiveCostEnvelope termBound := by
  have hproof : (proveMulOne term).payloadLength <=
      mulOneAxiomProof.payloadLength + specializationCost mulOneBody term := by
    simpa [specializationCost, Nat.add_assoc] using
      (proveMulOne_payloadLength_le term)
  have haxiom := mulOneAxiomProof_payloadLength_le_fixed
  have hcost := specializationCost_fixedFormula_le
    mulOneBody term termBound (by simp) hterm
  have hcast : (proveMulOneAtPaOne term).payloadLength =
      (proveMulOne term).payloadLength := by
    change (cast (mulOneAtPaOne_formula term)
      (proveMulOne term)).payloadLength = _
    exact cast_payloadLength _ _
  rw [hcast]
  unfold paPrimitiveCostEnvelope
  omega

theorem proveEqualitySymmetry_payloadLength_le_primitive
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (equalityProof : CertifiedPAProof
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition))
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (proveEqualitySymmetry left right equalityProof).payloadLength <=
      equalityProof.payloadLength + paPrimitiveCostEnvelope termBound := by
  have himplication := equalitySymmetryImplication_payloadLength_le left right
  have hproof := proveEqualitySymmetry_payloadLength_le
    left right equalityProof
  have haxiom := equalitySymmetryAxiomProof_payloadLength_le_fixed
  have hfirst := specializationCost_fixedFormula_le
    equalitySymmetryOuterBody left termBound (by simp) hleft
  have hsecond := specializationCost_stage1Formula_le
    (equalitySymmetryInnerBody left) right termBound
    (equalitySymmetryInnerBody_code_le_stage1 left termBound hleft) hright
  have hsource := equalityFormula_code_length_le_paEnvelope
    left right termBound hleft hright
  have htarget := equalityFormula_code_length_le_paEnvelope
    right left termBound hright hleft
  have hmp := modusPonensSyntaxBudget_le_paAssemblyEnvelope
    (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)
    (“!!right = !!left” : LO.FirstOrder.ArithmeticProposition)
    (paFormulaCodeEnvelope termBound) hsource htarget
  have hderived := paDerivedFormulaCodeEnvelope_le_localAssembly termBound
  have hmpLocal :
      modusPonensSyntaxBudget
        (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)
        (“!!right = !!left” : LO.FirstOrder.ArithmeticProposition) <=
        paLocalAssemblyCostEnvelope termBound :=
    hmp.trans hderived
  unfold paPrimitiveCostEnvelope
  omega

theorem proveEqualityTransitivity_payloadLength_le_primitive
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (leftProof : CertifiedPAProof
      (“!!left = !!middle” : LO.FirstOrder.ArithmeticProposition))
    (rightProof : CertifiedPAProof
      (“!!middle = !!right” : LO.FirstOrder.ArithmeticProposition))
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hmiddle : (binaryTermCode middle).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (proveEqualityTransitivity left middle right
      leftProof rightProof).payloadLength <=
      leftProof.payloadLength + rightProof.payloadLength +
        paPrimitiveCostEnvelope termBound := by
  have himplication := equalityTransitivityImplication_payloadLength_le
    left middle right
  have hproof := proveEqualityTransitivity_payloadLength_le
    left middle right leftProof rightProof
  have haxiom := equalityTransitivityAxiomProof_payloadLength_le_fixed
  have hfirst := specializationCost_fixedFormula_le
    equalityTransitivityOuterBody left termBound (by simp) hleft
  have hsecond := specializationCost_stage1Formula_le
    (equalityTransitivityMiddleBody left) middle termBound
    (equalityTransitivityMiddleBody_code_le_stage1 left termBound hleft)
    hmiddle
  have hthird := specializationCost_stage2Formula_le
    (equalityTransitivityInnerBody left middle) right termBound
    (equalityTransitivityInnerBody_code_le_stage2 left middle termBound
      hleft hmiddle) hright
  let firstEq :=
    (“!!left = !!middle” : LO.FirstOrder.ArithmeticProposition)
  let secondEq :=
    (“!!middle = !!right” : LO.FirstOrder.ArithmeticProposition)
  let finalEq :=
    (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)
  let secondImplication := secondEq 🡒 finalEq
  have hfirstEq : (binaryFormulaCode firstEq).length <=
      paFormulaCodeEnvelope termBound := by
    exact equalityFormula_code_length_le_paEnvelope
      left middle termBound hleft hmiddle
  have hsecondEq : (binaryFormulaCode secondEq).length <=
      paFormulaCodeEnvelope termBound := by
    exact equalityFormula_code_length_le_paEnvelope
      middle right termBound hmiddle hright
  have hfinalEq : (binaryFormulaCode finalEq).length <=
      paFormulaCodeEnvelope termBound := by
    exact equalityFormula_code_length_le_paEnvelope
      left right termBound hleft hright
  have hsecondImplicationRaw :=
    binaryFormulaCode_implication_length_le secondEq finalEq
  have hsecondImplication :
      (binaryFormulaCode secondImplication).length <=
        paDerivedFormulaCodeEnvelope termBound := by
    dsimp only [secondImplication]
    unfold paDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
    omega
  have hbaseToDerived := paFormulaCodeEnvelope_le_derived termBound
  have hmpFirst := modusPonensSyntaxBudget_le_paAssemblyEnvelope
    firstEq secondImplication (paDerivedFormulaCodeEnvelope termBound)
    (hfirstEq.trans hbaseToDerived) hsecondImplication
  have hmpSecond := modusPonensSyntaxBudget_le_paAssemblyEnvelope
    secondEq finalEq (paDerivedFormulaCodeEnvelope termBound)
    (hsecondEq.trans hbaseToDerived) (hfinalEq.trans hbaseToDerived)
  dsimp only [firstEq, secondEq, finalEq, secondImplication] at hmpFirst hmpSecond
  have hmpFirstLocal :
      modusPonensSyntaxBudget
        (“!!left = !!middle” : LO.FirstOrder.ArithmeticProposition)
        (“!!middle = !!right → !!left = !!right” :
          LO.FirstOrder.ArithmeticProposition) <=
        paLocalAssemblyCostEnvelope termBound := by
    simpa [paLocalAssemblyCostEnvelope] using hmpFirst
  have hmpSecondLocal :
      modusPonensSyntaxBudget
        (“!!middle = !!right” : LO.FirstOrder.ArithmeticProposition)
        (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition) <=
        paLocalAssemblyCostEnvelope termBound := by
    simpa [paLocalAssemblyCostEnvelope] using hmpSecond
  unfold equalityTransitivityFirstMPSyntaxBudget
    equalityTransitivitySecondMPSyntaxBudget at hproof
  unfold paPrimitiveCostEnvelope
  omega

theorem binaryFunctionTerm_code_length_le
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (first second : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryTermCode
      (binaryFunctionTerm functionSymbol first second)).length <=
      (binaryTermCode first).length + (binaryTermCode second).length +
        binaryFunctionTermCodeOverhead functionSymbol := by
  simp [binaryFunctionTerm, binaryTermCode, Matrix.fun_eq_vec_two,
    binaryFunctionTermCodeOverhead]
  omega

theorem truthFormula_code_length_le_seed :
    (binaryFormulaCode
      (⊤ : LO.FirstOrder.ArithmeticProposition)).length <=
      fixedPAFormulaSeed := by
  unfold fixedPAFormulaSeed
  omega

theorem binaryFunctionTermCodeOverhead_le_seed
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (hfunction : functionSymbol = Language.Add.add ∨
      functionSymbol = Language.Mul.mul) :
    binaryFunctionTermCodeOverhead functionSymbol <= fixedPAFormulaSeed := by
  rcases hfunction with h | h <;> subst functionSymbol <;>
    unfold fixedPAFormulaSeed <;> omega

theorem truthFormula_code_length_le_paEnvelope (termBound : Nat) :
    (binaryFormulaCode
      (⊤ : LO.FirstOrder.ArithmeticProposition)).length <=
      paFormulaCodeEnvelope termBound := by
  have htruth := truthFormula_code_length_le_seed
  have hstage := instantiatedFormulaStage0_le_envelope termBound
  unfold instantiatedFormulaStage0 at hstage
  unfold paFormulaCodeEnvelope
  omega

theorem binaryFunctionCongruenceInnerFormula_code_le_derived
    (leftSecond rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (binaryFormulaCode
      ((“!!leftSecond = !!rightSecond” :
          LO.FirstOrder.ArithmeticProposition) ⋏ ⊤)).length <=
      paDerivedFormulaCodeEnvelope termBound := by
  let equality :=
    (“!!leftSecond = !!rightSecond” :
      LO.FirstOrder.ArithmeticProposition)
  have hequality : (binaryFormulaCode equality).length <=
      paFormulaCodeEnvelope termBound :=
    equalityFormula_code_length_le_paEnvelope
      leftSecond rightSecond termBound hleftSecond hrightSecond
  have htruth := truthFormula_code_length_le_paEnvelope termBound
  have hand := binaryFormulaCode_and_length_le_local equality
    (⊤ : LO.FirstOrder.ArithmeticProposition)
  dsimp only [equality] at hequality hand
  unfold paDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
  omega

theorem binaryFunctionCongruenceAntecedent_code_le_localAssembly
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (binaryFormulaCode
      (binaryFunctionCongruenceAntecedent leftFirst leftSecond
        rightFirst rightSecond)).length <=
      paLocalAssemblyCostEnvelope termBound := by
  let firstEq :=
    (“!!leftFirst = !!rightFirst” : LO.FirstOrder.ArithmeticProposition)
  let inner :=
    ((“!!leftSecond = !!rightSecond” :
      LO.FirstOrder.ArithmeticProposition) ⋏ ⊤)
  have hfirstEq : (binaryFormulaCode firstEq).length <=
      paFormulaCodeEnvelope termBound :=
    equalityFormula_code_length_le_paEnvelope
      leftFirst rightFirst termBound hleftFirst hrightFirst
  have hinner : (binaryFormulaCode inner).length <=
      paDerivedFormulaCodeEnvelope termBound :=
    binaryFunctionCongruenceInnerFormula_code_le_derived
      leftSecond rightSecond termBound hleftSecond hrightSecond
  have hand := binaryFormulaCode_and_length_le_local firstEq inner
  have hbase := paFormulaCodeEnvelope_le_derived termBound
  simp only [binaryFunctionCongruenceAntecedent]
  dsimp only [firstEq, inner] at hfirstEq hinner hand
  unfold paLocalAssemblyCostEnvelope paAssemblySyntaxEnvelope
  omega

theorem binaryFunctionCongruenceConclusion_code_le_localAssembly
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hfunction : functionSymbol = Language.Add.add ∨
      functionSymbol = Language.Mul.mul)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (binaryFormulaCode
      (binaryFunctionCongruenceConclusion functionSymbol leftFirst leftSecond
        rightFirst rightSecond)).length <=
      paLocalAssemblyCostEnvelope termBound := by
  let leftApplication :=
    binaryFunctionTerm functionSymbol leftFirst leftSecond
  let rightApplication :=
    binaryFunctionTerm functionSymbol rightFirst rightSecond
  have hoverhead :=
    binaryFunctionTermCodeOverhead_le_seed functionSymbol hfunction
  have hleftApplicationRaw := binaryFunctionTerm_code_length_le
    functionSymbol leftFirst leftSecond
  have hrightApplicationRaw := binaryFunctionTerm_code_length_le
    functionSymbol rightFirst rightSecond
  have hequality := equalityFormula_code_length_le
    leftApplication rightApplication
  have hstage := instantiatedFormulaStage0_le_envelope termBound
  unfold instantiatedFormulaStage0 at hstage
  simp only [binaryFunctionCongruenceConclusion]
  dsimp only [leftApplication, rightApplication] at hequality
  unfold paLocalAssemblyCostEnvelope paDerivedFormulaCodeEnvelope
    paAssemblySyntaxEnvelope paFormulaCodeEnvelope
    paEqualityFormulaCodeEnvelope
  omega

theorem proveBinaryFunctionCongruence_payloadLength_le_primitive
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” : LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” : LO.FirstOrder.ArithmeticProposition))
    (termBound : Nat)
    (hfunction : functionSymbol = Language.Add.add ∨
      functionSymbol = Language.Mul.mul)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (proveBinaryFunctionCongruence functionSymbol leftFirst leftSecond
      rightFirst rightSecond firstProof secondProof).payloadLength <=
      firstProof.payloadLength + secondProof.payloadLength +
        paPrimitiveCostEnvelope termBound := by
  have hproof := proveBinaryFunctionCongruence_full_payloadLength_le
    functionSymbol leftFirst leftSecond rightFirst rightSecond
    firstProof secondProof
  have haxiom := binaryFunctionExtAxiomProof_payloadLength_le_fixed
    functionSymbol hfunction
  have hfirst := specializationCost_fixedFormula_le
    (binaryFunctionExtOuterBody functionSymbol) rightSecond termBound
    (by rcases hfunction with h | h <;> subst functionSymbol <;> simp)
    hrightSecond
  have hsecond := specializationCost_stage1Formula_le
    (binaryFunctionExtRightFirstBody functionSymbol rightSecond)
    rightFirst termBound
    (binaryFunctionExtRightFirstBody_code_le_stage1 functionSymbol
      rightSecond termBound hfunction hrightSecond)
    hrightFirst
  have hthird := specializationCost_stage2Formula_le
    (binaryFunctionExtLeftSecondBody functionSymbol rightFirst rightSecond)
    leftSecond termBound
    (binaryFunctionExtLeftSecondBody_code_le_stage2 functionSymbol
      rightFirst rightSecond termBound hfunction
      hrightFirst hrightSecond)
    hleftSecond
  have hfourth := specializationCost_stage3Formula_le
    (binaryFunctionExtAfterLeftSecondMatrix functionSymbol
      leftSecond rightFirst rightSecond)
    leftFirst termBound
    (binaryFunctionExtAfterLeftSecondMatrix_code_le_stage3 functionSymbol
      leftSecond rightFirst rightSecond termBound hfunction
      hleftSecond hrightFirst hrightSecond)
    hleftFirst
  have hinnerRaw := conjunctionSyntaxBudget_le_paAssemblyEnvelope
    (“!!leftSecond = !!rightSecond” :
      LO.FirstOrder.ArithmeticProposition)
    (⊤ : LO.FirstOrder.ArithmeticProposition)
    (paFormulaCodeEnvelope termBound)
    (equalityFormula_code_length_le_paEnvelope leftSecond rightSecond
      termBound hleftSecond hrightSecond)
    (truthFormula_code_length_le_paEnvelope termBound)
  have hinner :
      binaryFunctionCongruenceInnerConjunctionSyntaxBudget
        leftSecond rightSecond <= paDerivedFormulaCodeEnvelope termBound := by
    simpa [binaryFunctionCongruenceInnerConjunctionSyntaxBudget,
      paDerivedFormulaCodeEnvelope] using hinnerRaw
  have hfirstEq := equalityFormula_code_length_le_paEnvelope
    leftFirst rightFirst termBound hleftFirst hrightFirst
  have hinnerFormula :=
    binaryFunctionCongruenceInnerFormula_code_le_derived
      leftSecond rightSecond termBound hleftSecond hrightSecond
  have hbaseToLocal := (paFormulaCodeEnvelope_le_derived termBound).trans
    (paDerivedFormulaCodeEnvelope_le_localAssembly termBound)
  have hderivedToLocal :=
    paDerivedFormulaCodeEnvelope_le_localAssembly termBound
  have houterRaw := conjunctionSyntaxBudget_le_paAssemblyEnvelope
    (“!!leftFirst = !!rightFirst” :
      LO.FirstOrder.ArithmeticProposition)
    ((“!!leftSecond = !!rightSecond” :
      LO.FirstOrder.ArithmeticProposition) ⋏ ⊤)
    (paLocalAssemblyCostEnvelope termBound)
    (hfirstEq.trans hbaseToLocal)
    (hinnerFormula.trans hderivedToLocal)
  have houter :
      binaryFunctionCongruenceOuterConjunctionSyntaxBudget
        leftFirst leftSecond rightFirst rightSecond <=
        paPrimitiveAssemblyCostEnvelope termBound := by
    simpa [binaryFunctionCongruenceOuterConjunctionSyntaxBudget,
      paPrimitiveAssemblyCostEnvelope] using houterRaw
  have hantecedent :=
    binaryFunctionCongruenceAntecedent_code_le_localAssembly
      leftFirst leftSecond rightFirst rightSecond termBound
      hleftFirst hleftSecond hrightFirst hrightSecond
  have hconclusion :=
    binaryFunctionCongruenceConclusion_code_le_localAssembly
      functionSymbol leftFirst leftSecond rightFirst rightSecond termBound
      hfunction hleftFirst hleftSecond hrightFirst hrightSecond
  have hmpRaw := modusPonensSyntaxBudget_le_paAssemblyEnvelope
    (binaryFunctionCongruenceAntecedent leftFirst leftSecond
      rightFirst rightSecond)
    (binaryFunctionCongruenceConclusion functionSymbol leftFirst leftSecond
      rightFirst rightSecond)
    (paLocalAssemblyCostEnvelope termBound) hantecedent hconclusion
  have hmp :
      binaryFunctionCongruenceMPSyntaxBudget functionSymbol
        leftFirst leftSecond rightFirst rightSecond <=
        paPrimitiveAssemblyCostEnvelope termBound := by
    simpa [binaryFunctionCongruenceMPSyntaxBudget,
      paPrimitiveAssemblyCostEnvelope] using hmpRaw
  have hverum : 9 * verumSyntaxBudget <= fixedPAPayloadEnvelope := by
    unfold fixedPAPayloadEnvelope
    omega
  have haxiomSyntax :
      10 * axiomSyntaxBudget (.eqFuncExt functionSymbol) <=
        fixedPAPayloadEnvelope := by
    rcases hfunction with h | h <;> subst functionSymbol <;>
      unfold fixedPAPayloadEnvelope <;> omega
  have hderivedPrimitive :=
    (paDerivedFormulaCodeEnvelope_le_localAssembly termBound).trans
      (paLocalAssemblyCostEnvelope_le_primitiveAssembly termBound)
  unfold paPrimitiveCostEnvelope
  omega

theorem proveAddCongruence_payloadLength_le_primitive
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” : LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” : LO.FirstOrder.ArithmeticProposition))
    (termBound : Nat)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (proveAddCongruence leftFirst leftSecond rightFirst rightSecond
      firstProof secondProof).payloadLength <=
      firstProof.payloadLength + secondProof.payloadLength +
        paPrimitiveCostEnvelope termBound := by
  have hgeneric := proveBinaryFunctionCongruence_payloadLength_le_primitive
    Language.Add.add leftFirst leftSecond rightFirst rightSecond
    firstProof secondProof termBound (Or.inl rfl)
    hleftFirst hleftSecond hrightFirst hrightSecond
  have hcast :
      (proveAddCongruence leftFirst leftSecond rightFirst rightSecond
        firstProof secondProof).payloadLength =
      (proveBinaryFunctionCongruence Language.Add.add
        leftFirst leftSecond rightFirst rightSecond
        firstProof secondProof).payloadLength := by
    change (CertifiedPAProof.cast _ _).payloadLength = _
    exact cast_payloadLength _ _
  rw [hcast]
  exact hgeneric

theorem proveMulCongruence_payloadLength_le_primitive
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” : LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” : LO.FirstOrder.ArithmeticProposition))
    (termBound : Nat)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (proveMulCongruence leftFirst leftSecond rightFirst rightSecond
      firstProof secondProof).payloadLength <=
      firstProof.payloadLength + secondProof.payloadLength +
        paPrimitiveCostEnvelope termBound := by
  have hgeneric := proveBinaryFunctionCongruence_payloadLength_le_primitive
    Language.Mul.mul leftFirst leftSecond rightFirst rightSecond
    firstProof secondProof termBound (Or.inr rfl)
    hleftFirst hleftSecond hrightFirst hrightSecond
  have hcast :
      (proveMulCongruence leftFirst leftSecond rightFirst rightSecond
        firstProof secondProof).payloadLength =
      (proveBinaryFunctionCongruence Language.Mul.mul
        leftFirst leftSecond rightFirst rightSecond
        firstProof secondProof).payloadLength := by
    change (CertifiedPAProof.cast _ _).payloadLength = _
    exact cast_payloadLength _ _
  rw [hcast]
  exact hgeneric

/-! ## Honest term-code envelope for every local algebraic expression -/

theorem natSize_add_le (left right : Nat) :
    Nat.size (left + right) <= Nat.size left + Nat.size right + 1 := by
  rw [Nat.size_le]
  have hleft : left < 2 ^ Nat.size left := Nat.lt_size_self left
  have hright : right < 2 ^ Nat.size right := Nat.lt_size_self right
  have hleftPower : 2 ^ Nat.size left <=
      2 ^ (Nat.size left + Nat.size right) := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
      (Nat.le_add_right (Nat.size left) (Nat.size right))
  have hrightPower : 2 ^ Nat.size right <=
      2 ^ (Nat.size left + Nat.size right) := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
      (Nat.le_add_left (Nat.size right) (Nat.size left))
  calc
    left + right < 2 ^ Nat.size left + 2 ^ Nat.size right :=
      Nat.add_lt_add hleft hright
    _ <= 2 ^ (Nat.size left + Nat.size right) +
        2 ^ (Nat.size left + Nat.size right) :=
      Nat.add_le_add hleftPower hrightPower
    _ = 2 ^ (Nat.size left + Nat.size right + 1) := by
      rw [pow_succ]
      omega

theorem natSize_add_le_sum_of_right_ne_zero
    (left right : Nat) (hright : right ≠ 0) :
    Nat.size (left + right) <= Nat.size left + Nat.size right := by
  by_cases hleft : left = 0
  · subst left
    simp
  rw [Nat.size_le]
  have hleftLt : left < 2 ^ Nat.size left := Nat.lt_size_self left
  have hrightLt : right < 2 ^ Nat.size right := Nat.lt_size_self right
  have hleftSize : 1 <= Nat.size left := by
    have hpositive := Nat.size_pos.mpr (Nat.pos_of_ne_zero hleft)
    omega
  have hrightSize : 1 <= Nat.size right := by
    have hpositive := Nat.size_pos.mpr (Nat.pos_of_ne_zero hright)
    omega
  have hleftPower : 2 <= 2 ^ Nat.size left := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hleftSize
  have hrightPower : 2 <= 2 ^ Nat.size right := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hrightSize
  have hproduct :
      2 ^ Nat.size left + 2 ^ Nat.size right <=
        2 ^ Nat.size left * 2 ^ Nat.size right := by
    nlinarith
  calc
    left + right < 2 ^ Nat.size left + 2 ^ Nat.size right :=
      Nat.add_lt_add hleftLt hrightLt
    _ <= 2 ^ Nat.size left * 2 ^ Nat.size right := hproduct
    _ = 2 ^ (Nat.size left + Nat.size right) := by rw [pow_add]

def binaryNumeralTermCodeEnvelope (bitWidth : Nat) : Nat :=
  (binaryTermCode arithmeticZeroTerm).length +
    binaryNumeralStepBudget * bitWidth

theorem binaryNumeralTerm_code_length_le_envelope
    (value bitWidth : Nat) (hsize : Nat.size value <= bitWidth) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      binaryNumeralTermCodeEnvelope bitWidth := by
  have hcode := binaryNumeralTerm_code_length_le_size value
  unfold binaryNumeralTermCodeEnvelope
  exact hcode.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_left binaryNumeralStepBudget hsize) _)

def paTermCodeBaseEnvelope (bitWidth : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitWidth +
    (binaryTermCode paZeroTerm).length +
    (binaryTermCode paOneTerm).length +
    (binaryTermCode arithmeticTwoTerm).length + 1

def paTermOperationCodeOverhead : Nat :=
  binaryFunctionTermCodeOverhead Language.Add.add +
    binaryFunctionTermCodeOverhead Language.Mul.mul + 1

def paTermCodeStage : Nat -> Nat -> Nat
  | 0, bitWidth => paTermCodeBaseEnvelope bitWidth
  | depth + 1, bitWidth =>
      3 * paTermCodeStage depth bitWidth + paTermOperationCodeOverhead

def paCompilerTermCodeEnvelope (bitWidth : Nat) : Nat :=
  paTermCodeStage 16 bitWidth

theorem paTermCodeStage_le_succ (depth bitWidth : Nat) :
    paTermCodeStage depth bitWidth <=
      paTermCodeStage (depth + 1) bitWidth := by
  rw [paTermCodeStage]
  unfold paTermOperationCodeOverhead
  omega

theorem paTermCodeStage_mono_depth
    {firstDepth secondDepth bitWidth : Nat}
    (hdepth : firstDepth <= secondDepth) :
    paTermCodeStage firstDepth bitWidth <=
      paTermCodeStage secondDepth bitWidth := by
  induction secondDepth, hdepth using Nat.le_induction with
  | base => exact le_rfl
  | @succ secondDepth hdepth ih =>
      exact ih.trans (paTermCodeStage_le_succ secondDepth bitWidth)

theorem paTermCodeStage_le_compilerEnvelope
    (depth bitWidth : Nat) (hdepth : depth <= 16) :
    paTermCodeStage depth bitWidth <=
      paCompilerTermCodeEnvelope bitWidth := by
  exact paTermCodeStage_mono_depth hdepth

theorem binaryNumeralTerm_code_length_le_stage0
    (value bitWidth : Nat) (hsize : Nat.size value <= bitWidth) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      paTermCodeStage 0 bitWidth := by
  have h := binaryNumeralTerm_code_length_le_envelope value bitWidth hsize
  simp [paTermCodeStage, paTermCodeBaseEnvelope]
  omega

theorem paZeroTerm_code_length_le_stage0 (bitWidth : Nat) :
    (binaryTermCode paZeroTerm).length <=
      paTermCodeStage 0 bitWidth := by
  simp [paTermCodeStage, paTermCodeBaseEnvelope]
  omega

theorem paOneTerm_code_length_le_stage0 (bitWidth : Nat) :
    (binaryTermCode paOneTerm).length <=
      paTermCodeStage 0 bitWidth := by
  simp [paTermCodeStage, paTermCodeBaseEnvelope]
  omega

theorem arithmeticTwoTerm_code_length_le_stage0 (bitWidth : Nat) :
    (binaryTermCode arithmeticTwoTerm).length <=
      paTermCodeStage 0 bitWidth := by
  simp [paTermCodeStage, paTermCodeBaseEnvelope]
  omega

theorem paAddTerm_code_length_le_nextStage
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth bitWidth : Nat)
    (hleft : (binaryTermCode left).length <=
      paTermCodeStage depth bitWidth)
    (hright : (binaryTermCode right).length <=
      paTermCodeStage depth bitWidth) :
    (binaryTermCode (paAddTerm left right)).length <=
      paTermCodeStage (depth + 1) bitWidth := by
  have hcode := paAddTerm_code_length_le left right
  rw [paTermCodeStage]
  unfold paTermOperationCodeOverhead
  omega

theorem paMulTerm_code_length_le_nextStage
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth bitWidth : Nat)
    (hleft : (binaryTermCode left).length <=
      paTermCodeStage depth bitWidth)
    (hright : (binaryTermCode right).length <=
      paTermCodeStage depth bitWidth) :
    (binaryTermCode (paMulTerm left right)).length <=
      paTermCodeStage (depth + 1) bitWidth := by
  have hcode := paMulTerm_code_length_le left right
  rw [paTermCodeStage]
  unfold paTermOperationCodeOverhead
  omega

theorem paTermCodeStage_promote
    {term : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {firstDepth secondDepth bitWidth : Nat}
    (hterm : (binaryTermCode term).length <=
      paTermCodeStage firstDepth bitWidth)
    (hdepth : firstDepth <= secondDepth) :
    (binaryTermCode term).length <=
      paTermCodeStage secondDepth bitWidth :=
  hterm.trans (paTermCodeStage_mono_depth hdepth)

theorem paTermCodeStage_to_compilerEnvelope
    {term : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {depth bitWidth : Nat}
    (hterm : (binaryTermCode term).length <=
      paTermCodeStage depth bitWidth)
    (hdepth : depth <= 16) :
    (binaryTermCode term).length <=
      paCompilerTermCodeEnvelope bitWidth :=
  hterm.trans (paTermCodeStage_le_compilerEnvelope depth bitWidth hdepth)

/-- Operation-count presentation of the same finite local term grammar.  It
is convenient for auditing concrete branch terms because child budgets add. -/
inductive PACompilerGeneratedTerm (bitWidth : Nat) :
    Nat -> LO.FirstOrder.ArithmeticSemiterm Nat 0 -> Prop
  | numeral (value : Nat) (hsize : Nat.size value <= bitWidth) :
      PACompilerGeneratedTerm bitWidth 1 (shortBinaryNumeralTerm value)
  | zero : PACompilerGeneratedTerm bitWidth 1 paZeroTerm
  | one : PACompilerGeneratedTerm bitWidth 1 paOneTerm
  | two : PACompilerGeneratedTerm bitWidth 1 arithmeticTwoTerm
  | add {leftBudget rightBudget : Nat}
      {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
      (hleft : PACompilerGeneratedTerm bitWidth leftBudget left)
      (hright : PACompilerGeneratedTerm bitWidth rightBudget right) :
      PACompilerGeneratedTerm bitWidth (leftBudget + rightBudget + 1)
        (paAddTerm left right)
  | mul {leftBudget rightBudget : Nat}
      {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
      (hleft : PACompilerGeneratedTerm bitWidth leftBudget left)
      (hright : PACompilerGeneratedTerm bitWidth rightBudget right) :
      PACompilerGeneratedTerm bitWidth (leftBudget + rightBudget + 1)
        (paMulTerm left right)

def paGeneratedTermAtomEnvelope (bitWidth : Nat) : Nat :=
  paTermCodeBaseEnvelope bitWidth + paTermOperationCodeOverhead + 1

def paGeneratedTermCodeEnvelope (bitWidth : Nat) : Nat :=
  64 * paGeneratedTermAtomEnvelope bitWidth

theorem paTermOperationCodeOverhead_le_atomEnvelope (bitWidth : Nat) :
    paTermOperationCodeOverhead <= paGeneratedTermAtomEnvelope bitWidth := by
  unfold paGeneratedTermAtomEnvelope
  omega

theorem PACompilerGeneratedTerm_code_length_le
    {bitWidth budget : Nat}
    {term : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    (hterm : PACompilerGeneratedTerm bitWidth budget term) :
    (binaryTermCode term).length <=
      budget * paGeneratedTermAtomEnvelope bitWidth := by
  induction hterm with
  | numeral value hsize =>
      have hcode := binaryNumeralTerm_code_length_le_stage0
        value bitWidth hsize
      simp only [paTermCodeStage] at hcode
      unfold paGeneratedTermAtomEnvelope
      simpa using hcode.trans (by
        unfold paTermCodeBaseEnvelope
        omega)
  | zero =>
      have hcode := paZeroTerm_code_length_le_stage0 bitWidth
      simp only [paTermCodeStage] at hcode
      unfold paGeneratedTermAtomEnvelope
      simpa using hcode.trans (by
        unfold paTermCodeBaseEnvelope
        omega)
  | one =>
      have hcode := paOneTerm_code_length_le_stage0 bitWidth
      simp only [paTermCodeStage] at hcode
      unfold paGeneratedTermAtomEnvelope
      simpa using hcode.trans (by
        unfold paTermCodeBaseEnvelope
        omega)
  | two =>
      have hcode := arithmeticTwoTerm_code_length_le_stage0 bitWidth
      simp only [paTermCodeStage] at hcode
      unfold paGeneratedTermAtomEnvelope
      simpa using hcode.trans (by
        unfold paTermCodeBaseEnvelope
        omega)
  | @add leftBudget rightBudget left right hleft hright ihLeft ihRight =>
      have hcode := paAddTerm_code_length_le left right
      have hoverhead := paTermOperationCodeOverhead_le_atomEnvelope bitWidth
      unfold paTermOperationCodeOverhead at hoverhead
      calc
        (binaryTermCode (paAddTerm left right)).length <=
            (binaryTermCode left).length + (binaryTermCode right).length +
              binaryFunctionTermCodeOverhead Language.Add.add := hcode
        _ <= leftBudget * paGeneratedTermAtomEnvelope bitWidth +
            rightBudget * paGeneratedTermAtomEnvelope bitWidth +
              paGeneratedTermAtomEnvelope bitWidth := by omega
        _ = (leftBudget + rightBudget + 1) *
            paGeneratedTermAtomEnvelope bitWidth := by ring
  | @mul leftBudget rightBudget left right hleft hright ihLeft ihRight =>
      have hcode := paMulTerm_code_length_le left right
      have hoverhead := paTermOperationCodeOverhead_le_atomEnvelope bitWidth
      unfold paTermOperationCodeOverhead at hoverhead
      calc
        (binaryTermCode (paMulTerm left right)).length <=
            (binaryTermCode left).length + (binaryTermCode right).length +
              binaryFunctionTermCodeOverhead Language.Mul.mul := hcode
        _ <= leftBudget * paGeneratedTermAtomEnvelope bitWidth +
            rightBudget * paGeneratedTermAtomEnvelope bitWidth +
              paGeneratedTermAtomEnvelope bitWidth := by omega
        _ = (leftBudget + rightBudget + 1) *
            paGeneratedTermAtomEnvelope bitWidth := by ring

theorem PACompilerGeneratedTerm_code_length_le_envelope
    {bitWidth budget : Nat}
    {term : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    (hterm : PACompilerGeneratedTerm bitWidth budget term)
    (hbudget : budget <= 64) :
    (binaryTermCode term).length <=
      paGeneratedTermCodeEnvelope bitWidth := by
  have hcode := PACompilerGeneratedTerm_code_length_le hterm
  unfold paGeneratedTermCodeEnvelope
  exact hcode.trans (Nat.mul_le_mul_right _ hbudget)

def paAlgebraStepCostEnvelope (bitWidth : Nat) : Nat :=
  256 * paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope bitWidth)

theorem paPrimitiveCostEnvelope_le_algebraStep (bitWidth : Nat) :
    paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope bitWidth) <=
      paAlgebraStepCostEnvelope bitWidth := by
  unfold paAlgebraStepCostEnvelope
  have hpositive : 1 <= (256 : Nat) := by decide
  simpa [Nat.mul_comm] using Nat.mul_le_mul_right
    (paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope bitWidth)) hpositive

theorem generatedTerm_code_length_le_compiler
    {bitWidth budget : Nat}
    {term : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    (hterm : PACompilerGeneratedTerm bitWidth budget term)
    (hbudget : budget <= 64) :
    (binaryTermCode term).length <=
      paGeneratedTermCodeEnvelope bitWidth :=
  PACompilerGeneratedTerm_code_length_le_envelope hterm hbudget

theorem proveZeroAdd_payloadLength_le_algebraStep
    {bitWidth budget : Nat}
    {term : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    (hterm : PACompilerGeneratedTerm bitWidth budget term)
    (hbudget : budget <= 32) :
    (proveZeroAdd term).payloadLength <=
      paAlgebraStepCostEnvelope bitWidth := by
  let zeroPlusTerm := paAddTerm paZeroTerm term
  let termPlusZero := paAddTerm term paZeroTerm
  have hzero : PACompilerGeneratedTerm bitWidth 1 paZeroTerm := .zero
  have hzeroPlusTerm :
      PACompilerGeneratedTerm bitWidth (1 + budget + 1) zeroPlusTerm :=
    .add hzero hterm
  have htermPlusZero :
      PACompilerGeneratedTerm bitWidth (budget + 1 + 1) termPlusZero :=
    .add hterm hzero
  have htermCode := generatedTerm_code_length_le_compiler hterm (by omega)
  have hzeroCode := generatedTerm_code_length_le_compiler hzero (by omega)
  have hzeroPlusTermCode := generatedTerm_code_length_le_compiler
    hzeroPlusTerm (by omega)
  have htermPlusZeroCode := generatedTerm_code_length_le_compiler
    htermPlusZero (by omega)
  have hcomm := proveAddCommutativity_payloadLength_le_primitive
    paZeroTerm term (paGeneratedTermCodeEnvelope bitWidth)
    hzeroCode htermCode
  have haddZero := proveAddZeroAtPaZero_payloadLength_le_primitive
    term (paGeneratedTermCodeEnvelope bitWidth) htermCode
  have htrans := proveEqualityTransitivity_payloadLength_le_primitive
    zeroPlusTerm termPlusZero term
    (proveAddCommutativity paZeroTerm term)
    (proveAddZeroAtPaZero term)
    (paGeneratedTermCodeEnvelope bitWidth)
    hzeroPlusTermCode htermPlusZeroCode htermCode
  change
    (proveEqualityTransitivity zeroPlusTerm termPlusZero term
      (proveAddCommutativity paZeroTerm term)
      (proveAddZeroAtPaZero term)).payloadLength <= _
  calc
    _ <= (proveAddCommutativity paZeroTerm term).payloadLength +
        (proveAddZeroAtPaZero term).payloadLength +
        paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope bitWidth) :=
      htrans
    _ <= paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope bitWidth) +
        paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope bitWidth) +
        paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope bitWidth) := by
      exact Nat.add_le_add (Nat.add_le_add hcomm haddZero) le_rfl
    _ <= paAlgebraStepCostEnvelope bitWidth := by
      unfold paAlgebraStepCostEnvelope
      omega

theorem proveAddAssociativityReverse_payloadLength_le_algebraStep
    {bitWidth leftBudget middleBudget rightBudget : Nat}
    {left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    (hleft : PACompilerGeneratedTerm bitWidth leftBudget left)
    (hmiddle : PACompilerGeneratedTerm bitWidth middleBudget middle)
    (hright : PACompilerGeneratedTerm bitWidth rightBudget right)
    (hleftBudget : leftBudget <= 16)
    (hmiddleBudget : middleBudget <= 16)
    (hrightBudget : rightBudget <= 16) :
    (proveAddAssociativityReverse left middle right).payloadLength <=
      paAlgebraStepCostEnvelope bitWidth := by
  let leftMiddle := paAddTerm left middle
  let leftAssociated := paAddTerm leftMiddle right
  let middleRight := paAddTerm middle right
  let rightAssociated := paAddTerm left middleRight
  have hleftMiddle : PACompilerGeneratedTerm bitWidth
      (leftBudget + middleBudget + 1) leftMiddle := .add hleft hmiddle
  have hleftAssociated : PACompilerGeneratedTerm bitWidth
      ((leftBudget + middleBudget + 1) + rightBudget + 1)
      leftAssociated := .add hleftMiddle hright
  have hmiddleRight : PACompilerGeneratedTerm bitWidth
      (middleBudget + rightBudget + 1) middleRight := .add hmiddle hright
  have hrightAssociated : PACompilerGeneratedTerm bitWidth
      (leftBudget + (middleBudget + rightBudget + 1) + 1)
      rightAssociated := .add hleft hmiddleRight
  have hleftCode := generatedTerm_code_length_le_compiler hleft (by omega)
  have hmiddleCode := generatedTerm_code_length_le_compiler hmiddle (by omega)
  have hrightCode := generatedTerm_code_length_le_compiler hright (by omega)
  have hleftAssociatedCode := generatedTerm_code_length_le_compiler
    hleftAssociated (by omega)
  have hrightAssociatedCode := generatedTerm_code_length_le_compiler
    hrightAssociated (by omega)
  have hassoc := proveAddAssociativity_payloadLength_le_primitive
    left middle right (paGeneratedTermCodeEnvelope bitWidth)
    hleftCode hmiddleCode hrightCode
  have hsymm := proveEqualitySymmetry_payloadLength_le_primitive
    leftAssociated rightAssociated (proveAddAssociativity left middle right)
    (paGeneratedTermCodeEnvelope bitWidth)
    hleftAssociatedCode hrightAssociatedCode
  change
    (proveEqualitySymmetry leftAssociated rightAssociated
      (proveAddAssociativity left middle right)).payloadLength <= _
  calc
    _ <= (proveAddAssociativity left middle right).payloadLength +
        paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope bitWidth) :=
      hsymm
    _ <= paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope bitWidth) +
        paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope bitWidth) :=
      Nat.add_le_add_right hassoc _
    _ <= paAlgebraStepCostEnvelope bitWidth := by
      unfold paAlgebraStepCostEnvelope
      omega

theorem proveLeftDistributivityReverse_payloadLength_le_algebraStep
    {bitWidth factorBudget leftBudget rightBudget : Nat}
    {factor left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    (hfactor : PACompilerGeneratedTerm bitWidth factorBudget factor)
    (hleft : PACompilerGeneratedTerm bitWidth leftBudget left)
    (hright : PACompilerGeneratedTerm bitWidth rightBudget right)
    (hfactorBudget : factorBudget <= 12)
    (hleftBudget : leftBudget <= 12)
    (hrightBudget : rightBudget <= 12) :
    (proveLeftDistributivityReverse factor left right).payloadLength <=
      paAlgebraStepCostEnvelope bitWidth := by
  let leftPlusRight := paAddTerm left right
  let factored := paMulTerm factor leftPlusRight
  let leftProduct := paMulTerm factor left
  let rightProduct := paMulTerm factor right
  let distributed := paAddTerm leftProduct rightProduct
  have hleftPlusRight : PACompilerGeneratedTerm bitWidth
      (leftBudget + rightBudget + 1) leftPlusRight := .add hleft hright
  have hfactored : PACompilerGeneratedTerm bitWidth
      (factorBudget + (leftBudget + rightBudget + 1) + 1) factored :=
    .mul hfactor hleftPlusRight
  have hleftProduct : PACompilerGeneratedTerm bitWidth
      (factorBudget + leftBudget + 1) leftProduct := .mul hfactor hleft
  have hrightProduct : PACompilerGeneratedTerm bitWidth
      (factorBudget + rightBudget + 1) rightProduct := .mul hfactor hright
  have hdistributed : PACompilerGeneratedTerm bitWidth
      ((factorBudget + leftBudget + 1) +
        (factorBudget + rightBudget + 1) + 1) distributed :=
    .add hleftProduct hrightProduct
  have hfactorCode := generatedTerm_code_length_le_compiler hfactor (by omega)
  have hleftCode := generatedTerm_code_length_le_compiler hleft (by omega)
  have hrightCode := generatedTerm_code_length_le_compiler hright (by omega)
  have hfactoredCode := generatedTerm_code_length_le_compiler
    hfactored (by omega)
  have hdistributedCode := generatedTerm_code_length_le_compiler
    hdistributed (by omega)
  have hdistr := proveLeftDistributivity_payloadLength_le_primitive
    factor left right (paGeneratedTermCodeEnvelope bitWidth)
    hfactorCode hleftCode hrightCode
  have hsymm := proveEqualitySymmetry_payloadLength_le_primitive
    factored distributed (proveLeftDistributivity factor left right)
    (paGeneratedTermCodeEnvelope bitWidth) hfactoredCode hdistributedCode
  change
    (proveEqualitySymmetry factored distributed
      (proveLeftDistributivity factor left right)).payloadLength <= _
  calc
    _ <= (proveLeftDistributivity factor left right).payloadLength +
        paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope bitWidth) :=
      hsymm
    _ <= paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope bitWidth) +
        paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope bitWidth) :=
      Nat.add_le_add_right hdistr _
    _ <= paAlgebraStepCostEnvelope bitWidth := by
      unfold paAlgebraStepCostEnvelope
      omega

def paIncrementLocalCostEnvelope (bitWidth : Nat) : Nat :=
  32 * paAlgebraStepCostEnvelope bitWidth

def paBinaryOneBaseCostEnvelope (bitWidth : Nat) : Nat :=
  8 * paAlgebraStepCostEnvelope bitWidth

def paOneEqualsBinaryOneCostEnvelope (bitWidth : Nat) : Nat :=
  10 * paAlgebraStepCostEnvelope bitWidth

theorem paAlgebraStepCostEnvelope_le_incrementLocal (bitWidth : Nat) :
    paAlgebraStepCostEnvelope bitWidth <=
      paIncrementLocalCostEnvelope bitWidth := by
  unfold paIncrementLocalCostEnvelope
  omega

theorem proveOnePairToTwoMulOne_payloadLength_le_algebraStep
    (bitWidth : Nat) :
    proveOnePairToTwoMulOne.payloadLength <=
      paAlgebraStepCostEnvelope bitWidth := by
  let product := paMulTerm arithmeticTwoTerm paOneTerm
  have htwo : PACompilerGeneratedTerm bitWidth 1 arithmeticTwoTerm := .two
  have hone : PACompilerGeneratedTerm bitWidth 1 paOneTerm := .one
  have hproduct : PACompilerGeneratedTerm bitWidth 3 product := .mul htwo hone
  have htwoCode := generatedTerm_code_length_le_compiler htwo (by omega)
  have hproductCode := generatedTerm_code_length_le_compiler
    hproduct (by omega)
  have hmulOne := proveMulOneAtPaOne_payloadLength_le_primitive
    arithmeticTwoTerm (paGeneratedTermCodeEnvelope bitWidth) htwoCode
  have hsymmetry := proveEqualitySymmetry_payloadLength_le_primitive
    product arithmeticTwoTerm (proveMulOneAtPaOne arithmeticTwoTerm)
    (paGeneratedTermCodeEnvelope bitWidth) hproductCode htwoCode
  have hcast : proveOnePairToTwoMulOne.payloadLength =
      (proveEqualitySymmetry product arithmeticTwoTerm
        (proveMulOneAtPaOne arithmeticTwoTerm)).payloadLength := by
    change (CertifiedPAProof.cast _ _).payloadLength = _
    exact cast_payloadLength _ _
  rw [hcast]
  calc
    _ <= (proveMulOneAtPaOne arithmeticTwoTerm).payloadLength +
        paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope bitWidth) :=
      hsymmetry
    _ <= paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope bitWidth) +
        paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope bitWidth) :=
      Nat.add_le_add_right hmulOne _
    _ <= paAlgebraStepCostEnvelope bitWidth := by
      unfold paAlgebraStepCostEnvelope
      omega

theorem proveBinaryNumeralIncrementEven_payloadLength_le_algebraStep
    (high bitWidth : Nat) (hnonzero : high ≠ 0)
    (hsize : Nat.size high <= bitWidth) :
    (proveBinaryNumeralIncrementEven high hnonzero).payloadLength <=
      paAlgebraStepCostEnvelope bitWidth := by
  let highTerm := shortBinaryNumeralTerm high
  let doubled := paMulTerm arithmeticTwoTerm highTerm
  let evenTerm := paAddTerm doubled paOneTerm
  have hhigh : PACompilerGeneratedTerm bitWidth 1 highTerm :=
    .numeral high hsize
  have htwo : PACompilerGeneratedTerm bitWidth 1 arithmeticTwoTerm := .two
  have hone : PACompilerGeneratedTerm bitWidth 1 paOneTerm := .one
  have hdoubled : PACompilerGeneratedTerm bitWidth 3 doubled :=
    .mul htwo hhigh
  have heven : PACompilerGeneratedTerm bitWidth 5 evenTerm :=
    .add hdoubled hone
  have hevenCode := generatedTerm_code_length_le_compiler heven (by omega)
  have hreflexivity := proveEqualityReflexivityAtTerm_payloadLength_le_primitive
    evenTerm (paGeneratedTermCodeEnvelope bitWidth) hevenCode
  have hcast :
      (proveBinaryNumeralIncrementEven high hnonzero).payloadLength =
        (proveEqualityReflexivityAtTerm evenTerm).payloadLength := by
    change (CertifiedPAProof.cast _ _).payloadLength = _
    exact cast_payloadLength _ _
  rw [hcast]
  exact hreflexivity.trans
    (paPrimitiveCostEnvelope_le_algebraStep bitWidth)

theorem proveBinaryOneAlgebraEqualsOne_payloadLength_le_incrementLocal
    (bitWidth : Nat) :
    proveBinaryOneAlgebraEqualsOne.payloadLength <=
      paBinaryOneBaseCostEnvelope bitWidth := by
  let doubleZero := paMulTerm arithmeticTwoTerm paZeroTerm
  let zeroPlusOne := paAddTerm paZeroTerm paOneTerm
  let collapseDouble : CertifiedPAProof
      (“!!binaryOneAlgebraTerm = !!zeroPlusOne” :
        LO.FirstOrder.ArithmeticProposition) := by
    let raw := proveAddCongruence doubleZero paOneTerm paZeroTerm paOneTerm
        (proveMulZeroAtPaZero arithmeticTwoTerm)
        (proveEqualityReflexivityAtTerm paOneTerm)
    have hformula := addEqualityAsTerm_formula doubleZero paOneTerm
      paZeroTerm paOneTerm
    simpa [binaryOneAlgebraTerm, doubleZero, zeroPlusOne] using
      (CertifiedPAProof.cast hformula raw)
  let collapseZero : CertifiedPAProof
      (“!!zeroPlusOne = !!paOneTerm” :
        LO.FirstOrder.ArithmeticProposition) := by
    let raw := proveZeroAdd paOneTerm
    have hformula := addLeftAsTerm_formula paZeroTerm paOneTerm paOneTerm
    simpa [zeroPlusOne] using (CertifiedPAProof.cast hformula raw)
  have htwo : PACompilerGeneratedTerm bitWidth 1 arithmeticTwoTerm := .two
  have hzero : PACompilerGeneratedTerm bitWidth 1 paZeroTerm := .zero
  have hone : PACompilerGeneratedTerm bitWidth 1 paOneTerm := .one
  have hdoubleZero : PACompilerGeneratedTerm bitWidth 3 doubleZero :=
    .mul htwo hzero
  have hbinaryOne : PACompilerGeneratedTerm bitWidth 5
      binaryOneAlgebraTerm := by
    simpa [binaryOneAlgebraTerm, doubleZero] using
      (PACompilerGeneratedTerm.add hdoubleZero hone)
  have hzeroPlusOne : PACompilerGeneratedTerm bitWidth 3 zeroPlusOne :=
    .add hzero hone
  have hdoubleZeroCode := generatedTerm_code_length_le_compiler
    hdoubleZero (by omega)
  have honeCode := generatedTerm_code_length_le_compiler hone (by omega)
  have hbinaryOneCode := generatedTerm_code_length_le_compiler
    hbinaryOne (by omega)
  have hzeroPlusOneCode := generatedTerm_code_length_le_compiler
    hzeroPlusOne (by omega)
  have hmulZero := proveMulZeroAtPaZero_payloadLength_le_primitive
    arithmeticTwoTerm (paGeneratedTermCodeEnvelope bitWidth)
    (generatedTerm_code_length_le_compiler htwo (by omega))
  have hreflexive := proveEqualityReflexivityAtTerm_payloadLength_le_primitive
    paOneTerm (paGeneratedTermCodeEnvelope bitWidth) honeCode
  have hcollapseDoubleRaw := proveAddCongruence_payloadLength_le_primitive
    doubleZero paOneTerm paZeroTerm paOneTerm
    (proveMulZeroAtPaZero arithmeticTwoTerm)
    (proveEqualityReflexivityAtTerm paOneTerm)
    (paGeneratedTermCodeEnvelope bitWidth)
    hdoubleZeroCode honeCode
    (generatedTerm_code_length_le_compiler hzero (by omega)) honeCode
  have hcollapseZeroRaw := proveZeroAdd_payloadLength_le_algebraStep
    hone (by omega)
  have hcollapseDouble : collapseDouble.payloadLength <=
      3 * paPrimitiveCostEnvelope
        (paGeneratedTermCodeEnvelope bitWidth) := by
    have hcast : collapseDouble.payloadLength =
        (proveAddCongruence doubleZero paOneTerm paZeroTerm paOneTerm
          (proveMulZeroAtPaZero arithmeticTwoTerm)
          (proveEqualityReflexivityAtTerm paOneTerm)).payloadLength := by
      dsimp only [collapseDouble]
      change (CertifiedPAProof.cast _ _).payloadLength = _
      exact cast_payloadLength _ _
    rw [hcast]
    omega
  have hcollapseZero : collapseZero.payloadLength <=
      paAlgebraStepCostEnvelope bitWidth := by
    have hcast : collapseZero.payloadLength =
        (proveZeroAdd paOneTerm).payloadLength := by
      dsimp only [collapseZero]
      change (CertifiedPAProof.cast _ _).payloadLength = _
      exact cast_payloadLength _ _
    rw [hcast]
    exact hcollapseZeroRaw
  have htrans := proveEqualityTransitivity_payloadLength_le_primitive
    binaryOneAlgebraTerm zeroPlusOne paOneTerm
    collapseDouble collapseZero
    (paGeneratedTermCodeEnvelope bitWidth)
    hbinaryOneCode hzeroPlusOneCode honeCode
  change
    (proveEqualityTransitivity binaryOneAlgebraTerm zeroPlusOne paOneTerm
      collapseDouble collapseZero).payloadLength <= _
  calc
    _ <= collapseDouble.payloadLength + collapseZero.payloadLength +
        paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope bitWidth) :=
      htrans
    _ <= 3 * paPrimitiveCostEnvelope
          (paGeneratedTermCodeEnvelope bitWidth) +
        paAlgebraStepCostEnvelope bitWidth +
        paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope bitWidth) := by
      exact Nat.add_le_add (Nat.add_le_add hcollapseDouble hcollapseZero) le_rfl
    _ <= paBinaryOneBaseCostEnvelope bitWidth := by
      unfold paBinaryOneBaseCostEnvelope paAlgebraStepCostEnvelope
      omega

theorem proveOneEqualsBinaryOneAlgebra_payloadLength_le_incrementLocal
    (bitWidth : Nat) :
    proveOneEqualsBinaryOneAlgebra.payloadLength <=
      paOneEqualsBinaryOneCostEnvelope bitWidth := by
  have hone : PACompilerGeneratedTerm bitWidth 1 paOneTerm := .one
  have htwo : PACompilerGeneratedTerm bitWidth 1 arithmeticTwoTerm := .two
  have hzero : PACompilerGeneratedTerm bitWidth 1 paZeroTerm := .zero
  have hdoubleZero : PACompilerGeneratedTerm bitWidth 3
      (paMulTerm arithmeticTwoTerm paZeroTerm) := .mul htwo hzero
  have hbinaryOne : PACompilerGeneratedTerm bitWidth 5
      binaryOneAlgebraTerm := by
    simpa [binaryOneAlgebraTerm] using
      (PACompilerGeneratedTerm.add hdoubleZero hone)
  have hsymm := proveEqualitySymmetry_payloadLength_le_primitive
    binaryOneAlgebraTerm paOneTerm proveBinaryOneAlgebraEqualsOne
    (paGeneratedTermCodeEnvelope bitWidth)
    (generatedTerm_code_length_le_compiler hbinaryOne (by omega))
    (generatedTerm_code_length_le_compiler hone (by omega))
  change
    (proveEqualitySymmetry binaryOneAlgebraTerm paOneTerm
      proveBinaryOneAlgebraEqualsOne).payloadLength <= _
  have hbase :=
    proveBinaryOneAlgebraEqualsOne_payloadLength_le_incrementLocal bitWidth
  have hprimitive := paPrimitiveCostEnvelope_le_algebraStep bitWidth
  unfold paOneEqualsBinaryOneCostEnvelope paBinaryOneBaseCostEnvelope
    paAlgebraStepCostEnvelope at *
  omega

theorem proveBinaryNumeralIncrementZero_payloadLength_le_incrementLocal
    (bitWidth : Nat) :
    proveBinaryNumeralIncrementZero.payloadLength <=
      paIncrementLocalCostEnvelope bitWidth := by
  let zeroPlusOne := paAddTerm paZeroTerm paOneTerm
  let algebraProof : CertifiedPAProof
      (“!!zeroPlusOne = !!binaryOneAlgebraTerm” :
        LO.FirstOrder.ArithmeticProposition) :=
    proveEqualityTransitivity zeroPlusOne paOneTerm binaryOneAlgebraTerm
      (proveZeroAdd paOneTerm) proveOneEqualsBinaryOneAlgebra
  have hzero : PACompilerGeneratedTerm bitWidth 1 paZeroTerm := .zero
  have hone : PACompilerGeneratedTerm bitWidth 1 paOneTerm := .one
  have htwo : PACompilerGeneratedTerm bitWidth 1 arithmeticTwoTerm := .two
  have hzeroPlusOne : PACompilerGeneratedTerm bitWidth 3 zeroPlusOne :=
    .add hzero hone
  have hdoubleZero : PACompilerGeneratedTerm bitWidth 3
      (paMulTerm arithmeticTwoTerm paZeroTerm) := .mul htwo hzero
  have hbinaryOne : PACompilerGeneratedTerm bitWidth 5
      binaryOneAlgebraTerm := by
    simpa [binaryOneAlgebraTerm] using
      (PACompilerGeneratedTerm.add hdoubleZero hone)
  have hzeroAdd := proveZeroAdd_payloadLength_le_algebraStep hone (by omega)
  have honeEquals :=
    proveOneEqualsBinaryOneAlgebra_payloadLength_le_incrementLocal bitWidth
  have htrans := proveEqualityTransitivity_payloadLength_le_primitive
    zeroPlusOne paOneTerm binaryOneAlgebraTerm
    (proveZeroAdd paOneTerm) proveOneEqualsBinaryOneAlgebra
    (paGeneratedTermCodeEnvelope bitWidth)
    (generatedTerm_code_length_le_compiler hzeroPlusOne (by omega))
    (generatedTerm_code_length_le_compiler hone (by omega))
    (generatedTerm_code_length_le_compiler hbinaryOne (by omega))
  have halgebra : algebraProof.payloadLength <=
      paAlgebraStepCostEnvelope bitWidth +
        paOneEqualsBinaryOneCostEnvelope bitWidth +
        paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope bitWidth) := by
    dsimp only [algebraProof]
    exact htrans.trans (Nat.add_le_add
      (Nat.add_le_add hzeroAdd honeEquals) le_rfl)
  have hcast : proveBinaryNumeralIncrementZero.payloadLength =
      algebraProof.payloadLength := by
    unfold proveBinaryNumeralIncrementZero
    simp only [cast_payloadLength]
    rfl
  rw [hcast]
  exact halgebra.trans (by
    unfold paIncrementLocalCostEnvelope paOneEqualsBinaryOneCostEnvelope
      paAlgebraStepCostEnvelope
    omega)

theorem proveBinaryNumeralIncrementOddAlgebra_payloadLength_le
    (high bitWidth : Nat)
    (incrementHigh : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm high) paOneTerm) =
        !!(shortBinaryNumeralTerm (high + 1))” :
        LO.FirstOrder.ArithmeticProposition))
    (hhighSize : Nat.size high <= bitWidth)
    (hnextSize : Nat.size (high + 1) <= bitWidth) :
    (proveBinaryNumeralIncrementOddAlgebra high
      incrementHigh).payloadLength <=
      incrementHigh.payloadLength + paIncrementLocalCostEnvelope bitWidth := by
  let highTerm := shortBinaryNumeralTerm high
  let nextTerm := shortBinaryNumeralTerm (high + 1)
  let doubleHigh := paMulTerm arithmeticTwoTerm highTerm
  let onePair := paAddTerm paOneTerm paOneTerm
  let twoMulOne := paMulTerm arithmeticTwoTerm paOneTerm
  let highPlusOne := paAddTerm highTerm paOneTerm
  let source := binaryNumeralIncrementOddSource high
  let assocMiddle := binaryNumeralIncrementOddAssocMiddle high
  let mulMiddle := binaryNumeralIncrementOddMulMiddle high
  let factored := binaryNumeralIncrementOddFactored high
  let result := binaryNumeralIncrementOddResult high
  let association := proveBinaryNumeralIncrementOddAssociation high
  let associationRaw := proveAddAssociativity doubleHigh paOneTerm paOneTerm
  let replacePairRaw := proveAddCongruence
    doubleHigh onePair doubleHigh twoMulOne
    (proveEqualityReflexivityAtTerm doubleHigh)
    proveOnePairToTwoMulOne
  let replacePair := proveBinaryNumeralIncrementOddReplacePair high
  let factorRaw := proveLeftDistributivityReverse
    arithmeticTwoTerm highTerm paOneTerm
  let factor := proveBinaryNumeralIncrementOddFactor high
  let recurseRaw := proveMulCongruence
    arithmeticTwoTerm highPlusOne arithmeticTwoTerm nextTerm
    (proveEqualityReflexivityAtTerm arithmeticTwoTerm) incrementHigh
  let recurse := proveBinaryNumeralIncrementOddRecurse high incrementHigh
  let firstHalf := proveEqualityTransitivity
    source assocMiddle mulMiddle association replacePair
  let throughFactor := proveEqualityTransitivity
    source mulMiddle factored firstHalf factor
  have hhigh : PACompilerGeneratedTerm bitWidth 1 highTerm :=
    .numeral high hhighSize
  have hnext : PACompilerGeneratedTerm bitWidth 1 nextTerm :=
    .numeral (high + 1) hnextSize
  have htwo : PACompilerGeneratedTerm bitWidth 1 arithmeticTwoTerm := .two
  have hone : PACompilerGeneratedTerm bitWidth 1 paOneTerm := .one
  have hdoubleHigh : PACompilerGeneratedTerm bitWidth 3 doubleHigh :=
    .mul htwo hhigh
  have honePair : PACompilerGeneratedTerm bitWidth 3 onePair := .add hone hone
  have htwoMulOne : PACompilerGeneratedTerm bitWidth 3 twoMulOne :=
    .mul htwo hone
  have hhighPlusOne : PACompilerGeneratedTerm bitWidth 3 highPlusOne :=
    .add hhigh hone
  have hsource : PACompilerGeneratedTerm bitWidth 7 source := by
    simpa [source, highTerm, doubleHigh,
      binaryNumeralIncrementOddSource] using
      (PACompilerGeneratedTerm.add
        (PACompilerGeneratedTerm.add hdoubleHigh hone) hone)
  have hassocMiddle : PACompilerGeneratedTerm bitWidth 7 assocMiddle := by
    simpa [assocMiddle, highTerm, doubleHigh, onePair,
      binaryNumeralIncrementOddAssocMiddle] using
      (PACompilerGeneratedTerm.add hdoubleHigh honePair)
  have hmulMiddle : PACompilerGeneratedTerm bitWidth 7 mulMiddle := by
    simpa [mulMiddle, highTerm, doubleHigh, twoMulOne,
      binaryNumeralIncrementOddMulMiddle] using
      (PACompilerGeneratedTerm.add hdoubleHigh htwoMulOne)
  have hfactored : PACompilerGeneratedTerm bitWidth 5 factored := by
    simpa [factored, highTerm, highPlusOne,
      binaryNumeralIncrementOddFactored] using
      (PACompilerGeneratedTerm.mul htwo hhighPlusOne)
  have hresult : PACompilerGeneratedTerm bitWidth 3 result := by
    simpa [result, nextTerm, binaryNumeralIncrementOddResult] using
      (PACompilerGeneratedTerm.mul htwo hnext)
  let termEnvelope := paGeneratedTermCodeEnvelope bitWidth
  let primitive := paPrimitiveCostEnvelope termEnvelope
  have code
      {budget : Nat} {term : LO.FirstOrder.ArithmeticSemiterm Nat 0}
      (hterm : PACompilerGeneratedTerm bitWidth budget term)
      (hbudget : budget <= 64) :
      (binaryTermCode term).length <= termEnvelope := by
    exact generatedTerm_code_length_le_compiler hterm hbudget
  have hassociationRaw := proveAddAssociativity_payloadLength_le_primitive
    doubleHigh paOneTerm paOneTerm termEnvelope
    (code hdoubleHigh (by omega)) (code hone (by omega))
    (code hone (by omega))
  have hassociation : association.payloadLength <= primitive := by
    have hcast : association.payloadLength = associationRaw.payloadLength := by
      dsimp only [association]
      unfold proveBinaryNumeralIncrementOddAssociation
      exact cast_payloadLength _ _
    rw [hcast]
    exact hassociationRaw
  have hreflexiveDouble :=
    proveEqualityReflexivityAtTerm_payloadLength_le_primitive
      doubleHigh termEnvelope (code hdoubleHigh (by omega))
  have honePairProof :=
    proveOnePairToTwoMulOne_payloadLength_le_algebraStep bitWidth
  have hreplaceRaw := proveAddCongruence_payloadLength_le_primitive
    doubleHigh onePair doubleHigh twoMulOne
    (proveEqualityReflexivityAtTerm doubleHigh)
    proveOnePairToTwoMulOne termEnvelope
    (code hdoubleHigh (by omega)) (code honePair (by omega))
    (code hdoubleHigh (by omega)) (code htwoMulOne (by omega))
  have hreplace : replacePair.payloadLength <=
      primitive + paAlgebraStepCostEnvelope bitWidth + primitive := by
    have hcast : replacePair.payloadLength = replacePairRaw.payloadLength := by
      dsimp only [replacePair]
      unfold proveBinaryNumeralIncrementOddReplacePair
      change (CertifiedPAProof.cast _ _).payloadLength = _
      exact cast_payloadLength _ _
    rw [hcast]
    exact hreplaceRaw.trans
      (Nat.add_le_add (Nat.add_le_add hreflexiveDouble honePairProof) le_rfl)
  have hfactorRaw :=
    proveLeftDistributivityReverse_payloadLength_le_algebraStep
      htwo hhigh hone (by omega) (by omega) (by omega)
  have hfactor : factor.payloadLength <=
      paAlgebraStepCostEnvelope bitWidth := by
    have hcast : factor.payloadLength = factorRaw.payloadLength := by
      dsimp only [factor]
      unfold proveBinaryNumeralIncrementOddFactor
      exact cast_payloadLength _ _
    rw [hcast]
    exact hfactorRaw
  have hreflexiveTwo :=
    proveEqualityReflexivityAtTerm_payloadLength_le_primitive
      arithmeticTwoTerm termEnvelope (code htwo (by omega))
  have hrecurseRaw := proveMulCongruence_payloadLength_le_primitive
    arithmeticTwoTerm highPlusOne arithmeticTwoTerm nextTerm
    (proveEqualityReflexivityAtTerm arithmeticTwoTerm) incrementHigh
    termEnvelope (code htwo (by omega)) (code hhighPlusOne (by omega))
    (code htwo (by omega)) (code hnext (by omega))
  have hrecurse : recurse.payloadLength <=
      primitive + incrementHigh.payloadLength + primitive := by
    have hcast : recurse.payloadLength = recurseRaw.payloadLength := by
      dsimp only [recurse]
      unfold proveBinaryNumeralIncrementOddRecurse
      exact cast_payloadLength _ _
    rw [hcast]
    exact hrecurseRaw.trans
      (Nat.add_le_add (Nat.add_le_add hreflexiveTwo le_rfl) le_rfl)
  have hfirstHalf := proveEqualityTransitivity_payloadLength_le_primitive
    source assocMiddle mulMiddle association replacePair termEnvelope
    (code hsource (by omega)) (code hassocMiddle (by omega))
    (code hmulMiddle (by omega))
  have hthroughFactor := proveEqualityTransitivity_payloadLength_le_primitive
    source mulMiddle factored firstHalf factor termEnvelope
    (code hsource (by omega)) (code hmulMiddle (by omega))
    (code hfactored (by omega))
  have hfinal := proveEqualityTransitivity_payloadLength_le_primitive
    source factored result throughFactor recurse termEnvelope
    (code hsource (by omega)) (code hfactored (by omega))
    (code hresult (by omega))
  change
    (proveEqualityTransitivity source factored result
      throughFactor recurse).payloadLength <= _
  calc
    _ <= throughFactor.payloadLength + recurse.payloadLength + primitive :=
      hfinal
    _ <= (firstHalf.payloadLength + factor.payloadLength + primitive) +
        recurse.payloadLength + primitive := by
      exact Nat.add_le_add
        (Nat.add_le_add hthroughFactor le_rfl) le_rfl
    _ <= ((association.payloadLength + replacePair.payloadLength + primitive) +
          factor.payloadLength + primitive) + recurse.payloadLength +
        primitive := by
      exact Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add hfirstHalf le_rfl) le_rfl) le_rfl)
        le_rfl
    _ <= incrementHigh.payloadLength + paIncrementLocalCostEnvelope bitWidth := by
      unfold primitive termEnvelope paIncrementLocalCostEnvelope
        paAlgebraStepCostEnvelope at *
      omega

theorem proveBinaryNumeralIncrementOdd_payloadLength_le
    (high bitWidth : Nat)
    (incrementHigh : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm high) paOneTerm) =
        !!(shortBinaryNumeralTerm (high + 1))” :
        LO.FirstOrder.ArithmeticProposition))
    (hhighSize : Nat.size high <= bitWidth)
    (hnextSize : Nat.size (high + 1) <= bitWidth) :
    (proveBinaryNumeralIncrementOdd high incrementHigh).payloadLength <=
      incrementHigh.payloadLength + paIncrementLocalCostEnvelope bitWidth := by
  have halgebra := proveBinaryNumeralIncrementOddAlgebra_payloadLength_le
    high bitWidth incrementHigh hhighSize hnextSize
  have hcast :
      (proveBinaryNumeralIncrementOdd high incrementHigh).payloadLength =
        (proveBinaryNumeralIncrementOddAlgebra high
          incrementHigh).payloadLength := by
    change (CertifiedPAProof.cast _ _).payloadLength = _
    exact cast_payloadLength _ _
  rw [hcast]
  exact halgebra

theorem proveBinaryNumeralIncrement_payloadLength_le_external
    (value bitWidth : Nat) (hsize : Nat.size value <= bitWidth) :
    (proveBinaryNumeralIncrement value).payloadLength <=
      (Nat.size value + 1) * paIncrementLocalCostEnvelope bitWidth := by
  induction value using Nat.binaryRec' generalizing bitWidth with
  | zero =>
      have hzero :=
        proveBinaryNumeralIncrementZero_payloadLength_le_incrementLocal
          bitWidth
      rw [proveBinaryNumeralIncrement_zero]
      simpa using hzero
  | bit bit high hcanonical ih =>
      have hnonzero : Nat.bit bit high ≠ 0 :=
        Nat.bit_ne_zero_iff.mpr hcanonical
      have hsizeEq : Nat.size (Nat.bit bit high) = Nat.size high + 1 :=
        Nat.size_bit hnonzero
      have hhighSize : Nat.size high <= bitWidth := by omega
      have hnextRaw := natSize_add_one_le high
      have hnextSize : Nat.size (high + 1) <= bitWidth := by omega
      cases bit with
      | false =>
          have hhighNonzero : high ≠ 0 := by
            intro hz
            have himpossible := hcanonical hz
            simp at himpossible
          have heven :=
            proveBinaryNumeralIncrementEven_payloadLength_le_algebraStep
              high bitWidth hhighNonzero hhighSize
          have hlocal :=
            paAlgebraStepCostEnvelope_le_incrementLocal bitWidth
          rw [proveBinaryNumeralIncrement_bit_false high hhighNonzero]
          rw [hsizeEq]
          calc
            (proveBinaryNumeralIncrementEven high hhighNonzero).payloadLength <=
                paAlgebraStepCostEnvelope bitWidth := heven
            _ <= paIncrementLocalCostEnvelope bitWidth := hlocal
            _ <= (Nat.size high + 1 + 1) *
                paIncrementLocalCostEnvelope bitWidth := by
              have hcoefficient : 1 <= Nat.size high + 1 + 1 := by omega
              simpa using Nat.mul_le_mul_right
                (paIncrementLocalCostEnvelope bitWidth) hcoefficient
      | true =>
          have hrecursive := ih bitWidth hhighSize
          have hodd := proveBinaryNumeralIncrementOdd_payloadLength_le
            high bitWidth (proveBinaryNumeralIncrement high)
            hhighSize hnextSize
          rw [proveBinaryNumeralIncrement_bit_true high]
          rw [hsizeEq]
          calc
            (proveBinaryNumeralIncrementOdd high
                (proveBinaryNumeralIncrement high)).payloadLength <=
                (proveBinaryNumeralIncrement high).payloadLength +
                  paIncrementLocalCostEnvelope bitWidth := hodd
            _ <= (Nat.size high + 1) *
                  paIncrementLocalCostEnvelope bitWidth +
                paIncrementLocalCostEnvelope bitWidth :=
              Nat.add_le_add_right hrecursive _
            _ = (Nat.size high + 1 + 1) *
                paIncrementLocalCostEnvelope bitWidth := by ring

def binaryNumeralIncrementPayloadPolynomial (bitWidth : Nat) : Nat :=
  (bitWidth + 1) * paIncrementLocalCostEnvelope bitWidth

theorem proveBinaryNumeralIncrement_payloadLength_le_polynomial
    (value : Nat) :
    (proveBinaryNumeralIncrement value).payloadLength <=
      binaryNumeralIncrementPayloadPolynomial (Nat.size value) := by
  exact proveBinaryNumeralIncrement_payloadLength_le_external
    value (Nat.size value) le_rfl

theorem proveBinaryNumeralIncrement_payloadLength_le_width
    (value bitWidth : Nat) (hsize : Nat.size value <= bitWidth) :
    (proveBinaryNumeralIncrement value).payloadLength <=
      binaryNumeralIncrementPayloadPolynomial bitWidth := by
  have hproof := proveBinaryNumeralIncrement_payloadLength_le_external
    value bitWidth hsize
  unfold binaryNumeralIncrementPayloadPolynomial
  exact hproof.trans (Nat.mul_le_mul_right
    (paIncrementLocalCostEnvelope bitWidth)
    (Nat.add_le_add_right hsize 1))

/-! ## Binary addition branch and recursion bounds -/

def paAdditionWorkWidth (inputWidth : Nat) : Nat := inputWidth + 2

def paAdditionAlgebraCostEnvelope (inputWidth : Nat) : Nat :=
  16 * (paAlgebraStepCostEnvelope (paAdditionWorkWidth inputWidth) +
    binaryNumeralIncrementPayloadPolynomial
      (paAdditionWorkWidth inputWidth))

def paAdditionLocalCostEnvelope (inputWidth : Nat) : Nat :=
  16 * paAdditionAlgebraCostEnvelope inputWidth

theorem paAlgebraStep_le_additionAlgebra (inputWidth : Nat) :
    paAlgebraStepCostEnvelope (paAdditionWorkWidth inputWidth) <=
      paAdditionAlgebraCostEnvelope inputWidth := by
  unfold paAdditionAlgebraCostEnvelope
  omega

theorem incrementPolynomial_le_additionAlgebra (inputWidth : Nat) :
    binaryNumeralIncrementPayloadPolynomial
      (paAdditionWorkWidth inputWidth) <=
      paAdditionAlgebraCostEnvelope inputWidth := by
  unfold paAdditionAlgebraCostEnvelope
  omega

theorem paAdditionAlgebra_le_local (inputWidth : Nat) :
    paAdditionAlgebraCostEnvelope inputWidth <=
      paAdditionLocalCostEnvelope inputWidth := by
  unfold paAdditionLocalCostEnvelope
  omega

theorem numeral_size_le_additionWorkWidth_left
    (left right inputWidth : Nat)
    (hwidth : Nat.size left + Nat.size right <= inputWidth) :
    Nat.size left <= paAdditionWorkWidth inputWidth := by
  unfold paAdditionWorkWidth
  omega

theorem numeral_size_le_additionWorkWidth_right
    (left right inputWidth : Nat)
    (hwidth : Nat.size left + Nat.size right <= inputWidth) :
    Nat.size right <= paAdditionWorkWidth inputWidth := by
  unfold paAdditionWorkWidth
  omega

theorem sum_size_le_additionWorkWidth
    (left right inputWidth : Nat)
    (hwidth : Nat.size left + Nat.size right <= inputWidth) :
    Nat.size (left + right) <= paAdditionWorkWidth inputWidth := by
  have hsum := natSize_add_le left right
  unfold paAdditionWorkWidth
  omega

theorem proveBinaryNumeralAdditionZeroLeft_payloadLength_le
    (right inputWidth : Nat)
    (hrightSize : Nat.size right <= paAdditionWorkWidth inputWidth) :
    (proveBinaryNumeralAdditionZeroLeft right).payloadLength <=
      paAdditionAlgebraCostEnvelope inputWidth := by
  let rightTerm := shortBinaryNumeralTerm right
  have hright : PACompilerGeneratedTerm (paAdditionWorkWidth inputWidth) 1
      rightTerm := .numeral right hrightSize
  have hzeroAdd := proveZeroAdd_payloadLength_le_algebraStep
    hright (by omega)
  have hcast : (proveBinaryNumeralAdditionZeroLeft right).payloadLength =
      (proveZeroAdd rightTerm).payloadLength := by
    unfold proveBinaryNumeralAdditionZeroLeft
    simp only [cast_payloadLength]
    rfl
  rw [hcast]
  exact hzeroAdd.trans (paAlgebraStep_le_additionAlgebra inputWidth)

theorem proveBinaryNumeralAdditionZeroRight_payloadLength_le
    (left inputWidth : Nat)
    (hleftSize : Nat.size left <= paAdditionWorkWidth inputWidth) :
    (proveBinaryNumeralAdditionZeroRight left).payloadLength <=
      paAdditionAlgebraCostEnvelope inputWidth := by
  let leftTerm := shortBinaryNumeralTerm left
  have hleft : PACompilerGeneratedTerm (paAdditionWorkWidth inputWidth) 1
      leftTerm := .numeral left hleftSize
  have hcode := generatedTerm_code_length_le_compiler hleft (by omega)
  have haddZero := proveAddZeroAtPaZero_payloadLength_le_primitive
    leftTerm (paGeneratedTermCodeEnvelope (paAdditionWorkWidth inputWidth))
    hcode
  have hcast : (proveBinaryNumeralAdditionZeroRight left).payloadLength =
      (proveAddZeroAtPaZero leftTerm).payloadLength := by
    unfold proveBinaryNumeralAdditionZeroRight
    simp only [cast_payloadLength]
    rfl
  rw [hcast]
  exact haddZero.trans <| (paPrimitiveCostEnvelope_le_algebraStep
    (paAdditionWorkWidth inputWidth)).trans
      (paAlgebraStep_le_additionAlgebra inputWidth)

theorem proveBinaryAdditionEvenEvenAlgebra_payloadLength_le
    (leftHigh rightHigh inputWidth : Nat)
    (highProof : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm leftHigh)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(binaryAdditionHighSumTerm leftHigh rightHigh)” :
        LO.FirstOrder.ArithmeticProposition))
    (hwidth : Nat.size leftHigh + Nat.size rightHigh <= inputWidth) :
    (proveBinaryAdditionEvenEvenAlgebra leftHigh rightHigh
      highProof).payloadLength <=
      highProof.payloadLength + paAdditionAlgebraCostEnvelope inputWidth := by
  let workWidth := paAdditionWorkWidth inputWidth
  let termEnvelope := paGeneratedTermCodeEnvelope workWidth
  let primitive := paPrimitiveCostEnvelope termEnvelope
  let leftTerm := shortBinaryNumeralTerm leftHigh
  let rightTerm := shortBinaryNumeralTerm rightHigh
  let sumTerm := binaryAdditionHighSumTerm leftHigh rightHigh
  let highAdd := paAddTerm leftTerm rightTerm
  let doubledHighAdd := paMulTerm arithmeticTwoTerm highAdd
  let distributed := paAddTerm
    (paMulTerm arithmeticTwoTerm leftTerm)
    (paMulTerm arithmeticTwoTerm rightTerm)
  let result := paMulTerm arithmeticTwoTerm sumTerm
  let distributionRaw := proveDoubleSum leftTerm rightTerm
  let distribution : CertifiedPAProof
      (“!!distributed = !!doubledHighAdd” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := leftDistributivityReverseAsTerms_formula
      arithmeticTwoTerm leftTerm rightTerm
    simpa [distributed, doubledHighAdd, highAdd] using
      (CertifiedPAProof.cast hformula distributionRaw)
  let recurseRaw := proveMulCongruence
    arithmeticTwoTerm highAdd arithmeticTwoTerm sumTerm
    (proveEqualityReflexivityAtTerm arithmeticTwoTerm) highProof
  let recurse : CertifiedPAProof
      (“!!doubledHighAdd = !!result” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := mulEqualityAsTerm_formula
      arithmeticTwoTerm highAdd arithmeticTwoTerm sumTerm
    simpa [doubledHighAdd, result] using
      (CertifiedPAProof.cast hformula recurseRaw)
  have hleft : PACompilerGeneratedTerm workWidth 1 leftTerm :=
    .numeral leftHigh
      (numeral_size_le_additionWorkWidth_left
        leftHigh rightHigh inputWidth hwidth)
  have hright : PACompilerGeneratedTerm workWidth 1 rightTerm :=
    .numeral rightHigh
      (numeral_size_le_additionWorkWidth_right
        leftHigh rightHigh inputWidth hwidth)
  have hsum : PACompilerGeneratedTerm workWidth 1 sumTerm := by
    exact .numeral (leftHigh + rightHigh)
      (sum_size_le_additionWorkWidth leftHigh rightHigh inputWidth hwidth)
  have htwo : PACompilerGeneratedTerm workWidth 1 arithmeticTwoTerm := .two
  have hhighAdd : PACompilerGeneratedTerm workWidth 3 highAdd :=
    .add hleft hright
  have hdoubledHighAdd : PACompilerGeneratedTerm workWidth 5 doubledHighAdd :=
    .mul htwo hhighAdd
  have hleftDouble : PACompilerGeneratedTerm workWidth 3
      (paMulTerm arithmeticTwoTerm leftTerm) := .mul htwo hleft
  have hrightDouble : PACompilerGeneratedTerm workWidth 3
      (paMulTerm arithmeticTwoTerm rightTerm) := .mul htwo hright
  have hdistributed : PACompilerGeneratedTerm workWidth 7 distributed :=
    .add hleftDouble hrightDouble
  have hresult : PACompilerGeneratedTerm workWidth 3 result := .mul htwo hsum
  have code
      {budget : Nat} {term : LO.FirstOrder.ArithmeticSemiterm Nat 0}
      (hterm : PACompilerGeneratedTerm workWidth budget term)
      (hbudget : budget <= 64) :
      (binaryTermCode term).length <= termEnvelope :=
    generatedTerm_code_length_le_compiler hterm hbudget
  have hdistributionRaw :=
    proveLeftDistributivityReverse_payloadLength_le_algebraStep
      htwo hleft hright (by omega) (by omega) (by omega)
  have hdistribution : distribution.payloadLength <=
      paAlgebraStepCostEnvelope workWidth := by
    have hcast : distribution.payloadLength = distributionRaw.payloadLength := by
      dsimp only [distribution]
      change (CertifiedPAProof.cast _ _).payloadLength = _
      exact cast_payloadLength _ _
    rw [hcast]
    exact hdistributionRaw
  have hreflexive := proveEqualityReflexivityAtTerm_payloadLength_le_primitive
    arithmeticTwoTerm termEnvelope (code htwo (by omega))
  have hrecurseRaw := proveMulCongruence_payloadLength_le_primitive
    arithmeticTwoTerm highAdd arithmeticTwoTerm sumTerm
    (proveEqualityReflexivityAtTerm arithmeticTwoTerm) highProof
    termEnvelope (code htwo (by omega)) (code hhighAdd (by omega))
    (code htwo (by omega)) (code hsum (by omega))
  have hrecurse : recurse.payloadLength <=
      primitive + highProof.payloadLength + primitive := by
    have hcast : recurse.payloadLength = recurseRaw.payloadLength := by
      dsimp only [recurse]
      change (CertifiedPAProof.cast _ _).payloadLength = _
      exact cast_payloadLength _ _
    rw [hcast]
    exact hrecurseRaw.trans
      (Nat.add_le_add (Nat.add_le_add hreflexive le_rfl) le_rfl)
  have htrans := proveEqualityTransitivity_payloadLength_le_primitive
    distributed doubledHighAdd result distribution recurse termEnvelope
    (code hdistributed (by omega)) (code hdoubledHighAdd (by omega))
    (code hresult (by omega))
  change
    (proveEqualityTransitivity distributed doubledHighAdd result
      distribution recurse).payloadLength <= _
  calc
    _ <= distribution.payloadLength + recurse.payloadLength + primitive :=
      htrans
    _ <= paAlgebraStepCostEnvelope workWidth +
        (primitive + highProof.payloadLength + primitive) + primitive := by
      exact Nat.add_le_add
        (Nat.add_le_add hdistribution hrecurse) le_rfl
    _ <= highProof.payloadLength +
        paAdditionAlgebraCostEnvelope inputWidth := by
      unfold primitive termEnvelope paAdditionAlgebraCostEnvelope
        paAlgebraStepCostEnvelope workWidth
      omega

theorem proveBinaryNumeralAdditionEvenEven_payloadLength_le
    (leftHigh rightHigh inputWidth : Nat)
    (hleft : leftHigh ≠ 0) (hright : rightHigh ≠ 0)
    (highProof : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm leftHigh)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(binaryAdditionHighSumTerm leftHigh rightHigh)” :
        LO.FirstOrder.ArithmeticProposition))
    (hwidth : Nat.size leftHigh + Nat.size rightHigh <= inputWidth) :
    (proveBinaryNumeralAdditionEvenEven leftHigh rightHigh
      hleft hright highProof).payloadLength <=
      highProof.payloadLength + paAdditionAlgebraCostEnvelope inputWidth := by
  have halgebra := proveBinaryAdditionEvenEvenAlgebra_payloadLength_le
    leftHigh rightHigh inputWidth highProof hwidth
  have hcast :
      (proveBinaryNumeralAdditionEvenEven leftHigh rightHigh
        hleft hright highProof).payloadLength =
      (proveBinaryAdditionEvenEvenAlgebra leftHigh rightHigh
        highProof).payloadLength := by
    unfold proveBinaryNumeralAdditionEvenEven
    simp only [cast_payloadLength]
  rw [hcast]
  exact halgebra

theorem proveBinaryAdditionEvenOddAlgebra_payloadLength_le
    (leftHigh rightHigh inputWidth : Nat)
    (highProof : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm leftHigh)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(binaryAdditionHighSumTerm leftHigh rightHigh)” :
        LO.FirstOrder.ArithmeticProposition))
    (hwidth : Nat.size leftHigh + Nat.size rightHigh <= inputWidth) :
    (proveBinaryAdditionEvenOddAlgebra leftHigh rightHigh
      highProof).payloadLength <=
      highProof.payloadLength + paAdditionAlgebraCostEnvelope inputWidth := by
  let workWidth := paAdditionWorkWidth inputWidth
  let termEnvelope := paGeneratedTermCodeEnvelope workWidth
  let primitive := paPrimitiveCostEnvelope termEnvelope
  let leftTerm := shortBinaryNumeralTerm leftHigh
  let rightTerm := shortBinaryNumeralTerm rightHigh
  let sumTerm := binaryAdditionHighSumTerm leftHigh rightHigh
  let doubleLeft := paMulTerm arithmeticTwoTerm leftTerm
  let doubleRight := paMulTerm arithmeticTwoTerm rightTerm
  let source := paAddTerm doubleLeft (paAddTerm doubleRight paOneTerm)
  let grouped := paAddTerm (paAddTerm doubleLeft doubleRight) paOneTerm
  let highAdd := paAddTerm leftTerm rightTerm
  let doubledHighAdd := paMulTerm arithmeticTwoTerm highAdd
  let distributed := paAddTerm doubledHighAdd paOneTerm
  let result := paAddTerm (paMulTerm arithmeticTwoTerm sumTerm) paOneTerm
  let groupingRaw := proveAddAssociativityReverse
    doubleLeft doubleRight paOneTerm
  let grouping : CertifiedPAProof
      (“!!source = !!grouped” : LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      doubleLeft (paAddTerm doubleRight paOneTerm)
      (paAddTerm doubleLeft doubleRight) paOneTerm
    simpa [source, grouped] using
      (CertifiedPAProof.cast hformula groupingRaw)
  let doubleRaw := proveDoubleSum leftTerm rightTerm
  let doubleAsTerms : CertifiedPAProof
      (“!!(paAddTerm doubleLeft doubleRight) = !!doubledHighAdd” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := leftDistributivityReverseAsTerms_formula
      arithmeticTwoTerm leftTerm rightTerm
    simpa [doubleLeft, doubleRight, doubledHighAdd, highAdd] using
      (CertifiedPAProof.cast hformula doubleRaw)
  let distributeRaw := proveAddCongruence
    (paAddTerm doubleLeft doubleRight) paOneTerm
    doubledHighAdd paOneTerm doubleAsTerms
    (proveEqualityReflexivityAtTerm paOneTerm)
  let distribute : CertifiedPAProof
      (“!!grouped = !!distributed” : LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      (paAddTerm doubleLeft doubleRight) paOneTerm
      doubledHighAdd paOneTerm
    simpa [grouped, distributed] using
      (CertifiedPAProof.cast hformula distributeRaw)
  let recurseMulRaw := proveMulCongruence
    arithmeticTwoTerm highAdd arithmeticTwoTerm sumTerm
    (proveEqualityReflexivityAtTerm arithmeticTwoTerm) highProof
  let recurseMul : CertifiedPAProof
      (“!!doubledHighAdd =
        !!(paMulTerm arithmeticTwoTerm sumTerm)” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := mulEqualityAsTerm_formula
      arithmeticTwoTerm highAdd arithmeticTwoTerm sumTerm
    simpa [doubledHighAdd] using
      (CertifiedPAProof.cast hformula recurseMulRaw)
  let recurseRaw := proveAddCongruence
    doubledHighAdd paOneTerm
    (paMulTerm arithmeticTwoTerm sumTerm) paOneTerm
    recurseMul (proveEqualityReflexivityAtTerm paOneTerm)
  let recurse : CertifiedPAProof
      (“!!distributed = !!result” : LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      doubledHighAdd paOneTerm
      (paMulTerm arithmeticTwoTerm sumTerm) paOneTerm
    simpa [distributed, result] using
      (CertifiedPAProof.cast hformula recurseRaw)
  let firstHalf := proveEqualityTransitivity source grouped distributed
    grouping distribute
  have hleft : PACompilerGeneratedTerm workWidth 1 leftTerm :=
    .numeral leftHigh
      (numeral_size_le_additionWorkWidth_left
        leftHigh rightHigh inputWidth hwidth)
  have hright : PACompilerGeneratedTerm workWidth 1 rightTerm :=
    .numeral rightHigh
      (numeral_size_le_additionWorkWidth_right
        leftHigh rightHigh inputWidth hwidth)
  have hsum : PACompilerGeneratedTerm workWidth 1 sumTerm :=
    .numeral (leftHigh + rightHigh)
      (sum_size_le_additionWorkWidth leftHigh rightHigh inputWidth hwidth)
  have htwo : PACompilerGeneratedTerm workWidth 1 arithmeticTwoTerm := .two
  have hone : PACompilerGeneratedTerm workWidth 1 paOneTerm := .one
  have hdoubleLeft : PACompilerGeneratedTerm workWidth 3 doubleLeft :=
    .mul htwo hleft
  have hdoubleRight : PACompilerGeneratedTerm workWidth 3 doubleRight :=
    .mul htwo hright
  have hrightOdd : PACompilerGeneratedTerm workWidth 5
      (paAddTerm doubleRight paOneTerm) := .add hdoubleRight hone
  have hsource : PACompilerGeneratedTerm workWidth 9 source :=
    .add hdoubleLeft hrightOdd
  have hdoubleSum : PACompilerGeneratedTerm workWidth 7
      (paAddTerm doubleLeft doubleRight) := .add hdoubleLeft hdoubleRight
  have hgrouped : PACompilerGeneratedTerm workWidth 9 grouped :=
    .add hdoubleSum hone
  have hhighAdd : PACompilerGeneratedTerm workWidth 3 highAdd :=
    .add hleft hright
  have hdoubledHighAdd : PACompilerGeneratedTerm workWidth 5 doubledHighAdd :=
    .mul htwo hhighAdd
  have hdistributed : PACompilerGeneratedTerm workWidth 7 distributed :=
    .add hdoubledHighAdd hone
  have hsumDouble : PACompilerGeneratedTerm workWidth 3
      (paMulTerm arithmeticTwoTerm sumTerm) := .mul htwo hsum
  have hresult : PACompilerGeneratedTerm workWidth 5 result :=
    .add hsumDouble hone
  have code
      {budget : Nat} {term : LO.FirstOrder.ArithmeticSemiterm Nat 0}
      (hterm : PACompilerGeneratedTerm workWidth budget term)
      (hbudget : budget <= 64) :
      (binaryTermCode term).length <= termEnvelope :=
    generatedTerm_code_length_le_compiler hterm hbudget
  have hgroupingRaw :=
    proveAddAssociativityReverse_payloadLength_le_algebraStep
      hdoubleLeft hdoubleRight hone (by omega) (by omega) (by omega)
  have hgrouping : grouping.payloadLength <=
      paAlgebraStepCostEnvelope workWidth := by
    have hcast : grouping.payloadLength = groupingRaw.payloadLength := by
      dsimp only [grouping]
      change (CertifiedPAProof.cast _ _).payloadLength = _
      exact cast_payloadLength _ _
    rw [hcast]
    exact hgroupingRaw
  have hdoubleRaw :=
    proveLeftDistributivityReverse_payloadLength_le_algebraStep
      htwo hleft hright (by omega) (by omega) (by omega)
  have hdouble : doubleAsTerms.payloadLength <=
      paAlgebraStepCostEnvelope workWidth := by
    have hcast : doubleAsTerms.payloadLength = doubleRaw.payloadLength := by
      dsimp only [doubleAsTerms]
      change (CertifiedPAProof.cast _ _).payloadLength = _
      exact cast_payloadLength _ _
    rw [hcast]
    exact hdoubleRaw
  have hreflexiveOne := proveEqualityReflexivityAtTerm_payloadLength_le_primitive
    paOneTerm termEnvelope (code hone (by omega))
  have hdistributeRaw := proveAddCongruence_payloadLength_le_primitive
    (paAddTerm doubleLeft doubleRight) paOneTerm
    doubledHighAdd paOneTerm doubleAsTerms
    (proveEqualityReflexivityAtTerm paOneTerm) termEnvelope
    (code hdoubleSum (by omega)) (code hone (by omega))
    (code hdoubledHighAdd (by omega)) (code hone (by omega))
  have hdistribute : distribute.payloadLength <=
      paAlgebraStepCostEnvelope workWidth + primitive + primitive := by
    have hcast : distribute.payloadLength = distributeRaw.payloadLength := by
      dsimp only [distribute]
      change (CertifiedPAProof.cast _ _).payloadLength = _
      exact cast_payloadLength _ _
    rw [hcast]
    exact hdistributeRaw.trans
      (Nat.add_le_add (Nat.add_le_add hdouble hreflexiveOne) le_rfl)
  have hreflexiveTwo := proveEqualityReflexivityAtTerm_payloadLength_le_primitive
    arithmeticTwoTerm termEnvelope (code htwo (by omega))
  have hrecurseMulRaw := proveMulCongruence_payloadLength_le_primitive
    arithmeticTwoTerm highAdd arithmeticTwoTerm sumTerm
    (proveEqualityReflexivityAtTerm arithmeticTwoTerm) highProof
    termEnvelope (code htwo (by omega)) (code hhighAdd (by omega))
    (code htwo (by omega)) (code hsum (by omega))
  have hrecurseMul : recurseMul.payloadLength <=
      primitive + highProof.payloadLength + primitive := by
    have hcast : recurseMul.payloadLength = recurseMulRaw.payloadLength := by
      dsimp only [recurseMul]
      change (CertifiedPAProof.cast _ _).payloadLength = _
      exact cast_payloadLength _ _
    rw [hcast]
    exact hrecurseMulRaw.trans
      (Nat.add_le_add (Nat.add_le_add hreflexiveTwo le_rfl) le_rfl)
  have hrecurseRawBound := proveAddCongruence_payloadLength_le_primitive
    doubledHighAdd paOneTerm (paMulTerm arithmeticTwoTerm sumTerm) paOneTerm
    recurseMul (proveEqualityReflexivityAtTerm paOneTerm) termEnvelope
    (code hdoubledHighAdd (by omega)) (code hone (by omega))
    (code hsumDouble (by omega)) (code hone (by omega))
  have hrecurse : recurse.payloadLength <=
      (primitive + highProof.payloadLength + primitive) + primitive +
        primitive := by
    have hcast : recurse.payloadLength = recurseRaw.payloadLength := by
      dsimp only [recurse]
      change (CertifiedPAProof.cast _ _).payloadLength = _
      exact cast_payloadLength _ _
    rw [hcast]
    exact hrecurseRawBound.trans
      (Nat.add_le_add (Nat.add_le_add hrecurseMul hreflexiveOne) le_rfl)
  have hfirstHalf := proveEqualityTransitivity_payloadLength_le_primitive
    source grouped distributed grouping distribute termEnvelope
    (code hsource (by omega)) (code hgrouped (by omega))
    (code hdistributed (by omega))
  have hfinal := proveEqualityTransitivity_payloadLength_le_primitive
    source distributed result firstHalf recurse termEnvelope
    (code hsource (by omega)) (code hdistributed (by omega))
    (code hresult (by omega))
  change
    (proveEqualityTransitivity source distributed result
      firstHalf recurse).payloadLength <= _
  calc
    _ <= firstHalf.payloadLength + recurse.payloadLength + primitive := hfinal
    _ <= (grouping.payloadLength + distribute.payloadLength + primitive) +
        recurse.payloadLength + primitive := by
      exact Nat.add_le_add (Nat.add_le_add hfirstHalf le_rfl) le_rfl
    _ <= highProof.payloadLength +
        paAdditionAlgebraCostEnvelope inputWidth := by
      unfold primitive termEnvelope paAdditionAlgebraCostEnvelope
        paAlgebraStepCostEnvelope workWidth at *
      omega

theorem proveBinaryNumeralAdditionEvenOdd_payloadLength_le
    (leftHigh rightHigh inputWidth : Nat) (hleft : leftHigh ≠ 0)
    (highProof : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm leftHigh)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(binaryAdditionHighSumTerm leftHigh rightHigh)” :
        LO.FirstOrder.ArithmeticProposition))
    (hwidth : Nat.size leftHigh + Nat.size rightHigh <= inputWidth) :
    (proveBinaryNumeralAdditionEvenOdd leftHigh rightHigh
      hleft highProof).payloadLength <=
      highProof.payloadLength + paAdditionAlgebraCostEnvelope inputWidth := by
  have halgebra := proveBinaryAdditionEvenOddAlgebra_payloadLength_le
    leftHigh rightHigh inputWidth highProof hwidth
  have hcast :
      (proveBinaryNumeralAdditionEvenOdd leftHigh rightHigh
        hleft highProof).payloadLength =
      (proveBinaryAdditionEvenOddAlgebra leftHigh rightHigh
        highProof).payloadLength := by
    unfold proveBinaryNumeralAdditionEvenOdd
    simp only [cast_payloadLength]
  rw [hcast]
  exact halgebra

def paOddEvenBranchCostEnvelope (inputWidth : Nat) : Nat :=
  4 * paAdditionAlgebraCostEnvelope inputWidth

def paOddOddBranchCostEnvelope (inputWidth : Nat) : Nat :=
  8 * paAdditionAlgebraCostEnvelope inputWidth

theorem proveSwappedBinaryHighAddition_payloadLength_le
    (leftHigh rightHigh inputWidth : Nat)
    (highProof : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm leftHigh)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(binaryAdditionHighSumTerm leftHigh rightHigh)” :
        LO.FirstOrder.ArithmeticProposition))
    (hwidth : Nat.size leftHigh + Nat.size rightHigh <= inputWidth) :
    (proveSwappedBinaryHighAddition leftHigh rightHigh
      highProof).payloadLength <=
      highProof.payloadLength + paAdditionAlgebraCostEnvelope inputWidth := by
  let workWidth := paAdditionWorkWidth inputWidth
  let termEnvelope := paGeneratedTermCodeEnvelope workWidth
  let primitive := paPrimitiveCostEnvelope termEnvelope
  let leftTerm := shortBinaryNumeralTerm leftHigh
  let rightTerm := shortBinaryNumeralTerm rightHigh
  let leftPlusRight := binaryAdditionHighSumTerm leftHigh rightHigh
  let rightPlusLeft := binaryAdditionHighSumTerm rightHigh leftHigh
  let source := paAddTerm rightTerm leftTerm
  let middle := paAddTerm leftTerm rightTerm
  let commRaw := proveAddCommutativity rightTerm leftTerm
  let comm : CertifiedPAProof
      (“!!source = !!middle” : LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      rightTerm leftTerm leftTerm rightTerm
    exact CertifiedPAProof.cast hformula commRaw
  let throughOriginal := proveEqualityTransitivity
    source middle leftPlusRight comm highProof
  have hleft : PACompilerGeneratedTerm workWidth 1 leftTerm :=
    .numeral leftHigh
      (numeral_size_le_additionWorkWidth_left
        leftHigh rightHigh inputWidth hwidth)
  have hright : PACompilerGeneratedTerm workWidth 1 rightTerm :=
    .numeral rightHigh
      (numeral_size_le_additionWorkWidth_right
        leftHigh rightHigh inputWidth hwidth)
  have hsum : PACompilerGeneratedTerm workWidth 1 leftPlusRight :=
    .numeral (leftHigh + rightHigh)
      (sum_size_le_additionWorkWidth leftHigh rightHigh inputWidth hwidth)
  have hsource : PACompilerGeneratedTerm workWidth 3 source := .add hright hleft
  have hmiddle : PACompilerGeneratedTerm workWidth 3 middle := .add hleft hright
  have code
      {budget : Nat} {term : LO.FirstOrder.ArithmeticSemiterm Nat 0}
      (hterm : PACompilerGeneratedTerm workWidth budget term)
      (hbudget : budget <= 64) :
      (binaryTermCode term).length <= termEnvelope :=
    generatedTerm_code_length_le_compiler hterm hbudget
  have hcommRaw := proveAddCommutativity_payloadLength_le_primitive
    rightTerm leftTerm termEnvelope (code hright (by omega))
    (code hleft (by omega))
  have hcomm : comm.payloadLength <= primitive := by
    have hcast : comm.payloadLength = commRaw.payloadLength := by
      dsimp only [comm]
      exact cast_payloadLength _ _
    rw [hcast]
    exact hcommRaw
  have htrans := proveEqualityTransitivity_payloadLength_le_primitive
    source middle leftPlusRight comm highProof termEnvelope
    (code hsource (by omega)) (code hmiddle (by omega))
    (code hsum (by omega))
  have houterCast :
      (proveSwappedBinaryHighAddition leftHigh rightHigh
        highProof).payloadLength = throughOriginal.payloadLength := by
    unfold proveSwappedBinaryHighAddition
    simp only [cast_payloadLength]
    rfl
  rw [houterCast]
  calc
    _ <= comm.payloadLength + highProof.payloadLength + primitive := htrans
    _ <= primitive + highProof.payloadLength + primitive :=
      Nat.add_le_add (Nat.add_le_add hcomm le_rfl) le_rfl
    _ <= highProof.payloadLength +
        paAdditionAlgebraCostEnvelope inputWidth := by
      unfold primitive termEnvelope paAdditionAlgebraCostEnvelope
        paAlgebraStepCostEnvelope workWidth
      omega

theorem oddEvenSum_size_le_additionWorkWidth
    (leftHigh rightHigh inputWidth : Nat)
    (hwidth : Nat.size leftHigh + Nat.size rightHigh <= inputWidth) :
    Nat.size (Nat.bit true leftHigh + Nat.bit false rightHigh) <=
      paAdditionWorkWidth inputWidth := by
  have hsumEq :
      Nat.bit true leftHigh + Nat.bit false rightHigh =
        Nat.bit true (leftHigh + rightHigh) := by
    simp [Nat.bit_val, Nat.mul_add]
    omega
  have hsumNonzero : Nat.bit true (leftHigh + rightHigh) ≠ 0 := by
    simp [Nat.bit_val]
  rw [hsumEq, Nat.size_bit hsumNonzero]
  have hsum := natSize_add_le leftHigh rightHigh
  unfold paAdditionWorkWidth
  omega

theorem proveBinaryNumeralAdditionOddEven_payloadLength_le
    (leftHigh rightHigh inputWidth : Nat) (hright : rightHigh ≠ 0)
    (highProof : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm leftHigh)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(binaryAdditionHighSumTerm leftHigh rightHigh)” :
        LO.FirstOrder.ArithmeticProposition))
    (hwidth : Nat.size leftHigh + Nat.size rightHigh <= inputWidth) :
    (proveBinaryNumeralAdditionOddEven leftHigh rightHigh
      hright highProof).payloadLength <=
      highProof.payloadLength + paOddEvenBranchCostEnvelope inputWidth := by
  let workWidth := paAdditionWorkWidth inputWidth
  let termEnvelope := paGeneratedTermCodeEnvelope workWidth
  let primitive := paPrimitiveCostEnvelope termEnvelope
  let oddValue := Nat.bit true leftHigh
  let evenValue := Nat.bit false rightHigh
  let resultValue := oddValue + evenValue
  let swappedResultValue := evenValue + oddValue
  let oddTerm := shortBinaryNumeralTerm oddValue
  let evenTerm := shortBinaryNumeralTerm evenValue
  let resultTerm := shortBinaryNumeralTerm resultValue
  let swappedResultTerm := shortBinaryNumeralTerm swappedResultValue
  let source := paAddTerm oddTerm evenTerm
  let swapped := paAddTerm evenTerm oddTerm
  let commRaw := proveAddCommutativity oddTerm evenTerm
  let comm : CertifiedPAProof
      (“!!source = !!swapped” : LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      oddTerm evenTerm evenTerm oddTerm
    exact CertifiedPAProof.cast hformula commRaw
  let swappedHigh := proveSwappedBinaryHighAddition
    leftHigh rightHigh highProof
  let swappedResult := proveBinaryNumeralAdditionEvenOdd
    rightHigh leftHigh hright swappedHigh
  let throughSwap := proveEqualityTransitivity
    source swapped swappedResultTerm comm swappedResult
  have hleftBitNonzero : Nat.bit true leftHigh ≠ 0 := by simp [Nat.bit_val]
  have hrightBitNonzero : Nat.bit false rightHigh ≠ 0 := by
    simp [Nat.bit_val, hright]
  have hleftBitSize : Nat.size oddValue <= workWidth := by
    dsimp only [oddValue, workWidth]
    rw [Nat.size_bit hleftBitNonzero]
    unfold paAdditionWorkWidth
    omega
  have hrightBitSize : Nat.size evenValue <= workWidth := by
    dsimp only [evenValue, workWidth]
    rw [Nat.size_bit hrightBitNonzero]
    unfold paAdditionWorkWidth
    omega
  have hresultSize : Nat.size resultValue <= workWidth := by
    exact oddEvenSum_size_le_additionWorkWidth
      leftHigh rightHigh inputWidth hwidth
  have hswappedResultSize : Nat.size swappedResultValue <= workWidth := by
    dsimp only [swappedResultValue, evenValue, oddValue]
    rw [Nat.add_comm]
    exact oddEvenSum_size_le_additionWorkWidth
      leftHigh rightHigh inputWidth hwidth
  have hodd : PACompilerGeneratedTerm workWidth 1 oddTerm :=
    .numeral oddValue hleftBitSize
  have heven : PACompilerGeneratedTerm workWidth 1 evenTerm :=
    .numeral evenValue hrightBitSize
  have hresult : PACompilerGeneratedTerm workWidth 1 resultTerm :=
    .numeral resultValue hresultSize
  have hswappedResultTerm :
      PACompilerGeneratedTerm workWidth 1 swappedResultTerm :=
    .numeral swappedResultValue hswappedResultSize
  have hsource : PACompilerGeneratedTerm workWidth 3 source := .add hodd heven
  have hswapped : PACompilerGeneratedTerm workWidth 3 swapped := .add heven hodd
  have code
      {budget : Nat} {term : LO.FirstOrder.ArithmeticSemiterm Nat 0}
      (hterm : PACompilerGeneratedTerm workWidth budget term)
      (hbudget : budget <= 64) :
      (binaryTermCode term).length <= termEnvelope :=
    generatedTerm_code_length_le_compiler hterm hbudget
  have hcommRaw := proveAddCommutativity_payloadLength_le_primitive
    oddTerm evenTerm termEnvelope (code hodd (by omega))
    (code heven (by omega))
  have hcomm : comm.payloadLength <= primitive := by
    have hcast : comm.payloadLength = commRaw.payloadLength := by
      dsimp only [comm]
      exact cast_payloadLength _ _
    rw [hcast]
    exact hcommRaw
  have hswappedHigh := proveSwappedBinaryHighAddition_payloadLength_le
    leftHigh rightHigh inputWidth highProof hwidth
  have hswappedWidth : Nat.size rightHigh + Nat.size leftHigh <= inputWidth := by
    simpa [Nat.add_comm] using hwidth
  have hswappedResultBound :=
    proveBinaryNumeralAdditionEvenOdd_payloadLength_le
    rightHigh leftHigh inputWidth hright swappedHigh hswappedWidth
  have htrans := proveEqualityTransitivity_payloadLength_le_primitive
    source swapped swappedResultTerm comm swappedResult termEnvelope
    (code hsource (by omega)) (code hswapped (by omega))
    (code hswappedResultTerm (by omega))
  have houterCast :
      (proveBinaryNumeralAdditionOddEven leftHigh rightHigh
        hright highProof).payloadLength = throughSwap.payloadLength := by
    unfold proveBinaryNumeralAdditionOddEven
    simp only [cast_payloadLength]
    rfl
  rw [houterCast]
  calc
    _ <= comm.payloadLength + swappedResult.payloadLength + primitive := htrans
    _ <= primitive +
        ((highProof.payloadLength + paAdditionAlgebraCostEnvelope inputWidth) +
          paAdditionAlgebraCostEnvelope inputWidth) + primitive := by
      exact Nat.add_le_add
        (Nat.add_le_add hcomm
          (hswappedResultBound.trans
            (Nat.add_le_add_right hswappedHigh _))) le_rfl
    _ <= highProof.payloadLength + paOddEvenBranchCostEnvelope inputWidth := by
      unfold paOddEvenBranchCostEnvelope paAdditionAlgebraCostEnvelope
        paAlgebraStepCostEnvelope primitive termEnvelope workWidth
      omega

theorem proveBinaryNumeralAdditionOddOddNonzero_payloadLength_le
    (leftHigh rightHigh inputWidth : Nat) (hright : rightHigh ≠ 0)
    (highProof : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm leftHigh)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(binaryAdditionHighSumTerm leftHigh rightHigh)” :
        LO.FirstOrder.ArithmeticProposition))
    (hwidth : Nat.size leftHigh + Nat.size rightHigh <= inputWidth) :
    (proveBinaryNumeralAdditionOddOddNonzero leftHigh rightHigh
      hright highProof).payloadLength <=
      highProof.payloadLength + paOddOddBranchCostEnvelope inputWidth := by
  let workWidth := paAdditionWorkWidth inputWidth
  let termEnvelope := paGeneratedTermCodeEnvelope workWidth
  let primitive := paPrimitiveCostEnvelope termEnvelope
  let oddLeftValue := Nat.bit true leftHigh
  let evenRightValue := Nat.bit false rightHigh
  let intermediate := oddOddIntermediateValue leftHigh rightHigh
  let oddLeft := shortBinaryNumeralTerm oddLeftValue
  let rightTerm := shortBinaryNumeralTerm rightHigh
  let doubleRight := paMulTerm arithmeticTwoTerm rightTerm
  let oddRight := paAddTerm doubleRight paOneTerm
  let source := paAddTerm oddLeft oddRight
  let grouped := paAddTerm (paAddTerm oddLeft doubleRight) paOneTerm
  let intermediateTerm := shortBinaryNumeralTerm intermediate
  let normalizedGrouped := paAddTerm intermediateTerm paOneTerm
  let resultTerm := shortBinaryNumeralTerm (intermediate + 1)
  let associationRaw := proveAddAssociativityReverse
    oddLeft doubleRight paOneTerm
  let association : CertifiedPAProof
      (“!!source = !!grouped” : LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      oddLeft (paAddTerm doubleRight paOneTerm)
      (paAddTerm oddLeft doubleRight) paOneTerm
    simpa [source, grouped, oddRight] using
      (CertifiedPAProof.cast hformula associationRaw)
  let oddEven := proveBinaryNumeralAdditionOddEven
    leftHigh rightHigh hright highProof
  let normalizeInner : CertifiedPAProof
      (“!!(paAddTerm oddLeft doubleRight) = !!intermediateTerm” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula :
        (“!!(paAddTerm
            (shortBinaryNumeralTerm (Nat.bit true leftHigh))
            (shortBinaryNumeralTerm (Nat.bit false rightHigh))) =
          !!(shortBinaryNumeralTerm
            (Nat.bit true leftHigh + Nat.bit false rightHigh))” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(paAddTerm oddLeft doubleRight) = !!intermediateTerm” :
          LO.FirstOrder.ArithmeticProposition) := by
      rw [shortBinaryNumeralTerm_bit_false rightHigh hright]
      rfl
    exact CertifiedPAProof.cast hformula oddEven
  let liftRaw := proveAddCongruence
    (paAddTerm oddLeft doubleRight) paOneTerm
    intermediateTerm paOneTerm normalizeInner
    (proveEqualityReflexivityAtTerm paOneTerm)
  let lift : CertifiedPAProof
      (“!!grouped = !!normalizedGrouped” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      (paAddTerm oddLeft doubleRight) paOneTerm
      intermediateTerm paOneTerm
    simpa [grouped, normalizedGrouped] using
      (CertifiedPAProof.cast hformula liftRaw)
  let increment := proveBinaryNumeralIncrement intermediate
  let throughGrouping := proveEqualityTransitivity
    source grouped normalizedGrouped association lift
  let throughIncrement := proveEqualityTransitivity
    source normalizedGrouped resultTerm throughGrouping increment
  have hleftBitNonzero : Nat.bit true leftHigh ≠ 0 := by simp [Nat.bit_val]
  have hrightBitNonzero : Nat.bit false rightHigh ≠ 0 := by
    simp [Nat.bit_val, hright]
  have hleftBitSize : Nat.size oddLeftValue <= workWidth := by
    dsimp only [oddLeftValue, workWidth]
    rw [Nat.size_bit hleftBitNonzero]
    unfold paAdditionWorkWidth
    omega
  have hrightSize : Nat.size rightHigh <= workWidth :=
    numeral_size_le_additionWorkWidth_right
      leftHigh rightHigh inputWidth hwidth
  have hintermediateSize : Nat.size intermediate <= workWidth := by
    exact oddEvenSum_size_le_additionWorkWidth
      leftHigh rightHigh inputWidth hwidth
  have hintermediateSizeTight : Nat.size intermediate <= inputWidth + 1 := by
    have hsum := natSize_add_le_sum_of_right_ne_zero
      leftHigh rightHigh hright
    have hbitNonzero : Nat.bit true (leftHigh + rightHigh) ≠ 0 := by
      simp [Nat.bit_val]
    have hvalue : intermediate = Nat.bit true (leftHigh + rightHigh) := by
      simp [intermediate, oddOddIntermediateValue, Nat.bit_val, Nat.mul_add]
      omega
    rw [hvalue, Nat.size_bit hbitNonzero]
    omega
  have hresultSize : Nat.size (intermediate + 1) <= workWidth := by
    have hnext := natSize_add_one_le intermediate
    unfold workWidth paAdditionWorkWidth
    omega
  have hoddLeft : PACompilerGeneratedTerm workWidth 1 oddLeft :=
    .numeral oddLeftValue hleftBitSize
  have hrightTerm : PACompilerGeneratedTerm workWidth 1 rightTerm :=
    .numeral rightHigh hrightSize
  have htwo : PACompilerGeneratedTerm workWidth 1 arithmeticTwoTerm := .two
  have hone : PACompilerGeneratedTerm workWidth 1 paOneTerm := .one
  have hdoubleRight : PACompilerGeneratedTerm workWidth 3 doubleRight :=
    .mul htwo hrightTerm
  have hoddRight : PACompilerGeneratedTerm workWidth 5 oddRight :=
    .add hdoubleRight hone
  have hsource : PACompilerGeneratedTerm workWidth 7 source :=
    .add hoddLeft hoddRight
  have hinner : PACompilerGeneratedTerm workWidth 5
      (paAddTerm oddLeft doubleRight) := .add hoddLeft hdoubleRight
  have hgrouped : PACompilerGeneratedTerm workWidth 7 grouped :=
    .add hinner hone
  have hintermediate : PACompilerGeneratedTerm workWidth 1 intermediateTerm :=
    .numeral intermediate hintermediateSize
  have hnormalized : PACompilerGeneratedTerm workWidth 3 normalizedGrouped :=
    .add hintermediate hone
  have hresult : PACompilerGeneratedTerm workWidth 1 resultTerm :=
    .numeral (intermediate + 1) hresultSize
  have code
      {budget : Nat} {term : LO.FirstOrder.ArithmeticSemiterm Nat 0}
      (hterm : PACompilerGeneratedTerm workWidth budget term)
      (hbudget : budget <= 64) :
      (binaryTermCode term).length <= termEnvelope :=
    generatedTerm_code_length_le_compiler hterm hbudget
  have hassociationRaw :=
    proveAddAssociativityReverse_payloadLength_le_algebraStep
      hoddLeft hdoubleRight hone (by omega) (by omega) (by omega)
  have hassociation : association.payloadLength <=
      paAlgebraStepCostEnvelope workWidth := by
    have hcast : association.payloadLength = associationRaw.payloadLength := by
      dsimp only [association]
      change (CertifiedPAProof.cast _ _).payloadLength = _
      exact cast_payloadLength _ _
    rw [hcast]
    exact hassociationRaw
  have hoddEven := proveBinaryNumeralAdditionOddEven_payloadLength_le
    leftHigh rightHigh inputWidth hright highProof hwidth
  have hnormalize : normalizeInner.payloadLength <=
      highProof.payloadLength + paOddEvenBranchCostEnvelope inputWidth := by
    have hcast : normalizeInner.payloadLength = oddEven.payloadLength := by
      dsimp only [normalizeInner]
      exact cast_payloadLength _ _
    rw [hcast]
    exact hoddEven
  have hreflexiveOne := proveEqualityReflexivityAtTerm_payloadLength_le_primitive
    paOneTerm termEnvelope (code hone (by omega))
  have hliftRaw := proveAddCongruence_payloadLength_le_primitive
    (paAddTerm oddLeft doubleRight) paOneTerm intermediateTerm paOneTerm
    normalizeInner (proveEqualityReflexivityAtTerm paOneTerm)
    termEnvelope (code hinner (by omega)) (code hone (by omega))
    (code hintermediate (by omega)) (code hone (by omega))
  have hlift : lift.payloadLength <=
      (highProof.payloadLength + paOddEvenBranchCostEnvelope inputWidth) +
        primitive + primitive := by
    have hcast : lift.payloadLength = liftRaw.payloadLength := by
      dsimp only [lift]
      change (CertifiedPAProof.cast _ _).payloadLength = _
      exact cast_payloadLength _ _
    rw [hcast]
    exact hliftRaw.trans
      (Nat.add_le_add (Nat.add_le_add hnormalize hreflexiveOne) le_rfl)
  have hincrement := proveBinaryNumeralIncrement_payloadLength_le_width
    intermediate workWidth hintermediateSize
  have hgrouping := proveEqualityTransitivity_payloadLength_le_primitive
    source grouped normalizedGrouped association lift termEnvelope
    (code hsource (by omega)) (code hgrouped (by omega))
    (code hnormalized (by omega))
  have hfinal := proveEqualityTransitivity_payloadLength_le_primitive
    source normalizedGrouped resultTerm throughGrouping increment termEnvelope
    (code hsource (by omega)) (code hnormalized (by omega))
    (code hresult (by omega))
  have hincrementLocal : increment.payloadLength <=
      binaryNumeralIncrementPayloadPolynomial workWidth := by
    dsimp only [increment]
    exact hincrement
  have hgroupingLocal : throughGrouping.payloadLength <=
      association.payloadLength + lift.payloadLength + primitive := by
    dsimp only [throughGrouping]
    exact hgrouping
  have hfinalLocal : throughIncrement.payloadLength <=
      throughGrouping.payloadLength + increment.payloadLength + primitive := by
    dsimp only [throughIncrement]
    exact hfinal
  have houterCast :
      (proveBinaryNumeralAdditionOddOddNonzero leftHigh rightHigh
        hright highProof).payloadLength = throughIncrement.payloadLength := by
    unfold proveBinaryNumeralAdditionOddOddNonzero
    simp only [cast_payloadLength]
    rfl
  rw [houterCast]
  calc
    _ <= throughGrouping.payloadLength + increment.payloadLength + primitive :=
      hfinalLocal
    _ <= (association.payloadLength + lift.payloadLength + primitive) +
        increment.payloadLength + primitive := by
      exact Nat.add_le_add (Nat.add_le_add hgroupingLocal le_rfl) le_rfl
    _ <= highProof.payloadLength + paOddOddBranchCostEnvelope inputWidth := by
      unfold paOddOddBranchCostEnvelope paOddEvenBranchCostEnvelope
        paAdditionAlgebraCostEnvelope paAlgebraStepCostEnvelope
        binaryNumeralIncrementPayloadPolynomial primitive termEnvelope
        workWidth at *
      omega

theorem proveBinaryNumeralAdditionOddOddZero_payloadLength_le
    (leftHigh inputWidth : Nat)
    (hwidth : Nat.size leftHigh <= inputWidth) :
    (proveBinaryNumeralAdditionOddOddZero leftHigh).payloadLength <=
      paOddOddBranchCostEnvelope inputWidth := by
  let workWidth := paAdditionWorkWidth inputWidth
  let termEnvelope := paGeneratedTermCodeEnvelope workWidth
  let primitive := paPrimitiveCostEnvelope termEnvelope
  let oddLeftValue := Nat.bit true leftHigh
  let resultValue := oddLeftValue + 1
  let oddLeft := shortBinaryNumeralTerm oddLeftValue
  let doubleZero := paMulTerm arithmeticTwoTerm paZeroTerm
  let oddRight := paAddTerm doubleZero paOneTerm
  let source := paAddTerm oddLeft oddRight
  let innerWithDoubleZero := paAddTerm oddLeft doubleZero
  let grouped := paAddTerm innerWithDoubleZero paOneTerm
  let collapsed := paAddTerm oddLeft paOneTerm
  let resultTerm := shortBinaryNumeralTerm resultValue
  let associationRaw := proveAddAssociativityReverse
    oddLeft doubleZero paOneTerm
  let association : CertifiedPAProof
      (“!!source = !!grouped” : LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      oddLeft (paAddTerm doubleZero paOneTerm)
      (paAddTerm oddLeft doubleZero) paOneTerm
    simpa [source, grouped, oddRight, innerWithDoubleZero] using
      (CertifiedPAProof.cast hformula associationRaw)
  let collapseDouble : CertifiedPAProof
      (“!!doubleZero = !!paZeroTerm” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula :
        (“!!(paMulTerm arithmeticTwoTerm paZeroTerm) = !!paZeroTerm” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!doubleZero = !!paZeroTerm” :
          LO.FirstOrder.ArithmeticProposition) := by rfl
    exact CertifiedPAProof.cast hformula
      (proveMulZeroAtPaZero arithmeticTwoTerm)
  let collapseInnerRaw := proveAddCongruence
    oddLeft doubleZero oddLeft paZeroTerm
    (proveEqualityReflexivityAtTerm oddLeft) collapseDouble
  let collapseInnerToZero : CertifiedPAProof
      (“!!innerWithDoubleZero = !!(paAddTerm oddLeft paZeroTerm)” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      oddLeft doubleZero oddLeft paZeroTerm
    exact CertifiedPAProof.cast hformula collapseInnerRaw
  let collapseInner := proveEqualityTransitivity
    innerWithDoubleZero (paAddTerm oddLeft paZeroTerm) oddLeft
    collapseInnerToZero (proveAddZeroAtPaZero oddLeft)
  let liftRaw := proveAddCongruence
    innerWithDoubleZero paOneTerm oddLeft paOneTerm collapseInner
    (proveEqualityReflexivityAtTerm paOneTerm)
  let lift : CertifiedPAProof
      (“!!grouped = !!collapsed” : LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      innerWithDoubleZero paOneTerm oddLeft paOneTerm
    simpa [grouped, collapsed] using
      (CertifiedPAProof.cast hformula liftRaw)
  let increment := proveBinaryNumeralIncrement oddLeftValue
  let throughGrouping := proveEqualityTransitivity
    source grouped collapsed association lift
  let throughIncrement := proveEqualityTransitivity
    source collapsed resultTerm throughGrouping increment
  have hoddNonzero : oddLeftValue ≠ 0 := by
    simp [oddLeftValue, Nat.bit_val]
  have hoddSizeTight : Nat.size oddLeftValue <= inputWidth + 1 := by
    dsimp only [oddLeftValue]
    rw [Nat.size_bit hoddNonzero]
    omega
  have hoddSize : Nat.size oddLeftValue <= workWidth := by
    dsimp only [workWidth]
    unfold paAdditionWorkWidth
    omega
  have hresultSize : Nat.size resultValue <= workWidth := by
    have hnext := natSize_add_one_le oddLeftValue
    dsimp only [resultValue, workWidth]
    unfold paAdditionWorkWidth
    omega
  have hoddLeft : PACompilerGeneratedTerm workWidth 1 oddLeft :=
    .numeral oddLeftValue hoddSize
  have hzero : PACompilerGeneratedTerm workWidth 1 paZeroTerm := .zero
  have hone : PACompilerGeneratedTerm workWidth 1 paOneTerm := .one
  have htwo : PACompilerGeneratedTerm workWidth 1 arithmeticTwoTerm := .two
  have hdoubleZero : PACompilerGeneratedTerm workWidth 3 doubleZero :=
    .mul htwo hzero
  have hoddRight : PACompilerGeneratedTerm workWidth 5 oddRight :=
    .add hdoubleZero hone
  have hsource : PACompilerGeneratedTerm workWidth 7 source :=
    .add hoddLeft hoddRight
  have hinnerDouble : PACompilerGeneratedTerm workWidth 5 innerWithDoubleZero :=
    .add hoddLeft hdoubleZero
  have hgrouped : PACompilerGeneratedTerm workWidth 7 grouped :=
    .add hinnerDouble hone
  have hoddPlusZero : PACompilerGeneratedTerm workWidth 3
      (paAddTerm oddLeft paZeroTerm) := .add hoddLeft hzero
  have hcollapsed : PACompilerGeneratedTerm workWidth 3 collapsed :=
    .add hoddLeft hone
  have hresult : PACompilerGeneratedTerm workWidth 1 resultTerm :=
    .numeral resultValue hresultSize
  have code
      {budget : Nat} {term : LO.FirstOrder.ArithmeticSemiterm Nat 0}
      (hterm : PACompilerGeneratedTerm workWidth budget term)
      (hbudget : budget <= 64) :
      (binaryTermCode term).length <= termEnvelope :=
    generatedTerm_code_length_le_compiler hterm hbudget
  have hassociationRaw :=
    proveAddAssociativityReverse_payloadLength_le_algebraStep
      hoddLeft hdoubleZero hone (by omega) (by omega) (by omega)
  have hassociation : association.payloadLength <=
      paAlgebraStepCostEnvelope workWidth := by
    have hcast : association.payloadLength = associationRaw.payloadLength := by
      dsimp only [association]
      change (CertifiedPAProof.cast _ _).payloadLength = _
      exact cast_payloadLength _ _
    rw [hcast]
    exact hassociationRaw
  have hmulZero := proveMulZeroAtPaZero_payloadLength_le_primitive
    arithmeticTwoTerm termEnvelope (code htwo (by omega))
  have hcollapseDouble : collapseDouble.payloadLength <= primitive := by
    have hcast : collapseDouble.payloadLength =
        (proveMulZeroAtPaZero arithmeticTwoTerm).payloadLength := by
      dsimp only [collapseDouble]
      exact cast_payloadLength _ _
    rw [hcast]
    exact hmulZero
  have hreflexiveOdd := proveEqualityReflexivityAtTerm_payloadLength_le_primitive
    oddLeft termEnvelope (code hoddLeft (by omega))
  have hcollapseInnerRaw := proveAddCongruence_payloadLength_le_primitive
    oddLeft doubleZero oddLeft paZeroTerm
    (proveEqualityReflexivityAtTerm oddLeft) collapseDouble termEnvelope
    (code hoddLeft (by omega)) (code hdoubleZero (by omega))
    (code hoddLeft (by omega)) (code hzero (by omega))
  have hcollapseInnerToZero : collapseInnerToZero.payloadLength <=
      primitive + primitive + primitive := by
    have hcast : collapseInnerToZero.payloadLength =
        collapseInnerRaw.payloadLength := by
      dsimp only [collapseInnerToZero]
      exact cast_payloadLength _ _
    rw [hcast]
    exact hcollapseInnerRaw.trans
      (Nat.add_le_add (Nat.add_le_add hreflexiveOdd hcollapseDouble) le_rfl)
  have haddZeroOdd := proveAddZeroAtPaZero_payloadLength_le_primitive
    oddLeft termEnvelope (code hoddLeft (by omega))
  have hcollapseInner := proveEqualityTransitivity_payloadLength_le_primitive
    innerWithDoubleZero (paAddTerm oddLeft paZeroTerm) oddLeft
    collapseInnerToZero (proveAddZeroAtPaZero oddLeft) termEnvelope
    (code hinnerDouble (by omega)) (code hoddPlusZero (by omega))
    (code hoddLeft (by omega))
  have hcollapseInnerBound : collapseInner.payloadLength <=
      (primitive + primitive + primitive) + primitive + primitive := by
    dsimp only [collapseInner]
    exact hcollapseInner.trans
      (Nat.add_le_add
        (Nat.add_le_add hcollapseInnerToZero haddZeroOdd) le_rfl)
  have hreflexiveOne := proveEqualityReflexivityAtTerm_payloadLength_le_primitive
    paOneTerm termEnvelope (code hone (by omega))
  have hliftRaw := proveAddCongruence_payloadLength_le_primitive
    innerWithDoubleZero paOneTerm oddLeft paOneTerm collapseInner
    (proveEqualityReflexivityAtTerm paOneTerm) termEnvelope
    (code hinnerDouble (by omega)) (code hone (by omega))
    (code hoddLeft (by omega)) (code hone (by omega))
  have hlift : lift.payloadLength <=
      ((primitive + primitive + primitive) + primitive + primitive) +
        primitive + primitive := by
    have hcast : lift.payloadLength = liftRaw.payloadLength := by
      dsimp only [lift]
      change (CertifiedPAProof.cast _ _).payloadLength = _
      exact cast_payloadLength _ _
    rw [hcast]
    exact hliftRaw.trans
      (Nat.add_le_add
        (Nat.add_le_add hcollapseInnerBound hreflexiveOne) le_rfl)
  have hincrementRaw := proveBinaryNumeralIncrement_payloadLength_le_width
    oddLeftValue workWidth hoddSize
  have hincrement : increment.payloadLength <=
      binaryNumeralIncrementPayloadPolynomial workWidth := by
    dsimp only [increment]
    exact hincrementRaw
  have hgrouping := proveEqualityTransitivity_payloadLength_le_primitive
    source grouped collapsed association lift termEnvelope
    (code hsource (by omega)) (code hgrouped (by omega))
    (code hcollapsed (by omega))
  have hgroupingLocal : throughGrouping.payloadLength <=
      association.payloadLength + lift.payloadLength + primitive := by
    dsimp only [throughGrouping]
    exact hgrouping
  have hfinal := proveEqualityTransitivity_payloadLength_le_primitive
    source collapsed resultTerm throughGrouping increment termEnvelope
    (code hsource (by omega)) (code hcollapsed (by omega))
    (code hresult (by omega))
  have hfinalLocal : throughIncrement.payloadLength <=
      throughGrouping.payloadLength + increment.payloadLength + primitive := by
    dsimp only [throughIncrement]
    exact hfinal
  have houterCast :
      (proveBinaryNumeralAdditionOddOddZero leftHigh).payloadLength =
        throughIncrement.payloadLength := by
    unfold proveBinaryNumeralAdditionOddOddZero
    simp only [cast_payloadLength]
    rfl
  rw [houterCast]
  calc
    _ <= throughGrouping.payloadLength + increment.payloadLength + primitive :=
      hfinalLocal
    _ <= (association.payloadLength + lift.payloadLength + primitive) +
        increment.payloadLength + primitive := by
      exact Nat.add_le_add (Nat.add_le_add hgroupingLocal le_rfl) le_rfl
    _ <= paOddOddBranchCostEnvelope inputWidth := by
      unfold paOddOddBranchCostEnvelope paAdditionAlgebraCostEnvelope
        paAlgebraStepCostEnvelope binaryNumeralIncrementPayloadPolynomial
        primitive termEnvelope workWidth at *
      omega

theorem proveBinaryNumeralAdditionOddOdd_payloadLength_le
    (leftHigh rightHigh inputWidth : Nat)
    (highProof : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm leftHigh)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(binaryAdditionHighSumTerm leftHigh rightHigh)” :
        LO.FirstOrder.ArithmeticProposition))
    (hwidth : Nat.size leftHigh + Nat.size rightHigh <= inputWidth) :
    (proveBinaryNumeralAdditionOddOdd leftHigh rightHigh
      highProof).payloadLength <=
      highProof.payloadLength + paOddOddBranchCostEnvelope inputWidth := by
  by_cases hright : rightHigh = 0
  · subst rightHigh
    have hzero := proveBinaryNumeralAdditionOddOddZero_payloadLength_le
      leftHigh inputWidth (by simpa using hwidth)
    have heq :
        proveBinaryNumeralAdditionOddOdd leftHigh 0 highProof =
          proveBinaryNumeralAdditionOddOddZero leftHigh := by
      simp [proveBinaryNumeralAdditionOddOdd]
    rw [heq]
    exact hzero.trans (Nat.le_add_left _ _)
  · have hnonzero := proveBinaryNumeralAdditionOddOddNonzero_payloadLength_le
      leftHigh rightHigh inputWidth hright highProof hwidth
    have heq :
        proveBinaryNumeralAdditionOddOdd leftHigh rightHigh highProof =
          proveBinaryNumeralAdditionOddOddNonzero
            leftHigh rightHigh hright highProof := by
      simp [proveBinaryNumeralAdditionOddOdd, hright]
    rw [heq]
    exact hnonzero

theorem paOddOddBranch_le_additionLocal (inputWidth : Nat) :
    paOddOddBranchCostEnvelope inputWidth <=
      paAdditionLocalCostEnvelope inputWidth := by
  unfold paOddOddBranchCostEnvelope paAdditionLocalCostEnvelope
  omega

theorem paOddEvenBranch_le_additionLocal (inputWidth : Nat) :
    paOddEvenBranchCostEnvelope inputWidth <=
      paAdditionLocalCostEnvelope inputWidth := by
  unfold paOddEvenBranchCostEnvelope paAdditionLocalCostEnvelope
  omega

theorem proveBinaryNumeralAdditionBitStep_payloadLength_le
    (leftBit rightBit : Bool) (leftHigh rightHigh inputWidth : Nat)
    (hleftCanonical : leftHigh = 0 → leftBit = true)
    (hrightCanonical : rightHigh = 0 → rightBit = true)
    (highProof : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm leftHigh)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(binaryAdditionHighSumTerm leftHigh rightHigh)” :
        LO.FirstOrder.ArithmeticProposition))
    (hwidth : Nat.size leftHigh + Nat.size rightHigh <= inputWidth) :
    (proveBinaryNumeralAdditionBitStep leftBit rightBit leftHigh rightHigh
      hleftCanonical hrightCanonical highProof).payloadLength <=
      highProof.payloadLength + paAdditionLocalCostEnvelope inputWidth := by
  cases leftBit with
  | false =>
      have hleft : leftHigh ≠ 0 := by
        intro hz
        have himpossible := hleftCanonical hz
        simp at himpossible
      cases rightBit with
      | false =>
          have hright : rightHigh ≠ 0 := by
            intro hz
            have himpossible := hrightCanonical hz
            simp at himpossible
          have hbranch := proveBinaryNumeralAdditionEvenEven_payloadLength_le
            leftHigh rightHigh inputWidth hleft hright highProof hwidth
          change
            (proveBinaryNumeralAdditionEvenEven leftHigh rightHigh
              hleft hright highProof).payloadLength <= _
          exact hbranch.trans (Nat.add_le_add_left
            ((paAdditionAlgebra_le_local inputWidth)) _)
      | true =>
          have hbranch := proveBinaryNumeralAdditionEvenOdd_payloadLength_le
            leftHigh rightHigh inputWidth hleft highProof hwidth
          change
            (proveBinaryNumeralAdditionEvenOdd leftHigh rightHigh
              hleft highProof).payloadLength <= _
          exact hbranch.trans (Nat.add_le_add_left
            (paAdditionAlgebra_le_local inputWidth) _)
  | true =>
      cases rightBit with
      | false =>
          have hright : rightHigh ≠ 0 := by
            intro hz
            have himpossible := hrightCanonical hz
            simp at himpossible
          have hbranch := proveBinaryNumeralAdditionOddEven_payloadLength_le
            leftHigh rightHigh inputWidth hright highProof hwidth
          change
            (proveBinaryNumeralAdditionOddEven leftHigh rightHigh
              hright highProof).payloadLength <= _
          exact hbranch.trans (Nat.add_le_add_left
            (paOddEvenBranch_le_additionLocal inputWidth) _)
      | true =>
          have hbranch := proveBinaryNumeralAdditionOddOdd_payloadLength_le
            leftHigh rightHigh inputWidth highProof hwidth
          change
            (proveBinaryNumeralAdditionOddOdd leftHigh rightHigh
              highProof).payloadLength <= _
          exact hbranch.trans (Nat.add_le_add_left
            (paOddOddBranch_le_additionLocal inputWidth) _)

theorem proveBinaryNumeralAddition_payloadLength_le_external
    (left right inputWidth : Nat)
    (hwidth : Nat.size left + Nat.size right <= inputWidth) :
    (proveBinaryNumeralAddition left right).payloadLength <=
      (Nat.size left + 1) * paAdditionLocalCostEnvelope inputWidth := by
  induction left using Nat.binaryRec' generalizing right inputWidth with
  | zero =>
      rw [proveBinaryNumeralAddition_zero_left]
      have hrightSize : Nat.size right <= paAdditionWorkWidth inputWidth := by
        unfold paAdditionWorkWidth
        omega
      have hbase := proveBinaryNumeralAdditionZeroLeft_payloadLength_le
        right inputWidth hrightSize
      have hlocal := paAdditionAlgebra_le_local inputWidth
      simpa using hbase.trans hlocal
  | bit leftBit leftHigh hleftCanonical ih =>
      have hleftNonzero : Nat.bit leftBit leftHigh ≠ 0 :=
        Nat.bit_ne_zero_iff.mpr hleftCanonical
      have hleftSizeEq :
          Nat.size (Nat.bit leftBit leftHigh) = Nat.size leftHigh + 1 :=
        Nat.size_bit hleftNonzero
      induction right using Nat.binaryRec' generalizing inputWidth with
      | zero =>
          rw [proveBinaryNumeralAddition_bit_zero
            leftBit leftHigh hleftCanonical]
          have hleftValueSize :
              Nat.size (Nat.bit leftBit leftHigh) <=
                paAdditionWorkWidth inputWidth := by
            unfold paAdditionWorkWidth
            omega
          have hbase := proveBinaryNumeralAdditionZeroRight_payloadLength_le
            (Nat.bit leftBit leftHigh) inputWidth hleftValueSize
          have hlocal := paAdditionAlgebra_le_local inputWidth
          rw [hleftSizeEq]
          calc
            (proveBinaryNumeralAdditionZeroRight
                (Nat.bit leftBit leftHigh)).payloadLength <=
                paAdditionAlgebraCostEnvelope inputWidth := hbase
            _ <= paAdditionLocalCostEnvelope inputWidth := hlocal
            _ <= (Nat.size leftHigh + 1 + 1) *
                paAdditionLocalCostEnvelope inputWidth := by
              have hcoefficient : 1 <= Nat.size leftHigh + 1 + 1 := by omega
              simpa using Nat.mul_le_mul_right
                (paAdditionLocalCostEnvelope inputWidth) hcoefficient
      | bit rightBit rightHigh hrightCanonical _rightIH =>
          have hrightNonzero : Nat.bit rightBit rightHigh ≠ 0 :=
            Nat.bit_ne_zero_iff.mpr hrightCanonical
          have hrightSizeEq :
              Nat.size (Nat.bit rightBit rightHigh) =
                Nat.size rightHigh + 1 := Nat.size_bit hrightNonzero
          have hhighWidth :
              Nat.size leftHigh + Nat.size rightHigh <= inputWidth := by
            omega
          have hrecursive := ih rightHigh inputWidth hhighWidth
          have hstep := proveBinaryNumeralAdditionBitStep_payloadLength_le
            leftBit rightBit leftHigh rightHigh inputWidth
            hleftCanonical hrightCanonical
            (proveBinaryNumeralAddition leftHigh rightHigh) hhighWidth
          rw [proveBinaryNumeralAddition_bit_bit
            leftBit rightBit leftHigh rightHigh
            hleftCanonical hrightCanonical]
          rw [hleftSizeEq]
          calc
            (proveBinaryNumeralAdditionBitStep
                leftBit rightBit leftHigh rightHigh
                hleftCanonical hrightCanonical
                (proveBinaryNumeralAddition leftHigh rightHigh)).payloadLength <=
                (proveBinaryNumeralAddition leftHigh rightHigh).payloadLength +
                  paAdditionLocalCostEnvelope inputWidth := hstep
            _ <= (Nat.size leftHigh + 1) *
                  paAdditionLocalCostEnvelope inputWidth +
                paAdditionLocalCostEnvelope inputWidth :=
              Nat.add_le_add_right hrecursive _
            _ = (Nat.size leftHigh + 1 + 1) *
                paAdditionLocalCostEnvelope inputWidth := by ring

def binaryNumeralAdditionPayloadPolynomial (inputWidth : Nat) : Nat :=
  (inputWidth + 1) * paAdditionLocalCostEnvelope inputWidth

theorem proveBinaryNumeralAddition_payloadLength_le_polynomial
    (left right : Nat) :
    (proveBinaryNumeralAddition left right).payloadLength <=
      binaryNumeralAdditionPayloadPolynomial
        (Nat.size left + Nat.size right) := by
  let inputWidth := Nat.size left + Nat.size right
  have hproof := proveBinaryNumeralAddition_payloadLength_le_external
    left right inputWidth le_rfl
  unfold binaryNumeralAdditionPayloadPolynomial
  dsimp only [inputWidth] at hproof ⊢
  exact hproof.trans (Nat.mul_le_mul_right
    (paAdditionLocalCostEnvelope (Nat.size left + Nat.size right))
    (Nat.add_le_add_right
      (Nat.le_add_right (Nat.size left) (Nat.size right)) 1))

/-- Single public endpoint for `A04.14`: a real checker-accepted PA proof and
an explicit fixed polynomial payload bound in the total binary input width. -/
theorem proveBinaryNumeralAddition_checked_polynomial
    (left right : Nat) :
    listedCompactCertifiedPAProofVerifier
        (proveBinaryNumeralAddition left right).code
        (compactFormulaCode
          (“!!(paAddTerm (shortBinaryNumeralTerm left)
              (shortBinaryNumeralTerm right)) =
            !!(shortBinaryNumeralTerm (left + right))” :
            LO.FirstOrder.ArithmeticProposition)) = true ∧
      (proveBinaryNumeralAddition left right).payloadLength <=
        binaryNumeralAdditionPayloadPolynomial
          (Nat.size left + Nat.size right) := by
  exact ⟨proveBinaryNumeralAddition_verifier_eq_true left right,
    proveBinaryNumeralAddition_payloadLength_le_polynomial left right⟩

#print axioms paAddTerm_code_length_le
#print axioms paMulTerm_code_length_le
#print axioms equalityFormula_code_length_le
#print axioms binaryFormulaCode_substitution_one_length_le_envelope
#print axioms fixedFormulaCode_le_seed
#print axioms proveBinaryNumeralIncrement_payloadLength_le_polynomial
#print axioms proveBinaryNumeralAddition_payloadLength_le_polynomial
#print axioms proveBinaryNumeralAddition_checked_polynomial

end FoundationCompactPABinaryNumeralAdditionBounds
