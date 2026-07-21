import integration.FoundationCompactPAContextCostPolynomialBounds
import integration.FoundationCompactPAUnaryAtomicTransport
import integration.FoundationCompactPABinaryNumeralAdditionBounds
import integration.FoundationCompactPAQuantitativeOrderBounds

/-!
# Fixed polynomial ledger for unary atomic transport

This file compresses the fixed local work of one unary-term transport node.
Recursive child proofs are deliberately excluded from the local overhead and
will be summed by the structural term induction.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAUnaryAtomicTransportPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAQuantitativeFunctionCongruence
open FoundationCompactPAUnaryTermSubstitutionEquality
open FoundationCompactPAUnaryTermEqualityImplication
open FoundationCompactPAUnaryAtomicTransport
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPANegativeEqualityBounds

def unaryTransportTermEnvelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (openTermCodeBound : Nat) : Nat :=
  unaryTermSubstitutionCodeEnvelope left right openTermCodeBound

def unaryTransportFormulaEnvelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat) : Nat :=
  4 * (paPrimitiveAssemblyCostEnvelope termBound +
    paFormulaCodeEnvelope
      ((binaryTermCode left).length + (binaryTermCode right).length) + 1)

def unaryTransportLocalEnvelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (openTermCodeBound : Nat) : Nat :=
  let termBound := unaryTransportTermEnvelope
    left right openTermCodeBound
  let formulaBound := unaryTransportFormulaEnvelope
    left right termBound
  16 * (paPrimitiveCostEnvelope termBound +
    smallContextAssemblyEnvelope formulaBound + 1)

theorem paFormulaCodeEnvelope_le_unaryTransportFormulaEnvelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat) :
    paFormulaCodeEnvelope termBound <=
      unaryTransportFormulaEnvelope left right termBound := by
  unfold unaryTransportFormulaEnvelope paPrimitiveAssemblyCostEnvelope
    paLocalAssemblyCostEnvelope paDerivedFormulaCodeEnvelope
    paAssemblySyntaxEnvelope
  omega

theorem paDerivedFormulaCodeEnvelope_le_unaryTransportFormulaEnvelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat) :
    paDerivedFormulaCodeEnvelope termBound <=
      unaryTransportFormulaEnvelope left right termBound := by
  unfold unaryTransportFormulaEnvelope paPrimitiveAssemblyCostEnvelope
    paLocalAssemblyCostEnvelope paDerivedFormulaCodeEnvelope
    paAssemblySyntaxEnvelope
  omega

theorem paLocalAssemblyCostEnvelope_le_unaryTransportFormulaEnvelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat) :
    paLocalAssemblyCostEnvelope termBound <=
      unaryTransportFormulaEnvelope left right termBound := by
  unfold unaryTransportFormulaEnvelope paPrimitiveAssemblyCostEnvelope
    paLocalAssemblyCostEnvelope paDerivedFormulaCodeEnvelope
    paAssemblySyntaxEnvelope
  omega

theorem paPrimitiveAssemblyCostEnvelope_le_unaryTransportFormulaEnvelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat) :
    paPrimitiveAssemblyCostEnvelope termBound <=
      unaryTransportFormulaEnvelope left right termBound := by
  unfold unaryTransportFormulaEnvelope
  omega

theorem parameterEqualityContext_formulaCodeBound_transport
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat) :
    FormulaCodeBound (parameterEqualityContext left right)
      (unaryTransportFormulaEnvelope left right termBound) := by
  let parameterTermBound :=
    (binaryTermCode left).length + (binaryTermCode right).length
  have hleft : (binaryTermCode left).length <= parameterTermBound := by
    simp only [parameterTermBound]
    omega
  have hright : (binaryTermCode right).length <= parameterTermBound := by
    simp only [parameterTermBound]
    omega
  have hequality := equalityFormula_code_length_le_paEnvelope
    left right parameterTermBound hleft hright
  change (binaryFormulaCode (parameterEqualityFormula left right)).length <=
    paFormulaCodeEnvelope parameterTermBound at hequality
  have hnegative := binaryFormulaCode_neg_length_le
    (parameterEqualityFormula left right)
  intro formula hformula
  simp only [parameterEqualityContext, Finset.mem_singleton] at hformula
  subst formula
  unfold unaryTransportFormulaEnvelope
  dsimp only [parameterTermBound] at hequality hnegative ⊢
  omega

theorem parameterEqualityContext_card_le_transport
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (parameterEqualityContext left right).card <= 4 := by
  simp [parameterEqualityContext]

theorem binaryFunctionExtImplication_payloadLength_le_primitive
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
    (binaryFunctionExtImplication functionSymbol
      leftFirst leftSecond rightFirst rightSecond).payloadLength <=
      paPrimitiveCostEnvelope termBound := by
  have hraw := binaryFunctionExtImplication_payloadLength_le
    functionSymbol leftFirst leftSecond rightFirst rightSecond
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
  unfold paPrimitiveCostEnvelope
  omega

def binaryFunctionNodeLocalOverhead
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  let Gamma := parameterEqualityContext left right
  let leftFirst := instantiateUnaryTerm (arguments 0) left
  let leftSecond := instantiateUnaryTerm (arguments 1) left
  let rightFirst := instantiateUnaryTerm (arguments 0) right
  let rightSecond := instantiateUnaryTerm (arguments 1) right
  let firstFormula := unaryTermEqualityFormula (arguments 0) left right
  let secondFormula := unaryTermEqualityFormula (arguments 1) left right
  let truthFormula := (⊤ : LO.FirstOrder.ArithmeticProposition)
  let innerFormula := secondFormula ⋏ truthFormula
  let antecedentFormula := binaryFunctionCongruenceAntecedent
    leftFirst leftSecond rightFirst rightSecond
  let conclusionFormula := binaryFunctionCongruenceConclusion functionSymbol
    leftFirst leftSecond rightFirst rightSecond
  let implicationFormula := antecedentFormula 🡒 conclusionFormula
  verumProof.payloadLength +
    weakeningFullAssemblyCost (insert truthFormula Gamma) +
    CertifiedPAContextProof.conjunctionFullAssemblyCost
      Gamma secondFormula truthFormula +
    CertifiedPAContextProof.conjunctionFullAssemblyCost
      Gamma firstFormula innerFormula +
    (binaryFunctionExtImplication functionSymbol
      leftFirst leftSecond rightFirst rightSecond).payloadLength +
    weakeningFullAssemblyCost (insert implicationFormula Gamma) +
    contextualModusPonensFullAssemblyCost
      Gamma antecedentFormula conclusionFormula

theorem binaryFunctionNodeLocalOverhead_le_uniform
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (openTermCodeBound : Nat)
    (hfunction : functionSymbol = Language.Add.add ∨
      functionSymbol = Language.Mul.mul)
    (hfirst : (binaryTermCode (arguments 0)).length <= openTermCodeBound)
    (hsecond : (binaryTermCode (arguments 1)).length <= openTermCodeBound) :
    binaryFunctionNodeLocalOverhead functionSymbol arguments left right <=
      unaryTransportLocalEnvelope left right openTermCodeBound := by
  let Gamma := parameterEqualityContext left right
  let termBound := unaryTransportTermEnvelope
    left right openTermCodeBound
  let formulaBound := unaryTransportFormulaEnvelope left right termBound
  let leftFirst := instantiateUnaryTerm (arguments 0) left
  let leftSecond := instantiateUnaryTerm (arguments 1) left
  let rightFirst := instantiateUnaryTerm (arguments 0) right
  let rightSecond := instantiateUnaryTerm (arguments 1) right
  let firstFormula := unaryTermEqualityFormula (arguments 0) left right
  let secondFormula := unaryTermEqualityFormula (arguments 1) left right
  let truthFormula := (⊤ : LO.FirstOrder.ArithmeticProposition)
  let innerFormula := secondFormula ⋏ truthFormula
  let antecedentFormula := binaryFunctionCongruenceAntecedent
    leftFirst leftSecond rightFirst rightSecond
  let conclusionFormula := binaryFunctionCongruenceConclusion functionSymbol
    leftFirst leftSecond rightFirst rightSecond
  let implicationFormula := antecedentFormula 🡒 conclusionFormula
  have hleftFirst := instantiateUnaryTerm_left_code_length_le_envelope
    (arguments 0) left right openTermCodeBound hfirst
  have hleftSecond := instantiateUnaryTerm_left_code_length_le_envelope
    (arguments 1) left right openTermCodeBound hsecond
  have hrightFirst := instantiateUnaryTerm_right_code_length_le_envelope
    (arguments 0) left right openTermCodeBound hfirst
  have hrightSecond := instantiateUnaryTerm_right_code_length_le_envelope
    (arguments 1) left right openTermCodeBound hsecond
  change (binaryTermCode leftFirst).length <= termBound at hleftFirst
  change (binaryTermCode leftSecond).length <= termBound at hleftSecond
  change (binaryTermCode rightFirst).length <= termBound at hrightFirst
  change (binaryTermCode rightSecond).length <= termBound at hrightSecond
  have hfirstFormula := equalityFormula_code_length_le_paEnvelope
    leftFirst rightFirst termBound hleftFirst hrightFirst
  have hsecondFormula := equalityFormula_code_length_le_paEnvelope
    leftSecond rightSecond termBound hleftSecond hrightSecond
  have htruth := truthFormula_code_length_le_paEnvelope termBound
  have hinner := binaryFunctionCongruenceInnerFormula_code_le_derived
    leftSecond rightSecond termBound hleftSecond hrightSecond
  have hantecedent := binaryFunctionCongruenceAntecedent_code_le_localAssembly
    leftFirst leftSecond rightFirst rightSecond termBound
    hleftFirst hleftSecond hrightFirst hrightSecond
  change (binaryFormulaCode antecedentFormula).length <=
    paLocalAssemblyCostEnvelope termBound at hantecedent
  have hconclusion := binaryFunctionCongruenceConclusion_code_le_localAssembly
    functionSymbol leftFirst leftSecond rightFirst rightSecond termBound
    hfunction hleftFirst hleftSecond hrightFirst hrightSecond
  change (binaryFormulaCode conclusionFormula).length <=
    paLocalAssemblyCostEnvelope termBound at hconclusion
  have himplicationRaw := binaryFormulaCode_implication_length_le
    antecedentFormula conclusionFormula
  have himplication : (binaryFormulaCode implicationFormula).length <=
      paPrimitiveAssemblyCostEnvelope termBound := by
    dsimp only [implicationFormula] at himplicationRaw ⊢
    unfold paPrimitiveAssemblyCostEnvelope paAssemblySyntaxEnvelope
    omega
  have hnegatedImplication := binaryFormulaCode_neg_length_le
    implicationFormula
  have hnegatedConclusion := binaryFormulaCode_neg_length_le
    conclusionFormula
  have hformula := paFormulaCodeEnvelope_le_unaryTransportFormulaEnvelope
    left right termBound
  have hderived := paDerivedFormulaCodeEnvelope_le_unaryTransportFormulaEnvelope
    left right termBound
  have hlocal := paLocalAssemblyCostEnvelope_le_unaryTransportFormulaEnvelope
    left right termBound
  have hprimitive :=
    paPrimitiveAssemblyCostEnvelope_le_unaryTransportFormulaEnvelope
      left right termBound
  have hfirstFormulaBound : (binaryFormulaCode firstFormula).length <=
      formulaBound := by
    change (binaryFormulaCode
      (unaryTermEqualityFormula (arguments 0) left right)).length <= _
    simpa only [firstFormula, unaryTermEqualityFormula] using
      hfirstFormula.trans hformula
  have hsecondFormulaBound : (binaryFormulaCode secondFormula).length <=
      formulaBound := by
    change (binaryFormulaCode
      (unaryTermEqualityFormula (arguments 1) left right)).length <= _
    simpa only [secondFormula, unaryTermEqualityFormula] using
      hsecondFormula.trans hformula
  have htruthBound : (binaryFormulaCode truthFormula).length <=
      formulaBound := htruth.trans hformula
  have hinnerBound : (binaryFormulaCode innerFormula).length <=
      formulaBound := hinner.trans hderived
  have hantecedentBound : (binaryFormulaCode antecedentFormula).length <=
      formulaBound := hantecedent.trans hlocal
  have hconclusionBound : (binaryFormulaCode conclusionFormula).length <=
      formulaBound := hconclusion.trans hlocal
  have himplicationBound : (binaryFormulaCode implicationFormula).length <=
      formulaBound := himplication.trans hprimitive
  have hnegatedImplicationBound :
      (binaryFormulaCode (∼implicationFormula)).length <= formulaBound := by
    unfold formulaBound unaryTransportFormulaEnvelope
    omega
  have hnegatedConclusionBound :
      (binaryFormulaCode (∼conclusionFormula)).length <= formulaBound := by
    have hlocalPrimitive :=
      paLocalAssemblyCostEnvelope_le_primitiveAssembly termBound
    unfold formulaBound unaryTransportFormulaEnvelope
    omega
  have hcontext : FormulaCodeBound Gamma formulaBound := by
    simpa only [Gamma, formulaBound] using
      parameterEqualityContext_formulaCodeBound_transport
        left right termBound
  have hcontextCard : Gamma.card <= 4 := by
    simpa only [Gamma] using
      parameterEqualityContext_card_le_transport left right
  have htruthContext := hcontext.insert htruthBound
  have himplicationContext := hcontext.insert himplicationBound
  have htruthCard : (insert truthFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le truthFormula Gamma
    omega
  have himplicationCard : (insert implicationFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le implicationFormula Gamma
    omega
  have hverum := verumProof_payloadLength_le_fixed
  have hverumPrimitive : verumProof.payloadLength <=
      paPrimitiveCostEnvelope termBound := by
    unfold paPrimitiveCostEnvelope
    omega
  have htruthWeakening := weakeningFullAssemblyCost_le_small
    (insert truthFormula Gamma) formulaBound htruthCard htruthContext
  have himplicationWeakening := weakeningFullAssemblyCost_le_small
    (insert implicationFormula Gamma) formulaBound
    himplicationCard himplicationContext
  have hinnerConjunction := conjunctionFullAssemblyCost_le_small
    Gamma secondFormula truthFormula formulaBound hcontextCard hcontext
    hsecondFormulaBound htruthBound hinnerBound
  have hantecedentConjunction := conjunctionFullAssemblyCost_le_small
    Gamma firstFormula innerFormula formulaBound hcontextCard hcontext
    hfirstFormulaBound hinnerBound hantecedentBound
  have himplicationProof :=
    binaryFunctionExtImplication_payloadLength_le_primitive
      functionSymbol leftFirst leftSecond rightFirst rightSecond termBound
      hfunction hleftFirst hleftSecond hrightFirst hrightSecond
  have hmp := contextualModusPonensFullAssemblyCost_le_small
    Gamma antecedentFormula conclusionFormula formulaBound
    hcontextCard hcontext hantecedentBound hconclusionBound
    himplicationBound hnegatedImplicationBound hnegatedConclusionBound
  unfold binaryFunctionNodeLocalOverhead unaryTransportLocalEnvelope
  dsimp only [Gamma, termBound, formulaBound, leftFirst, leftSecond,
    rightFirst, rightSecond, firstFormula, secondFormula, truthFormula,
    innerFormula, antecedentFormula, conclusionFormula, implicationFormula]
    at hverumPrimitive htruthWeakening himplicationWeakening
      hinnerConjunction hantecedentConjunction himplicationProof hmp ⊢
  omega

theorem unaryTermEqualityUnderAssumptionStructuralPayloadBound_add_eq
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    unaryTermEqualityUnderAssumptionStructuralPayloadBound
        (Semiterm.func Language.ORing.Func.add arguments) left right =
      unaryTermEqualityUnderAssumptionStructuralPayloadBound
          (arguments 0) left right +
        unaryTermEqualityUnderAssumptionStructuralPayloadBound
          (arguments 1) left right +
        binaryFunctionNodeLocalOverhead
          Language.Add.add arguments left right := by
  unfold unaryTermEqualityUnderAssumptionStructuralPayloadBound
    binaryFunctionNodeLocalOverhead
  rw [compileUnaryTermEqualityUnderAssumptionDetailed.eq_def]
  dsimp only
  omega

theorem unaryTermEqualityUnderAssumptionStructuralPayloadBound_mul_eq
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    unaryTermEqualityUnderAssumptionStructuralPayloadBound
        (Semiterm.func Language.ORing.Func.mul arguments) left right =
      unaryTermEqualityUnderAssumptionStructuralPayloadBound
          (arguments 0) left right +
        unaryTermEqualityUnderAssumptionStructuralPayloadBound
          (arguments 1) left right +
        binaryFunctionNodeLocalOverhead
          Language.Mul.mul arguments left right := by
  unfold unaryTermEqualityUnderAssumptionStructuralPayloadBound
    binaryFunctionNodeLocalOverhead
  rw [compileUnaryTermEqualityUnderAssumptionDetailed.eq_def]
  dsimp only
  omega

def reflexivityNodeLocalOverhead
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  let Gamma := parameterEqualityContext left right
  let formula :=
    (“!!term = !!term” : LO.FirstOrder.ArithmeticProposition)
  (proveEqualityReflexivityAtTerm term).payloadLength +
    weakeningFullAssemblyCost (insert formula Gamma)

theorem reflexivityNodeLocalOverhead_le_uniform
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (openTermCodeBound : Nat)
    (hterm : (binaryTermCode term).length <=
      unaryTransportTermEnvelope left right openTermCodeBound) :
    reflexivityNodeLocalOverhead term left right <=
      unaryTransportLocalEnvelope left right openTermCodeBound := by
  let Gamma := parameterEqualityContext left right
  let termBound := unaryTransportTermEnvelope
    left right openTermCodeBound
  let formulaBound := unaryTransportFormulaEnvelope left right termBound
  let formula :=
    (“!!term = !!term” : LO.FirstOrder.ArithmeticProposition)
  have hformulaRaw := equalityFormula_code_length_le_paEnvelope
    term term termBound hterm hterm
  have hformulaEnvelope :=
    paFormulaCodeEnvelope_le_unaryTransportFormulaEnvelope
      left right termBound
  have hformula : (binaryFormulaCode formula).length <= formulaBound := by
    simpa only [formula, formulaBound] using
      hformulaRaw.trans hformulaEnvelope
  have hcontext : FormulaCodeBound Gamma formulaBound := by
    simpa only [Gamma, formulaBound] using
      parameterEqualityContext_formulaCodeBound_transport
        left right termBound
  have hcontextCard : Gamma.card <= 4 := by
    simpa only [Gamma] using
      parameterEqualityContext_card_le_transport left right
  have hinsert := hcontext.insert hformula
  have hinsertCard : (insert formula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le formula Gamma
    omega
  have hreflexivity := proveEqualityReflexivityAtTerm_payloadLength_le_primitive
    term termBound hterm
  have hweakening := weakeningFullAssemblyCost_le_small
    (insert formula Gamma) formulaBound hinsertCard hinsert
  unfold reflexivityNodeLocalOverhead unaryTransportLocalEnvelope
  dsimp only [Gamma, termBound, formulaBound, formula]
    at hreflexivity hweakening ⊢
  omega

theorem parameterEqualityFormula_code_le_transport
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat) :
    (binaryFormulaCode (parameterEqualityFormula left right)).length <=
      unaryTransportFormulaEnvelope left right termBound := by
  let parameterTermBound :=
    (binaryTermCode left).length + (binaryTermCode right).length
  have hleft : (binaryTermCode left).length <= parameterTermBound := by
    simp only [parameterTermBound]
    omega
  have hright : (binaryTermCode right).length <= parameterTermBound := by
    simp only [parameterTermBound]
    omega
  have hequality := equalityFormula_code_length_le_paEnvelope
    left right parameterTermBound hleft hright
  change (binaryFormulaCode (parameterEqualityFormula left right)).length <=
    paFormulaCodeEnvelope parameterTermBound at hequality
  unfold unaryTransportFormulaEnvelope
  dsimp only [parameterTermBound] at hequality ⊢
  omega

theorem assumptionNodeLocalOverhead_le_uniform
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (openTermCodeBound : Nat) :
    assumptionFullPayloadCost (parameterEqualityContext left right)
        (parameterEqualityFormula left right) <=
      unaryTransportLocalEnvelope left right openTermCodeBound := by
  let termBound := unaryTransportTermEnvelope
    left right openTermCodeBound
  let formulaBound := unaryTransportFormulaEnvelope left right termBound
  have hformula :
      (binaryFormulaCode (parameterEqualityFormula left right)).length <=
        formulaBound := by
    simpa only [formulaBound] using
      parameterEqualityFormula_code_le_transport left right termBound
  have hcontext :
      FormulaCodeBound (parameterEqualityContext left right) formulaBound := by
    simpa only [formulaBound] using
      parameterEqualityContext_formulaCodeBound_transport
        left right termBound
  have hcard := parameterEqualityContext_card_le_transport left right
  have hassumption := assumptionFullPayloadCost_le_small
    (parameterEqualityContext left right)
    (parameterEqualityFormula left right) formulaBound
    hcard hcontext hformula
  unfold unaryTransportLocalEnvelope
  dsimp only [termBound, formulaBound] at hassumption ⊢
  omega

theorem unaryTermEqualityUnderAssumptionStructuralPayloadBound_bvar_eq
    (index : Fin 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    unaryTermEqualityUnderAssumptionStructuralPayloadBound
        (#index : LO.FirstOrder.ArithmeticSemiterm Nat 1) left right =
      assumptionFullPayloadCost (parameterEqualityContext left right)
        (parameterEqualityFormula left right) := by
  have hindex : index = 0 := Fin.eq_zero index
  subst index
  unfold unaryTermEqualityUnderAssumptionStructuralPayloadBound
  rw [compileUnaryTermEqualityUnderAssumptionDetailed.eq_def]

theorem unaryTermEqualityUnderAssumptionStructuralPayloadBound_fvar_eq
    (index : Nat)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    unaryTermEqualityUnderAssumptionStructuralPayloadBound
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat 1) left right =
      reflexivityNodeLocalOverhead
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat 0) left right := by
  have heq := congrArg
    (fun compilation => compilation.structuralPayloadBound)
    (compileUnaryTermEqualityUnderAssumptionDetailed.eq_def
      (&index : LO.FirstOrder.ArithmeticSemiterm Nat 1) left right)
  unfold unaryTermEqualityUnderAssumptionStructuralPayloadBound
    reflexivityNodeLocalOverhead
  simpa only using heq

theorem unaryTermEqualityUnderAssumptionStructuralPayloadBound_zero_eq
    (arguments : Fin 0 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    unaryTermEqualityUnderAssumptionStructuralPayloadBound
        (Semiterm.func Language.ORing.Func.zero arguments) left right =
      reflexivityNodeLocalOverhead
        (Semiterm.func Language.Zero.zero ![]) left right := by
  have heq := congrArg
    (fun compilation => compilation.structuralPayloadBound)
    (compileUnaryTermEqualityUnderAssumptionDetailed.eq_def
      (Semiterm.func Language.ORing.Func.zero arguments) left right)
  unfold unaryTermEqualityUnderAssumptionStructuralPayloadBound
    reflexivityNodeLocalOverhead
  simpa only using heq

theorem unaryTermEqualityUnderAssumptionStructuralPayloadBound_one_eq
    (arguments : Fin 0 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    unaryTermEqualityUnderAssumptionStructuralPayloadBound
        (Semiterm.func Language.ORing.Func.one arguments) left right =
      reflexivityNodeLocalOverhead
        (Semiterm.func Language.One.one ![]) left right := by
  have heq := congrArg
    (fun compilation => compilation.structuralPayloadBound)
    (compileUnaryTermEqualityUnderAssumptionDetailed.eq_def
      (Semiterm.func Language.ORing.Func.one arguments) left right)
  unfold unaryTermEqualityUnderAssumptionStructuralPayloadBound
    reflexivityNodeLocalOverhead
  simpa only using heq

theorem unaryTermEqualityUnderAssumptionStructuralPayloadBound_le_symbolCount
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (openTermCodeBound : Nat)
    (hterm : (binaryTermCode term).length <= openTermCodeBound) :
    unaryTermEqualityUnderAssumptionStructuralPayloadBound term left right <=
      termSymbolCount term *
        unaryTransportLocalEnvelope left right openTermCodeBound := by
  induction term with
  | bvar index =>
      rw [unaryTermEqualityUnderAssumptionStructuralPayloadBound_bvar_eq]
      have hlocal := assumptionNodeLocalOverhead_le_uniform
        left right openTermCodeBound
      simpa [termSymbolCount] using hlocal
  | fvar index =>
      have hinstantiated :=
        instantiateUnaryTerm_left_code_length_le_envelope
          (&index : LO.FirstOrder.ArithmeticSemiterm Nat 1)
          left right openTermCodeBound hterm
      have hclosed :
          (binaryTermCode
            (&index : LO.FirstOrder.ArithmeticSemiterm Nat 0)).length <=
          unaryTransportTermEnvelope left right openTermCodeBound := by
        simpa [instantiateUnaryTerm, unaryTransportTermEnvelope] using
          hinstantiated
      rw [unaryTermEqualityUnderAssumptionStructuralPayloadBound_fvar_eq]
      have hlocal := reflexivityNodeLocalOverhead_le_uniform
        (&index : LO.FirstOrder.ArithmeticSemiterm Nat 0)
        left right openTermCodeBound hclosed
      simpa [termSymbolCount] using hlocal
  | @func functionArity functionSymbol arguments ih =>
      cases functionSymbol with
      | zero =>
          have hinstantiated :=
            instantiateUnaryTerm_left_code_length_le_envelope
              (Semiterm.func Language.ORing.Func.zero arguments)
              left right openTermCodeBound hterm
          have hclosed :
              (binaryTermCode
                (Semiterm.func Language.Zero.zero ![] :
                  LO.FirstOrder.ArithmeticSemiterm Nat 0)).length <=
              unaryTransportTermEnvelope left right openTermCodeBound := by
            have hsame :
                (binaryTermCode
                  (Semiterm.func Language.Zero.zero ![] :
                    LO.FirstOrder.ArithmeticSemiterm Nat 0)).length =
                (binaryTermCode
                  (Semiterm.func Language.ORing.Func.zero ![] :
                    LO.FirstOrder.ArithmeticSemiterm Nat 0)).length := by
              decide
            rw [hsame]
            simpa [instantiateUnaryTerm, unaryTransportTermEnvelope,
              Matrix.empty_eq] using hinstantiated
          rw [unaryTermEqualityUnderAssumptionStructuralPayloadBound_zero_eq]
          have hlocal := reflexivityNodeLocalOverhead_le_uniform
            (Semiterm.func Language.Zero.zero ![])
            left right openTermCodeBound hclosed
          simpa [termSymbolCount] using hlocal
      | one =>
          have hinstantiated :=
            instantiateUnaryTerm_left_code_length_le_envelope
              (Semiterm.func Language.ORing.Func.one arguments)
              left right openTermCodeBound hterm
          have hclosed :
              (binaryTermCode
                (Semiterm.func Language.One.one ![] :
                  LO.FirstOrder.ArithmeticSemiterm Nat 0)).length <=
              unaryTransportTermEnvelope left right openTermCodeBound := by
            have hsame :
                (binaryTermCode
                  (Semiterm.func Language.One.one ![] :
                    LO.FirstOrder.ArithmeticSemiterm Nat 0)).length =
                (binaryTermCode
                  (Semiterm.func Language.ORing.Func.one ![] :
                    LO.FirstOrder.ArithmeticSemiterm Nat 0)).length := by
              decide
            rw [hsame]
            simpa [instantiateUnaryTerm, unaryTransportTermEnvelope,
              Matrix.empty_eq] using hinstantiated
          rw [unaryTermEqualityUnderAssumptionStructuralPayloadBound_one_eq]
          have hlocal := reflexivityNodeLocalOverhead_le_uniform
            (Semiterm.func Language.One.one ![])
            left right openTermCodeBound hclosed
          simpa [termSymbolCount] using hlocal
      | add =>
          have hfirstCode :=
            (binaryTermCode_argument_length_le
              Language.Add.add arguments 0).trans hterm
          have hsecondCode :=
            (binaryTermCode_argument_length_le
              Language.Add.add arguments 1).trans hterm
          have hfirst := ih 0 hfirstCode
          have hsecond := ih 1 hsecondCode
          have hlocal := binaryFunctionNodeLocalOverhead_le_uniform
            Language.Add.add arguments left right openTermCodeBound
            (Or.inl rfl) hfirstCode hsecondCode
          rw [unaryTermEqualityUnderAssumptionStructuralPayloadBound_add_eq]
          calc
            unaryTermEqualityUnderAssumptionStructuralPayloadBound
                  (arguments 0) left right +
                unaryTermEqualityUnderAssumptionStructuralPayloadBound
                  (arguments 1) left right +
                binaryFunctionNodeLocalOverhead
                  Language.Add.add arguments left right <=
              termSymbolCount (arguments 0) *
                  unaryTransportLocalEnvelope
                    left right openTermCodeBound +
                termSymbolCount (arguments 1) *
                  unaryTransportLocalEnvelope
                    left right openTermCodeBound +
                unaryTransportLocalEnvelope
                  left right openTermCodeBound := by
              omega
            _ = termSymbolCount
                  (Semiterm.func Language.ORing.Func.add arguments) *
                unaryTransportLocalEnvelope
                  left right openTermCodeBound := by
              rw [termSymbolCount_binary_function]
              ring
      | mul =>
          have hfirstCode :=
            (binaryTermCode_argument_length_le
              Language.Mul.mul arguments 0).trans hterm
          have hsecondCode :=
            (binaryTermCode_argument_length_le
              Language.Mul.mul arguments 1).trans hterm
          have hfirst := ih 0 hfirstCode
          have hsecond := ih 1 hsecondCode
          have hlocal := binaryFunctionNodeLocalOverhead_le_uniform
            Language.Mul.mul arguments left right openTermCodeBound
            (Or.inr rfl) hfirstCode hsecondCode
          rw [unaryTermEqualityUnderAssumptionStructuralPayloadBound_mul_eq]
          calc
            unaryTermEqualityUnderAssumptionStructuralPayloadBound
                  (arguments 0) left right +
                unaryTermEqualityUnderAssumptionStructuralPayloadBound
                  (arguments 1) left right +
                binaryFunctionNodeLocalOverhead
                  Language.Mul.mul arguments left right <=
              termSymbolCount (arguments 0) *
                  unaryTransportLocalEnvelope
                    left right openTermCodeBound +
                termSymbolCount (arguments 1) *
                  unaryTransportLocalEnvelope
                    left right openTermCodeBound +
                unaryTransportLocalEnvelope
                  left right openTermCodeBound := by
              omega
            _ = termSymbolCount
                  (Semiterm.func Language.ORing.Func.mul arguments) *
                unaryTransportLocalEnvelope
                  left right openTermCodeBound := by
              rw [termSymbolCount_binary_function]
              ring

def unaryTermEqualityUnderAssumptionPayloadPolynomial
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  (binaryTermCode term).length *
    unaryTransportLocalEnvelope left right
      (binaryTermCode term).length

theorem unaryTermEqualityUnderAssumptionStructuralPayloadBound_le_polynomial
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    unaryTermEqualityUnderAssumptionStructuralPayloadBound term left right <=
      unaryTermEqualityUnderAssumptionPayloadPolynomial term left right := by
  have hstructural :=
    unaryTermEqualityUnderAssumptionStructuralPayloadBound_le_symbolCount
      term left right (binaryTermCode term).length le_rfl
  have hsymbols := termSymbolCount_le_binaryTermCode_length term
  exact hstructural.trans (by
    unfold unaryTermEqualityUnderAssumptionPayloadPolynomial
    exact Nat.mul_le_mul_right _ hsymbols)

theorem compileUnaryTermEqualityUnderAssumption_payloadLength_le_polynomial
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (compileUnaryTermEqualityUnderAssumption term left right).payloadLength <=
      unaryTermEqualityUnderAssumptionPayloadPolynomial term left right := by
  exact (compileUnaryTermEqualityUnderAssumption_payloadLength_le
    term left right).trans
      (unaryTermEqualityUnderAssumptionStructuralPayloadBound_le_polynomial
        term left right)

/-! ## The two PA relation-extensionality axioms under one fixed envelope -/

def fixedPARelationFormulaSeed : Nat :=
  (binaryFormulaCode
      (binaryRelationExtOuterBody Language.ORing.Rel.eq)).length +
    (binaryFormulaCode
      (binaryRelationExtOuterBody Language.ORing.Rel.lt)).length + 1

def relationFormulaStage0 : Nat := fixedPARelationFormulaSeed

def relationFormulaStage1 (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope relationFormulaStage0 termBound

def relationFormulaStage2 (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope (relationFormulaStage1 termBound) termBound

def relationFormulaStage3 (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope (relationFormulaStage2 termBound) termBound

def relationFormulaStage4 (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope (relationFormulaStage3 termBound) termBound

def relationFormulaCodeEnvelope (termBound : Nat) : Nat :=
  relationFormulaStage0 + relationFormulaStage1 termBound +
    relationFormulaStage2 termBound + relationFormulaStage3 termBound +
    relationFormulaStage4 termBound + 1

def relationSpecializationScaleEnvelope (termBound : Nat) : Nat :=
  relationFormulaCodeEnvelope termBound + termBound + 1

def relationSpecializationCostEnvelope (termBound : Nat) : Nat :=
  192 + 2048 * relationSpecializationScaleEnvelope termBound *
    relationSpecializationScaleEnvelope termBound *
    relationSpecializationScaleEnvelope termBound

def fixedPARelationPayloadEnvelope : Nat :=
  (32 + 10 * axiomSyntaxBudget
      (.eqRelExt Language.ORing.Rel.eq)) +
    (32 + 10 * axiomSyntaxBudget
      (.eqRelExt Language.ORing.Rel.lt)) + 1

def relationImplicationPayloadEnvelope (termBound : Nat) : Nat :=
  fixedPARelationPayloadEnvelope +
    4 * relationSpecializationCostEnvelope termBound

theorem binaryRelationExtOuterBody_code_le_relationStage0
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2) :
    (binaryFormulaCode
      (binaryRelationExtOuterBody relationSymbol)).length <=
      relationFormulaStage0 := by
  cases relationSymbol <;>
    unfold relationFormulaStage0 fixedPARelationFormulaSeed <;> omega

theorem relationFormulaStage_le_envelope
    (stage termBound : Nat)
    (hstage : stage = relationFormulaStage0 ∨
      stage = relationFormulaStage1 termBound ∨
      stage = relationFormulaStage2 termBound ∨
      stage = relationFormulaStage3 termBound ∨
      stage = relationFormulaStage4 termBound) :
    stage <= relationFormulaCodeEnvelope termBound := by
  rcases hstage with h | h | h | h | h <;> subst stage <;>
    unfold relationFormulaCodeEnvelope <;> omega

theorem binaryRelationExtRightFirstBody_code_le_relationStage1
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (binaryFormulaCode
      (binaryRelationExtRightFirstBody relationSymbol rightSecond)).length <=
      relationFormulaStage1 termBound := by
  exact instantiatedUniversalBody_code_le_next
    (binaryRelationExtOuterBody relationSymbol)
    (binaryRelationExtRightFirstBody relationSymbol rightSecond)
    rightSecond relationFormulaStage0 termBound
    (binaryRelationExtOuterBody_code_le_relationStage0 relationSymbol)
    hrightSecond
    (binaryRelationExtAfterRightSecond_formula relationSymbol rightSecond)

theorem binaryRelationExtLeftSecondBody_code_le_relationStage2
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (rightFirst rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (binaryFormulaCode
      (binaryRelationExtLeftSecondBody relationSymbol
        rightFirst rightSecond)).length <= relationFormulaStage2 termBound := by
  exact instantiatedUniversalBody_code_le_next
    (binaryRelationExtRightFirstBody relationSymbol rightSecond)
    (binaryRelationExtLeftSecondBody relationSymbol rightFirst rightSecond)
    rightFirst (relationFormulaStage1 termBound) termBound
    (binaryRelationExtRightFirstBody_code_le_relationStage1
      relationSymbol rightSecond termBound hrightSecond)
    hrightFirst
    (binaryRelationExtAfterRightFirst_formula relationSymbol
      rightFirst rightSecond)

theorem binaryRelationExtAfterLeftSecondMatrix_code_le_relationStage3
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (binaryFormulaCode
      (binaryRelationExtAfterLeftSecondMatrix relationSymbol
        leftSecond rightFirst rightSecond)).length <=
      relationFormulaStage3 termBound := by
  exact instantiatedUniversalBody_code_le_next
    (binaryRelationExtLeftSecondBody relationSymbol rightFirst rightSecond)
    (binaryRelationExtAfterLeftSecondMatrix relationSymbol
      leftSecond rightFirst rightSecond)
    leftSecond (relationFormulaStage2 termBound) termBound
    (binaryRelationExtLeftSecondBody_code_le_relationStage2
      relationSymbol rightFirst rightSecond termBound
      hrightFirst hrightSecond)
    hleftSecond
    (binaryRelationExtAfterLeftSecond_formula relationSymbol
      leftSecond rightFirst rightSecond)

theorem specializationCost_le_relationEnvelope
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hformula : (binaryFormulaCode formula).length <=
      relationFormulaCodeEnvelope termBound)
    (hwitness : (binaryTermCode witness).length <= termBound) :
    specializationCost formula witness <=
      relationSpecializationCostEnvelope termBound := by
  have hscale : specializationScale formula witness <=
      relationSpecializationScaleEnvelope termBound := by
    simp [specializationScale, relationSpecializationScaleEnvelope]
    omega
  simp only [specializationCost, relationSpecializationCostEnvelope]
  gcongr

theorem binaryRelationExtAxiomProof_payloadLength_le_relationFixed
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2) :
    (binaryRelationExtAxiomProof relationSymbol).payloadLength <=
      fixedPARelationPayloadEnvelope := by
  calc
    (binaryRelationExtAxiomProof relationSymbol).payloadLength <=
        32 + 10 * axiomSyntaxBudget (.eqRelExt relationSymbol) :=
      binaryRelationExtAxiomProof_payloadLength_le relationSymbol
    _ <= fixedPARelationPayloadEnvelope := by
      cases relationSymbol <;>
        unfold fixedPARelationPayloadEnvelope <;> omega

theorem binaryRelationExtImplication_payloadLength_le_relationEnvelope
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (binaryRelationExtImplication relationSymbol
      leftFirst leftSecond rightFirst rightSecond).payloadLength <=
      relationImplicationPayloadEnvelope termBound := by
  have hraw := binaryRelationExtImplication_payloadLength_le
    relationSymbol leftFirst leftSecond rightFirst rightSecond
  have haxiom :=
    binaryRelationExtAxiomProof_payloadLength_le_relationFixed relationSymbol
  have hfirst := specializationCost_le_relationEnvelope
    (binaryRelationExtOuterBody relationSymbol) rightSecond termBound
    ((binaryRelationExtOuterBody_code_le_relationStage0 relationSymbol).trans
      (relationFormulaStage_le_envelope relationFormulaStage0 termBound
        (Or.inl rfl)))
    hrightSecond
  have hsecond := specializationCost_le_relationEnvelope
    (binaryRelationExtRightFirstBody relationSymbol rightSecond)
    rightFirst termBound
    ((binaryRelationExtRightFirstBody_code_le_relationStage1
      relationSymbol rightSecond termBound hrightSecond).trans
        (relationFormulaStage_le_envelope
          (relationFormulaStage1 termBound) termBound
          (Or.inr (Or.inl rfl))))
    hrightFirst
  have hthird := specializationCost_le_relationEnvelope
    (binaryRelationExtLeftSecondBody relationSymbol rightFirst rightSecond)
    leftSecond termBound
    ((binaryRelationExtLeftSecondBody_code_le_relationStage2
      relationSymbol rightFirst rightSecond termBound
      hrightFirst hrightSecond).trans
        (relationFormulaStage_le_envelope
          (relationFormulaStage2 termBound) termBound
          (Or.inr (Or.inr (Or.inl rfl)))))
    hleftSecond
  have hfourth := specializationCost_le_relationEnvelope
    (binaryRelationExtAfterLeftSecondMatrix relationSymbol
      leftSecond rightFirst rightSecond)
    leftFirst termBound
    ((binaryRelationExtAfterLeftSecondMatrix_code_le_relationStage3
      relationSymbol leftSecond rightFirst rightSecond termBound
      hleftSecond hrightFirst hrightSecond).trans
        (relationFormulaStage_le_envelope
          (relationFormulaStage3 termBound) termBound
          (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    hleftFirst
  unfold relationImplicationPayloadEnvelope
  omega

/-! ## Uniform local ledger for relation transport in the equality context -/

def atomicRelationFormulaEnvelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat) : Nat :=
  8 * (unaryTransportFormulaEnvelope left right termBound +
    orderPrimitiveFormulaCodeEnvelope termBound +
    relationFormulaCodeEnvelope termBound + 1)

def relationTransportLocalEnvelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat) : Nat :=
  16 * (fixedPAPayloadEnvelope +
    relationImplicationPayloadEnvelope termBound +
    smallContextAssemblyEnvelope
      (atomicRelationFormulaEnvelope left right termBound) + 1)

theorem unaryTransportFormulaEnvelope_le_atomicRelation
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat) :
    unaryTransportFormulaEnvelope left right termBound <=
      atomicRelationFormulaEnvelope left right termBound := by
  unfold atomicRelationFormulaEnvelope
  omega

theorem orderAtomicFormulaCodeEnvelope_le_atomicRelation
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat) :
    orderAtomicFormulaCodeEnvelope termBound <=
      atomicRelationFormulaEnvelope left right termBound := by
  have hderived := orderAtomic_le_derived termBound
  have hlocal := orderDerived_le_local termBound
  have hprimitive := orderLocal_le_primitive termBound
  unfold atomicRelationFormulaEnvelope
  omega

theorem orderDerivedFormulaCodeEnvelope_le_atomicRelation
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat) :
    orderDerivedFormulaCodeEnvelope termBound <=
      atomicRelationFormulaEnvelope left right termBound := by
  have hlocal := orderDerived_le_local termBound
  have hprimitive := orderLocal_le_primitive termBound
  unfold atomicRelationFormulaEnvelope
  omega

theorem orderLocalFormulaCodeEnvelope_le_atomicRelation
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat) :
    orderLocalFormulaCodeEnvelope termBound <=
      atomicRelationFormulaEnvelope left right termBound := by
  have hprimitive := orderLocal_le_primitive termBound
  unfold atomicRelationFormulaEnvelope
  omega

theorem orderPrimitiveFormulaCodeEnvelope_le_atomicRelation
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat) :
    orderPrimitiveFormulaCodeEnvelope termBound <=
      atomicRelationFormulaEnvelope left right termBound := by
  unfold atomicRelationFormulaEnvelope
  omega

theorem binaryRelationFormula_code_le_orderAtomic
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (first second : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hfirst : (binaryTermCode first).length <= termBound)
    (hsecond : (binaryTermCode second).length <= termBound) :
    (binaryFormulaCode
      (binaryRelationFormula relationSymbol first second)).length <=
      orderAtomicFormulaCodeEnvelope termBound := by
  cases relationSymbol with
  | eq =>
      change (binaryFormulaCode
        (“!!first = !!second” :
          LO.FirstOrder.ArithmeticProposition)).length <= _
      exact equalityFormula_code_le_orderAtomic
        first second termBound hfirst hsecond
  | lt =>
      change (binaryFormulaCode
        (“!!first < !!second” :
          LO.FirstOrder.ArithmeticProposition)).length <= _
      exact lessThanFormula_code_le_orderAtomic
        first second termBound hfirst hsecond

theorem binaryRelationCongruenceConclusion_code_le_relationDerived
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (binaryFormulaCode
      (binaryRelationCongruenceConclusion relationSymbol
        leftFirst leftSecond rightFirst rightSecond)).length <=
      orderDerivedFormulaCodeEnvelope termBound := by
  have hleft := binaryRelationFormula_code_le_orderAtomic
    relationSymbol leftFirst leftSecond termBound hleftFirst hleftSecond
  have hright := binaryRelationFormula_code_le_orderAtomic
    relationSymbol rightFirst rightSecond termBound hrightFirst hrightSecond
  have himplication := binaryFormulaCode_implication_length_le
    (binaryRelationFormula relationSymbol leftFirst leftSecond)
    (binaryRelationFormula relationSymbol rightFirst rightSecond)
  unfold binaryRelationCongruenceConclusion
  unfold orderDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
  omega

theorem relationTransportImplicationStructuralPayloadBound_le_uniform
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstPayloadLength secondPayloadLength termBound : Nat)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    relationTransportImplicationStructuralPayloadBound
        (parameterEqualityContext left right) relationSymbol
        leftFirst leftSecond rightFirst rightSecond
        firstPayloadLength secondPayloadLength <=
      firstPayloadLength + secondPayloadLength +
        relationTransportLocalEnvelope left right termBound := by
  let Gamma := parameterEqualityContext left right
  let formulaBound := atomicRelationFormulaEnvelope left right termBound
  let firstFormula :=
    (“!!leftFirst = !!rightFirst” :
      LO.FirstOrder.ArithmeticProposition)
  let secondFormula :=
    (“!!leftSecond = !!rightSecond” :
      LO.FirstOrder.ArithmeticProposition)
  let truthFormula := (⊤ : LO.FirstOrder.ArithmeticProposition)
  let innerFormula := secondFormula ⋏ truthFormula
  let antecedentFormula := binaryRelationCongruenceAntecedent
    leftFirst leftSecond rightFirst rightSecond
  let conclusionFormula := binaryRelationCongruenceConclusion relationSymbol
    leftFirst leftSecond rightFirst rightSecond
  let implicationFormula := antecedentFormula 🡒 conclusionFormula
  have hcontextRaw := parameterEqualityContext_formulaCodeBound_transport
    left right termBound
  have hcontext : FormulaCodeBound Gamma formulaBound := by
    intro formula hformula
    exact (hcontextRaw formula hformula).trans
      (unaryTransportFormulaEnvelope_le_atomicRelation
        left right termBound)
  have hcontextCard : Gamma.card <= 4 := by
    simpa only [Gamma] using parameterEqualityContext_card_le_transport
      left right
  have hfirstFormulaRaw := equalityFormula_code_le_orderAtomic
    leftFirst rightFirst termBound hleftFirst hrightFirst
  have hsecondFormulaRaw := equalityFormula_code_le_orderAtomic
    leftSecond rightSecond termBound hleftSecond hrightSecond
  have htruthRaw := truthFormula_code_le_orderAtomic termBound
  have hinnerRaw := equalityTruthConjunction_code_le_derived
    leftSecond rightSecond termBound hleftSecond hrightSecond
  have hantecedentRaw := relationCongruenceAntecedent_code_le_local
    leftFirst leftSecond rightFirst rightSecond termBound
    hleftFirst hleftSecond hrightFirst hrightSecond
  have hconclusionRaw :=
    binaryRelationCongruenceConclusion_code_le_relationDerived
      relationSymbol leftFirst leftSecond rightFirst rightSecond termBound
      hleftFirst hleftSecond hrightFirst hrightSecond
  have hfirstFormula : (binaryFormulaCode firstFormula).length <=
      formulaBound := by
    exact hfirstFormulaRaw.trans
      (orderAtomicFormulaCodeEnvelope_le_atomicRelation
        left right termBound)
  have hsecondFormula : (binaryFormulaCode secondFormula).length <=
      formulaBound := by
    exact hsecondFormulaRaw.trans
      (orderAtomicFormulaCodeEnvelope_le_atomicRelation
        left right termBound)
  have htruth : (binaryFormulaCode truthFormula).length <=
      formulaBound := by
    exact htruthRaw.trans
      (orderAtomicFormulaCodeEnvelope_le_atomicRelation
        left right termBound)
  have hinner : (binaryFormulaCode innerFormula).length <=
      formulaBound := by
    exact hinnerRaw.trans
      (orderDerivedFormulaCodeEnvelope_le_atomicRelation
        left right termBound)
  have hantecedent : (binaryFormulaCode antecedentFormula).length <=
      formulaBound := by
    exact hantecedentRaw.trans
      (orderLocalFormulaCodeEnvelope_le_atomicRelation
        left right termBound)
  have hconclusion : (binaryFormulaCode conclusionFormula).length <=
      formulaBound := by
    exact hconclusionRaw.trans
      (orderDerivedFormulaCodeEnvelope_le_atomicRelation
        left right termBound)
  have hderivedLocal := orderDerived_le_local termBound
  have hlocalPrimitive := orderLocal_le_primitive termBound
  have hprimitiveEight :
      8 <= orderPrimitiveFormulaCodeEnvelope termBound := by
    unfold orderPrimitiveFormulaCodeEnvelope paAssemblySyntaxEnvelope
    omega
  have hconclusionTight :
      (binaryFormulaCode conclusionFormula).length <=
        orderPrimitiveFormulaCodeEnvelope termBound := by
    dsimp only [conclusionFormula]
    exact (hconclusionRaw.trans hderivedLocal).trans hlocalPrimitive
  have htagFive : (binaryNatCode 5).length <= 8 := by decide
  have himplicationRaw := binaryFormulaCode_implication_length_le
    antecedentFormula conclusionFormula
  have himplicationTight :
      (binaryFormulaCode implicationFormula).length <=
        4 * orderPrimitiveFormulaCodeEnvelope termBound := by
    dsimp only [implicationFormula, antecedentFormula, conclusionFormula]
    dsimp only [antecedentFormula, conclusionFormula] at himplicationRaw
    omega
  have himplication : (binaryFormulaCode implicationFormula).length <=
      formulaBound := by
    unfold formulaBound atomicRelationFormulaEnvelope
    omega
  have hnegatedImplicationRaw := binaryFormulaCode_neg_length_le
    implicationFormula
  have hnegatedConclusionRaw := binaryFormulaCode_neg_length_le
    conclusionFormula
  have hnegatedImplication :
      (binaryFormulaCode (∼implicationFormula)).length <= formulaBound := by
    unfold formulaBound atomicRelationFormulaEnvelope
    omega
  have hnegatedConclusion :
      (binaryFormulaCode (∼conclusionFormula)).length <= formulaBound := by
    unfold formulaBound atomicRelationFormulaEnvelope
    omega
  have htruthContext := hcontext.insert htruth
  have himplicationContext := hcontext.insert himplication
  have htruthCard : (insert truthFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le truthFormula Gamma
    omega
  have himplicationCard : (insert implicationFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le implicationFormula Gamma
    omega
  have hverum := verumProof_payloadLength_le_fixed
  have hweakTruth := weakeningFullAssemblyCost_le_small
    (insert truthFormula Gamma) formulaBound htruthCard htruthContext
  have hinnerCost := conjunctionFullAssemblyCost_le_small
    Gamma secondFormula truthFormula formulaBound
    hcontextCard hcontext hsecondFormula htruth hinner
  have hantecedentCost := conjunctionFullAssemblyCost_le_small
    Gamma firstFormula innerFormula formulaBound
    hcontextCard hcontext hfirstFormula hinner hantecedent
  have himplicationTheorem :=
    binaryRelationExtImplication_payloadLength_le_relationEnvelope
      relationSymbol leftFirst leftSecond rightFirst rightSecond termBound
      hleftFirst hleftSecond hrightFirst hrightSecond
  have hweakImplication := weakeningFullAssemblyCost_le_small
    (insert implicationFormula Gamma) formulaBound
    himplicationCard himplicationContext
  have hmp := contextualModusPonensFullAssemblyCost_le_small
    Gamma antecedentFormula conclusionFormula formulaBound
    hcontextCard hcontext hantecedent hconclusion himplication
    hnegatedImplication hnegatedConclusion
  unfold relationTransportImplicationStructuralPayloadBound
  dsimp only [Gamma, formulaBound, firstFormula, secondFormula, truthFormula,
    innerFormula, antecedentFormula, conclusionFormula,
    implicationFormula] at *
  unfold relationTransportLocalEnvelope
  omega

/-! ## Shared formula and symmetry costs for positive and negative atoms -/

def atomicTransportPayloadEnvelope
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (openTermCodeBound sourcePayloadBound : Nat) : Nat :=
  let termBound := unaryTransportTermEnvelope
    left right openTermCodeBound
  let formulaBound := atomicRelationFormulaEnvelope left right termBound
  sourcePayloadBound +
    2 * openTermCodeBound *
      unaryTransportLocalEnvelope left right openTermCodeBound +
    2 * paPrimitiveCostEnvelope termBound +
    relationTransportLocalEnvelope left right termBound +
    8 * smallContextAssemblyEnvelope formulaBound + 1

theorem substitutionFormulaCodeEnvelope_mono_local
    {smallFormula largeFormula smallTerm largeTerm : Nat}
    (hformula : smallFormula <= largeFormula)
    (hterm : smallTerm <= largeTerm) :
    substitutionFormulaCodeEnvelope smallFormula smallTerm <=
      substitutionFormulaCodeEnvelope largeFormula largeTerm := by
  unfold substitutionFormulaCodeEnvelope
  gcongr

theorem instantiatedFormulaCodeEnvelope_mono_local
    {small large : Nat} (h : small <= large) :
    instantiatedFormulaCodeEnvelope small <=
      instantiatedFormulaCodeEnvelope large := by
  have hstageOne := substitutionFormulaCodeEnvelope_mono_local
    (smallFormula := instantiatedFormulaStage0)
    (largeFormula := instantiatedFormulaStage0) le_rfl h
  change instantiatedFormulaStage1 small <=
    instantiatedFormulaStage1 large at hstageOne
  have hstageTwo := substitutionFormulaCodeEnvelope_mono_local
    hstageOne h
  change instantiatedFormulaStage2 small <=
    instantiatedFormulaStage2 large at hstageTwo
  have hstageThree := substitutionFormulaCodeEnvelope_mono_local
    hstageTwo h
  change instantiatedFormulaStage3 small <=
    instantiatedFormulaStage3 large at hstageThree
  have hstageFour := substitutionFormulaCodeEnvelope_mono_local
    hstageThree h
  change instantiatedFormulaStage4 small <=
    instantiatedFormulaStage4 large at hstageFour
  unfold instantiatedFormulaCodeEnvelope
  omega

theorem paFormulaCodeEnvelope_mono_local
    {small large : Nat} (h : small <= large) :
    paFormulaCodeEnvelope small <= paFormulaCodeEnvelope large := by
  have hinstantiated := instantiatedFormulaCodeEnvelope_mono_local h
  unfold paFormulaCodeEnvelope paEqualityFormulaCodeEnvelope
  omega

theorem paAssemblySyntaxEnvelope_mono_local
    {small large : Nat} (h : small <= large) :
    paAssemblySyntaxEnvelope small <= paAssemblySyntaxEnvelope large := by
  unfold paAssemblySyntaxEnvelope
  omega

theorem paPrimitiveAssemblyCostEnvelope_mono_local
    {small large : Nat} (h : small <= large) :
    paPrimitiveAssemblyCostEnvelope small <=
      paPrimitiveAssemblyCostEnvelope large := by
  have hformula := paFormulaCodeEnvelope_mono_local h
  have hderived := paAssemblySyntaxEnvelope_mono_local hformula
  have hlocal := paAssemblySyntaxEnvelope_mono_local hderived
  exact paAssemblySyntaxEnvelope_mono_local hlocal

theorem paSpecializationCostEnvelope_mono_local
    {small large : Nat} (h : small <= large) :
    paSpecializationCostEnvelope small <=
      paSpecializationCostEnvelope large := by
  have hformula := instantiatedFormulaCodeEnvelope_mono_local h
  have hscale : paSpecializationScaleEnvelope small <=
      paSpecializationScaleEnvelope large := by
    unfold paSpecializationScaleEnvelope
    omega
  unfold paSpecializationCostEnvelope
  gcongr

theorem paPrimitiveCostEnvelope_mono_local
    {small large : Nat} (h : small <= large) :
    paPrimitiveCostEnvelope small <= paPrimitiveCostEnvelope large := by
  have hspecialization := paSpecializationCostEnvelope_mono_local h
  have hformula := paFormulaCodeEnvelope_mono_local h
  have hderived := paAssemblySyntaxEnvelope_mono_local hformula
  have hlocal := paAssemblySyntaxEnvelope_mono_local hderived
  have hprimitive := paAssemblySyntaxEnvelope_mono_local hlocal
  have hlocalAlias : paLocalAssemblyCostEnvelope small <=
      paLocalAssemblyCostEnvelope large := by
    unfold paLocalAssemblyCostEnvelope paDerivedFormulaCodeEnvelope
    exact hlocal
  have hprimitiveAlias : paPrimitiveAssemblyCostEnvelope small <=
      paPrimitiveAssemblyCostEnvelope large :=
    paPrimitiveAssemblyCostEnvelope_mono_local h
  unfold paPrimitiveCostEnvelope
  omega

theorem relationFormulaCodeEnvelope_mono_local
    {small large : Nat} (h : small <= large) :
    relationFormulaCodeEnvelope small <=
      relationFormulaCodeEnvelope large := by
  have hstageOne := substitutionFormulaCodeEnvelope_mono_local
    (smallFormula := relationFormulaStage0)
    (largeFormula := relationFormulaStage0) le_rfl h
  change relationFormulaStage1 small <=
    relationFormulaStage1 large at hstageOne
  have hstageTwo := substitutionFormulaCodeEnvelope_mono_local
    hstageOne h
  change relationFormulaStage2 small <=
    relationFormulaStage2 large at hstageTwo
  have hstageThree := substitutionFormulaCodeEnvelope_mono_local
    hstageTwo h
  change relationFormulaStage3 small <=
    relationFormulaStage3 large at hstageThree
  have hstageFour := substitutionFormulaCodeEnvelope_mono_local
    hstageThree h
  change relationFormulaStage4 small <=
    relationFormulaStage4 large at hstageFour
  unfold relationFormulaCodeEnvelope
  omega

theorem relationSpecializationCostEnvelope_mono_local
    {small large : Nat} (h : small <= large) :
    relationSpecializationCostEnvelope small <=
      relationSpecializationCostEnvelope large := by
  have hformula := relationFormulaCodeEnvelope_mono_local h
  have hscale : relationSpecializationScaleEnvelope small <=
      relationSpecializationScaleEnvelope large := by
    unfold relationSpecializationScaleEnvelope
    omega
  unfold relationSpecializationCostEnvelope
  gcongr

theorem relationImplicationPayloadEnvelope_mono_local
    {small large : Nat} (h : small <= large) :
    relationImplicationPayloadEnvelope small <=
      relationImplicationPayloadEnvelope large := by
  have hspecialization := relationSpecializationCostEnvelope_mono_local h
  unfold relationImplicationPayloadEnvelope
  omega

theorem orderPrimitiveFormulaCodeEnvelope_mono_local
    {small large : Nat} (h : small <= large) :
    orderPrimitiveFormulaCodeEnvelope small <=
      orderPrimitiveFormulaCodeEnvelope large := by
  have hpa := paFormulaCodeEnvelope_mono_local h
  have hatomic : orderAtomicFormulaCodeEnvelope small <=
      orderAtomicFormulaCodeEnvelope large := by
    unfold orderAtomicFormulaCodeEnvelope
    omega
  have hderived := paAssemblySyntaxEnvelope_mono_local hatomic
  have hlocal := paAssemblySyntaxEnvelope_mono_local hderived
  exact paAssemblySyntaxEnvelope_mono_local hlocal

theorem smallContextAssemblyEnvelope_mono_local
    {small large : Nat} (h : small <= large) :
    smallContextAssemblyEnvelope small <=
      smallContextAssemblyEnvelope large := by
  unfold smallContextAssemblyEnvelope smallSequentCodeEnvelope
  omega

theorem unaryTransportTermEnvelope_mono
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    {small large : Nat} (h : small <= large) :
    unaryTransportTermEnvelope left right small <=
      unaryTransportTermEnvelope left right large := by
  unfold unaryTransportTermEnvelope unaryTermSubstitutionCodeEnvelope
  exact Nat.mul_le_mul_left _ h

theorem unaryTransportFormulaEnvelope_mono
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    {small large : Nat} (h : small <= large) :
    unaryTransportFormulaEnvelope left right small <=
      unaryTransportFormulaEnvelope left right large := by
  have hprimitive := paPrimitiveAssemblyCostEnvelope_mono_local h
  unfold unaryTransportFormulaEnvelope
  omega

theorem unaryTransportLocalEnvelope_mono
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    {small large : Nat} (h : small <= large) :
    unaryTransportLocalEnvelope left right small <=
      unaryTransportLocalEnvelope left right large := by
  have hterm := unaryTransportTermEnvelope_mono left right h
  have hprimitive := paPrimitiveCostEnvelope_mono_local hterm
  have hformula := unaryTransportFormulaEnvelope_mono left right hterm
  have hcontext := smallContextAssemblyEnvelope_mono_local hformula
  unfold unaryTransportLocalEnvelope
  dsimp only
  omega

theorem atomicRelationFormulaEnvelope_mono
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    {small large : Nat} (h : small <= large) :
    atomicRelationFormulaEnvelope left right small <=
      atomicRelationFormulaEnvelope left right large := by
  have hunary := unaryTransportFormulaEnvelope_mono left right h
  have horder := orderPrimitiveFormulaCodeEnvelope_mono_local h
  have hrelation := relationFormulaCodeEnvelope_mono_local h
  unfold atomicRelationFormulaEnvelope
  omega

theorem relationTransportLocalEnvelope_mono
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    {small large : Nat} (h : small <= large) :
    relationTransportLocalEnvelope left right small <=
      relationTransportLocalEnvelope left right large := by
  have himplication := relationImplicationPayloadEnvelope_mono_local h
  have hformula := atomicRelationFormulaEnvelope_mono left right h
  have hcontext := smallContextAssemblyEnvelope_mono_local hformula
  unfold relationTransportLocalEnvelope
  omega

theorem atomicTransportPayloadEnvelope_mono
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    {smallOpen largeOpen smallSource largeSource : Nat}
    (hopen : smallOpen <= largeOpen)
    (hsource : smallSource <= largeSource) :
    atomicTransportPayloadEnvelope left right smallOpen smallSource <=
      atomicTransportPayloadEnvelope left right largeOpen largeSource := by
  have hterm := unaryTransportTermEnvelope_mono left right hopen
  have hunary := unaryTransportLocalEnvelope_mono left right hopen
  have hprimitive := paPrimitiveCostEnvelope_mono_local hterm
  have hrelation := relationTransportLocalEnvelope_mono left right hterm
  have hformula := atomicRelationFormulaEnvelope_mono left right hterm
  have hcontext := smallContextAssemblyEnvelope_mono_local hformula
  unfold atomicTransportPayloadEnvelope
  dsimp only
  gcongr

/-! ## A term-independent envelope for varying closed parameters -/

def uniformUnaryTransportTermEnvelope
    (closedTermCodeBound openTermCodeBound : Nat) : Nat :=
  2 * closedTermCodeBound * openTermCodeBound

def uniformUnaryTransportFormulaEnvelope
    (closedTermCodeBound termBound : Nat) : Nat :=
  4 * (paPrimitiveAssemblyCostEnvelope termBound +
    paFormulaCodeEnvelope (2 * closedTermCodeBound) + 1)

def uniformUnaryTransportLocalEnvelope
    (closedTermCodeBound openTermCodeBound : Nat) : Nat :=
  let termBound := uniformUnaryTransportTermEnvelope
    closedTermCodeBound openTermCodeBound
  let formulaBound := uniformUnaryTransportFormulaEnvelope
    closedTermCodeBound termBound
  16 * (paPrimitiveCostEnvelope termBound +
    smallContextAssemblyEnvelope formulaBound + 1)

def uniformAtomicRelationFormulaEnvelope
    (closedTermCodeBound termBound : Nat) : Nat :=
  8 * (uniformUnaryTransportFormulaEnvelope
      closedTermCodeBound termBound +
    orderPrimitiveFormulaCodeEnvelope termBound +
    relationFormulaCodeEnvelope termBound + 1)

def uniformRelationTransportLocalEnvelope
    (closedTermCodeBound termBound : Nat) : Nat :=
  16 * (fixedPAPayloadEnvelope +
    relationImplicationPayloadEnvelope termBound +
    smallContextAssemblyEnvelope
      (uniformAtomicRelationFormulaEnvelope
        closedTermCodeBound termBound) + 1)

def uniformAtomicTransportPayloadEnvelope
    (closedTermCodeBound openTermCodeBound sourcePayloadBound : Nat) : Nat :=
  let termBound := uniformUnaryTransportTermEnvelope
    closedTermCodeBound openTermCodeBound
  let formulaBound := uniformAtomicRelationFormulaEnvelope
    closedTermCodeBound termBound
  sourcePayloadBound +
    2 * openTermCodeBound *
      uniformUnaryTransportLocalEnvelope
        closedTermCodeBound openTermCodeBound +
    2 * paPrimitiveCostEnvelope termBound +
    uniformRelationTransportLocalEnvelope
      closedTermCodeBound termBound +
    8 * smallContextAssemblyEnvelope formulaBound + 1

theorem unaryTransportTermEnvelope_le_uniform
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (closedTermCodeBound openTermCodeBound : Nat)
    (hleft : (binaryTermCode left).length <= closedTermCodeBound)
    (hright : (binaryTermCode right).length <= closedTermCodeBound) :
    unaryTransportTermEnvelope left right openTermCodeBound <=
      uniformUnaryTransportTermEnvelope
        closedTermCodeBound openTermCodeBound := by
  unfold unaryTransportTermEnvelope unaryTermSubstitutionCodeEnvelope
    uniformUnaryTransportTermEnvelope substitutionCodeFactor
  gcongr
  omega

theorem unaryTransportFormulaEnvelope_le_uniform
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (closedTermCodeBound : Nat)
    {smallTermBound largeTermBound : Nat}
    (hleft : (binaryTermCode left).length <= closedTermCodeBound)
    (hright : (binaryTermCode right).length <= closedTermCodeBound)
    (hterm : smallTermBound <= largeTermBound) :
    unaryTransportFormulaEnvelope left right smallTermBound <=
      uniformUnaryTransportFormulaEnvelope
        closedTermCodeBound largeTermBound := by
  have hprimitive := paPrimitiveAssemblyCostEnvelope_mono_local hterm
  have hformulaArgument :
      (binaryTermCode left).length + (binaryTermCode right).length <=
        2 * closedTermCodeBound := by omega
  have hformula := paFormulaCodeEnvelope_mono_local hformulaArgument
  unfold unaryTransportFormulaEnvelope
    uniformUnaryTransportFormulaEnvelope
  omega

theorem unaryTransportLocalEnvelope_le_uniform
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (closedTermCodeBound openTermCodeBound : Nat)
    (hleft : (binaryTermCode left).length <= closedTermCodeBound)
    (hright : (binaryTermCode right).length <= closedTermCodeBound) :
    unaryTransportLocalEnvelope left right openTermCodeBound <=
      uniformUnaryTransportLocalEnvelope
        closedTermCodeBound openTermCodeBound := by
  let smallTermBound := unaryTransportTermEnvelope
    left right openTermCodeBound
  let largeTermBound := uniformUnaryTransportTermEnvelope
    closedTermCodeBound openTermCodeBound
  have hterm : smallTermBound <= largeTermBound :=
    unaryTransportTermEnvelope_le_uniform left right
      closedTermCodeBound openTermCodeBound hleft hright
  have hprimitive := paPrimitiveCostEnvelope_mono_local hterm
  have hformula := unaryTransportFormulaEnvelope_le_uniform
    left right closedTermCodeBound hleft hright hterm
  have hcontext := smallContextAssemblyEnvelope_mono_local hformula
  unfold unaryTransportLocalEnvelope uniformUnaryTransportLocalEnvelope
  dsimp only [smallTermBound, largeTermBound] at hprimitive hformula hcontext ⊢
  omega

theorem atomicRelationFormulaEnvelope_le_uniform
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (closedTermCodeBound : Nat)
    {smallTermBound largeTermBound : Nat}
    (hleft : (binaryTermCode left).length <= closedTermCodeBound)
    (hright : (binaryTermCode right).length <= closedTermCodeBound)
    (hterm : smallTermBound <= largeTermBound) :
    atomicRelationFormulaEnvelope left right smallTermBound <=
      uniformAtomicRelationFormulaEnvelope
        closedTermCodeBound largeTermBound := by
  have hunary := unaryTransportFormulaEnvelope_le_uniform
    left right closedTermCodeBound hleft hright hterm
  have horder := orderPrimitiveFormulaCodeEnvelope_mono_local hterm
  have hrelation := relationFormulaCodeEnvelope_mono_local hterm
  unfold atomicRelationFormulaEnvelope
    uniformAtomicRelationFormulaEnvelope
  omega

theorem relationTransportLocalEnvelope_le_uniform
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (closedTermCodeBound : Nat)
    {smallTermBound largeTermBound : Nat}
    (hleft : (binaryTermCode left).length <= closedTermCodeBound)
    (hright : (binaryTermCode right).length <= closedTermCodeBound)
    (hterm : smallTermBound <= largeTermBound) :
    relationTransportLocalEnvelope left right smallTermBound <=
      uniformRelationTransportLocalEnvelope
        closedTermCodeBound largeTermBound := by
  have himplication := relationImplicationPayloadEnvelope_mono_local hterm
  have hformula := atomicRelationFormulaEnvelope_le_uniform
    left right closedTermCodeBound hleft hright hterm
  have hcontext := smallContextAssemblyEnvelope_mono_local hformula
  unfold relationTransportLocalEnvelope
    uniformRelationTransportLocalEnvelope
  omega

theorem atomicTransportPayloadEnvelope_le_uniform
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (closedTermCodeBound openTermCodeBound sourcePayloadBound : Nat)
    (hleft : (binaryTermCode left).length <= closedTermCodeBound)
    (hright : (binaryTermCode right).length <= closedTermCodeBound) :
    atomicTransportPayloadEnvelope
        left right openTermCodeBound sourcePayloadBound <=
      uniformAtomicTransportPayloadEnvelope
        closedTermCodeBound openTermCodeBound sourcePayloadBound := by
  let smallTermBound := unaryTransportTermEnvelope
    left right openTermCodeBound
  let largeTermBound := uniformUnaryTransportTermEnvelope
    closedTermCodeBound openTermCodeBound
  have hterm : smallTermBound <= largeTermBound :=
    unaryTransportTermEnvelope_le_uniform left right
      closedTermCodeBound openTermCodeBound hleft hright
  have hunary := unaryTransportLocalEnvelope_le_uniform
    left right closedTermCodeBound openTermCodeBound hleft hright
  have hprimitive := paPrimitiveCostEnvelope_mono_local hterm
  have hrelation := relationTransportLocalEnvelope_le_uniform
    left right closedTermCodeBound hleft hright hterm
  have hformula := atomicRelationFormulaEnvelope_le_uniform
    left right closedTermCodeBound hleft hright hterm
  have hcontext := smallContextAssemblyEnvelope_mono_local hformula
  unfold atomicTransportPayloadEnvelope
    uniformAtomicTransportPayloadEnvelope
  dsimp only [smallTermBound, largeTermBound] at hterm hunary hprimitive hrelation hformula hcontext
  dsimp only
  gcongr

theorem parameterEqualityContext_formulaCodeBound_atomicRelation
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat) :
    FormulaCodeBound (parameterEqualityContext left right)
      (atomicRelationFormulaEnvelope left right termBound) := by
  intro formula hformula
  exact (parameterEqualityContext_formulaCodeBound_transport
    left right termBound formula hformula).trans
      (unaryTransportFormulaEnvelope_le_atomicRelation
        left right termBound)

theorem binaryRelationImplication_code_le_orderDerived
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (binaryFormulaCode
      (binaryRelationFormula relationSymbol leftFirst leftSecond 🡒
        binaryRelationFormula relationSymbol
          rightFirst rightSecond)).length <=
      orderDerivedFormulaCodeEnvelope termBound := by
  have hleft := binaryRelationFormula_code_le_orderAtomic
    relationSymbol leftFirst leftSecond termBound hleftFirst hleftSecond
  have hright := binaryRelationFormula_code_le_orderAtomic
    relationSymbol rightFirst rightSecond termBound hrightFirst hrightSecond
  have hraw := binaryFormulaCode_implication_length_le
    (binaryRelationFormula relationSymbol leftFirst leftSecond)
    (binaryRelationFormula relationSymbol rightFirst rightSecond)
  have htag : (binaryNatCode 5).length <= 8 := by decide
  have hderivedLower :
      8 <= orderDerivedFormulaCodeEnvelope termBound := by
    unfold orderDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
    omega
  unfold orderDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
  omega

theorem binaryRelationImplication_code_le_atomicRelation
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (parameterLeft parameterRight :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (binaryFormulaCode
      (binaryRelationFormula relationSymbol leftFirst leftSecond 🡒
        binaryRelationFormula relationSymbol
          rightFirst rightSecond)).length <=
      atomicRelationFormulaEnvelope parameterLeft parameterRight termBound :=
  (binaryRelationImplication_code_le_orderDerived relationSymbol
    leftFirst leftSecond rightFirst rightSecond termBound
    hleftFirst hleftSecond hrightFirst hrightSecond).trans
    (orderDerivedFormulaCodeEnvelope_le_atomicRelation
      parameterLeft parameterRight termBound)

theorem binaryRelationNegatedImplication_code_le_atomicRelation
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (parameterLeft parameterRight :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    (binaryFormulaCode
      (∼(binaryRelationFormula relationSymbol leftFirst leftSecond 🡒
        binaryRelationFormula relationSymbol
          rightFirst rightSecond))).length <=
      atomicRelationFormulaEnvelope parameterLeft parameterRight termBound := by
  have himplication := binaryRelationImplication_code_le_orderDerived
    relationSymbol leftFirst leftSecond rightFirst rightSecond termBound
    hleftFirst hleftSecond hrightFirst hrightSecond
  have hraw := binaryFormulaCode_neg_length_le
    (binaryRelationFormula relationSymbol leftFirst leftSecond 🡒
      binaryRelationFormula relationSymbol rightFirst rightSecond)
  have hderivedLocal := orderDerived_le_local termBound
  have hlocalPrimitive := orderLocal_le_primitive termBound
  unfold atomicRelationFormulaEnvelope
  omega

theorem binaryRelationNegatedFormula_code_le_atomicRelation
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (first second : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (parameterLeft parameterRight :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hfirst : (binaryTermCode first).length <= termBound)
    (hsecond : (binaryTermCode second).length <= termBound) :
    (binaryFormulaCode
      (∼binaryRelationFormula relationSymbol first second)).length <=
      atomicRelationFormulaEnvelope parameterLeft parameterRight termBound := by
  have hatom := binaryRelationFormula_code_le_orderAtomic
    relationSymbol first second termBound hfirst hsecond
  have hraw := binaryFormulaCode_neg_length_le
    (binaryRelationFormula relationSymbol first second)
  have hatomicDerived := orderAtomic_le_derived termBound
  have hderivedLocal := orderDerived_le_local termBound
  have hlocalPrimitive := orderLocal_le_primitive termBound
  unfold atomicRelationFormulaEnvelope
  omega

theorem contextualEqualitySymmetryStructuralPayloadBound_le_uniform
    (leftTerm rightTerm parameterLeft parameterRight :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourcePayloadBound termBound : Nat)
    (hleftTerm : (binaryTermCode leftTerm).length <= termBound)
    (hrightTerm : (binaryTermCode rightTerm).length <= termBound) :
    contextualEqualitySymmetryStructuralPayloadBound
        (parameterEqualityContext parameterLeft parameterRight)
        leftTerm rightTerm sourcePayloadBound <=
      sourcePayloadBound + paPrimitiveCostEnvelope termBound +
        2 * smallContextAssemblyEnvelope
          (atomicRelationFormulaEnvelope
            parameterLeft parameterRight termBound) := by
  let Gamma := parameterEqualityContext parameterLeft parameterRight
  let formulaBound := atomicRelationFormulaEnvelope
    parameterLeft parameterRight termBound
  let antecedent :=
    (“!!leftTerm = !!rightTerm” :
      LO.FirstOrder.ArithmeticProposition)
  let consequent :=
    (“!!rightTerm = !!leftTerm” :
      LO.FirstOrder.ArithmeticProposition)
  let implication := antecedent 🡒 consequent
  have hcontext : FormulaCodeBound Gamma formulaBound := by
    simpa only [Gamma, formulaBound] using
      parameterEqualityContext_formulaCodeBound_atomicRelation
        parameterLeft parameterRight termBound
  have hcontextCard : Gamma.card <= 4 := by
    simpa only [Gamma] using parameterEqualityContext_card_le_transport
      parameterLeft parameterRight
  have hantecedentRaw := equalityFormula_code_le_orderAtomic
    leftTerm rightTerm termBound hleftTerm hrightTerm
  have hconsequentRaw := equalityFormula_code_le_orderAtomic
    rightTerm leftTerm termBound hrightTerm hleftTerm
  have hantecedent : (binaryFormulaCode antecedent).length <=
      formulaBound := hantecedentRaw.trans
    (orderAtomicFormulaCodeEnvelope_le_atomicRelation
      parameterLeft parameterRight termBound)
  have hconsequent : (binaryFormulaCode consequent).length <=
      formulaBound := hconsequentRaw.trans
    (orderAtomicFormulaCodeEnvelope_le_atomicRelation
      parameterLeft parameterRight termBound)
  have hconsequentTight : (binaryFormulaCode consequent).length <=
      orderAtomicFormulaCodeEnvelope termBound := by
    simpa only [consequent] using hconsequentRaw
  have himplicationRaw := binaryFormulaCode_implication_length_le
    antecedent consequent
  have htag : (binaryNatCode 5).length <= 8 := by decide
  have hatomicDerived := orderAtomic_le_derived termBound
  have hderivedLocal := orderDerived_le_local termBound
  have hlocalPrimitive := orderLocal_le_primitive termBound
  have hderivedLower :
      8 <= orderDerivedFormulaCodeEnvelope termBound := by
    unfold orderDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
    omega
  have himplicationTight : (binaryFormulaCode implication).length <=
      orderDerivedFormulaCodeEnvelope termBound := by
    dsimp only [implication, antecedent, consequent]
    dsimp only [antecedent, consequent] at himplicationRaw
    unfold orderDerivedFormulaCodeEnvelope paAssemblySyntaxEnvelope
    omega
  have himplication : (binaryFormulaCode implication).length <=
      formulaBound := by
    unfold formulaBound atomicRelationFormulaEnvelope
    omega
  have hnegatedImplicationRaw := binaryFormulaCode_neg_length_le implication
  have hnegatedConsequentRaw := binaryFormulaCode_neg_length_le consequent
  have hnegatedImplication :
      (binaryFormulaCode (∼implication)).length <= formulaBound := by
    unfold formulaBound atomicRelationFormulaEnvelope
    omega
  have hnegatedConsequent :
      (binaryFormulaCode (∼consequent)).length <= formulaBound := by
    unfold formulaBound atomicRelationFormulaEnvelope
    omega
  have himplicationPayload :=
    equalitySymmetryImplication_payloadLength_le_primitive
      leftTerm rightTerm termBound hleftTerm hrightTerm
  have himplicationContext := hcontext.insert himplication
  have himplicationCard : (insert implication Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le implication Gamma
    omega
  have hweakening := weakeningFullAssemblyCost_le_small
    (insert implication Gamma) formulaBound
    himplicationCard himplicationContext
  have hmp := contextualModusPonensFullAssemblyCost_le_small
    Gamma antecedent consequent formulaBound hcontextCard hcontext
    hantecedent hconsequent himplication
    hnegatedImplication hnegatedConsequent
  unfold contextualEqualitySymmetryStructuralPayloadBound
  dsimp only [Gamma, formulaBound, antecedent, consequent, implication] at *
  omega

theorem unaryTermEqualityUnderAssumptionStructuralPayloadBound_le_openCode
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (openTermCodeBound : Nat)
    (hterm : (binaryTermCode term).length <= openTermCodeBound) :
    unaryTermEqualityUnderAssumptionStructuralPayloadBound term left right <=
      openTermCodeBound *
        unaryTransportLocalEnvelope left right openTermCodeBound := by
  have hstructural :=
    unaryTermEqualityUnderAssumptionStructuralPayloadBound_le_symbolCount
      term left right openTermCodeBound hterm
  have hsymbols := (termSymbolCount_le_binaryTermCode_length term).trans hterm
  exact hstructural.trans (Nat.mul_le_mul_right _ hsymbols)

theorem positiveTransportUnderAssumptionStructuralPayloadBound_le_polynomial
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourcePayloadBound openTermCodeBound : Nat)
    (hfirstArgument :
      (binaryTermCode (arguments 0)).length <= openTermCodeBound)
    (hsecondArgument :
      (binaryTermCode (arguments 1)).length <= openTermCodeBound) :
    positiveTransportUnderAssumptionStructuralPayloadBound
        relationSymbol arguments left right sourcePayloadBound <=
      atomicTransportPayloadEnvelope
        left right openTermCodeBound sourcePayloadBound := by
  let Gamma := parameterEqualityContext left right
  let termBound := unaryTransportTermEnvelope
    left right openTermCodeBound
  let formulaBound := atomicRelationFormulaEnvelope left right termBound
  let leftFirst := instantiateUnaryTerm (arguments 0) left
  let leftSecond := instantiateUnaryTerm (arguments 1) left
  let rightFirst := instantiateUnaryTerm (arguments 0) right
  let rightSecond := instantiateUnaryTerm (arguments 1) right
  let sourceFormula := unaryRelationFormula relationSymbol arguments left
  let targetFormula := unaryRelationFormula relationSymbol arguments right
  have hleftFirst := instantiateUnaryTerm_left_code_length_le_envelope
    (arguments 0) left right openTermCodeBound hfirstArgument
  have hleftSecond := instantiateUnaryTerm_left_code_length_le_envelope
    (arguments 1) left right openTermCodeBound hsecondArgument
  have hrightFirst := instantiateUnaryTerm_right_code_length_le_envelope
    (arguments 0) left right openTermCodeBound hfirstArgument
  have hrightSecond := instantiateUnaryTerm_right_code_length_le_envelope
    (arguments 1) left right openTermCodeBound hsecondArgument
  change (binaryTermCode leftFirst).length <= termBound at hleftFirst
  change (binaryTermCode leftSecond).length <= termBound at hleftSecond
  change (binaryTermCode rightFirst).length <= termBound at hrightFirst
  change (binaryTermCode rightSecond).length <= termBound at hrightSecond
  have hfirstPayload :=
    unaryTermEqualityUnderAssumptionStructuralPayloadBound_le_openCode
      (arguments 0) left right openTermCodeBound hfirstArgument
  have hsecondPayload :=
    unaryTermEqualityUnderAssumptionStructuralPayloadBound_le_openCode
      (arguments 1) left right openTermCodeBound hsecondArgument
  have himplicationRaw :=
    relationTransportImplicationStructuralPayloadBound_le_uniform
      relationSymbol leftFirst leftSecond rightFirst rightSecond left right
      (unaryTermEqualityUnderAssumptionStructuralPayloadBound
        (arguments 0) left right)
      (unaryTermEqualityUnderAssumptionStructuralPayloadBound
        (arguments 1) left right)
      termBound hleftFirst hleftSecond hrightFirst hrightSecond
  have himplication :
      positiveTransportImplicationStructuralPayloadBound
          relationSymbol arguments left right <=
        2 * openTermCodeBound *
            unaryTransportLocalEnvelope left right openTermCodeBound +
          relationTransportLocalEnvelope left right termBound := by
    unfold positiveTransportImplicationStructuralPayloadBound
    dsimp only [leftFirst, leftSecond, rightFirst, rightSecond] at himplicationRaw
    calc
      relationTransportImplicationStructuralPayloadBound
            (parameterEqualityContext left right) relationSymbol
            (instantiateUnaryTerm (arguments 0) left)
            (instantiateUnaryTerm (arguments 1) left)
            (instantiateUnaryTerm (arguments 0) right)
            (instantiateUnaryTerm (arguments 1) right)
            (unaryTermEqualityUnderAssumptionStructuralPayloadBound
              (arguments 0) left right)
            (unaryTermEqualityUnderAssumptionStructuralPayloadBound
              (arguments 1) left right) <=
          unaryTermEqualityUnderAssumptionStructuralPayloadBound
              (arguments 0) left right +
            unaryTermEqualityUnderAssumptionStructuralPayloadBound
              (arguments 1) left right +
            relationTransportLocalEnvelope left right termBound :=
        himplicationRaw
      _ <= (openTermCodeBound *
              unaryTransportLocalEnvelope left right openTermCodeBound) +
            (openTermCodeBound *
              unaryTransportLocalEnvelope left right openTermCodeBound) +
            relationTransportLocalEnvelope left right termBound := by
        omega
      _ = 2 * openTermCodeBound *
              unaryTransportLocalEnvelope left right openTermCodeBound +
            relationTransportLocalEnvelope left right termBound := by
        ring
  have hsourceRaw := binaryRelationFormula_code_le_orderAtomic
    relationSymbol leftFirst leftSecond termBound hleftFirst hleftSecond
  have htargetRaw := binaryRelationFormula_code_le_orderAtomic
    relationSymbol rightFirst rightSecond termBound hrightFirst hrightSecond
  have hsource : (binaryFormulaCode sourceFormula).length <= formulaBound := by
    change (binaryFormulaCode
      (binaryRelationFormula relationSymbol leftFirst leftSecond)).length <= _
    exact hsourceRaw.trans
      (orderAtomicFormulaCodeEnvelope_le_atomicRelation
        left right termBound)
  have htarget : (binaryFormulaCode targetFormula).length <= formulaBound := by
    change (binaryFormulaCode
      (binaryRelationFormula relationSymbol rightFirst rightSecond)).length <= _
    exact htargetRaw.trans
      (orderAtomicFormulaCodeEnvelope_le_atomicRelation
        left right termBound)
  have hformulaImplication :
      (binaryFormulaCode (sourceFormula 🡒 targetFormula)).length <=
        formulaBound := by
    change (binaryFormulaCode
      (binaryRelationFormula relationSymbol leftFirst leftSecond 🡒
        binaryRelationFormula relationSymbol
          rightFirst rightSecond)).length <= _
    exact binaryRelationImplication_code_le_atomicRelation
      relationSymbol leftFirst leftSecond rightFirst rightSecond
      left right termBound
      hleftFirst hleftSecond hrightFirst hrightSecond
  have hnegatedImplication :
      (binaryFormulaCode (∼(sourceFormula 🡒 targetFormula))).length <=
        formulaBound := by
    change (binaryFormulaCode
      (∼(binaryRelationFormula relationSymbol leftFirst leftSecond 🡒
        binaryRelationFormula relationSymbol
          rightFirst rightSecond))).length <= _
    exact binaryRelationNegatedImplication_code_le_atomicRelation
      relationSymbol leftFirst leftSecond rightFirst rightSecond
      left right termBound
      hleftFirst hleftSecond hrightFirst hrightSecond
  have hnegatedTarget :
      (binaryFormulaCode (∼targetFormula)).length <= formulaBound := by
    change (binaryFormulaCode
      (∼binaryRelationFormula relationSymbol
        rightFirst rightSecond)).length <= _
    exact binaryRelationNegatedFormula_code_le_atomicRelation
      relationSymbol rightFirst rightSecond left right termBound
      hrightFirst hrightSecond
  have hcontext : FormulaCodeBound Gamma formulaBound := by
    simpa only [Gamma, formulaBound] using
      parameterEqualityContext_formulaCodeBound_atomicRelation
        left right termBound
  have hcontextCard : Gamma.card <= 4 := by
    simpa only [Gamma] using parameterEqualityContext_card_le_transport
      left right
  have hsourceContext := hcontext.insert hsource
  have hsourceCard : (insert sourceFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le sourceFormula Gamma
    omega
  have hweakening := weakeningFullAssemblyCost_le_small
    (insert sourceFormula Gamma) formulaBound hsourceCard hsourceContext
  have hmp := contextualModusPonensFullAssemblyCost_le_small
    Gamma sourceFormula targetFormula formulaBound hcontextCard hcontext
    hsource htarget hformulaImplication hnegatedImplication hnegatedTarget
  unfold positiveTransportUnderAssumptionStructuralPayloadBound
  dsimp only [Gamma, termBound, formulaBound, sourceFormula, targetFormula,
    leftFirst, leftSecond, rightFirst, rightSecond] at *
  unfold atomicTransportPayloadEnvelope
  dsimp only
  omega

theorem negativeTransportUnderAssumptionStructuralPayloadBound_le_polynomial
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourcePayloadBound openTermCodeBound : Nat)
    (hfirstArgument :
      (binaryTermCode (arguments 0)).length <= openTermCodeBound)
    (hsecondArgument :
      (binaryTermCode (arguments 1)).length <= openTermCodeBound) :
    negativeTransportUnderAssumptionStructuralPayloadBound
        relationSymbol arguments left right sourcePayloadBound <=
      atomicTransportPayloadEnvelope
        left right openTermCodeBound sourcePayloadBound := by
  let Gamma := parameterEqualityContext left right
  let termBound := unaryTransportTermEnvelope
    left right openTermCodeBound
  let formulaBound := atomicRelationFormulaEnvelope left right termBound
  let localTermCost :=
    openTermCodeBound *
      unaryTransportLocalEnvelope left right openTermCodeBound
  let localContextCost := smallContextAssemblyEnvelope formulaBound
  let leftFirst := instantiateUnaryTerm (arguments 0) left
  let leftSecond := instantiateUnaryTerm (arguments 1) left
  let rightFirst := instantiateUnaryTerm (arguments 0) right
  let rightSecond := instantiateUnaryTerm (arguments 1) right
  let leftAtom := unaryRelationFormula relationSymbol arguments left
  let rightAtom := unaryRelationFormula relationSymbol arguments right
  have hleftFirst := instantiateUnaryTerm_left_code_length_le_envelope
    (arguments 0) left right openTermCodeBound hfirstArgument
  have hleftSecond := instantiateUnaryTerm_left_code_length_le_envelope
    (arguments 1) left right openTermCodeBound hsecondArgument
  have hrightFirst := instantiateUnaryTerm_right_code_length_le_envelope
    (arguments 0) left right openTermCodeBound hfirstArgument
  have hrightSecond := instantiateUnaryTerm_right_code_length_le_envelope
    (arguments 1) left right openTermCodeBound hsecondArgument
  change (binaryTermCode leftFirst).length <= termBound at hleftFirst
  change (binaryTermCode leftSecond).length <= termBound at hleftSecond
  change (binaryTermCode rightFirst).length <= termBound at hrightFirst
  change (binaryTermCode rightSecond).length <= termBound at hrightSecond
  have hfirstForward :=
    unaryTermEqualityUnderAssumptionStructuralPayloadBound_le_openCode
      (arguments 0) left right openTermCodeBound hfirstArgument
  have hsecondForward :=
    unaryTermEqualityUnderAssumptionStructuralPayloadBound_le_openCode
      (arguments 1) left right openTermCodeBound hsecondArgument
  have hfirstReverseRaw :=
    contextualEqualitySymmetryStructuralPayloadBound_le_uniform
      leftFirst rightFirst left right
      (unaryTermEqualityUnderAssumptionStructuralPayloadBound
        (arguments 0) left right)
      termBound hleftFirst hrightFirst
  have hsecondReverseRaw :=
    contextualEqualitySymmetryStructuralPayloadBound_le_uniform
      leftSecond rightSecond left right
      (unaryTermEqualityUnderAssumptionStructuralPayloadBound
        (arguments 1) left right)
      termBound hleftSecond hrightSecond
  have hfirstReverse :
      contextualEqualitySymmetryStructuralPayloadBound Gamma
          leftFirst rightFirst
          (unaryTermEqualityUnderAssumptionStructuralPayloadBound
            (arguments 0) left right) <=
        localTermCost + paPrimitiveCostEnvelope termBound +
          2 * localContextCost := by
    dsimp only [Gamma, localTermCost, localContextCost, formulaBound]
      at hfirstReverseRaw ⊢
    omega
  have hsecondReverse :
      contextualEqualitySymmetryStructuralPayloadBound Gamma
          leftSecond rightSecond
          (unaryTermEqualityUnderAssumptionStructuralPayloadBound
            (arguments 1) left right) <=
        localTermCost + paPrimitiveCostEnvelope termBound +
          2 * localContextCost := by
    dsimp only [Gamma, localTermCost, localContextCost, formulaBound]
      at hsecondReverseRaw ⊢
    omega
  have hreverseImplicationRaw :=
    relationTransportImplicationStructuralPayloadBound_le_uniform
      relationSymbol rightFirst rightSecond leftFirst leftSecond left right
      (contextualEqualitySymmetryStructuralPayloadBound Gamma
        leftFirst rightFirst
        (unaryTermEqualityUnderAssumptionStructuralPayloadBound
          (arguments 0) left right))
      (contextualEqualitySymmetryStructuralPayloadBound Gamma
        leftSecond rightSecond
        (unaryTermEqualityUnderAssumptionStructuralPayloadBound
          (arguments 1) left right))
      termBound hrightFirst hrightSecond hleftFirst hleftSecond
  have hreverseImplication :
      relationTransportImplicationStructuralPayloadBound Gamma relationSymbol
          rightFirst rightSecond leftFirst leftSecond
          (contextualEqualitySymmetryStructuralPayloadBound Gamma
            leftFirst rightFirst
            (unaryTermEqualityUnderAssumptionStructuralPayloadBound
              (arguments 0) left right))
          (contextualEqualitySymmetryStructuralPayloadBound Gamma
            leftSecond rightSecond
            (unaryTermEqualityUnderAssumptionStructuralPayloadBound
              (arguments 1) left right)) <=
        2 * localTermCost + 2 * paPrimitiveCostEnvelope termBound +
          relationTransportLocalEnvelope left right termBound +
          4 * localContextCost := by
    calc
      relationTransportImplicationStructuralPayloadBound Gamma relationSymbol
            rightFirst rightSecond leftFirst leftSecond
            (contextualEqualitySymmetryStructuralPayloadBound Gamma
              leftFirst rightFirst
              (unaryTermEqualityUnderAssumptionStructuralPayloadBound
                (arguments 0) left right))
            (contextualEqualitySymmetryStructuralPayloadBound Gamma
              leftSecond rightSecond
              (unaryTermEqualityUnderAssumptionStructuralPayloadBound
                (arguments 1) left right)) <=
          contextualEqualitySymmetryStructuralPayloadBound Gamma
              leftFirst rightFirst
              (unaryTermEqualityUnderAssumptionStructuralPayloadBound
                (arguments 0) left right) +
            contextualEqualitySymmetryStructuralPayloadBound Gamma
              leftSecond rightSecond
              (unaryTermEqualityUnderAssumptionStructuralPayloadBound
                (arguments 1) left right) +
            relationTransportLocalEnvelope left right termBound :=
        hreverseImplicationRaw
      _ <= (localTermCost + paPrimitiveCostEnvelope termBound +
              2 * localContextCost) +
            (localTermCost + paPrimitiveCostEnvelope termBound +
              2 * localContextCost) +
            relationTransportLocalEnvelope left right termBound := by
        omega
      _ = 2 * localTermCost + 2 * paPrimitiveCostEnvelope termBound +
            relationTransportLocalEnvelope left right termBound +
            4 * localContextCost := by
        ring
  have hleftAtomRaw := binaryRelationFormula_code_le_orderAtomic
    relationSymbol leftFirst leftSecond termBound hleftFirst hleftSecond
  have hrightAtomRaw := binaryRelationFormula_code_le_orderAtomic
    relationSymbol rightFirst rightSecond termBound hrightFirst hrightSecond
  have hleftAtom : (binaryFormulaCode leftAtom).length <= formulaBound := by
    change (binaryFormulaCode
      (binaryRelationFormula relationSymbol leftFirst leftSecond)).length <= _
    exact hleftAtomRaw.trans
      (orderAtomicFormulaCodeEnvelope_le_atomicRelation
        left right termBound)
  have hrightAtom : (binaryFormulaCode rightAtom).length <= formulaBound := by
    change (binaryFormulaCode
      (binaryRelationFormula relationSymbol rightFirst rightSecond)).length <= _
    exact hrightAtomRaw.trans
      (orderAtomicFormulaCodeEnvelope_le_atomicRelation
        left right termBound)
  have himplication :
      (binaryFormulaCode (rightAtom 🡒 leftAtom)).length <=
        formulaBound := by
    change (binaryFormulaCode
      (binaryRelationFormula relationSymbol rightFirst rightSecond 🡒
        binaryRelationFormula relationSymbol
          leftFirst leftSecond)).length <= _
    exact binaryRelationImplication_code_le_atomicRelation
      relationSymbol rightFirst rightSecond leftFirst leftSecond
      left right termBound
      hrightFirst hrightSecond hleftFirst hleftSecond
  have hnegatedImplication :
      (binaryFormulaCode (∼(rightAtom 🡒 leftAtom))).length <=
        formulaBound := by
    change (binaryFormulaCode
      (∼(binaryRelationFormula relationSymbol rightFirst rightSecond 🡒
        binaryRelationFormula relationSymbol
          leftFirst leftSecond))).length <= _
    exact binaryRelationNegatedImplication_code_le_atomicRelation
      relationSymbol rightFirst rightSecond leftFirst leftSecond
      left right termBound
      hrightFirst hrightSecond hleftFirst hleftSecond
  have hnegatedLeftAtom :
      (binaryFormulaCode (∼leftAtom)).length <= formulaBound := by
    change (binaryFormulaCode
      (∼binaryRelationFormula relationSymbol
        leftFirst leftSecond)).length <= _
    exact binaryRelationNegatedFormula_code_le_atomicRelation
      relationSymbol leftFirst leftSecond left right termBound
      hleftFirst hleftSecond
  have hnegatedRightAtom :
      (binaryFormulaCode (∼rightAtom)).length <= formulaBound := by
    change (binaryFormulaCode
      (∼binaryRelationFormula relationSymbol
        rightFirst rightSecond)).length <= _
    exact binaryRelationNegatedFormula_code_le_atomicRelation
      relationSymbol rightFirst rightSecond left right termBound
      hrightFirst hrightSecond
  have hcontext : FormulaCodeBound Gamma formulaBound := by
    simpa only [Gamma, formulaBound] using
      parameterEqualityContext_formulaCodeBound_atomicRelation
        left right termBound
  have hcontextCard : Gamma.card <= 4 := by
    simpa only [Gamma] using parameterEqualityContext_card_le_transport
      left right
  have hsourceContext := hcontext.insert hnegatedLeftAtom
  have hsourceCard : (insert (∼leftAtom) Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le (∼leftAtom) Gamma
    omega
  have hweakening := weakeningFullAssemblyCost_le_small
    (insert (∼leftAtom) Gamma) formulaBound hsourceCard hsourceContext
  have hmodusTollens := modusTollensFullAssemblyCost_le_small
    Gamma rightAtom leftAtom formulaBound hcontextCard hcontext
    hrightAtom hleftAtom himplication hnegatedImplication
    hnegatedRightAtom hnegatedLeftAtom
  have htermCostIdentity :
      2 * openTermCodeBound *
          unaryTransportLocalEnvelope left right openTermCodeBound =
        2 * localTermCost := by
    dsimp only [localTermCost]
    ring
  unfold negativeTransportUnderAssumptionStructuralPayloadBound
  dsimp only [Gamma, termBound, formulaBound, localTermCost,
    localContextCost, leftFirst, leftSecond, rightFirst, rightSecond,
    leftAtom, rightAtom] at *
  unfold atomicTransportPayloadEnvelope
  dsimp only
  omega

#print axioms binaryFunctionExtImplication_payloadLength_le_primitive
#print axioms binaryFunctionNodeLocalOverhead_le_uniform
#print axioms unaryTermEqualityUnderAssumptionStructuralPayloadBound_add_eq
#print axioms unaryTermEqualityUnderAssumptionStructuralPayloadBound_mul_eq
#print axioms reflexivityNodeLocalOverhead_le_uniform
#print axioms assumptionNodeLocalOverhead_le_uniform
#print axioms unaryTermEqualityUnderAssumptionStructuralPayloadBound_le_polynomial
#print axioms compileUnaryTermEqualityUnderAssumption_payloadLength_le_polynomial
#print axioms binaryRelationExtOuterBody_code_le_relationStage0
#print axioms binaryRelationExtImplication_payloadLength_le_relationEnvelope
#print axioms relationTransportImplicationStructuralPayloadBound_le_uniform
#print axioms positiveTransportUnderAssumptionStructuralPayloadBound_le_polynomial
#print axioms negativeTransportUnderAssumptionStructuralPayloadBound_le_polynomial
#print axioms atomicTransportPayloadEnvelope_le_uniform

end FoundationCompactPAUnaryAtomicTransportPolynomialBounds
