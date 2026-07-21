import integration.FoundationCompactPAValuationTermCompilerBounds
import integration.FoundationCompactPAUnaryAtomicTransportPolynomialBounds

/-!
# Public recursive bounds for valuation-term compilation

The existing structural resource follows the real compiler but still uses the
exact short-to-unary bridge resource at free-variable leaves.  Here that leaf
is replaced by its proved public polynomial and the replacement is propagated
through the complete normalization recursion.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPAValuationTermCompilerPublicBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeEqualityTransitivity
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABinaryNumeralMultiplicationBounds
open FoundationCompactPACertifiedContextEquality
open FoundationCompactPAQuantitativeFunctionCongruence
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerBounds

/-! ## Transparent context and congruence resources -/

def formulaCodeSum (Gamma : Finset ValuationFormula) : Nat :=
  Gamma.sum fun formula => (binaryFormulaCode formula).length

theorem formulaCode_le_formulaCodeSum
    {Gamma : Finset ValuationFormula} {formula : ValuationFormula}
    (hformula : formula ∈ Gamma) :
    (binaryFormulaCode formula).length <= formulaCodeSum Gamma := by
  unfold formulaCodeSum
  exact Finset.single_le_sum
    (fun candidate _ => Nat.zero_le (binaryFormulaCode candidate).length)
    hformula

theorem valuationContext_card_le_four_of_subset_singleton
    (vars : Finset Nat) (valuation : Nat -> Nat)
    (hvars : vars ⊆ {0}) :
    (valuationContext vars valuation).card <= 4 := by
  have hcard : vars.card <= 4 := by
    have hsubset := Finset.card_le_card hvars
    simp only [Finset.card_singleton] at hsubset
    omega
  have himage : (valuationContext vars valuation).card <= vars.card := by
    unfold valuationContext
    exact Finset.card_image_le
  exact himage.trans hcard

theorem valuationContext_card_le_four_of_card_le_four
    (vars : Finset Nat) (valuation : Nat -> Nat)
    (hvars : vars.card <= 4) :
    (valuationContext vars valuation).card <= 4 := by
  have himage : (valuationContext vars valuation).card <= vars.card := by
    unfold valuationContext
    exact Finset.card_image_le
  exact himage.trans hvars

/-! ## Uniform code bound for valuation contexts -/

/-- Formula-code envelope for one valuation assumption when both its unary
value term and its free-variable term have public bounds. -/
def valuationEqualityAssumptionFormulaCodeEnvelope
    (numericBound variableTermCodeBound : Nat) : Nat :=
  2 *
    (FoundationCompactPAFiniteExhaustionPolynomialBounds.iteratedSuccessorTermCodePolynomial
        0 numericBound +
      variableTermCodeBound +
      FoundationCompactPAFiniteExhaustionPolynomialBounds.finiteCaseEqualityFormulaCodeOverhead)

theorem valuationEqualityAssumption_code_le_uniform
    (valuation : Nat -> Nat) (index numericBound variableTermCodeBound : Nat)
    (hvalue : valuation index <= numericBound)
    (hvariable :
      (binaryTermCode (&index : ValuationTerm)).length <=
        variableTermCodeBound) :
    (binaryFormulaCode (valuationEqualityAssumption valuation index)).length <=
      valuationEqualityAssumptionFormulaCodeEnvelope numericBound
        variableTermCodeBound := by
  let valueTerm := iteratedSuccessorTerm 0 (valuation index)
  let variableTerm := (&index : ValuationTerm)
  let equalityFormula := finiteCaseEqualityFormula valueTerm variableTerm
  have hvalueRaw :=
    FoundationCompactPAFiniteExhaustionPolynomialBounds.iteratedSuccessorTerm_code_length_le_polynomial
      0 (valuation index)
  have hvalueMono :=
    FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds.iteratedSuccessorTermCodePolynomial_mono
      0 hvalue
  have hvalueCode : (binaryTermCode valueTerm).length <=
      FoundationCompactPAFiniteExhaustionPolynomialBounds.iteratedSuccessorTermCodePolynomial
        0 numericBound := by
    exact hvalueRaw.trans hvalueMono
  have hequality :=
    FoundationCompactPAFiniteExhaustionPolynomialBounds.finiteCaseEqualityFormula_code_length_le
      valueTerm variableTerm
  have hnegation :=
    FoundationCompactSyntaxTransformationCodeBounds.binaryFormulaCode_neg_length_le
      equalityFormula
  unfold valuationEqualityAssumption
    valuationEqualityAssumptionFormulaCodeEnvelope
  dsimp only [valueTerm, variableTerm, equalityFormula] at *
  omega

/-- A fixed-cardinality sum envelope for an entire valuation context. -/
def valuationContextFormulaCodeSumEnvelope
    (cardBound numericBound variableTermCodeBound : Nat) : Nat :=
  cardBound *
    valuationEqualityAssumptionFormulaCodeEnvelope numericBound
      variableTermCodeBound

theorem valuationContext_formulaCodeSum_le_uniform
    (vars : Finset Nat) (valuation : Nat -> Nat)
    (cardBound numericBound variableTermCodeBound : Nat)
    (hcard : vars.card <= cardBound)
    (hvalues : forall index, index ∈ vars -> valuation index <= numericBound)
    (hvariables : forall index, index ∈ vars ->
      (binaryTermCode (&index : ValuationTerm)).length <=
        variableTermCodeBound) :
    formulaCodeSum (valuationContext vars valuation) <=
      valuationContextFormulaCodeSumEnvelope cardBound numericBound
        variableTermCodeBound := by
  have hcontextCard : (valuationContext vars valuation).card <= cardBound := by
    have himage : (valuationContext vars valuation).card <= vars.card := by
      unfold valuationContext
      exact Finset.card_image_le
    exact himage.trans hcard
  have hformula : forall formula, formula ∈ valuationContext vars valuation ->
      (binaryFormulaCode formula).length <=
        valuationEqualityAssumptionFormulaCodeEnvelope numericBound
          variableTermCodeBound := by
    intro formula hformula
    rcases Finset.mem_image.mp hformula with ⟨index, hindex, rfl⟩
    exact valuationEqualityAssumption_code_le_uniform valuation index
      numericBound variableTermCodeBound (hvalues index hindex)
      (hvariables index hindex)
  have hsum :
      (valuationContext vars valuation).sum
          (fun formula => (binaryFormulaCode formula).length) <=
        (valuationContext vars valuation).card *
          valuationEqualityAssumptionFormulaCodeEnvelope numericBound
            variableTermCodeBound := by
    simpa [nsmul_eq_mul] using
      (valuationContext vars valuation).sum_le_card_nsmul
        (fun formula => (binaryFormulaCode formula).length)
        (valuationEqualityAssumptionFormulaCodeEnvelope numericBound
          variableTermCodeBound) hformula
  unfold formulaCodeSum valuationContextFormulaCodeSumEnvelope
  exact hsum.trans (Nat.mul_le_mul_right _ hcontextCard)

def contextFormulaResource
    (Gamma : Finset ValuationFormula) (formula : ValuationFormula) : Nat :=
  formulaCodeSum Gamma + (binaryFormulaCode formula).length + 1

theorem contextFormulaResource_context
    (Gamma : Finset ValuationFormula) (formula : ValuationFormula) :
    FormulaCodeBound Gamma (contextFormulaResource Gamma formula) := by
  intro candidate hcandidate
  have hsum := formulaCode_le_formulaCodeSum hcandidate
  unfold contextFormulaResource
  omega

theorem contextFormulaResource_formula
    (Gamma : Finset ValuationFormula) (formula : ValuationFormula) :
    (binaryFormulaCode formula).length <=
      contextFormulaResource Gamma formula := by
  unfold contextFormulaResource
  omega

def contextualBinaryFunctionCongruenceTermResource
    (leftFirst leftSecond rightFirst rightSecond : ValuationTerm) : Nat :=
  (binaryTermCode leftFirst).length +
    (binaryTermCode leftSecond).length +
    (binaryTermCode rightFirst).length +
    (binaryTermCode rightSecond).length + 1

def contextualBinaryFunctionCongruenceFormulaResource
    (Gamma : Finset ValuationFormula)
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond : ValuationTerm) : Nat :=
  let firstFormula :=
    (“!!leftFirst = !!rightFirst” : ValuationFormula)
  let secondFormula :=
    (“!!leftSecond = !!rightSecond” : ValuationFormula)
  let truthFormula := (⊤ : ValuationFormula)
  let innerFormula := secondFormula ⋏ truthFormula
  let antecedentFormula := binaryFunctionCongruenceAntecedent
    leftFirst leftSecond rightFirst rightSecond
  let conclusionFormula := binaryFunctionCongruenceConclusion functionSymbol
    leftFirst leftSecond rightFirst rightSecond
  let implicationFormula := antecedentFormula 🡒 conclusionFormula
  formulaCodeSum Gamma +
    (binaryFormulaCode firstFormula).length +
    (binaryFormulaCode secondFormula).length +
    (binaryFormulaCode truthFormula).length +
    (binaryFormulaCode innerFormula).length +
    (binaryFormulaCode antecedentFormula).length +
    (binaryFormulaCode conclusionFormula).length +
    (binaryFormulaCode implicationFormula).length +
    (binaryFormulaCode (∼implicationFormula)).length +
    (binaryFormulaCode (∼conclusionFormula)).length + 1

theorem contextualBinaryFunctionCongruenceFormulaResource_context
    (Gamma : Finset ValuationFormula)
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond : ValuationTerm) :
    FormulaCodeBound Gamma
      (contextualBinaryFunctionCongruenceFormulaResource Gamma
        functionSymbol leftFirst leftSecond rightFirst rightSecond) := by
  intro formula hformula
  have hsum := formulaCode_le_formulaCodeSum hformula
  unfold contextualBinaryFunctionCongruenceFormulaResource
  dsimp only
  omega

theorem contextualBinaryFunctionCongruenceFormulaResource_first
    (Gamma : Finset ValuationFormula)
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond : ValuationTerm) :
    (binaryFormulaCode
      (“!!leftFirst = !!rightFirst” : ValuationFormula)).length <=
      contextualBinaryFunctionCongruenceFormulaResource Gamma
        functionSymbol leftFirst leftSecond rightFirst rightSecond := by
  unfold contextualBinaryFunctionCongruenceFormulaResource
  dsimp only
  omega

theorem contextualBinaryFunctionCongruenceFormulaResource_second
    (Gamma : Finset ValuationFormula)
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond : ValuationTerm) :
    (binaryFormulaCode
      (“!!leftSecond = !!rightSecond” : ValuationFormula)).length <=
      contextualBinaryFunctionCongruenceFormulaResource Gamma
        functionSymbol leftFirst leftSecond rightFirst rightSecond := by
  unfold contextualBinaryFunctionCongruenceFormulaResource
  dsimp only
  omega

def contextualBinaryFunctionCongruenceLocalEnvelope
    (Gamma : Finset ValuationFormula)
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond : ValuationTerm) : Nat :=
  2 * paPrimitiveCostEnvelope
      (contextualBinaryFunctionCongruenceTermResource
        leftFirst leftSecond rightFirst rightSecond) +
    5 * smallContextAssemblyEnvelope
      (contextualBinaryFunctionCongruenceFormulaResource Gamma
        functionSymbol leftFirst leftSecond rightFirst rightSecond)

theorem contextualBinaryFunctionCongruenceStructuralPayloadBound_le_public
    (Gamma : Finset ValuationFormula)
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond : ValuationTerm)
    (firstPayloadLength secondPayloadLength : Nat)
    (hfunction : functionSymbol = Language.Add.add ∨
      functionSymbol = Language.Mul.mul)
    (hcard : Gamma.card <= 4) :
    contextualBinaryFunctionCongruenceStructuralPayloadBound Gamma
        functionSymbol leftFirst leftSecond rightFirst rightSecond
        firstPayloadLength secondPayloadLength <=
      firstPayloadLength + secondPayloadLength +
        contextualBinaryFunctionCongruenceLocalEnvelope Gamma
          functionSymbol leftFirst leftSecond rightFirst rightSecond := by
  let termResource := contextualBinaryFunctionCongruenceTermResource
    leftFirst leftSecond rightFirst rightSecond
  let formulaResource := contextualBinaryFunctionCongruenceFormulaResource
    Gamma functionSymbol leftFirst leftSecond rightFirst rightSecond
  let firstFormula :=
    (“!!leftFirst = !!rightFirst” : ValuationFormula)
  let secondFormula :=
    (“!!leftSecond = !!rightSecond” : ValuationFormula)
  let truthFormula := (⊤ : ValuationFormula)
  let innerFormula := secondFormula ⋏ truthFormula
  let antecedentFormula := binaryFunctionCongruenceAntecedent
    leftFirst leftSecond rightFirst rightSecond
  let conclusionFormula := binaryFunctionCongruenceConclusion functionSymbol
    leftFirst leftSecond rightFirst rightSecond
  let implicationFormula := antecedentFormula 🡒 conclusionFormula
  have hleftFirst : (binaryTermCode leftFirst).length <= termResource := by
    unfold termResource contextualBinaryFunctionCongruenceTermResource
    omega
  have hleftSecond : (binaryTermCode leftSecond).length <= termResource := by
    unfold termResource contextualBinaryFunctionCongruenceTermResource
    omega
  have hrightFirst : (binaryTermCode rightFirst).length <= termResource := by
    unfold termResource contextualBinaryFunctionCongruenceTermResource
    omega
  have hrightSecond : (binaryTermCode rightSecond).length <= termResource := by
    unfold termResource contextualBinaryFunctionCongruenceTermResource
    omega
  have hcontext : FormulaCodeBound Gamma formulaResource := by
    simpa only [formulaResource] using
      contextualBinaryFunctionCongruenceFormulaResource_context Gamma
        functionSymbol leftFirst leftSecond rightFirst rightSecond
  have hfirstFormula : (binaryFormulaCode firstFormula).length <=
      formulaResource := by
    simpa only [formulaResource, firstFormula] using
      contextualBinaryFunctionCongruenceFormulaResource_first Gamma
        functionSymbol leftFirst leftSecond rightFirst rightSecond
  have hsecondFormula : (binaryFormulaCode secondFormula).length <=
      formulaResource := by
    simpa only [formulaResource, secondFormula] using
      contextualBinaryFunctionCongruenceFormulaResource_second Gamma
        functionSymbol leftFirst leftSecond rightFirst rightSecond
  have htruthFormula : (binaryFormulaCode truthFormula).length <=
      formulaResource := by
    unfold formulaResource
      contextualBinaryFunctionCongruenceFormulaResource
    dsimp only [truthFormula]
    omega
  have hinnerFormula : (binaryFormulaCode innerFormula).length <=
      formulaResource := by
    unfold formulaResource
      contextualBinaryFunctionCongruenceFormulaResource
    dsimp only [secondFormula, truthFormula, innerFormula]
    omega
  have hantecedentFormula :
      (binaryFormulaCode antecedentFormula).length <= formulaResource := by
    unfold formulaResource
      contextualBinaryFunctionCongruenceFormulaResource
    dsimp only [antecedentFormula]
    omega
  have hconclusionFormula :
      (binaryFormulaCode conclusionFormula).length <= formulaResource := by
    unfold formulaResource
      contextualBinaryFunctionCongruenceFormulaResource
    dsimp only [conclusionFormula]
    omega
  have himplicationFormula :
      (binaryFormulaCode implicationFormula).length <= formulaResource := by
    unfold formulaResource
      contextualBinaryFunctionCongruenceFormulaResource
    dsimp only [antecedentFormula, conclusionFormula, implicationFormula]
    omega
  have hnegatedImplicationFormula :
      (binaryFormulaCode (∼implicationFormula)).length <=
        formulaResource := by
    unfold formulaResource
      contextualBinaryFunctionCongruenceFormulaResource
    dsimp only [antecedentFormula, conclusionFormula, implicationFormula]
    omega
  have hnegatedConclusionFormula :
      (binaryFormulaCode (∼conclusionFormula)).length <=
        formulaResource := by
    unfold formulaResource
      contextualBinaryFunctionCongruenceFormulaResource
    dsimp only [conclusionFormula]
    omega
  have htruthContext : FormulaCodeBound (insert truthFormula Gamma)
      formulaResource := hcontext.insert htruthFormula
  have himplicationContext :
      FormulaCodeBound (insert implicationFormula Gamma) formulaResource :=
    hcontext.insert himplicationFormula
  have htruthCard : (insert truthFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le truthFormula Gamma
    omega
  have himplicationCard : (insert implicationFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le implicationFormula Gamma
    omega
  have hverumFixed := verumProof_payloadLength_le_fixed
  have hverum : CertifiedPAProof.verumProof.payloadLength <=
      paPrimitiveCostEnvelope termResource := by
    unfold paPrimitiveCostEnvelope
    omega
  have himplicationProof :=
    binaryFunctionExtImplication_payloadLength_le_primitive
      functionSymbol leftFirst leftSecond rightFirst rightSecond
      termResource hfunction hleftFirst hleftSecond hrightFirst hrightSecond
  have htruthWeakening := weakeningFullAssemblyCost_le_small
    (insert truthFormula Gamma) formulaResource htruthCard htruthContext
  have himplicationWeakening := weakeningFullAssemblyCost_le_small
    (insert implicationFormula Gamma) formulaResource himplicationCard
      himplicationContext
  have hinnerConjunction := conjunctionFullAssemblyCost_le_small
    Gamma secondFormula truthFormula formulaResource hcard hcontext
      hsecondFormula htruthFormula hinnerFormula
  have hantecedentConjunction := conjunctionFullAssemblyCost_le_small
    Gamma firstFormula innerFormula formulaResource hcard hcontext
      hfirstFormula hinnerFormula hantecedentFormula
  have hmp := contextualModusPonensFullAssemblyCost_le_small
    Gamma antecedentFormula conclusionFormula formulaResource
      hcard hcontext hantecedentFormula hconclusionFormula
      himplicationFormula hnegatedImplicationFormula
      hnegatedConclusionFormula
  simp only [contextualBinaryFunctionCongruenceStructuralPayloadBound,
    contextualBinaryFunctionCongruenceLocalEnvelope]
  dsimp only [termResource, formulaResource, firstFormula, secondFormula,
    truthFormula, innerFormula, antecedentFormula, conclusionFormula,
    implicationFormula] at *
  omega

/-! ## Public recursion for instantiated-term transport -/

def instantiatedTermTransportNodePayloadResource
    (valuation : Nat -> Nat)
    (term : ValuationTerm)
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm) : Nat :=
  let Gamma := valuationContext term.freeVariables valuation
  let leftFirst := instantiateTerm valuation (args 0)
  let leftSecond := instantiateTerm valuation (args 1)
  let rightFirst := args 0
  let rightSecond := args 1
  let leftFormula :=
    (“!!leftFirst = !!rightFirst” : ValuationFormula)
  let rightFormula :=
    (“!!leftSecond = !!rightSecond” : ValuationFormula)
  let leftBound :=
    instantiatedTermTransportPayloadResource valuation (args 0) +
      weakeningFullAssemblyCost (insert leftFormula Gamma)
  let rightBound :=
    instantiatedTermTransportPayloadResource valuation (args 1) +
      weakeningFullAssemblyCost (insert rightFormula Gamma)
  contextualBinaryFunctionCongruenceStructuralPayloadBound Gamma
    functionSymbol leftFirst leftSecond rightFirst rightSecond
    leftBound rightBound

def instantiatedTermTransportNodePayloadPolynomial
    (valuation : Nat -> Nat)
    (term : ValuationTerm)
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm)
    (leftPayloadBound rightPayloadBound : Nat) : Nat :=
  let Gamma := valuationContext term.freeVariables valuation
  let leftFirst := instantiateTerm valuation (args 0)
  let leftSecond := instantiateTerm valuation (args 1)
  let rightFirst := args 0
  let rightSecond := args 1
  let formulaResource :=
    contextualBinaryFunctionCongruenceFormulaResource Gamma functionSymbol
      leftFirst leftSecond rightFirst rightSecond
  leftPayloadBound + rightPayloadBound +
    2 * smallContextAssemblyEnvelope formulaResource +
    contextualBinaryFunctionCongruenceLocalEnvelope Gamma functionSymbol
      leftFirst leftSecond rightFirst rightSecond

def instantiatedTermTransportPayloadPolynomial
    (valuation : Nat -> Nat) : ValuationTerm -> Nat
  | #index => Fin.elim0 index
  | &index =>
      let Gamma := valuationContext ({index} : Finset Nat) valuation
      let formula :=
        (“!!(iteratedSuccessorTerm 0 (valuation index)) =
          !!(&index : ValuationTerm)” : ValuationFormula)
      smallContextAssemblyEnvelope (contextFormulaResource Gamma formula)
  | .func .zero args =>
      let term := (.func .zero args : ValuationTerm)
      let Gamma := valuationContext term.freeVariables valuation
      let formula :=
        (“!!(instantiateTerm valuation term) = !!term” : ValuationFormula)
      paPrimitiveCostEnvelope (binaryTermCode term).length +
        smallContextAssemblyEnvelope (contextFormulaResource Gamma formula)
  | .func .one args =>
      let term := (.func .one args : ValuationTerm)
      let Gamma := valuationContext term.freeVariables valuation
      let formula :=
        (“!!(instantiateTerm valuation term) = !!term” : ValuationFormula)
      paPrimitiveCostEnvelope (binaryTermCode term).length +
        smallContextAssemblyEnvelope (contextFormulaResource Gamma formula)
  | .func .add args =>
      instantiatedTermTransportNodePayloadPolynomial valuation
        (.func .add args : ValuationTerm) Language.Add.add args
        (instantiatedTermTransportPayloadPolynomial valuation (args 0))
        (instantiatedTermTransportPayloadPolynomial valuation (args 1))
  | .func .mul args =>
      instantiatedTermTransportNodePayloadPolynomial valuation
        (.func .mul args : ValuationTerm) Language.Mul.mul args
        (instantiatedTermTransportPayloadPolynomial valuation (args 0))
        (instantiatedTermTransportPayloadPolynomial valuation (args 1))

theorem instantiatedTermTransportNodePayloadResource_le_public
    (valuation : Nat -> Nat)
    (term : ValuationTerm)
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm)
    (leftPublicBound rightPublicBound : Nat)
    (hfunction : functionSymbol = Language.Add.add ∨
      functionSymbol = Language.Mul.mul)
    (hvars : term.freeVariables.card <= 4)
    (hleft : instantiatedTermTransportPayloadResource valuation (args 0) <=
      leftPublicBound)
    (hright : instantiatedTermTransportPayloadResource valuation (args 1) <=
      rightPublicBound) :
    instantiatedTermTransportNodePayloadResource valuation term
        functionSymbol args <=
      instantiatedTermTransportNodePayloadPolynomial valuation
        term functionSymbol args leftPublicBound rightPublicBound := by
  let Gamma := valuationContext term.freeVariables valuation
  let leftFirst := instantiateTerm valuation (args 0)
  let leftSecond := instantiateTerm valuation (args 1)
  let rightFirst := args 0
  let rightSecond := args 1
  let leftFormula :=
    (“!!leftFirst = !!rightFirst” : ValuationFormula)
  let rightFormula :=
    (“!!leftSecond = !!rightSecond” : ValuationFormula)
  let leftBound :=
    instantiatedTermTransportPayloadResource valuation (args 0) +
      weakeningFullAssemblyCost (insert leftFormula Gamma)
  let rightBound :=
    instantiatedTermTransportPayloadResource valuation (args 1) +
      weakeningFullAssemblyCost (insert rightFormula Gamma)
  let formulaResource :=
    contextualBinaryFunctionCongruenceFormulaResource Gamma functionSymbol
      leftFirst leftSecond rightFirst rightSecond
  have hcard : Gamma.card <= 4 := by
    exact valuationContext_card_le_four_of_card_le_four
      term.freeVariables valuation hvars
  have hcontext : FormulaCodeBound Gamma formulaResource := by
    simpa only [formulaResource] using
      contextualBinaryFunctionCongruenceFormulaResource_context Gamma
        functionSymbol leftFirst leftSecond rightFirst rightSecond
  have hleftFormula : (binaryFormulaCode leftFormula).length <=
      formulaResource := by
    simpa only [formulaResource, leftFormula, leftFirst, rightFirst] using
      contextualBinaryFunctionCongruenceFormulaResource_first Gamma
        functionSymbol leftFirst leftSecond rightFirst rightSecond
  have hrightFormula : (binaryFormulaCode rightFormula).length <=
      formulaResource := by
    simpa only [formulaResource, rightFormula, leftSecond, rightSecond] using
      contextualBinaryFunctionCongruenceFormulaResource_second Gamma
        functionSymbol leftFirst leftSecond rightFirst rightSecond
  have hleftInsertCard : (insert leftFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le leftFormula Gamma
    omega
  have hrightInsertCard : (insert rightFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le rightFormula Gamma
    omega
  have hleftWeakening := weakeningFullAssemblyCost_le_small
    (insert leftFormula Gamma) formulaResource hleftInsertCard
      (hcontext.insert hleftFormula)
  have hrightWeakening := weakeningFullAssemblyCost_le_small
    (insert rightFormula Gamma) formulaResource hrightInsertCard
      (hcontext.insert hrightFormula)
  have hlocal :=
    contextualBinaryFunctionCongruenceStructuralPayloadBound_le_public
      Gamma functionSymbol leftFirst leftSecond rightFirst rightSecond
      leftBound rightBound hfunction hcard
  calc
    instantiatedTermTransportNodePayloadResource valuation term
        functionSymbol args =
      contextualBinaryFunctionCongruenceStructuralPayloadBound Gamma
        functionSymbol leftFirst leftSecond rightFirst rightSecond
        leftBound rightBound := by rfl
    _ <= leftBound + rightBound +
        contextualBinaryFunctionCongruenceLocalEnvelope Gamma
          functionSymbol leftFirst leftSecond rightFirst rightSecond :=
      hlocal
    _ <= leftPublicBound + rightPublicBound +
          2 * smallContextAssemblyEnvelope formulaResource +
          contextualBinaryFunctionCongruenceLocalEnvelope Gamma
            functionSymbol leftFirst leftSecond rightFirst rightSecond := by
      dsimp only [leftBound, rightBound]
      omega
    _ = instantiatedTermTransportNodePayloadPolynomial valuation term
          functionSymbol args leftPublicBound rightPublicBound := by
      unfold instantiatedTermTransportNodePayloadPolynomial
      rfl

theorem instantiatedTermTransportPayloadResource_le_publicPolynomial
    (valuation : Nat -> Nat) :
    (term : ValuationTerm) -> term.freeVariables.card <= 4 ->
    instantiatedTermTransportPayloadResource valuation term <=
      instantiatedTermTransportPayloadPolynomial valuation term
  | #index, _ => Fin.elim0 index
  | &index, _ => by
      let Gamma := valuationContext ({index} : Finset Nat) valuation
      let formula :=
        (“!!(iteratedSuccessorTerm 0 (valuation index)) =
          !!(&index : ValuationTerm)” : ValuationFormula)
      have hcard : Gamma.card <= 4 := by
        have himage : Gamma.card <= ({index} : Finset Nat).card := by
          dsimp only [Gamma]
          unfold valuationContext
          exact Finset.card_image_le
        simp only [Finset.card_singleton] at himage
        omega
      have hcontext := contextFormulaResource_context Gamma formula
      have hformula := contextFormulaResource_formula Gamma formula
      have hassumption := assumptionFullPayloadCost_le_small
        Gamma formula (contextFormulaResource Gamma formula)
        hcard hcontext hformula
      simpa only [instantiatedTermTransportPayloadResource,
        instantiatedTermTransportPayloadPolynomial, Gamma, formula] using
        hassumption
  | .func .zero args, hvars => by
      let term := (.func .zero args : ValuationTerm)
      let Gamma := valuationContext term.freeVariables valuation
      let formula :=
        (“!!(instantiateTerm valuation term) = !!term” : ValuationFormula)
      have hcard : Gamma.card <= 4 :=
        valuationContext_card_le_four_of_card_le_four
          term.freeVariables valuation hvars
      have hcontext := contextFormulaResource_context Gamma formula
      have hformula := contextFormulaResource_formula Gamma formula
      have hinsertCard : (insert formula Gamma).card <= 8 := by
        have hstep := Finset.card_insert_le formula Gamma
        omega
      have hweakening := weakeningFullAssemblyCost_le_small
        (insert formula Gamma) (contextFormulaResource Gamma formula)
        hinsertCard (hcontext.insert hformula)
      simp only [instantiatedTermTransportPayloadResource,
        instantiatedTermTransportPayloadPolynomial]
      dsimp only [term, Gamma, formula] at hweakening ⊢
      omega
  | .func .one args, hvars => by
      let term := (.func .one args : ValuationTerm)
      let Gamma := valuationContext term.freeVariables valuation
      let formula :=
        (“!!(instantiateTerm valuation term) = !!term” : ValuationFormula)
      have hcard : Gamma.card <= 4 :=
        valuationContext_card_le_four_of_card_le_four
          term.freeVariables valuation hvars
      have hcontext := contextFormulaResource_context Gamma formula
      have hformula := contextFormulaResource_formula Gamma formula
      have hinsertCard : (insert formula Gamma).card <= 8 := by
        have hstep := Finset.card_insert_le formula Gamma
        omega
      have hweakening := weakeningFullAssemblyCost_le_small
        (insert formula Gamma) (contextFormulaResource Gamma formula)
        hinsertCard (hcontext.insert hformula)
      simp only [instantiatedTermTransportPayloadResource,
        instantiatedTermTransportPayloadPolynomial]
      dsimp only [term, Gamma, formula] at hweakening ⊢
      omega
  | .func .add args, hvars => by
      have hleftSubset : (args 0).freeVariables ⊆
          (.func Language.Add.add args : ValuationTerm).freeVariables := by
        intro candidate hcandidate
        exact freeVariables_arg_subset_func
          Language.Add.add args 0 hcandidate
      have hrightSubset : (args 1).freeVariables ⊆
          (.func Language.Add.add args : ValuationTerm).freeVariables := by
        intro candidate hcandidate
        exact freeVariables_arg_subset_func
          Language.Add.add args 1 hcandidate
      have hleftVars : (args 0).freeVariables.card <= 4 :=
        (Finset.card_le_card hleftSubset).trans hvars
      have hrightVars : (args 1).freeVariables.card <= 4 :=
        (Finset.card_le_card hrightSubset).trans hvars
      have hleft :=
        instantiatedTermTransportPayloadResource_le_publicPolynomial
          valuation (args 0) hleftVars
      have hright :=
        instantiatedTermTransportPayloadResource_le_publicPolynomial
          valuation (args 1) hrightVars
      simpa only [instantiatedTermTransportPayloadResource,
        instantiatedTermTransportPayloadPolynomial,
        instantiatedTermTransportNodePayloadResource] using
        instantiatedTermTransportNodePayloadResource_le_public
          valuation (.func .add args : ValuationTerm)
          Language.Add.add args
          (instantiatedTermTransportPayloadPolynomial valuation (args 0))
          (instantiatedTermTransportPayloadPolynomial valuation (args 1))
          (Or.inl rfl) hvars hleft hright
  | .func .mul args, hvars => by
      have hleftSubset : (args 0).freeVariables ⊆
          (.func Language.Mul.mul args : ValuationTerm).freeVariables := by
        intro candidate hcandidate
        exact freeVariables_arg_subset_func
          Language.Mul.mul args 0 hcandidate
      have hrightSubset : (args 1).freeVariables ⊆
          (.func Language.Mul.mul args : ValuationTerm).freeVariables := by
        intro candidate hcandidate
        exact freeVariables_arg_subset_func
          Language.Mul.mul args 1 hcandidate
      have hleftVars : (args 0).freeVariables.card <= 4 :=
        (Finset.card_le_card hleftSubset).trans hvars
      have hrightVars : (args 1).freeVariables.card <= 4 :=
        (Finset.card_le_card hrightSubset).trans hvars
      have hleft :=
        instantiatedTermTransportPayloadResource_le_publicPolynomial
          valuation (args 0) hleftVars
      have hright :=
        instantiatedTermTransportPayloadResource_le_publicPolynomial
          valuation (args 1) hrightVars
      simpa only [instantiatedTermTransportPayloadResource,
        instantiatedTermTransportPayloadPolynomial,
        instantiatedTermTransportNodePayloadResource] using
        instantiatedTermTransportNodePayloadResource_le_public
          valuation (.func .mul args : ValuationTerm)
          Language.Mul.mul args
          (instantiatedTermTransportPayloadPolynomial valuation (args 0))
          (instantiatedTermTransportPayloadPolynomial valuation (args 1))
          (Or.inr rfl) hvars hleft hright

def instantiatedTermNormalizationPayloadPolynomial
    (valuation : Nat -> Nat) : ValuationTerm -> Nat
  | #index => Fin.elim0 index
  | &index => shortToIteratedPayloadPolynomial (valuation index)
  | .func .zero _ => shortToIteratedPayloadPolynomial 0
  | .func .one _ => paMultiplicationLocalCostEnvelope 0
  | .func .add args =>
      instantiatedTermNormalizationPayloadPolynomial valuation (args 0) +
        instantiatedTermNormalizationPayloadPolynomial valuation (args 1) +
        binaryNumeralAdditionPayloadPolynomial
          (Nat.size (termValue valuation (args 0)) +
            Nat.size (termValue valuation (args 1))) +
        3 * paPrimitiveCostEnvelope
          (additionNormalizationStepTermCodeResource valuation args)
  | .func .mul args =>
      instantiatedTermNormalizationPayloadPolynomial valuation (args 0) +
        instantiatedTermNormalizationPayloadPolynomial valuation (args 1) +
        binaryNumeralMultiplicationPayloadPolynomial
          (Nat.size (termValue valuation (args 0)) +
            Nat.size (termValue valuation (args 1))) +
        3 * paPrimitiveCostEnvelope
          (multiplicationNormalizationStepTermCodeResource valuation args)

theorem instantiatedTermNormalizationPayloadResource_le_publicPolynomial
    (valuation : Nat -> Nat) :
    (term : ValuationTerm) ->
    instantiatedTermNormalizationPayloadResource valuation term <=
      instantiatedTermNormalizationPayloadPolynomial valuation term
  | #index => Fin.elim0 index
  | &index => by
      simpa only [instantiatedTermNormalizationPayloadResource,
        instantiatedTermNormalizationPayloadPolynomial] using
        shortToIteratedPayloadResource_le_publicPolynomial (valuation index)
  | .func .zero args => by
      simpa only [instantiatedTermNormalizationPayloadResource,
        instantiatedTermNormalizationPayloadPolynomial] using
        shortToIteratedPayloadResource_le_publicPolynomial 0
  | .func .one args => by
      simp only [instantiatedTermNormalizationPayloadResource,
        instantiatedTermNormalizationPayloadPolynomial]
      exact le_rfl
  | .func .add args => by
      have hleft :=
        instantiatedTermNormalizationPayloadResource_le_publicPolynomial
          valuation (args 0)
      have hright :=
        instantiatedTermNormalizationPayloadResource_le_publicPolynomial
          valuation (args 1)
      simp only [instantiatedTermNormalizationPayloadResource,
        instantiatedTermNormalizationPayloadPolynomial]
      omega
  | .func .mul args => by
      have hleft :=
        instantiatedTermNormalizationPayloadResource_le_publicPolynomial
          valuation (args 0)
      have hright :=
        instantiatedTermNormalizationPayloadResource_le_publicPolynomial
          valuation (args 1)
      simp only [instantiatedTermNormalizationPayloadResource,
        instantiatedTermNormalizationPayloadPolynomial]
      omega

def contextualizedNormalizationPayloadPolynomial
    (valuation : Nat -> Nat) (term : ValuationTerm) : Nat :=
  let Gamma := valuationContext term.freeVariables valuation
  let formula :=
    (“!!(shortBinaryNumeralTerm (termValue valuation term)) =
      !!(instantiateTerm valuation term)” : ValuationFormula)
  instantiatedTermNormalizationPayloadPolynomial valuation term +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert formula Gamma)

theorem contextualizedNormalizationPayloadResource_le_publicPolynomial
    (valuation : Nat -> Nat) (term : ValuationTerm) :
    contextualizedNormalizationPayloadResource valuation term <=
      contextualizedNormalizationPayloadPolynomial valuation term := by
  have hnormalization :=
    instantiatedTermNormalizationPayloadResource_le_publicPolynomial
      valuation term
  simp only [contextualizedNormalizationPayloadResource,
    contextualizedNormalizationPayloadPolynomial]
  exact Nat.add_le_add_right hnormalization _

theorem contextualEqualityTransitivityStructuralPayloadBound_mono_left
    (Gamma : Finset ValuationFormula)
    (left middle right : ValuationTerm)
    (rightPayloadLength leftPayloadLength leftPayloadBound : Nat)
    (hleft : leftPayloadLength <= leftPayloadBound) :
    contextualEqualityTransitivityStructuralPayloadBound Gamma
        left middle right leftPayloadLength rightPayloadLength <=
      contextualEqualityTransitivityStructuralPayloadBound Gamma
        left middle right leftPayloadBound rightPayloadLength := by
  simp only [contextualEqualityTransitivityStructuralPayloadBound]
  omega

theorem contextualEqualityTransitivityStructuralPayloadBound_mono
    (Gamma : Finset ValuationFormula)
    (left middle right : ValuationTerm)
    (leftPayloadLength rightPayloadLength
      leftPayloadBound rightPayloadBound : Nat)
    (hleft : leftPayloadLength <= leftPayloadBound)
    (hright : rightPayloadLength <= rightPayloadBound) :
    contextualEqualityTransitivityStructuralPayloadBound Gamma
        left middle right leftPayloadLength rightPayloadLength <=
      contextualEqualityTransitivityStructuralPayloadBound Gamma
        left middle right leftPayloadBound rightPayloadBound := by
  simp only [contextualEqualityTransitivityStructuralPayloadBound]
  omega

/-! ## Uniform outer ledger for contextual term equality -/

def termEqualityFormulaStageOneCodeEnvelope (termBound : Nat) : Nat :=
  4 * (paFormulaCodeEnvelope termBound +
    (binaryNatCode 5).length + 1)

def termEqualityFormulaStageTwoCodeEnvelope (termBound : Nat) : Nat :=
  4 * (termEqualityFormulaStageOneCodeEnvelope termBound +
    (binaryNatCode 4).length + (binaryNatCode 5).length + 1)

def termEqualityFormulaClosureCodeEnvelope (termBound : Nat) : Nat :=
  2 * termEqualityFormulaStageTwoCodeEnvelope termBound + 1

def termEqualityContextFormulaResourceEnvelope
    (contextBound termBound : Nat) : Nat :=
  contextBound + 6 * termEqualityFormulaClosureCodeEnvelope termBound + 1

def contextualEqualityTransitivityUniformPayloadBound
    (contextBound termBound leftPayloadBound rightPayloadBound : Nat) : Nat :=
  leftPayloadBound + rightPayloadBound +
    paPrimitiveCostEnvelope termBound +
    3 * smallContextAssemblyEnvelope
      (termEqualityContextFormulaResourceEnvelope contextBound termBound)

theorem contextualEqualityTransitivityStructuralPayloadBound_le_uniform
    (Gamma : Finset ValuationFormula)
    (left middle right : ValuationTerm)
    (leftPayloadBound rightPayloadBound contextBound termBound : Nat)
    (hcard : Gamma.card <= 4)
    (hcontext : formulaCodeSum Gamma <= contextBound)
    (hleft : (binaryTermCode left).length <= termBound)
    (hmiddle : (binaryTermCode middle).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    contextualEqualityTransitivityStructuralPayloadBound Gamma
        left middle right leftPayloadBound rightPayloadBound <=
      contextualEqualityTransitivityUniformPayloadBound contextBound
        termBound leftPayloadBound rightPayloadBound := by
  let firstFormula :=
    (“!!left = !!middle” : ValuationFormula)
  let secondFormula :=
    (“!!middle = !!right” : ValuationFormula)
  let resultFormula :=
    (“!!left = !!right” : ValuationFormula)
  let afterFirstFormula := secondFormula 🡒 resultFormula
  let theoremFormula := firstFormula 🡒 afterFirstFormula
  let formulaResource :=
    termEqualityContextFormulaResourceEnvelope contextBound termBound
  have hfirstFormula : (binaryFormulaCode firstFormula).length <=
      paFormulaCodeEnvelope termBound := by
    simpa only [firstFormula] using
      equalityFormula_code_length_le_paEnvelope left middle termBound
        hleft hmiddle
  have hsecondFormula : (binaryFormulaCode secondFormula).length <=
      paFormulaCodeEnvelope termBound := by
    simpa only [secondFormula] using
      equalityFormula_code_length_le_paEnvelope middle right termBound
        hmiddle hright
  have hresultFormula : (binaryFormulaCode resultFormula).length <=
      paFormulaCodeEnvelope termBound := by
    simpa only [resultFormula] using
      equalityFormula_code_length_le_paEnvelope left right termBound
        hleft hright
  have hafterFirstFormula :
      (binaryFormulaCode afterFirstFormula).length <=
        termEqualityFormulaStageOneCodeEnvelope termBound := by
    have hraw := binaryFormulaCode_implication_length_le
      secondFormula resultFormula
    unfold termEqualityFormulaStageOneCodeEnvelope
    dsimp only [afterFirstFormula] at *
    omega
  have htheoremFormula : (binaryFormulaCode theoremFormula).length <=
      termEqualityFormulaStageTwoCodeEnvelope termBound := by
    have hraw := binaryFormulaCode_implication_length_le
      firstFormula afterFirstFormula
    unfold termEqualityFormulaStageTwoCodeEnvelope
      termEqualityFormulaStageOneCodeEnvelope at hafterFirstFormula ⊢
    dsimp only [theoremFormula]
    omega
  have hbaseClosure : paFormulaCodeEnvelope termBound <=
      termEqualityFormulaClosureCodeEnvelope termBound := by
    unfold termEqualityFormulaClosureCodeEnvelope
      termEqualityFormulaStageTwoCodeEnvelope
      termEqualityFormulaStageOneCodeEnvelope
    omega
  have hstageOneClosure : termEqualityFormulaStageOneCodeEnvelope termBound <=
      termEqualityFormulaClosureCodeEnvelope termBound := by
    unfold termEqualityFormulaClosureCodeEnvelope
      termEqualityFormulaStageTwoCodeEnvelope
    omega
  have hstageTwoClosure : termEqualityFormulaStageTwoCodeEnvelope termBound <=
      termEqualityFormulaClosureCodeEnvelope termBound := by
    unfold termEqualityFormulaClosureCodeEnvelope
    omega
  have hfirstClosure := hfirstFormula.trans hbaseClosure
  have hsecondClosure := hsecondFormula.trans hbaseClosure
  have hresultClosure := hresultFormula.trans hbaseClosure
  have hafterFirstClosure := hafterFirstFormula.trans hstageOneClosure
  have htheoremClosure := htheoremFormula.trans hstageTwoClosure
  have hnegTheorem : (binaryFormulaCode (∼theoremFormula)).length <=
      termEqualityFormulaClosureCodeEnvelope termBound := by
    have hraw :=
      FoundationCompactSyntaxTransformationCodeBounds.binaryFormulaCode_neg_length_le
        theoremFormula
    unfold termEqualityFormulaClosureCodeEnvelope
    omega
  have hnegAfterFirst :
      (binaryFormulaCode (∼afterFirstFormula)).length <=
        termEqualityFormulaClosureCodeEnvelope termBound := by
    have hraw :=
      FoundationCompactSyntaxTransformationCodeBounds.binaryFormulaCode_neg_length_le
        afterFirstFormula
    unfold termEqualityFormulaClosureCodeEnvelope
      termEqualityFormulaStageTwoCodeEnvelope
    omega
  have hnegResult : (binaryFormulaCode (∼resultFormula)).length <=
      termEqualityFormulaClosureCodeEnvelope termBound := by
    have hraw :=
      FoundationCompactSyntaxTransformationCodeBounds.binaryFormulaCode_neg_length_le
        resultFormula
    unfold termEqualityFormulaClosureCodeEnvelope
      termEqualityFormulaStageTwoCodeEnvelope
      termEqualityFormulaStageOneCodeEnvelope
    omega
  have hcontextResource : FormulaCodeBound Gamma formulaResource := by
    intro formula hformula
    have hsum := formulaCode_le_formulaCodeSum hformula
    unfold formulaResource termEqualityContextFormulaResourceEnvelope
    omega
  have hformulaResource : forall formula : ValuationFormula,
      (binaryFormulaCode formula).length <=
        termEqualityFormulaClosureCodeEnvelope termBound ->
      (binaryFormulaCode formula).length <= formulaResource := by
    intro formula hformula
    unfold formulaResource termEqualityContextFormulaResourceEnvelope
    omega
  have hfirstResource := hformulaResource firstFormula hfirstClosure
  have hsecondResource := hformulaResource secondFormula hsecondClosure
  have hresultResource := hformulaResource resultFormula hresultClosure
  have hafterFirstResource :=
    hformulaResource afterFirstFormula hafterFirstClosure
  have htheoremResource := hformulaResource theoremFormula htheoremClosure
  have hnegTheoremResource := hformulaResource (∼theoremFormula) hnegTheorem
  have hnegAfterFirstResource :=
    hformulaResource (∼afterFirstFormula) hnegAfterFirst
  have hnegResultResource := hformulaResource (∼resultFormula) hnegResult
  have htheoremProofRaw := equalityTransitivityImplication_payloadLength_le
    left middle right
  have hfirstSpecialization := specializationCost_fixedFormula_le
    equalityTransitivityOuterBody left termBound (by simp) hleft
  have hsecondSpecialization := specializationCost_stage1Formula_le
    (equalityTransitivityMiddleBody left) middle termBound
    (equalityTransitivityMiddleBody_code_le_stage1
      left termBound hleft) hmiddle
  have hthirdSpecialization := specializationCost_stage2Formula_le
    (equalityTransitivityInnerBody left middle) right termBound
    (equalityTransitivityInnerBody_code_le_stage2
      left middle termBound hleft hmiddle) hright
  have haxiom := equalityTransitivityAxiomProof_payloadLength_le_fixed
  have htheoremProof :
      (equalityTransitivityImplication left middle right).payloadLength <=
        paPrimitiveCostEnvelope termBound := by
    unfold paPrimitiveCostEnvelope
    omega
  have hinsertCard : (insert theoremFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le theoremFormula Gamma
    omega
  have hweakening := weakeningFullAssemblyCost_le_small
    (insert theoremFormula Gamma) formulaResource hinsertCard
    (hcontextResource.insert htheoremResource)
  have hfirstMp := contextualModusPonensFullAssemblyCost_le_small
    Gamma firstFormula afterFirstFormula formulaResource hcard
    hcontextResource hfirstResource hafterFirstResource htheoremResource
    hnegTheoremResource hnegAfterFirstResource
  have hsecondMp := contextualModusPonensFullAssemblyCost_le_small
    Gamma secondFormula resultFormula formulaResource hcard
    hcontextResource hsecondResource hresultResource hafterFirstResource
    hnegAfterFirstResource hnegResultResource
  simp only [contextualEqualityTransitivityStructuralPayloadBound,
    contextualEqualityTransitivityUniformPayloadBound]
  dsimp only [firstFormula, secondFormula, resultFormula,
    afterFirstFormula, theoremFormula, formulaResource] at *
  omega

/-- Intermediate public replacement of every recursive normalization leaf.
The transport tree remains visible and will next be bounded by its syntax
scale; it is not accepted as an external parameter. -/
def compileTermValueEqualityNormalizationPublicBound
    (valuation : Nat -> Nat) (term : ValuationTerm) : Nat :=
  let Gamma := valuationContext term.freeVariables valuation
  contextualEqualityTransitivityStructuralPayloadBound
    Gamma
    (shortBinaryNumeralTerm (termValue valuation term))
    (instantiateTerm valuation term) term
    (contextualizedNormalizationPayloadPolynomial valuation term)
    (instantiatedTermTransportPayloadResource valuation term)

theorem compileTermValueEqualityPayloadResource_le_normalizationPublicBound
    (valuation : Nat -> Nat) (term : ValuationTerm) :
    compileTermValueEqualityPayloadResource valuation term <=
      compileTermValueEqualityNormalizationPublicBound valuation term := by
  have hnormalization :=
    contextualizedNormalizationPayloadResource_le_publicPolynomial
      valuation term
  unfold compileTermValueEqualityPayloadResource
    compileTermValueEqualityNormalizationPublicBound
  exact contextualEqualityTransitivityStructuralPayloadBound_mono_left
    _ _ _ _ _ _ _ hnormalization

def contextualizedNormalizationPayloadSyntaxPolynomial
    (valuation : Nat -> Nat) (term : ValuationTerm) : Nat :=
  let Gamma := valuationContext term.freeVariables valuation
  let formula :=
    (“!!(shortBinaryNumeralTerm (termValue valuation term)) =
      !!(instantiateTerm valuation term)” : ValuationFormula)
  instantiatedTermNormalizationPayloadPolynomial valuation term +
    smallContextAssemblyEnvelope (contextFormulaResource Gamma formula)

theorem contextualizedNormalizationPayloadResource_le_syntaxPolynomial
    (valuation : Nat -> Nat) (term : ValuationTerm)
    (hvars : term.freeVariables.card <= 4) :
    contextualizedNormalizationPayloadResource valuation term <=
      contextualizedNormalizationPayloadSyntaxPolynomial valuation term := by
  let Gamma := valuationContext term.freeVariables valuation
  let formula :=
    (“!!(shortBinaryNumeralTerm (termValue valuation term)) =
      !!(instantiateTerm valuation term)” : ValuationFormula)
  have hnormalization :=
    instantiatedTermNormalizationPayloadResource_le_publicPolynomial
      valuation term
  have hcard : Gamma.card <= 4 :=
    valuationContext_card_le_four_of_card_le_four
      term.freeVariables valuation hvars
  have hcontext := contextFormulaResource_context Gamma formula
  have hformula := contextFormulaResource_formula Gamma formula
  have hinsertCard : (insert formula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le formula Gamma
    omega
  have hweakening := weakeningFullAssemblyCost_le_small
    (insert formula Gamma) (contextFormulaResource Gamma formula)
    hinsertCard (hcontext.insert hformula)
  unfold contextualizedNormalizationPayloadResource
    contextualizedNormalizationPayloadSyntaxPolynomial
  dsimp only [Gamma, formula] at hweakening ⊢
  omega

def compileTermValueEqualityPayloadPolynomial
    (valuation : Nat -> Nat) (term : ValuationTerm) : Nat :=
  let Gamma := valuationContext term.freeVariables valuation
  contextualEqualityTransitivityStructuralPayloadBound Gamma
    (shortBinaryNumeralTerm (termValue valuation term))
    (instantiateTerm valuation term) term
    (contextualizedNormalizationPayloadSyntaxPolynomial valuation term)
    (instantiatedTermTransportPayloadPolynomial valuation term)

theorem compileTermValueEqualityPayloadPolynomial_le_uniform
    (valuation : Nat -> Nat) (term : ValuationTerm)
    (contextBound termBound normalizationBound transportBound : Nat)
    (hcard : (valuationContext term.freeVariables valuation).card <= 4)
    (hcontext : formulaCodeSum
      (valuationContext term.freeVariables valuation) <= contextBound)
    (hshort : (binaryTermCode
      (shortBinaryNumeralTerm (termValue valuation term))).length <=
        termBound)
    (hinstantiated : (binaryTermCode (instantiateTerm valuation term)).length <=
      termBound)
    (hterm : (binaryTermCode term).length <= termBound)
    (hnormalization :
      contextualizedNormalizationPayloadSyntaxPolynomial valuation term <=
        normalizationBound)
    (htransport : instantiatedTermTransportPayloadPolynomial valuation term <=
      transportBound) :
    compileTermValueEqualityPayloadPolynomial valuation term <=
      contextualEqualityTransitivityUniformPayloadBound contextBound termBound
        normalizationBound transportBound := by
  unfold compileTermValueEqualityPayloadPolynomial
  calc
    contextualEqualityTransitivityStructuralPayloadBound
        (valuationContext term.freeVariables valuation)
        (shortBinaryNumeralTerm (termValue valuation term))
        (instantiateTerm valuation term) term
        (contextualizedNormalizationPayloadSyntaxPolynomial valuation term)
        (instantiatedTermTransportPayloadPolynomial valuation term) <=
      contextualEqualityTransitivityStructuralPayloadBound
        (valuationContext term.freeVariables valuation)
        (shortBinaryNumeralTerm (termValue valuation term))
        (instantiateTerm valuation term) term normalizationBound
        transportBound :=
      contextualEqualityTransitivityStructuralPayloadBound_mono
        _ _ _ _ _ _ _ _ hnormalization htransport
    _ <= contextualEqualityTransitivityUniformPayloadBound contextBound
        termBound normalizationBound transportBound :=
      contextualEqualityTransitivityStructuralPayloadBound_le_uniform
        (valuationContext term.freeVariables valuation)
        (shortBinaryNumeralTerm (termValue valuation term))
        (instantiateTerm valuation term) term normalizationBound
        transportBound contextBound termBound hcard hcontext hshort
        hinstantiated hterm

/-! ## Free-variable leaf of the uniform term compiler -/

theorem shortToIteratedPayloadPolynomial_mono_public :
    Monotone shortToIteratedPayloadPolynomial := by
  intro small large hbound
  have hstep := shortToIteratedStepPayloadPolynomial_mono hbound
  unfold shortToIteratedPayloadPolynomial
  gcongr

def valuationFvarFormulaResourceEnvelope
    (contextBound termBound : Nat) : Nat :=
  contextBound + paFormulaCodeEnvelope termBound + 1

def valuationFvarNormalizationUniformPayloadBound
    (numericBound contextBound termBound : Nat) : Nat :=
  shortToIteratedPayloadPolynomial numericBound +
    smallContextAssemblyEnvelope
      (valuationFvarFormulaResourceEnvelope contextBound termBound)

def valuationFvarTransportUniformPayloadBound
    (contextBound termBound : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (valuationFvarFormulaResourceEnvelope contextBound termBound)

def valuationFvarTermEqualityUniformPayloadPolynomial
    (numericBound contextBound termBound : Nat) : Nat :=
  contextualEqualityTransitivityUniformPayloadBound contextBound termBound
    (valuationFvarNormalizationUniformPayloadBound numericBound contextBound
      termBound)
    (valuationFvarTransportUniformPayloadBound contextBound termBound)

theorem compileTermValueEqualityPayloadPolynomial_fvar_le_uniform
    (valuation : Nat -> Nat) (index : Nat)
    (numericBound contextBound termBound : Nat)
    (hvalue : valuation index <= numericBound)
    (hcontext : formulaCodeSum
      (valuationContext ({index} : Finset Nat) valuation) <= contextBound)
    (hshort : (binaryTermCode
      (shortBinaryNumeralTerm (valuation index))).length <= termBound)
    (hiterated : (binaryTermCode
      (iteratedSuccessorTerm 0 (valuation index))).length <= termBound)
    (hvariable : (binaryTermCode (&index : ValuationTerm)).length <=
      termBound) :
    compileTermValueEqualityPayloadPolynomial valuation
        (&index : ValuationTerm) <=
      valuationFvarTermEqualityUniformPayloadPolynomial numericBound
        contextBound termBound := by
  let Gamma := valuationContext ({index} : Finset Nat) valuation
  let shortTerm := shortBinaryNumeralTerm (valuation index)
  let iteratedTerm := iteratedSuccessorTerm 0 (valuation index)
  let normalizationFormula :=
    (“!!shortTerm = !!iteratedTerm” : ValuationFormula)
  let transportFormula :=
    (“!!iteratedTerm = !!(&index : ValuationTerm)” : ValuationFormula)
  let formulaResource :=
    valuationFvarFormulaResourceEnvelope contextBound termBound
  have hnormalizationFormula :
      (binaryFormulaCode normalizationFormula).length <=
        paFormulaCodeEnvelope termBound := by
    simpa only [normalizationFormula] using
      equalityFormula_code_length_le_paEnvelope shortTerm iteratedTerm
        termBound hshort hiterated
  have htransportFormula :
      (binaryFormulaCode transportFormula).length <=
        paFormulaCodeEnvelope termBound := by
    simpa only [transportFormula] using
      equalityFormula_code_length_le_paEnvelope iteratedTerm
        (&index : ValuationTerm) termBound hiterated hvariable
  have hnormalizationResource :
      contextFormulaResource Gamma normalizationFormula <=
        formulaResource := by
    unfold contextFormulaResource formulaResource
      valuationFvarFormulaResourceEnvelope
    dsimp only [Gamma]
    omega
  have htransportResource :
      contextFormulaResource Gamma transportFormula <=
        formulaResource := by
    unfold contextFormulaResource formulaResource
      valuationFvarFormulaResourceEnvelope
    dsimp only [Gamma]
    omega
  have hnormalizationAssembly :=
    smallContextAssemblyEnvelope_mono_local hnormalizationResource
  have htransportAssembly :=
    smallContextAssemblyEnvelope_mono_local htransportResource
  have hunary := shortToIteratedPayloadPolynomial_mono_public hvalue
  have hnormalization :
      contextualizedNormalizationPayloadSyntaxPolynomial valuation
          (&index : ValuationTerm) <=
        valuationFvarNormalizationUniformPayloadBound numericBound
          contextBound termBound := by
    simp only [contextualizedNormalizationPayloadSyntaxPolynomial,
      instantiatedTermNormalizationPayloadPolynomial, termValue_fvar,
      instantiateTerm, Semiterm.freeVariables_fvar]
    dsimp only [Gamma, shortTerm, iteratedTerm, normalizationFormula,
      formulaResource] at hnormalizationAssembly ⊢
    unfold valuationFvarNormalizationUniformPayloadBound
    omega
  have htransport :
      instantiatedTermTransportPayloadPolynomial valuation
          (&index : ValuationTerm) <=
        valuationFvarTransportUniformPayloadBound contextBound
          termBound := by
    simp only [instantiatedTermTransportPayloadPolynomial]
    dsimp only [Gamma, iteratedTerm, transportFormula, formulaResource]
      at htransportAssembly ⊢
    unfold valuationFvarTransportUniformPayloadBound
    exact htransportAssembly
  have hcard :
      (valuationContext (&index : ValuationTerm).freeVariables valuation).card <=
        4 := by
    have himage :
        (valuationContext ({index} : Finset Nat) valuation).card <= 1 := by
      unfold valuationContext
      simpa only [Finset.card_singleton] using
        (Finset.card_image_le :
          (Finset.image (valuationEqualityAssumption valuation)
            ({index} : Finset Nat)).card <= ({index} : Finset Nat).card)
    simpa using himage.trans (by omega)
  have hcontextTerm : formulaCodeSum
      (valuationContext (&index : ValuationTerm).freeVariables valuation) <=
        contextBound := by
    simpa using hcontext
  have hshortTerm : (binaryTermCode
      (shortBinaryNumeralTerm
        (termValue valuation (&index : ValuationTerm)))).length <=
        termBound := by simpa using hshort
  have hinstantiated :
      (binaryTermCode
        (instantiateTerm valuation (&index : ValuationTerm))).length <=
          termBound := by simpa [instantiateTerm] using hiterated
  unfold valuationFvarTermEqualityUniformPayloadPolynomial
  exact compileTermValueEqualityPayloadPolynomial_le_uniform valuation
    (&index : ValuationTerm) contextBound termBound
    (valuationFvarNormalizationUniformPayloadBound numericBound contextBound
      termBound)
    (valuationFvarTransportUniformPayloadBound contextBound termBound)
    hcard hcontextTerm hshortTerm hinstantiated hvariable hnormalization
    htransport

theorem compileTermValueEqualityPayloadResource_le_publicPolynomial_of_card
    (valuation : Nat -> Nat) (term : ValuationTerm)
    (hvars : term.freeVariables.card <= 4) :
    compileTermValueEqualityPayloadResource valuation term <=
      compileTermValueEqualityPayloadPolynomial valuation term := by
  have hnormalization :=
    contextualizedNormalizationPayloadResource_le_syntaxPolynomial
      valuation term hvars
  have htransport :=
    instantiatedTermTransportPayloadResource_le_publicPolynomial
      valuation term hvars
  unfold compileTermValueEqualityPayloadResource
    compileTermValueEqualityPayloadPolynomial
  exact contextualEqualityTransitivityStructuralPayloadBound_mono
    _ _ _ _ _ _ _ _ hnormalization htransport

theorem compileTermValueEqualityPayloadResource_le_publicPolynomial
    (valuation : Nat -> Nat) (term : ValuationTerm)
    (hvars : term.freeVariables ⊆ {0}) :
    compileTermValueEqualityPayloadResource valuation term <=
      compileTermValueEqualityPayloadPolynomial valuation term := by
  have hcardSubset := Finset.card_le_card hvars
  have hcard : term.freeVariables.card <= 4 := by
    simp only [Finset.card_singleton] at hcardSubset
    omega
  exact compileTermValueEqualityPayloadResource_le_publicPolynomial_of_card
    valuation term hcard

#print axioms
  contextualBinaryFunctionCongruenceStructuralPayloadBound_le_public
#print axioms valuationEqualityAssumption_code_le_uniform
#print axioms valuationContext_formulaCodeSum_le_uniform
#print axioms
  instantiatedTermTransportNodePayloadResource_le_public
#print axioms
  instantiatedTermTransportPayloadResource_le_publicPolynomial
#print axioms
  contextualEqualityTransitivityStructuralPayloadBound_le_uniform
#print axioms compileTermValueEqualityPayloadPolynomial_le_uniform
#print axioms
  compileTermValueEqualityPayloadPolynomial_fvar_le_uniform
#print axioms
  instantiatedTermNormalizationPayloadResource_le_publicPolynomial
#print axioms
  contextualizedNormalizationPayloadResource_le_publicPolynomial
#print axioms
  compileTermValueEqualityPayloadResource_le_normalizationPublicBound
#print axioms
  contextualizedNormalizationPayloadResource_le_syntaxPolynomial
#print axioms
  compileTermValueEqualityPayloadResource_le_publicPolynomial_of_card
#print axioms
  compileTermValueEqualityPayloadResource_le_publicPolynomial

end FoundationCompactPAValuationTermCompilerPublicBounds
