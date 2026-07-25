import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds
import integration.FoundationCompactPAValuationTermCompilerUniformMonotoneBounds
import integration.FoundationCompactPAValuationTermCompilerFixedPolynomialBounds
import integration.FoundationCompactPABoundedUniversalPolynomialBounds
import integration.FoundationCompactPANegativeEqualityBounds

/-!
# Fixed polynomial bounds for valuation atomic compilation

This file removes the remaining term- and valuation-shaped coordinates from
the positive binary-relation compiler.  Two source terms whose free variables
are contained in `{0}` are charged only to a numeric bound and a canonical
term-code bound.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactPAClosedAtomicCompiler
open FoundationCompactPAClosedAtomicCompiler.ClosedPATerm
open FoundationCompactPAClosedAtomicCompilerBounds
open FoundationCompactPAClosedAtomicCompilerBounds.ClosedPATerm
open FoundationCompactPAClosedAtomicCompilerBounds.ClosedPATerm.ClosedPAAtomicLiteralBounds
open FoundationCompactPABoundedUniversalCertificateCode
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPABoundedUniversalPolynomialBounds.ClosedPAAtomicLiteralBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerBounds
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationTermCompilerUniformBounds
open FoundationCompactPAValuationTermCompilerFixedPolynomialBounds
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAUnaryAtomicTransport
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPANegativeEqualityBounds

def arbitraryContextRelationFormulaEnvelope
    (contextCodeBound termCodeBound : Nat) : Nat :=
  contextCodeBound +
    16 * (orderPrimitiveFormulaCodeEnvelope termCodeBound + 1)

def arbitraryContextRelationTransportLocalEnvelope
    (contextCodeBound termCodeBound : Nat) : Nat :=
  16 * (fixedPAPayloadEnvelope +
    relationImplicationPayloadEnvelope termCodeBound +
    smallContextAssemblyEnvelope
      (arbitraryContextRelationFormulaEnvelope contextCodeBound
        termCodeBound) + 1)

theorem relationTransportImplicationStructuralPayloadBound_le_arbitraryContext
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstPayloadLength secondPayloadLength contextCodeBound termCodeBound : Nat)
    (hcard : Gamma.card <= 4)
    (hcontext : FormulaCodeBound Gamma contextCodeBound)
    (hleftFirst : (binaryTermCode leftFirst).length <= termCodeBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termCodeBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termCodeBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termCodeBound) :
    relationTransportImplicationStructuralPayloadBound Gamma relationSymbol
        leftFirst leftSecond rightFirst rightSecond
        firstPayloadLength secondPayloadLength <=
      firstPayloadLength + secondPayloadLength +
        arbitraryContextRelationTransportLocalEnvelope contextCodeBound
          termCodeBound := by
  let formulaBound := arbitraryContextRelationFormulaEnvelope
    contextCodeBound termCodeBound
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
  have hcontextLarge : FormulaCodeBound Gamma formulaBound := by
    intro formula hformula
    have hsmall := hcontext formula hformula
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega
  have hfirstFormulaRaw := equalityFormula_code_le_orderAtomic
    leftFirst rightFirst termCodeBound hleftFirst hrightFirst
  have hsecondFormulaRaw := equalityFormula_code_le_orderAtomic
    leftSecond rightSecond termCodeBound hleftSecond hrightSecond
  have htruthRaw := truthFormula_code_le_orderAtomic termCodeBound
  have hinnerRaw := equalityTruthConjunction_code_le_derived
    leftSecond rightSecond termCodeBound hleftSecond hrightSecond
  have hantecedentRaw := relationCongruenceAntecedent_code_le_local
    leftFirst leftSecond rightFirst rightSecond termCodeBound
    hleftFirst hleftSecond hrightFirst hrightSecond
  have hconclusionRaw :=
    binaryRelationCongruenceConclusion_code_le_relationDerived
      relationSymbol leftFirst leftSecond rightFirst rightSecond termCodeBound
      hleftFirst hleftSecond hrightFirst hrightSecond
  have hatomicPrimitive :=
    (orderAtomic_le_derived termCodeBound).trans
      ((orderDerived_le_local termCodeBound).trans
        (orderLocal_le_primitive termCodeBound))
  have hderivedPrimitive := (orderDerived_le_local termCodeBound).trans
    (orderLocal_le_primitive termCodeBound)
  have hlocalPrimitive := orderLocal_le_primitive termCodeBound
  have hfirstFormula : (binaryFormulaCode firstFormula).length <=
      formulaBound := by
    exact (hfirstFormulaRaw.trans hatomicPrimitive).trans (by
      unfold formulaBound arbitraryContextRelationFormulaEnvelope
      omega)
  have hsecondFormula : (binaryFormulaCode secondFormula).length <=
      formulaBound := by
    exact (hsecondFormulaRaw.trans hatomicPrimitive).trans (by
      unfold formulaBound arbitraryContextRelationFormulaEnvelope
      omega)
  have htruth : (binaryFormulaCode truthFormula).length <=
      formulaBound := by
    exact (htruthRaw.trans hatomicPrimitive).trans (by
      unfold formulaBound arbitraryContextRelationFormulaEnvelope
      omega)
  have hinner : (binaryFormulaCode innerFormula).length <= formulaBound := by
    exact (hinnerRaw.trans hderivedPrimitive).trans (by
      unfold formulaBound arbitraryContextRelationFormulaEnvelope
      omega)
  have hantecedent : (binaryFormulaCode antecedentFormula).length <=
      formulaBound := by
    exact (hantecedentRaw.trans hlocalPrimitive).trans (by
      unfold formulaBound arbitraryContextRelationFormulaEnvelope
      omega)
  have hconclusion : (binaryFormulaCode conclusionFormula).length <=
      formulaBound := by
    exact (hconclusionRaw.trans hderivedPrimitive).trans (by
      unfold formulaBound arbitraryContextRelationFormulaEnvelope
      omega)
  have hantecedentTight :
      (binaryFormulaCode antecedentFormula).length <=
        orderPrimitiveFormulaCodeEnvelope termCodeBound := by
    dsimp only [antecedentFormula]
    exact hantecedentRaw.trans hlocalPrimitive
  have hconclusionTight :
      (binaryFormulaCode conclusionFormula).length <=
        orderPrimitiveFormulaCodeEnvelope termCodeBound := by
    dsimp only [conclusionFormula]
    exact hconclusionRaw.trans hderivedPrimitive
  have himplicationRaw := binaryFormulaCode_implication_length_le
    antecedentFormula conclusionFormula
  have htagFive : (binaryNatCode 5).length <= 8 := by decide
  have himplicationTight :
      (binaryFormulaCode implicationFormula).length <=
        4 * orderPrimitiveFormulaCodeEnvelope termCodeBound + 8 := by
    dsimp only [implicationFormula] at *
    omega
  have himplication : (binaryFormulaCode implicationFormula).length <=
      formulaBound := by
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega
  have hnegatedImplicationRaw := binaryFormulaCode_neg_length_le
    implicationFormula
  have hnegatedConclusionRaw := binaryFormulaCode_neg_length_le
    conclusionFormula
  have hnegatedImplication :
      (binaryFormulaCode (∼implicationFormula)).length <= formulaBound := by
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega
  have hnegatedConclusion :
      (binaryFormulaCode (∼conclusionFormula)).length <= formulaBound := by
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega
  have htruthContext := hcontextLarge.insert htruth
  have himplicationContext := hcontextLarge.insert himplication
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
    Gamma secondFormula truthFormula formulaBound hcard hcontextLarge
    hsecondFormula htruth hinner
  have hantecedentCost := conjunctionFullAssemblyCost_le_small
    Gamma firstFormula innerFormula formulaBound hcard hcontextLarge
    hfirstFormula hinner hantecedent
  have himplicationTheorem :=
    binaryRelationExtImplication_payloadLength_le_relationEnvelope
      relationSymbol leftFirst leftSecond rightFirst rightSecond termCodeBound
      hleftFirst hleftSecond hrightFirst hrightSecond
  have hweakImplication := weakeningFullAssemblyCost_le_small
    (insert implicationFormula Gamma) formulaBound himplicationCard
    himplicationContext
  have hmp := contextualModusPonensFullAssemblyCost_le_small
    Gamma antecedentFormula conclusionFormula formulaBound hcard hcontextLarge
    hantecedent hconclusion himplication hnegatedImplication
    hnegatedConclusion
  unfold relationTransportImplicationStructuralPayloadBound
    arbitraryContextRelationTransportLocalEnvelope
  dsimp only [formulaBound, firstFormula, secondFormula, truthFormula,
    innerFormula, antecedentFormula, conclusionFormula, implicationFormula]
    at *
  omega

def arbitraryContextEqualitySymmetryLocalEnvelope
    (contextCodeBound termCodeBound : Nat) : Nat :=
  paPrimitiveCostEnvelope termCodeBound +
    2 * smallContextAssemblyEnvelope
      (arbitraryContextRelationFormulaEnvelope contextCodeBound termCodeBound)

theorem contextualEqualitySymmetryStructuralPayloadBound_le_arbitraryContext
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (sourcePayloadBound contextCodeBound termCodeBound : Nat)
    (hcard : Gamma.card <= 4)
    (hcontext : FormulaCodeBound Gamma contextCodeBound)
    (hleft : (binaryTermCode left).length <= termCodeBound)
    (hright : (binaryTermCode right).length <= termCodeBound) :
    contextualEqualitySymmetryStructuralPayloadBound Gamma left right
        sourcePayloadBound <=
      sourcePayloadBound +
        arbitraryContextEqualitySymmetryLocalEnvelope contextCodeBound
          termCodeBound := by
  let formulaBound :=
    arbitraryContextRelationFormulaEnvelope contextCodeBound termCodeBound
  let antecedent :=
    (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)
  let consequent :=
    (“!!right = !!left” : LO.FirstOrder.ArithmeticProposition)
  let implication := antecedent 🡒 consequent
  have hcontextLarge : FormulaCodeBound Gamma formulaBound := by
    intro formula hformula
    have hsmall := hcontext formula hformula
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega
  have hantecedentRaw := equalityFormula_code_le_orderAtomic
    left right termCodeBound hleft hright
  have hconsequentRaw := equalityFormula_code_le_orderAtomic
    right left termCodeBound hright hleft
  have hatomicPrimitive :=
    (orderAtomic_le_derived termCodeBound).trans
      ((orderDerived_le_local termCodeBound).trans
        (orderLocal_le_primitive termCodeBound))
  have hantecedent : (binaryFormulaCode antecedent).length <=
      formulaBound := (hantecedentRaw.trans hatomicPrimitive).trans (by
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega)
  have hconsequent : (binaryFormulaCode consequent).length <=
      formulaBound := (hconsequentRaw.trans hatomicPrimitive).trans (by
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega)
  have hantecedentTight :
      (binaryFormulaCode antecedent).length <=
        orderPrimitiveFormulaCodeEnvelope termCodeBound := by
    exact hantecedentRaw.trans hatomicPrimitive
  have hconsequentTight :
      (binaryFormulaCode consequent).length <=
        orderPrimitiveFormulaCodeEnvelope termCodeBound := by
    exact hconsequentRaw.trans hatomicPrimitive
  have himplicationRaw := binaryFormulaCode_implication_length_le
    antecedent consequent
  have htagFive : (binaryNatCode 5).length <= 8 := by decide
  have himplicationTight :
      (binaryFormulaCode implication).length <=
        3 * orderPrimitiveFormulaCodeEnvelope termCodeBound + 8 := by
    dsimp only [implication]
    omega
  have himplication : (binaryFormulaCode implication).length <=
      formulaBound := by
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega
  have hnegatedImplicationRaw := binaryFormulaCode_neg_length_le implication
  have hnegatedConsequentRaw := binaryFormulaCode_neg_length_le consequent
  have hnegatedImplication :
      (binaryFormulaCode (∼implication)).length <= formulaBound := by
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega
  have hnegatedConsequent :
      (binaryFormulaCode (∼consequent)).length <= formulaBound := by
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega
  have himplicationContext := hcontextLarge.insert himplication
  have himplicationCard : (insert implication Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le implication Gamma
    omega
  have hsymmetry :=
    equalitySymmetryImplication_payloadLength_le_primitive left right
      termCodeBound hleft hright
  have hweak := weakeningFullAssemblyCost_le_small
    (insert implication Gamma) formulaBound himplicationCard
      himplicationContext
  have hmp := contextualModusPonensFullAssemblyCost_le_small Gamma
    antecedent consequent formulaBound hcard hcontextLarge hantecedent
    hconsequent himplication hnegatedImplication hnegatedConsequent
  unfold contextualEqualitySymmetryStructuralPayloadBound
    arbitraryContextEqualitySymmetryLocalEnvelope
  dsimp only [formulaBound, antecedent, consequent, implication] at *
  omega

def valuationAtomicContextCodePolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  valuationContextFormulaCodeSumEnvelope 1 numericBound termCodeBound

def valuationAtomicTermCodePolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  valuationTermShortNumeralCodePolynomial numericBound termCodeBound +
    termCodeBound + 1

def valuationAtomicSourcePayloadPolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  8 * cumulativeAtomicPrimitiveEnvelope
    (2 * valuationTermValueWidthPolynomial numericBound termCodeBound + 5)

def compilePositiveRelationFixedPayloadPolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  let contextBound := valuationAtomicContextCodePolynomial
    numericBound termCodeBound
  let relationTermBound := valuationAtomicTermCodePolynomial
    numericBound termCodeBound
  let formulaBound := arbitraryContextRelationFormulaEnvelope
    contextBound relationTermBound
  let equalityBound := compileTermValueEqualityFixedPayloadPolynomial
    numericBound termCodeBound
  2 * equalityBound +
    valuationAtomicSourcePayloadPolynomial numericBound termCodeBound +
    arbitraryContextRelationTransportLocalEnvelope contextBound
      relationTermBound +
    4 * smallContextAssemblyEnvelope formulaBound + 1

private theorem valuation_le_of_mem_subset_singleton
    (valuation : Nat -> Nat) (numericBound : Nat) (vars : Finset Nat)
    (hvars : vars ⊆ {0}) (hzero : valuation 0 <= numericBound) :
    forall index, index ∈ vars -> valuation index <= numericBound := by
  intro index hindex
  have hsingleton := hvars hindex
  simp only [Finset.mem_singleton] at hsingleton
  subst index
  exact hzero

private theorem binaryRelationVariables_subset_singleton
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm)
    (hfirst : (args 0).freeVariables ⊆ {0})
    (hsecond : (args 1).freeVariables ⊆ {0}) :
    (LO.FirstOrder.Semiformula.rel relationSymbol args).freeVariables ⊆
      {0} := by
  intro index hindex
  rw [LO.FirstOrder.Semiformula.freeVariables_rel] at hindex
  rcases Finset.mem_biUnion.mp hindex with ⟨coordinate, _, hcoordinate⟩
  cases coordinate using Fin.cases with
  | zero => exact hfirst hcoordinate
  | succ coordinate =>
      cases coordinate using Fin.cases with
      | zero => exact hsecond hcoordinate
      | succ coordinate => exact Fin.elim0 coordinate

private theorem binaryRelationVariableTermCode_le
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm) (termCodeBound : Nat)
    (hfirstCode : (binaryTermCode (args 0)).length <= termCodeBound)
    (hsecondCode : (binaryTermCode (args 1)).length <= termCodeBound) :
    forall index,
      index ∈ (LO.FirstOrder.Semiformula.rel relationSymbol args).freeVariables ->
      (binaryTermCode (&index : ValuationTerm)).length <= termCodeBound := by
  intro index hindex
  rw [LO.FirstOrder.Semiformula.freeVariables_rel] at hindex
  rcases Finset.mem_biUnion.mp hindex with ⟨coordinate, _, hcoordinate⟩
  cases coordinate using Fin.cases with
  | zero =>
      exact (freeVariableTermCode_length_le_termCode_length index
        (args 0) hcoordinate).trans hfirstCode
  | succ coordinate =>
      cases coordinate using Fin.cases with
      | zero =>
          exact (freeVariableTermCode_length_le_termCode_length index
            (args 1) hcoordinate).trans hsecondCode
      | succ coordinate => exact Fin.elim0 coordinate

private theorem termValue_size_le_atomicPolynomial
    (valuation : Nat -> Nat) (numericBound termCodeBound : Nat)
    (term : ValuationTerm)
    (hvalues : forall index, index ∈ term.freeVariables ->
      valuation index <= numericBound)
    (hcode : (binaryTermCode term).length <= termCodeBound) :
    Nat.size (termValue valuation term) <=
      valuationTermValueWidthPolynomial numericBound termCodeBound := by
  have hvalue := termValue_le_valuationTermValueEnvelope valuation
    numericBound term hvalues
  have hsize := Nat.size_le_size hvalue
  exact hsize.trans
    (valuationTermValueEnvelope_size_le_polynomial numericBound termCodeBound
      term hcode)

private theorem positiveRelationSourcePayloadResource_le_fixed
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm)
    (numericBound termCodeBound : Nat)
    (hfirstValues : forall index, index ∈ (args 0).freeVariables ->
      valuation index <= numericBound)
    (hsecondValues : forall index, index ∈ (args 1).freeVariables ->
      valuation index <= numericBound)
    (hfirstCode : (binaryTermCode (args 0)).length <= termCodeBound)
    (hsecondCode : (binaryTermCode (args 1)).length <= termCodeBound) :
    positiveRelationSourcePayloadResource valuation relationSymbol args <=
      valuationAtomicSourcePayloadPolynomial numericBound termCodeBound := by
  have hfirstSize := termValue_size_le_atomicPolynomial valuation
    numericBound termCodeBound (args 0) hfirstValues hfirstCode
  have hsecondSize := termValue_size_le_atomicPolynomial valuation
    numericBound termCodeBound (args 1) hsecondValues hsecondCode
  cases relationSymbol with
  | eq =>
      let literal : ClosedPAAtomicLiteral :=
        .equality (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1)))
      have huniform := payloadPolynomial_le_uniform literal
      have hresource :
          FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight
              literal <=
            2 * valuationTermValueWidthPolynomial numericBound termCodeBound +
              5 := by
        simp only [literal,
          FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight,
          FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.resourceWeight,
          ClosedPATerm.nodeCount, ClosedPATerm.leafBitWeight]
        omega
      have hcumulative := cumulativeAtomicPrimitiveEnvelope_mono hresource
      unfold FoundationCompactPABoundedUniversalPolynomialBounds.ClosedPAAtomicLiteralBounds.uniformPayloadPolynomial at huniform
      have htotal := huniform.trans (Nat.mul_le_mul_left 8 hcumulative)
      simpa only [positiveRelationSourcePayloadResource,
        valuationAtomicSourcePayloadPolynomial, literal] using htotal
  | lt =>
      let literal : ClosedPAAtomicLiteral :=
        .lessThan (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1)))
      have huniform := payloadPolynomial_le_uniform literal
      have hresource :
          FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight
              literal <=
            2 * valuationTermValueWidthPolynomial numericBound termCodeBound +
              5 := by
        simp only [literal,
          FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight,
          FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.resourceWeight,
          ClosedPATerm.nodeCount, ClosedPATerm.leafBitWeight]
        omega
      have hcumulative := cumulativeAtomicPrimitiveEnvelope_mono hresource
      unfold FoundationCompactPABoundedUniversalPolynomialBounds.ClosedPAAtomicLiteralBounds.uniformPayloadPolynomial at huniform
      have htotal := huniform.trans (Nat.mul_le_mul_left 8 hcumulative)
      simpa only [positiveRelationSourcePayloadResource,
        valuationAtomicSourcePayloadPolynomial, literal] using htotal

private theorem negativeRelationSourcePayloadResource_le_fixed
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm)
    (numericBound termCodeBound : Nat)
    (hfirstValues : forall index, index ∈ (args 0).freeVariables ->
      valuation index <= numericBound)
    (hsecondValues : forall index, index ∈ (args 1).freeVariables ->
      valuation index <= numericBound)
    (hfirstCode : (binaryTermCode (args 0)).length <= termCodeBound)
    (hsecondCode : (binaryTermCode (args 1)).length <= termCodeBound) :
    negativeRelationSourcePayloadResource valuation relationSymbol args <=
      valuationAtomicSourcePayloadPolynomial numericBound termCodeBound := by
  have hfirstSize := termValue_size_le_atomicPolynomial valuation
    numericBound termCodeBound (args 0) hfirstValues hfirstCode
  have hsecondSize := termValue_size_le_atomicPolynomial valuation
    numericBound termCodeBound (args 1) hsecondValues hsecondCode
  cases relationSymbol with
  | eq =>
      let literal : ClosedPAAtomicLiteral :=
        .disequality (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1)))
      have huniform := payloadPolynomial_le_uniform literal
      have hresource :
          FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight
              literal <=
            2 * valuationTermValueWidthPolynomial numericBound termCodeBound +
              5 := by
        simp only [literal,
          FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight,
          FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.resourceWeight,
          ClosedPATerm.nodeCount, ClosedPATerm.leafBitWeight]
        omega
      have hcumulative := cumulativeAtomicPrimitiveEnvelope_mono hresource
      unfold FoundationCompactPABoundedUniversalPolynomialBounds.ClosedPAAtomicLiteralBounds.uniformPayloadPolynomial at huniform
      have htotal := huniform.trans (Nat.mul_le_mul_left 8 hcumulative)
      simpa only [negativeRelationSourcePayloadResource,
        valuationAtomicSourcePayloadPolynomial, literal] using htotal
  | lt =>
      let literal : ClosedPAAtomicLiteral :=
        .notLessThan (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1)))
      have huniform := payloadPolynomial_le_uniform literal
      have hresource :
          FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight
              literal <=
            2 * valuationTermValueWidthPolynomial numericBound termCodeBound +
              5 := by
        simp only [literal,
          FoundationCompactPABoundedUniversalCertificateCode.ClosedPAAtomicLiteral.resourceWeight,
          FoundationCompactPABoundedUniversalCertificateCode.ClosedPATerm.resourceWeight,
          ClosedPATerm.nodeCount, ClosedPATerm.leafBitWeight]
        omega
      have hcumulative := cumulativeAtomicPrimitiveEnvelope_mono hresource
      unfold FoundationCompactPABoundedUniversalPolynomialBounds.ClosedPAAtomicLiteralBounds.uniformPayloadPolynomial at huniform
      have htotal := huniform.trans (Nat.mul_le_mul_left 8 hcumulative)
      simpa only [negativeRelationSourcePayloadResource,
        valuationAtomicSourcePayloadPolynomial, literal] using htotal

theorem compilePositiveRelationPayloadPolynomial_le_fixed_of_values
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm)
    (numericBound termCodeBound : Nat)
    (hfirst : (args 0).freeVariables ⊆ {0})
    (hsecond : (args 1).freeVariables ⊆ {0})
    (hfirstValues : forall index, index ∈ (args 0).freeVariables ->
      valuation index <= numericBound)
    (hsecondValues : forall index, index ∈ (args 1).freeVariables ->
      valuation index <= numericBound)
    (hfirstCode : (binaryTermCode (args 0)).length <= termCodeBound)
    (hsecondCode : (binaryTermCode (args 1)).length <= termCodeBound) :
    compilePositiveRelationPayloadPolynomial valuation relationSymbol args <=
      compilePositiveRelationFixedPayloadPolynomial numericBound
        termCodeBound := by
  let vars := (LO.FirstOrder.Semiformula.rel relationSymbol args).freeVariables
  let Gamma := valuationContext vars valuation
  let contextBound := valuationAtomicContextCodePolynomial
    numericBound termCodeBound
  let relationTermBound := valuationAtomicTermCodePolynomial
    numericBound termCodeBound
  let formulaBound := arbitraryContextRelationFormulaEnvelope
    contextBound relationTermBound
  let equalityBound := compileTermValueEqualityFixedPayloadPolynomial
    numericBound termCodeBound
  let firstTerm := shortBinaryNumeralTerm (termValue valuation (args 0))
  let secondTerm := shortBinaryNumeralTerm (termValue valuation (args 1))
  let firstFormula :=
    (“!!firstTerm = !!(args 0)” : LO.FirstOrder.ArithmeticProposition)
  let secondFormula :=
    (“!!secondTerm = !!(args 1)” : LO.FirstOrder.ArithmeticProposition)
  let sourceFormula := binaryRelationFormula relationSymbol firstTerm secondTerm
  let targetFormula := binaryRelationFormula relationSymbol (args 0) (args 1)
  have hfirstCard : (args 0).freeVariables.card <= 4 := by
    exact (Finset.card_le_card hfirst).trans (by simp)
  have hsecondCard : (args 1).freeVariables.card <= 4 := by
    exact (Finset.card_le_card hsecond).trans (by simp)
  have hfirstEqualityCoordinate :=
    compileTermValueEqualityPayloadPolynomial_le_coordinate valuation
      numericBound (args 0) hfirstCard hfirstValues
  have hsecondEqualityCoordinate :=
    compileTermValueEqualityPayloadPolynomial_le_coordinate valuation
      numericBound (args 1) hsecondCard hsecondValues
  have hfirstEqualityFixed :=
    compileTermValueEqualityUniformPayloadPolynomial_le_fixed numericBound
      termCodeBound (args 0) hfirstCard hfirstCode
  have hsecondEqualityFixed :=
    compileTermValueEqualityUniformPayloadPolynomial_le_fixed numericBound
      termCodeBound (args 1) hsecondCard hsecondCode
  have hfirstEquality :
      compileTermValueEqualityPayloadPolynomial valuation (args 0) <=
        equalityBound := hfirstEqualityCoordinate.trans hfirstEqualityFixed
  have hsecondEquality :
      compileTermValueEqualityPayloadPolynomial valuation (args 1) <=
        equalityBound := hsecondEqualityCoordinate.trans hsecondEqualityFixed
  have hvars := binaryRelationVariables_subset_singleton relationSymbol args
    hfirst hsecond
  have hvarsCard : vars.card <= 1 := by
    exact (Finset.card_le_card hvars).trans (by simp)
  have hvarsValues : forall index, index ∈ vars ->
      valuation index <= numericBound := by
    intro index hindex
    dsimp only [vars] at hindex
    rw [LO.FirstOrder.Semiformula.freeVariables_rel] at hindex
    rcases Finset.mem_biUnion.mp hindex with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact hfirstValues index hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact hsecondValues index hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  have hvarsTerms := binaryRelationVariableTermCode_le relationSymbol args
    termCodeBound hfirstCode hsecondCode
  have hcontextSum : formulaCodeSum Gamma <= contextBound := by
    dsimp only [Gamma, vars, contextBound]
    exact valuationContext_formulaCodeSum_le_uniform vars valuation 1
      numericBound termCodeBound hvarsCard hvarsValues hvarsTerms
  have hcontext : FormulaCodeBound Gamma contextBound := by
    intro formula hformula
    exact (formulaCode_le_formulaCodeSum hformula).trans hcontextSum
  have hcontextLarge : FormulaCodeBound Gamma formulaBound := by
    intro formula hformula
    have hsmall := hcontext formula hformula
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega
  have hcontextCard : Gamma.card <= 4 :=
    valuationContext_card_le_four_of_subset_singleton vars valuation hvars
  have hfirstShortRaw := shortNumeralTerm_code_length_le_uniform valuation
    numericBound (args 0) hfirstValues
  have hsecondShortRaw := shortNumeralTerm_code_length_le_uniform valuation
    numericBound (args 1) hsecondValues
  have hfirstShortPoly := valuationTermShortNumeralCodeEnvelope_le_polynomial
    numericBound termCodeBound (args 0) hfirstCode
  have hsecondShortPoly := valuationTermShortNumeralCodeEnvelope_le_polynomial
    numericBound termCodeBound (args 1) hsecondCode
  have hfirstTerm : (binaryTermCode firstTerm).length <= relationTermBound := by
    exact (hfirstShortRaw.trans hfirstShortPoly).trans (by
      unfold relationTermBound valuationAtomicTermCodePolynomial
      omega)
  have hsecondTerm : (binaryTermCode secondTerm).length <= relationTermBound := by
    exact (hsecondShortRaw.trans hsecondShortPoly).trans (by
      unfold relationTermBound valuationAtomicTermCodePolynomial
      omega)
  have hfirstOriginal : (binaryTermCode (args 0)).length <=
      relationTermBound := hfirstCode.trans (by
    unfold relationTermBound valuationAtomicTermCodePolynomial
    omega)
  have hsecondOriginal : (binaryTermCode (args 1)).length <=
      relationTermBound := hsecondCode.trans (by
    unfold relationTermBound valuationAtomicTermCodePolynomial
    omega)
  have hfirstFormulaRaw := equalityFormula_code_le_orderAtomic firstTerm
    (args 0) relationTermBound hfirstTerm hfirstOriginal
  have hsecondFormulaRaw := equalityFormula_code_le_orderAtomic secondTerm
    (args 1) relationTermBound hsecondTerm hsecondOriginal
  have hatomicPrimitive :=
    (orderAtomic_le_derived relationTermBound).trans
      ((orderDerived_le_local relationTermBound).trans
        (orderLocal_le_primitive relationTermBound))
  have hfirstFormula : (binaryFormulaCode firstFormula).length <=
      formulaBound := (hfirstFormulaRaw.trans hatomicPrimitive).trans (by
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega)
  have hsecondFormula : (binaryFormulaCode secondFormula).length <=
      formulaBound := (hsecondFormulaRaw.trans hatomicPrimitive).trans (by
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega)
  have hsourceFormulaRaw := binaryRelationFormula_code_le_orderAtomic
    relationSymbol firstTerm secondTerm relationTermBound hfirstTerm hsecondTerm
  have htargetFormulaRaw := binaryRelationFormula_code_le_orderAtomic
    relationSymbol (args 0) (args 1) relationTermBound hfirstOriginal
      hsecondOriginal
  have hsourceFormula : (binaryFormulaCode sourceFormula).length <=
      formulaBound := (hsourceFormulaRaw.trans hatomicPrimitive).trans (by
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega)
  have htargetFormula : (binaryFormulaCode targetFormula).length <=
      formulaBound := (htargetFormulaRaw.trans hatomicPrimitive).trans (by
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega)
  have hsourceFormulaTight : (binaryFormulaCode sourceFormula).length <=
      orderPrimitiveFormulaCodeEnvelope relationTermBound := by
    dsimp only [sourceFormula]
    exact hsourceFormulaRaw.trans hatomicPrimitive
  have htargetFormulaTight : (binaryFormulaCode targetFormula).length <=
      orderPrimitiveFormulaCodeEnvelope relationTermBound := by
    dsimp only [targetFormula]
    exact htargetFormulaRaw.trans hatomicPrimitive
  have himplicationRaw := binaryFormulaCode_implication_length_le
    sourceFormula targetFormula
  have htagFive : (binaryNatCode 5).length <= 8 := by decide
  have himplicationTight :
      (binaryFormulaCode (sourceFormula 🡒 targetFormula)).length <=
        4 * orderPrimitiveFormulaCodeEnvelope relationTermBound + 8 := by
    omega
  have himplication : (binaryFormulaCode (sourceFormula 🡒 targetFormula)).length <=
      formulaBound := by
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega
  have hnegatedImplicationRaw := binaryFormulaCode_neg_length_le
    (sourceFormula 🡒 targetFormula)
  have hnegatedTargetRaw := binaryFormulaCode_neg_length_le targetFormula
  have hnegatedImplication :
      (binaryFormulaCode (∼(sourceFormula 🡒 targetFormula))).length <=
        formulaBound := by
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega
  have hnegatedTarget : (binaryFormulaCode (∼targetFormula)).length <=
      formulaBound := by
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega
  have hfirstInsertContext := hcontextLarge.insert hfirstFormula
  have hsecondInsertContext := hcontextLarge.insert hsecondFormula
  have hsourceInsertContext := hcontextLarge.insert hsourceFormula
  have hfirstInsertCard : (insert firstFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le firstFormula Gamma
    omega
  have hsecondInsertCard : (insert secondFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le secondFormula Gamma
    omega
  have hsourceInsertCard : (insert sourceFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le sourceFormula Gamma
    omega
  have hweakFirst := weakeningFullAssemblyCost_le_small
    (insert firstFormula Gamma) formulaBound hfirstInsertCard
      hfirstInsertContext
  have hweakSecond := weakeningFullAssemblyCost_le_small
    (insert secondFormula Gamma) formulaBound hsecondInsertCard
      hsecondInsertContext
  have hweakSource := weakeningFullAssemblyCost_le_small
    (insert sourceFormula Gamma) formulaBound hsourceInsertCard
      hsourceInsertContext
  have htransport :=
    relationTransportImplicationStructuralPayloadBound_le_arbitraryContext
      Gamma relationSymbol firstTerm secondTerm (args 0) (args 1)
      (compileTermValueEqualityPayloadPolynomial valuation (args 0) +
        weakeningFullAssemblyCost (insert firstFormula Gamma))
      (compileTermValueEqualityPayloadPolynomial valuation (args 1) +
        weakeningFullAssemblyCost (insert secondFormula Gamma))
      contextBound relationTermBound hcontextCard hcontext hfirstTerm
      hsecondTerm hfirstOriginal hsecondOriginal
  have hsource := positiveRelationSourcePayloadResource_le_fixed valuation
    relationSymbol args numericBound termCodeBound hfirstValues hsecondValues
    hfirstCode hsecondCode
  have hmp := contextualModusPonensFullAssemblyCost_le_small Gamma
    sourceFormula targetFormula formulaBound hcontextCard hcontextLarge
    hsourceFormula htargetFormula himplication hnegatedImplication
    hnegatedTarget
  unfold compilePositiveRelationPayloadPolynomial
    compilePositiveRelationFixedPayloadPolynomial
  dsimp only [vars, Gamma, contextBound, relationTermBound, formulaBound,
    equalityBound, firstTerm, secondTerm, firstFormula, secondFormula,
    sourceFormula, targetFormula] at *
  omega

theorem compilePositiveRelationPayloadResource_le_fixed_of_closed
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (first second : ValuationTerm)
    (numericBound termCodeBound : Nat)
    (hfirstClosed : first.freeVariables = ∅)
    (hsecondClosed : second.freeVariables = ∅)
    (hfirstCode : (binaryTermCode first).length <= termCodeBound)
    (hsecondCode : (binaryTermCode second).length <= termCodeBound) :
    compilePositiveRelationPayloadResource valuation relationSymbol
        ![first, second] <=
      compilePositiveRelationFixedPayloadPolynomial numericBound
        termCodeBound := by
  have hfirstSubset : first.freeVariables ⊆ {0} := by
    rw [hfirstClosed]
    simp
  have hsecondSubset : second.freeVariables ⊆ {0} := by
    rw [hsecondClosed]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    valuation relationSymbol ![first, second] hfirstSubset hsecondSubset
  have hfixed :=
    compilePositiveRelationPayloadPolynomial_le_fixed_of_values valuation
      relationSymbol ![first, second] numericBound termCodeBound hfirstSubset
      hsecondSubset (by
        intro index hindex
        change index ∈ first.freeVariables at hindex
        rw [hfirstClosed] at hindex
        simp at hindex)
      (by
        intro index hindex
        change index ∈ second.freeVariables at hindex
        rw [hsecondClosed] at hindex
        simp at hindex)
      hfirstCode hsecondCode
  exact hpublic.trans hfixed

theorem compilePositiveRelationPayloadPolynomial_le_fixed
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm)
    (numericBound termCodeBound : Nat)
    (hfirst : (args 0).freeVariables ⊆ {0})
    (hsecond : (args 1).freeVariables ⊆ {0})
    (hzero : valuation 0 <= numericBound)
    (hfirstCode : (binaryTermCode (args 0)).length <= termCodeBound)
    (hsecondCode : (binaryTermCode (args 1)).length <= termCodeBound) :
    compilePositiveRelationPayloadPolynomial valuation relationSymbol args <=
      compilePositiveRelationFixedPayloadPolynomial numericBound
        termCodeBound := by
  exact compilePositiveRelationPayloadPolynomial_le_fixed_of_values valuation
    relationSymbol args numericBound termCodeBound hfirst hsecond
    (valuation_le_of_mem_subset_singleton valuation numericBound
      (args 0).freeVariables hfirst hzero)
    (valuation_le_of_mem_subset_singleton valuation numericBound
      (args 1).freeVariables hsecond hzero)
    hfirstCode hsecondCode

def compileNegativeRelationFixedPayloadPolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  let contextBound := valuationAtomicContextCodePolynomial
    numericBound termCodeBound
  let relationTermBound := valuationAtomicTermCodePolynomial
    numericBound termCodeBound
  let formulaBound := arbitraryContextRelationFormulaEnvelope
    contextBound relationTermBound
  let equalityBound := compileTermValueEqualityFixedPayloadPolynomial
    numericBound termCodeBound
  let assemblyBound := smallContextAssemblyEnvelope formulaBound
  let forwardBound := equalityBound + assemblyBound
  let reverseBound := forwardBound +
    arbitraryContextEqualitySymmetryLocalEnvelope contextBound
      relationTermBound
  2 * reverseBound +
    arbitraryContextRelationTransportLocalEnvelope contextBound
      relationTermBound +
    valuationAtomicSourcePayloadPolynomial numericBound termCodeBound +
    3 * assemblyBound + 1

theorem compileNegativeRelationPayloadResource_le_fixed_of_closed
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (first second : ValuationTerm)
    (numericBound termCodeBound : Nat)
    (hfirstClosed : first.freeVariables = ∅)
    (hsecondClosed : second.freeVariables = ∅)
    (hfirstCode : (binaryTermCode first).length <= termCodeBound)
    (hsecondCode : (binaryTermCode second).length <= termCodeBound) :
    compileNegativeRelationPayloadResource valuation relationSymbol
        ![first, second] <=
      compileNegativeRelationFixedPayloadPolynomial numericBound
        termCodeBound := by
  let args : Fin 2 -> ValuationTerm := ![first, second]
  let vars :=
    (LO.FirstOrder.Semiformula.nrel relationSymbol args).freeVariables
  let Gamma := valuationContext vars valuation
  let contextBound := valuationAtomicContextCodePolynomial
    numericBound termCodeBound
  let relationTermBound := valuationAtomicTermCodePolynomial
    numericBound termCodeBound
  let formulaBound := arbitraryContextRelationFormulaEnvelope
    contextBound relationTermBound
  let equalityBound := compileTermValueEqualityFixedPayloadPolynomial
    numericBound termCodeBound
  let assemblyBound := smallContextAssemblyEnvelope formulaBound
  let forwardBound := equalityBound + assemblyBound
  let reverseBound := forwardBound +
    arbitraryContextEqualitySymmetryLocalEnvelope contextBound
      relationTermBound
  let firstTerm := shortBinaryNumeralTerm (termValue valuation first)
  let secondTerm := shortBinaryNumeralTerm (termValue valuation second)
  let firstFormula :=
    (“!!firstTerm = !!first” : LO.FirstOrder.ArithmeticProposition)
  let secondFormula :=
    (“!!secondTerm = !!second” : LO.FirstOrder.ArithmeticProposition)
  let sourceFormula :=
    binaryRelationFormula relationSymbol firstTerm secondTerm
  let targetFormula := binaryRelationFormula relationSymbol first second
  have hfirstSubset : first.freeVariables ⊆ {0} := by
    rw [hfirstClosed]
    simp
  have hsecondSubset : second.freeVariables ⊆ {0} := by
    rw [hsecondClosed]
    simp
  have hfirstValues : forall index, index ∈ first.freeVariables ->
      valuation index <= numericBound := by
    intro index hindex
    rw [hfirstClosed] at hindex
    simp at hindex
  have hsecondValues : forall index, index ∈ second.freeVariables ->
      valuation index <= numericBound := by
    intro index hindex
    rw [hsecondClosed] at hindex
    simp at hindex
  have hfirstCard : first.freeVariables.card <= 4 := by
    rw [hfirstClosed]
    simp
  have hsecondCard : second.freeVariables.card <= 4 := by
    rw [hsecondClosed]
    simp
  have hfirstEqualityCoordinate :=
    compileTermValueEqualityPayloadPolynomial_le_coordinate valuation
      numericBound first hfirstCard hfirstValues
  have hsecondEqualityCoordinate :=
    compileTermValueEqualityPayloadPolynomial_le_coordinate valuation
      numericBound second hsecondCard hsecondValues
  have hfirstEqualityFixed :=
    compileTermValueEqualityUniformPayloadPolynomial_le_fixed numericBound
      termCodeBound first hfirstCard hfirstCode
  have hsecondEqualityFixed :=
    compileTermValueEqualityUniformPayloadPolynomial_le_fixed numericBound
      termCodeBound second hsecondCard hsecondCode
  have hfirstEqualityPolynomial :
      compileTermValueEqualityPayloadPolynomial valuation first <=
        equalityBound :=
    hfirstEqualityCoordinate.trans hfirstEqualityFixed
  have hsecondEqualityPolynomial :
      compileTermValueEqualityPayloadPolynomial valuation second <=
        equalityBound :=
    hsecondEqualityCoordinate.trans hsecondEqualityFixed
  have hfirstEquality :
      compileTermValueEqualityPayloadResource valuation first <=
        equalityBound :=
    (compileTermValueEqualityPayloadResource_le_publicPolynomial valuation
      first hfirstSubset).trans hfirstEqualityPolynomial
  have hsecondEquality :
      compileTermValueEqualityPayloadResource valuation second <=
        equalityBound :=
    (compileTermValueEqualityPayloadResource_le_publicPolynomial valuation
      second hsecondSubset).trans hsecondEqualityPolynomial
  have hvarsEmpty : vars = ∅ := by
    ext index
    simp [vars, args, LO.FirstOrder.Semiformula.freeVariables_nrel,
      Matrix.fun_eq_vec_two, hfirstClosed, hsecondClosed]
  have hGammaEmpty : Gamma = ∅ := by
    simp [Gamma, hvarsEmpty, valuationContext]
  have hcontext : FormulaCodeBound Gamma contextBound := by
    rw [hGammaEmpty]
    intro formula hformula
    simp at hformula
  have hcontextLarge : FormulaCodeBound Gamma formulaBound := by
    intro formula hformula
    have hsmall := hcontext formula hformula
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega
  have hcontextCard : Gamma.card <= 4 := by
    rw [hGammaEmpty]
    simp
  have hfirstShortRaw := shortNumeralTerm_code_length_le_uniform valuation
    numericBound first hfirstValues
  have hsecondShortRaw := shortNumeralTerm_code_length_le_uniform valuation
    numericBound second hsecondValues
  have hfirstShortPoly :=
    valuationTermShortNumeralCodeEnvelope_le_polynomial numericBound
      termCodeBound first hfirstCode
  have hsecondShortPoly :=
    valuationTermShortNumeralCodeEnvelope_le_polynomial numericBound
      termCodeBound second hsecondCode
  have hfirstTerm :
      (binaryTermCode firstTerm).length <= relationTermBound := by
    exact (hfirstShortRaw.trans hfirstShortPoly).trans (by
      unfold relationTermBound valuationAtomicTermCodePolynomial
      omega)
  have hsecondTerm :
      (binaryTermCode secondTerm).length <= relationTermBound := by
    exact (hsecondShortRaw.trans hsecondShortPoly).trans (by
      unfold relationTermBound valuationAtomicTermCodePolynomial
      omega)
  have hfirstOriginal :
      (binaryTermCode first).length <= relationTermBound :=
    hfirstCode.trans (by
      unfold relationTermBound valuationAtomicTermCodePolynomial
      omega)
  have hsecondOriginal :
      (binaryTermCode second).length <= relationTermBound :=
    hsecondCode.trans (by
      unfold relationTermBound valuationAtomicTermCodePolynomial
      omega)
  have hfirstFormulaRaw := equalityFormula_code_le_orderAtomic firstTerm
    first relationTermBound hfirstTerm hfirstOriginal
  have hsecondFormulaRaw := equalityFormula_code_le_orderAtomic secondTerm
    second relationTermBound hsecondTerm hsecondOriginal
  have hatomicPrimitive :=
    (orderAtomic_le_derived relationTermBound).trans
      ((orderDerived_le_local relationTermBound).trans
        (orderLocal_le_primitive relationTermBound))
  have hfirstFormula :
      (binaryFormulaCode firstFormula).length <= formulaBound :=
    (hfirstFormulaRaw.trans hatomicPrimitive).trans (by
      unfold formulaBound arbitraryContextRelationFormulaEnvelope
      omega)
  have hsecondFormula :
      (binaryFormulaCode secondFormula).length <= formulaBound :=
    (hsecondFormulaRaw.trans hatomicPrimitive).trans (by
      unfold formulaBound arbitraryContextRelationFormulaEnvelope
      omega)
  have hsourceFormulaRaw := binaryRelationFormula_code_le_orderAtomic
    relationSymbol firstTerm secondTerm relationTermBound hfirstTerm
      hsecondTerm
  have htargetFormulaRaw := binaryRelationFormula_code_le_orderAtomic
    relationSymbol first second relationTermBound hfirstOriginal
      hsecondOriginal
  have hsourceFormula :
      (binaryFormulaCode sourceFormula).length <= formulaBound :=
    (hsourceFormulaRaw.trans hatomicPrimitive).trans (by
      unfold formulaBound arbitraryContextRelationFormulaEnvelope
      omega)
  have htargetFormula :
      (binaryFormulaCode targetFormula).length <= formulaBound :=
    (htargetFormulaRaw.trans hatomicPrimitive).trans (by
      unfold formulaBound arbitraryContextRelationFormulaEnvelope
      omega)
  have hsourceFormulaTight :
      (binaryFormulaCode sourceFormula).length <=
        orderPrimitiveFormulaCodeEnvelope relationTermBound :=
    hsourceFormulaRaw.trans hatomicPrimitive
  have htargetFormulaTight :
      (binaryFormulaCode targetFormula).length <=
        orderPrimitiveFormulaCodeEnvelope relationTermBound :=
    htargetFormulaRaw.trans hatomicPrimitive
  have hnegatedSourceRaw := binaryFormulaCode_neg_length_le sourceFormula
  have hnegatedTargetRaw := binaryFormulaCode_neg_length_le targetFormula
  have hnegatedSource :
      (binaryFormulaCode (∼sourceFormula)).length <= formulaBound := by
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega
  have hnegatedTarget :
      (binaryFormulaCode (∼targetFormula)).length <= formulaBound := by
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega
  have himplicationRaw := binaryFormulaCode_implication_length_le
    targetFormula sourceFormula
  have htagFive : (binaryNatCode 5).length <= 8 := by decide
  have himplicationTight :
      (binaryFormulaCode (targetFormula 🡒 sourceFormula)).length <=
        3 * orderPrimitiveFormulaCodeEnvelope relationTermBound + 8 := by
    omega
  have himplication :
      (binaryFormulaCode (targetFormula 🡒 sourceFormula)).length <=
        formulaBound := by
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega
  have hnegatedImplicationRaw := binaryFormulaCode_neg_length_le
    (targetFormula 🡒 sourceFormula)
  have hnegatedImplication :
      (binaryFormulaCode (∼(targetFormula 🡒 sourceFormula))).length <=
        formulaBound := by
    unfold formulaBound arbitraryContextRelationFormulaEnvelope
    omega
  have hfirstInsertContext := hcontextLarge.insert hfirstFormula
  have hsecondInsertContext := hcontextLarge.insert hsecondFormula
  have hsourceInsertContext := hcontextLarge.insert hnegatedSource
  have hfirstInsertCard : (insert firstFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le firstFormula Gamma
    omega
  have hsecondInsertCard : (insert secondFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le secondFormula Gamma
    omega
  have hsourceInsertCard : (insert (∼sourceFormula) Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le (∼sourceFormula) Gamma
    omega
  have hweakFirst := weakeningFullAssemblyCost_le_small
    (insert firstFormula Gamma) formulaBound hfirstInsertCard
      hfirstInsertContext
  have hweakSecond := weakeningFullAssemblyCost_le_small
    (insert secondFormula Gamma) formulaBound hsecondInsertCard
      hsecondInsertContext
  have hweakSource := weakeningFullAssemblyCost_le_small
    (insert (∼sourceFormula) Gamma) formulaBound hsourceInsertCard
      hsourceInsertContext
  have hfirstForward :
      compileTermValueEqualityPayloadResource valuation first +
          weakeningFullAssemblyCost (insert firstFormula Gamma) <=
        forwardBound := by
    dsimp only [forwardBound, assemblyBound]
    omega
  have hsecondForward :
      compileTermValueEqualityPayloadResource valuation second +
          weakeningFullAssemblyCost (insert secondFormula Gamma) <=
        forwardBound := by
    dsimp only [forwardBound, assemblyBound]
    omega
  have hfirstReverseRaw :=
    contextualEqualitySymmetryStructuralPayloadBound_le_arbitraryContext
      Gamma firstTerm first
      (compileTermValueEqualityPayloadResource valuation first +
        weakeningFullAssemblyCost (insert firstFormula Gamma))
      contextBound relationTermBound hcontextCard hcontext hfirstTerm
      hfirstOriginal
  have hsecondReverseRaw :=
    contextualEqualitySymmetryStructuralPayloadBound_le_arbitraryContext
      Gamma secondTerm second
      (compileTermValueEqualityPayloadResource valuation second +
        weakeningFullAssemblyCost (insert secondFormula Gamma))
      contextBound relationTermBound hcontextCard hcontext hsecondTerm
      hsecondOriginal
  have hfirstReverse :
      contextualEqualitySymmetryStructuralPayloadBound Gamma firstTerm first
          (compileTermValueEqualityPayloadResource valuation first +
            weakeningFullAssemblyCost (insert firstFormula Gamma)) <=
        reverseBound := by
    dsimp only [reverseBound]
    omega
  have hsecondReverse :
      contextualEqualitySymmetryStructuralPayloadBound Gamma secondTerm second
          (compileTermValueEqualityPayloadResource valuation second +
            weakeningFullAssemblyCost (insert secondFormula Gamma)) <=
        reverseBound := by
    dsimp only [reverseBound]
    omega
  have htransportRaw :=
    relationTransportImplicationStructuralPayloadBound_le_arbitraryContext
      Gamma relationSymbol first second firstTerm secondTerm
      (contextualEqualitySymmetryStructuralPayloadBound Gamma firstTerm first
        (compileTermValueEqualityPayloadResource valuation first +
          weakeningFullAssemblyCost (insert firstFormula Gamma)))
      (contextualEqualitySymmetryStructuralPayloadBound Gamma secondTerm second
        (compileTermValueEqualityPayloadResource valuation second +
          weakeningFullAssemblyCost (insert secondFormula Gamma)))
      contextBound relationTermBound hcontextCard hcontext hfirstOriginal
      hsecondOriginal hfirstTerm hsecondTerm
  have hsource :=
    negativeRelationSourcePayloadResource_le_fixed valuation relationSymbol
      args numericBound termCodeBound (by
        intro index hindex
        change index ∈ first.freeVariables at hindex
        exact hfirstValues index hindex)
      (by
        intro index hindex
        change index ∈ second.freeVariables at hindex
        exact hsecondValues index hindex)
      (by simpa [args, Matrix.fun_eq_vec_two] using hfirstCode)
      (by simpa [args, Matrix.fun_eq_vec_two] using hsecondCode)
  have hmt := modusTollensFullAssemblyCost_le_small Gamma targetFormula
    sourceFormula formulaBound hcontextCard hcontextLarge htargetFormula
    hsourceFormula himplication hnegatedImplication hnegatedTarget
    hnegatedSource
  unfold compileNegativeRelationPayloadResource
    compileNegativeRelationFixedPayloadPolynomial
  dsimp only [args, vars, Gamma, contextBound, relationTermBound, formulaBound,
    equalityBound, assemblyBound, forwardBound, reverseBound, firstTerm,
    secondTerm, firstFormula, secondFormula, sourceFormula, targetFormula] at *
  simp [Matrix.fun_eq_vec_two] at *
  omega

#print axioms
  relationTransportImplicationStructuralPayloadBound_le_arbitraryContext
#print axioms
  contextualEqualitySymmetryStructuralPayloadBound_le_arbitraryContext
#print axioms positiveRelationSourcePayloadResource_le_fixed
#print axioms negativeRelationSourcePayloadResource_le_fixed
#print axioms compilePositiveRelationPayloadPolynomial_le_fixed_of_values
#print axioms compilePositiveRelationPayloadResource_le_fixed_of_closed
#print axioms compilePositiveRelationPayloadPolynomial_le_fixed
#print axioms compileNegativeRelationPayloadResource_le_fixed_of_closed

end FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
