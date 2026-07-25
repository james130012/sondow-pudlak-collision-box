import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexContextualBranchesFixedBounds
import integration.FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds

/-!
# Syntax and local assembly bounds for the open-index universal shell

This layer supplies one term-code coordinate, one formula-code coordinate, and
small-context bounds for the contextual discharge and universal-introduction
nodes used by the complete term-bounded universal compiler.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 150000
set_option Elab.async false

namespace FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalShellSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextDischarge
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextUniversalIntroduction
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexContextualBranchesFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalFixedBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds
open FoundationCompactSyntaxTransformationCodeBounds

def fixedWidthOpenIndexUniversalShellTermPolynomial (scale : Nat) : Nat :=
  shiftedBoundFixedTermCodePolynomial scale + 4 * scale +
    (binaryTermCode (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)).length + 1

def fixedWidthOpenIndexUniversalShellRawFormulaPolynomial
    (scale : Nat) : Nat :=
  let termBound := fixedWidthOpenIndexUniversalShellTermPolynomial scale
  fixedWidthOpenIndexUniversalClosedFormulaPolynomial scale +
    shiftedBoundFixedFormulaCodePolynomial scale +
    paFormulaCodeEnvelope termBound +
    (2 * termBound + finiteCaseLessThanFormulaCodeOverhead) +
    fixedWidthOpenIndexUniversalBodyCodePolynomial scale + 1

def fixedWidthOpenIndexUniversalShellSourceFormulaPolynomial
    (scale : Nat) : Nat :=
  16 * fixedWidthOpenIndexUniversalShellRawFormulaPolynomial scale + 128

def fixedWidthOpenIndexUniversalShellFormulaPolynomial
    (scale : Nat) : Nat :=
  64 * fixedWidthOpenIndexUniversalShellSourceFormulaPolynomial scale + 64

def fixedWidthOpenIndexUniversalShellLocalPayloadPolynomial
    (scale : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (fixedWidthOpenIndexUniversalShellFormulaPolynomial scale)

theorem contextualDischargeFullAssemblyCost_le_openIndexUniversalShell
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (hcard : Gamma.card <= 4)
    (hGamma : FormulaCodeBound Gamma resource)
    (hconsequent : (binaryFormulaCode consequent).length <= resource)
    (himplication :
      (binaryFormulaCode (antecedent 🡒 consequent)).length <= resource)
    (hnegatedAntecedent :
      (binaryFormulaCode (∼antecedent)).length <= resource) :
    contextualDischargeFullAssemblyCost Gamma antecedent consequent <=
      smallContextAssemblyEnvelope resource := by
  let implication := contextualImplicationFormula antecedent consequent
  let rootContext := insert implication Gamma
  let premiseContext := contextualDischargePremiseContext Gamma antecedent
    consequent
  have himplicationCode : (binaryFormulaCode implication).length <= resource := by
    simpa only [implication, contextualImplicationFormula] using himplication
  have hrootBound : FormulaCodeBound rootContext resource :=
    hGamma.insert himplicationCode
  have hpremiseBound : FormulaCodeBound premiseContext resource := by
    dsimp only [premiseContext]
    unfold contextualDischargePremiseContext
    exact ((hGamma.insert himplicationCode).insert hconsequent).insert
      hnegatedAntecedent
  have hrootCardTight : rootContext.card <= 5 := by
    have hstep := Finset.card_insert_le implication Gamma
    dsimp only [rootContext]
    omega
  have hrootCard : rootContext.card <= 8 := hrootCardTight.trans (by omega)
  have hpremiseCard : premiseContext.card <= 8 := by
    have hfirst := Finset.card_insert_le
      (contextualImplicationFormula antecedent consequent) Gamma
    have hsecond := Finset.card_insert_le consequent
      (insert (contextualImplicationFormula antecedent consequent) Gamma)
    have hthird := Finset.card_insert_le (∼antecedent)
      (insert consequent
        (insert (contextualImplicationFormula antecedent consequent) Gamma))
    dsimp only [premiseContext]
    unfold contextualDischargePremiseContext
    omega
  have hrootSequent := binarySequentCode_length_le_small rootContext resource
    hrootCard hrootBound
  have hpremiseSequent := binarySequentCode_length_le_small premiseContext
    resource hpremiseCard hpremiseBound
  have htagFour : (binaryNatCode 4).length <= 32 := by decide
  have htagSeven : (binaryNatCode 7).length <= 32 := by decide
  unfold contextualDischargeFullAssemblyCost contextualDischargeDerivationCost
    smallContextAssemblyEnvelope
  dsimp only [rootContext, premiseContext, implication]
    at hrootSequent hpremiseSequent ⊢
  omega

theorem contextualUniversalIntroductionFullAssemblyCost_le_openIndexUniversalShell
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (sourceResource resource : Nat)
    (hcard : Gamma.card <= 4)
    (hGamma : FormulaCodeBound Gamma sourceResource)
    (hbody : (binaryFormulaCode body).length <= resource)
    (hfreeBody : (binaryFormulaCode (Rewriting.free body)).length <= resource)
    (huniversal :
      (binaryFormulaCode
        (∀⁰ body : LO.FirstOrder.ArithmeticProposition)).length <=
          sourceResource)
    (hshift : 2 * sourceResource <= resource) :
    contextualUniversalIntroductionFullAssemblyCost Gamma body <=
      smallContextAssemblyEnvelope resource := by
  let universalFormula := (∀⁰ body : LO.FirstOrder.ArithmeticProposition)
  let rootContext := insert universalFormula Gamma
  let shiftedRoot := rootContext.image Rewriting.shift
  let premiseContext := insert (Rewriting.free body) shiftedRoot
  have hrootBound : FormulaCodeBound rootContext sourceResource :=
    hGamma.insert huniversal
  have hshiftedRootBound : FormulaCodeBound shiftedRoot resource := by
    intro formula hformula
    rcases Finset.mem_image.mp hformula with ⟨source, hsource, rfl⟩
    have hsourceCode := hrootBound source hsource
    exact (binaryFormulaCode_shift_length_le source).trans (by omega)
  have hpremiseBound : FormulaCodeBound premiseContext resource :=
    hshiftedRootBound.insert hfreeBody
  have hrootCardTight : rootContext.card <= 5 := by
    have hstep := Finset.card_insert_le universalFormula Gamma
    dsimp only [rootContext]
    omega
  have hrootCard : rootContext.card <= 8 := hrootCardTight.trans (by omega)
  have hshiftedRootCard : shiftedRoot.card <= 5 := by
    exact Finset.card_image_le.trans hrootCardTight
  have hpremiseCard : premiseContext.card <= 8 := by
    have hstep := Finset.card_insert_le (Rewriting.free body) shiftedRoot
    dsimp only [premiseContext]
    omega
  have hrootSequent := binarySequentCode_length_le_small rootContext resource
    hrootCard (fun formula hformula =>
      (hrootBound formula hformula).trans (by omega))
  have hpremiseSequent := binarySequentCode_length_le_small premiseContext
    resource hpremiseCard hpremiseBound
  have htagFive : (binaryNatCode 5).length <= 32 := by decide
  have htagSeven : (binaryNatCode 7).length <= 32 := by decide
  unfold contextualUniversalIntroductionFullAssemblyCost
    contextualUniversalIntroductionDerivationCost
    contextualUniversalIntroductionPremiseContext smallContextAssemblyEnvelope
  dsimp only [universalFormula, rootContext, shiftedRoot, premiseContext]
    at hrootSequent hpremiseSequent ⊢
  omega

#print axioms contextualDischargeFullAssemblyCost_le_openIndexUniversalShell
#print axioms
  contextualUniversalIntroductionFullAssemblyCost_le_openIndexUniversalShell

end FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalShellSyntaxFixedBounds
