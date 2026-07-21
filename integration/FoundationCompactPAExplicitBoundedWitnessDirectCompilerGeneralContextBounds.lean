import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds

/-!
# General context bounds for direct bounded-witness compilation

The complete formula-code sum controls both the number and the size of formulas
in a finite context.  This removes the fixed context-cardinality premise from
the quantitative bounded-witness compiler.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPANegativeEqualityBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactSyntaxTransformationBounds
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABoundedWitnessGuardCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitWitnessExsClosureBuilder
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds

def generalContextCoordinate (resource : Nat) : Nat :=
  4 * resource + 4

def generalSequentCodeEnvelope (resource : Nat) : Nat :=
  (binaryNatCode (generalContextCoordinate resource)).length +
    generalContextCoordinate resource * generalContextCoordinate resource

def generalContextAssemblyEnvelope (resource : Nat) : Nat :=
  4096 + 32 * generalSequentCodeEnvelope resource +
    32 * generalContextCoordinate resource

theorem formulaCodeSum_card_le
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition) :
    Gamma.card <= formulaCodeSum Gamma := by
  rw [Finset.card_eq_sum_ones]
  unfold formulaCodeSum
  apply Finset.sum_le_sum
  intro formula hformula
  exact (one_le_formulaSymbolCount formula).trans
    (formulaSymbolCount_le_binaryFormulaCode_length formula)

theorem formulaCodeSum_insert_le
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition) :
    formulaCodeSum (insert formula Gamma) <=
      (binaryFormulaCode formula).length + formulaCodeSum Gamma := by
  unfold formulaCodeSum
  by_cases hformula : formula ∈ Gamma
  · rw [Finset.insert_eq_of_mem hformula]
    omega
  · rw [Finset.sum_insert hformula]

theorem formulaCodeSum_insert_insert_le
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (first second : LO.FirstOrder.ArithmeticProposition) :
    formulaCodeSum (insert first (insert second Gamma)) <=
      (binaryFormulaCode first).length +
        (binaryFormulaCode second).length + formulaCodeSum Gamma := by
  calc
    formulaCodeSum (insert first (insert second Gamma)) <=
        (binaryFormulaCode first).length +
          formulaCodeSum (insert second Gamma) :=
      formulaCodeSum_insert_le _ _
    _ <=
        (binaryFormulaCode first).length +
          ((binaryFormulaCode second).length + formulaCodeSum Gamma) :=
      Nat.add_le_add_left (formulaCodeSum_insert_le _ _) _
    _ = _ := by omega

theorem binarySequentCode_length_le_general
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (hsum : formulaCodeSum Gamma <= generalContextCoordinate resource) :
    (binarySequentCode Gamma).length <=
      generalSequentCodeEnvelope resource := by
  have hcard : Gamma.card <= generalContextCoordinate resource :=
    (formulaCodeSum_card_le Gamma).trans hsum
  have hformula : ∀ formula ∈ Gamma,
      (binaryFormulaCode formula).length <=
        generalContextCoordinate resource := by
    intro formula hformula
    exact (formulaCode_le_formulaCodeSum hformula).trans hsum
  exact binarySequentCode_length_le_uniform Gamma
    (generalContextCoordinate resource) (generalContextCoordinate resource)
    hcard hformula

theorem weakeningFullAssemblyCost_le_general
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (hsum : formulaCodeSum Gamma <= generalContextCoordinate resource) :
    weakeningFullAssemblyCost Gamma <=
      generalContextAssemblyEnvelope resource := by
  have hsequent := binarySequentCode_length_le_general Gamma resource hsum
  have htag : (binaryNatCode 7).length <= 32 := by decide
  unfold weakeningFullAssemblyCost generalContextAssemblyEnvelope
  omega

theorem conjunctionFullAssemblyCost_le_general
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (left right : LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (hresource : 1 <= resource)
    (hGamma : formulaCodeSum Gamma <= resource)
    (hleft : (binaryFormulaCode left).length <= resource)
    (hright : (binaryFormulaCode right).length <= resource)
    (hconjunction :
      (binaryFormulaCode (left ⋏ right)).length <= resource) :
    conjunctionFullAssemblyCost Gamma left right <=
      generalContextAssemblyEnvelope resource := by
  have hrootSum :
      formulaCodeSum (insert (left ⋏ right) Gamma) <=
        generalContextCoordinate resource := by
    have hraw := formulaCodeSum_insert_le Gamma (left ⋏ right)
    unfold generalContextCoordinate
    omega
  have hleftSum :
      formulaCodeSum (insert left (insert (left ⋏ right) Gamma)) <=
        generalContextCoordinate resource := by
    have hraw := formulaCodeSum_insert_insert_le Gamma left (left ⋏ right)
    unfold generalContextCoordinate
    omega
  have hrightSum :
      formulaCodeSum (insert right (insert (left ⋏ right) Gamma)) <=
        generalContextCoordinate resource := by
    have hraw := formulaCodeSum_insert_insert_le Gamma right (left ⋏ right)
    unfold generalContextCoordinate
    omega
  have hroot := binarySequentCode_length_le_general
    (insert (left ⋏ right) Gamma) resource hrootSum
  have hleftSequent := binarySequentCode_length_le_general
    (insert left (insert (left ⋏ right) Gamma)) resource hleftSum
  have hrightSequent := binarySequentCode_length_le_general
    (insert right (insert (left ⋏ right) Gamma)) resource hrightSum
  have hcoordinate : resource <= generalContextCoordinate resource := by
    unfold generalContextCoordinate
    omega
  have htag3 : (binaryNatCode 3).length <= 32 := by decide
  have htag7 : (binaryNatCode 7).length <= 32 := by decide
  simp only [conjunctionFullAssemblyCost, conjunctionDerivationCost]
  unfold generalContextAssemblyEnvelope
  omega

theorem existsIntroFullAssemblyCost_le_general
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (resource : Nat)
    (hresource : 1 <= resource)
    (hGamma : formulaCodeSum Gamma <= resource)
    (hformula : (binaryFormulaCode formula).length <= resource)
    (hwitness : (binaryTermCode witness).length <= resource)
    (hinstantiated :
      (binaryFormulaCode (formula/[witness])).length <= resource)
    (hexistential :
      (binaryFormulaCode (∃⁰ formula :
        LO.FirstOrder.ArithmeticProposition)).length <= resource) :
    existsIntroFullAssemblyCost Gamma formula witness <=
      generalContextAssemblyEnvelope resource := by
  have hrootSum : formulaCodeSum
      (insert (∃⁰ formula : LO.FirstOrder.ArithmeticProposition) Gamma) <=
      generalContextCoordinate resource := by
    have hraw := formulaCodeSum_insert_le Gamma
      (∃⁰ formula : LO.FirstOrder.ArithmeticProposition)
    unfold generalContextCoordinate
    omega
  have hpremiseSum :
      formulaCodeSum (insert (formula/[witness])
        (insert (∃⁰ formula : LO.FirstOrder.ArithmeticProposition) Gamma)) <=
        generalContextCoordinate resource := by
    have hraw := formulaCodeSum_insert_insert_le
      Gamma (formula/[witness])
        (∃⁰ formula : LO.FirstOrder.ArithmeticProposition)
    unfold generalContextCoordinate
    omega
  have hroot := binarySequentCode_length_le_general
    (insert (∃⁰ formula : LO.FirstOrder.ArithmeticProposition) Gamma)
    resource hrootSum
  have hpremise := binarySequentCode_length_le_general
    (insert (formula/[witness])
      (insert (∃⁰ formula : LO.FirstOrder.ArithmeticProposition) Gamma))
    resource hpremiseSum
  have hcoordinate : resource <= generalContextCoordinate resource := by
    unfold generalContextCoordinate
    omega
  have htag6 : (binaryNatCode 6).length <= 32 := by decide
  have htag7 : (binaryNatCode 7).length <= 32 := by decide
  simp only [existsIntroFullAssemblyCost, existsIntroDerivationCost]
  unfold generalContextAssemblyEnvelope
  omega

def explicitBoundedWitnessDirectHeadGeneralPayloadPolynomial
    (valuation : Nat -> Nat) {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat) : Nat :=
  boundedWitnessGuardPayloadPolynomial
      (boundedWitnessGuardBitWidth (values 0) bound) +
    6 * generalContextAssemblyEnvelope
      (explicitBoundedWitnessDirectHeadSyntaxResource
        valuation bound body values)

theorem explicitBoundedWitnessDirectHeadPayloadEnvelope_le_general
    (valuation : Nat -> Nat) {arity : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat) :
    explicitBoundedWitnessDirectHeadPayloadEnvelope
        valuation bound body values <=
      explicitBoundedWitnessDirectHeadGeneralPayloadPolynomial
        valuation bound body values := by
  let witnessBody := explicitWitnessBodyAfterTail body values
  let witnessTerm := shortBinaryNumeralTerm (values 0)
  let guard := boundedWitnessGuardFormula (values 0) bound
  let installedFormula := witnessBody/[witnessTerm]
  let matrix := guard ⋏ installedFormula
  let boundedMatrix : ArithmeticSemiformula Nat 1 :=
    Semiformula.Operator.LT.lt.operator
        ![(#0 : ArithmeticSemiterm Nat 1),
          Rew.bShift ‘!!(shortBinaryNumeralTerm bound) + 1’] ⋏
      witnessBody
  let instantiated := boundedMatrix/[witnessTerm]
  let existential := (∃⁰ boundedMatrix : ValuationFormula)
  let guardContext := valuationContext guard.freeVariables valuation
  let matrixContext := valuationContext matrix.freeVariables valuation
  let existentialContext :=
    valuationContext existential.freeVariables valuation
  let resource := explicitBoundedWitnessDirectHeadSyntaxResource
    valuation bound body values
  have hresource : 1 <= resource := by
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext]
    omega
  have hguardContextSum : formulaCodeSum guardContext <= resource := by
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext]
    omega
  have hmatrixContextSum : formulaCodeSum matrixContext <= resource := by
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext]
    omega
  have hexistentialContextSum :
      formulaCodeSum existentialContext <= resource := by
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext]
    omega
  have hguardCode : (binaryFormulaCode guard).length <= resource := by
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext]
    omega
  have hinstalledCode :
      (binaryFormulaCode installedFormula).length <= resource := by
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext]
    omega
  have hmatrixCode : (binaryFormulaCode matrix).length <= resource := by
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext]
    omega
  have hboundedMatrixCode :
      (binaryFormulaCode boundedMatrix).length <= resource := by
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext]
    omega
  have hinstantiatedCode :
      (binaryFormulaCode instantiated).length <= resource := by
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext]
    omega
  have hexistentialCode :
      (binaryFormulaCode existential).length <= resource := by
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext]
    omega
  have hwitnessCode : (binaryTermCode witnessTerm).length <= resource := by
    dsimp only [resource]
    unfold explicitBoundedWitnessDirectHeadSyntaxResource
    dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
      boundedMatrix, instantiated, existential, guardContext, matrixContext,
      existentialContext]
    omega
  have hguardInsertSum :
      formulaCodeSum (insert guard guardContext) <=
        generalContextCoordinate resource := by
    have hraw := formulaCodeSum_insert_le guardContext guard
    unfold generalContextCoordinate
    omega
  have hmatrixGuardSum :
      formulaCodeSum (insert guard matrixContext) <=
        generalContextCoordinate resource := by
    have hraw := formulaCodeSum_insert_le matrixContext guard
    unfold generalContextCoordinate
    omega
  have hmatrixInstalledSum :
      formulaCodeSum (insert installedFormula matrixContext) <=
        generalContextCoordinate resource := by
    have hraw := formulaCodeSum_insert_le matrixContext installedFormula
    unfold generalContextCoordinate
    omega
  have hexistentialInsertSum :
      formulaCodeSum (insert instantiated existentialContext) <=
        generalContextCoordinate resource := by
    have hraw := formulaCodeSum_insert_le existentialContext instantiated
    unfold generalContextCoordinate
    omega
  have hweakGuard := weakeningFullAssemblyCost_le_general
    (insert guard guardContext) resource hguardInsertSum
  have hweakGuardMatrix := weakeningFullAssemblyCost_le_general
    (insert guard matrixContext) resource hmatrixGuardSum
  have hweakInstalled := weakeningFullAssemblyCost_le_general
    (insert installedFormula matrixContext) resource hmatrixInstalledSum
  have hconjunction := conjunctionFullAssemblyCost_le_general
    matrixContext guard installedFormula resource hresource
    hmatrixContextSum hguardCode hinstalledCode hmatrixCode
  have hweakInstantiated := weakeningFullAssemblyCost_le_general
    (insert instantiated existentialContext) resource
      hexistentialInsertSum
  have hexists := existsIntroFullAssemblyCost_le_general
    existentialContext boundedMatrix witnessTerm resource hresource
    hexistentialContextSum hboundedMatrixCode hwitnessCode
    hinstantiatedCode hexistentialCode
  unfold explicitBoundedWitnessDirectHeadPayloadEnvelope
    explicitBoundedWitnessDirectHeadGeneralPayloadPolynomial
  dsimp only [witnessBody, witnessTerm, guard, installedFormula, matrix,
    boundedMatrix, instantiated, existential, guardContext, matrixContext,
    existentialContext, resource]
    at hweakGuard hweakGuardMatrix hweakInstalled hconjunction
      hweakInstantiated hexists ⊢
  omega

#print axioms formulaCodeSum_card_le
#print axioms binarySequentCode_length_le_general
#print axioms weakeningFullAssemblyCost_le_general
#print axioms conjunctionFullAssemblyCost_le_general
#print axioms existsIntroFullAssemblyCost_le_general
#print axioms explicitBoundedWitnessDirectHeadPayloadEnvelope_le_general

end FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
