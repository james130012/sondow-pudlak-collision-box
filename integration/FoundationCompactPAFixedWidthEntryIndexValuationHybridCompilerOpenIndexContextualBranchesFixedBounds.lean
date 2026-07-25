import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalFixedBounds

/-!
# Fixed bounds for the contextual finite-branch shell

The bit branches are already scalarized by the imported layer.  This file
charges the surrounding finite exhaustion, lower branch, disjunction
elimination, and closed-assumption cut to the same open-index scale.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option Elab.async false

namespace FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexContextualBranchesFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPABoundedUniversalCompiler
open FoundationCompactPABoundedUniversalCompilerBounds
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionSuccessor
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexAtomicGuardBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexScalarBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalFixedBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxTransformationCodeBounds

def fixedWidthOpenIndexUniversalClosedFormulaPolynomial
    (scale : Nat) : Nat :=
  fixedWidthOpenIndexUniversalFormulaPolynomial scale +
    2 * fixedWidthOpenIndexUniversalSyntaxPolynomial scale + 1

def fixedWidthOpenIndexContextualBranchesFixedPayloadPolynomial
    (scale : Nat) : Nat :=
  let syntaxBound := fixedWidthOpenIndexUniversalSyntaxPolynomial scale
  fixedWidthOpenIndexUniversalBranchesFullyFixedPayloadPolynomial scale +
    cumulativeFiniteExhaustionPayloadPolynomial syntaxBound +
    boundedUniversalFiniteExhaustionSpecializationEnvelope syntaxBound +
    4 * smallContextAssemblyEnvelope
      (fixedWidthOpenIndexUniversalClosedFormulaPolynomial scale)

def fixedWidthOpenIndexContextualBranchesEqualityExposedPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let Gamma := valuationContext outerFormula.freeVariables valuation
  let bound := termValue valuation widthTerm
  contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (fixedWidthBitBranchesOpenIndexEqualityExposedPayloadPolynomial valuation
      tableTerm widthTerm indexTerm valueTerm)

theorem cutClosedAssumptionFullAssemblyCost_le_openIndexUniversal
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (caseFormula target : LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (hcard : Gamma.card <= 4)
    (hGamma : FormulaCodeBound Gamma resource)
    (hcase : (binaryFormulaCode caseFormula).length <= resource)
    (hnegatedCase : (binaryFormulaCode (∼caseFormula)).length <= resource)
    (htarget : (binaryFormulaCode target).length <= resource) :
    cutClosedAssumptionFullAssemblyCost Gamma caseFormula target <=
      smallContextAssemblyEnvelope resource := by
  let rootContext := insert target Gamma
  let caseContext := insert caseFormula rootContext
  let negatedCaseContext := insert (∼caseFormula) rootContext
  have hrootBound : FormulaCodeBound rootContext resource :=
    hGamma.insert htarget
  have hcaseBound : FormulaCodeBound caseContext resource :=
    hrootBound.insert hcase
  have hnegatedCaseBound : FormulaCodeBound negatedCaseContext resource :=
    hrootBound.insert hnegatedCase
  have hrootCardTight : rootContext.card <= 5 := by
    have hstep := Finset.card_insert_le target Gamma
    dsimp only [rootContext]
    omega
  have hrootCard : rootContext.card <= 8 := hrootCardTight.trans (by omega)
  have hcaseCard : caseContext.card <= 8 := by
    have hstep := Finset.card_insert_le caseFormula rootContext
    dsimp only [caseContext]
    omega
  have hnegatedCaseCard : negatedCaseContext.card <= 8 := by
    have hstep := Finset.card_insert_le (∼caseFormula) rootContext
    dsimp only [negatedCaseContext]
    omega
  have hrootSequent := binarySequentCode_length_le_small rootContext resource
    hrootCard hrootBound
  have hcaseSequent := binarySequentCode_length_le_small caseContext resource
    hcaseCard hcaseBound
  have hnegatedCaseSequent := binarySequentCode_length_le_small
    negatedCaseContext resource hnegatedCaseCard hnegatedCaseBound
  have htagSeven : (binaryNatCode 7).length <= 32 := by decide
  have htagNine : (binaryNatCode 9).length <= 32 := by decide
  unfold cutClosedAssumptionFullAssemblyCost
    cutClosedAssumptionDerivationCost smallContextAssemblyEnvelope
  dsimp only [rootContext, caseContext, negatedCaseContext]
    at hrootSequent hcaseSequent hnegatedCaseSequent ⊢
  omega

theorem lowerBoundContradictionFullPayloadCost_le_openIndexUniversal
    (bound : Nat)
    (target : LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (htarget : (binaryFormulaCode target).length <= resource)
    (hfiniteBound : (binaryFormulaCode (finiteBoundFormula bound)).length <=
      resource)
    (hnegatedFiniteBound :
      (binaryFormulaCode (∼finiteBoundFormula bound)).length <= resource)
    (hdoubleNegatedFiniteBound :
      (binaryFormulaCode
        (∼finiteLowerBoundFormula bound (&0))).length <= resource) :
    lowerBoundContradictionFullPayloadCost bound target <=
      smallContextAssemblyEnvelope resource := by
  let Gamma := insert target
    (insert (∼finiteLowerBoundFormula bound (&0))
      (finiteBoundContext bound))
  have hbase : FormulaCodeBound (finiteBoundContext bound) resource := by
    intro formula hformula
    simp only [finiteBoundContext, Finset.mem_singleton] at hformula
    subst formula
    exact hnegatedFiniteBound
  have hGamma : FormulaCodeBound Gamma resource :=
    (hbase.insert hdoubleNegatedFiniteBound).insert htarget
  have hcard : Gamma.card <= 8 := by
    have hbaseCard : (finiteBoundContext bound).card <= 1 := by
      simp [finiteBoundContext]
    have hfirst := Finset.card_insert_le
      (∼finiteLowerBoundFormula bound (&0)) (finiteBoundContext bound)
    have hsecond := Finset.card_insert_le target
      (insert (∼finiteLowerBoundFormula bound (&0))
        (finiteBoundContext bound))
    dsimp only [Gamma]
    omega
  have hsequent := binarySequentCode_length_le_small Gamma resource hcard hGamma
  have htagZero : (binaryNatCode 0).length <= 32 := by decide
  unfold lowerBoundContradictionFullPayloadCost smallContextAssemblyEnvelope
  dsimp only [Gamma] at hsequent ⊢
  omega

theorem contextualBranchesUnderBoundPayloadEnvelope_le_components
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (bound : Nat)
    (targetFormula : LO.FirstOrder.ArithmeticProposition)
    (caseResource caseBound cumulativeBound specializationBound
      localBound : Nat)
    (hcase : caseResource <= caseBound)
    (hexhaustion :
      finiteExhaustionAtEigenvariableStructuralPayloadBound bound <=
        cumulativeBound + specializationBound)
    (hlower : lowerBoundContradictionFullPayloadCost bound targetFormula <=
      localBound)
    (hweak : weakeningFullAssemblyCost
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula bound (&0))
          (contextualFiniteBoundContext Gamma bound))) <= localBound)
    (heliminate :
      CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
        (contextualFiniteBoundContext Gamma bound) targetFormula
        (finiteEqualityCases (&0) bound)
        (finiteLowerBoundFormula bound (&0)) <= localBound)
    (hcut : cutClosedAssumptionFullAssemblyCost
      (contextualFiniteBoundContext Gamma bound)
      (finiteExhaustionFormula bound (&0)) targetFormula <= localBound) :
    contextualBranchesUnderBoundPayloadEnvelope Gamma bound targetFormula
        caseResource <=
      caseBound + cumulativeBound + specializationBound + 4 * localBound := by
  unfold contextualBranchesUnderBoundPayloadEnvelope
    lowerBranchStructuralPayloadBound
  omega

theorem fixedWidthContextualBranchesEqualityExposedPayloadPolynomial_le_fixed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (scale : Nat)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    fixedWidthOpenIndexContextualBranchesEqualityExposedPayloadPolynomial
        valuation tableTerm widthTerm indexTerm valueTerm <=
      fixedWidthOpenIndexContextualBranchesFixedPayloadPolynomial scale := by
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let shiftedGamma := Gamma.image Rewriting.shift
  let bound := termValue valuation widthTerm
  let syntaxBound := fixedWidthOpenIndexUniversalSyntaxPolynomial scale
  let formulaBound := fixedWidthOpenIndexUniversalClosedFormulaPolynomial scale
  let caseResource :=
    fixedWidthBitBranchesOpenIndexEqualityExposedPayloadPolynomial valuation
      tableTerm widthTerm indexTerm valueTerm
  let caseBound := fixedWidthOpenIndexUniversalBranchesFullyFixedPayloadPolynomial
    scale
  let targetFormula := Rewriting.free body
  let finiteContext := contextualFiniteBoundContext shiftedGamma bound
  let localBound := smallContextAssemblyEnvelope formulaBound
  have hboundScale : bound <= scale := by
    have hraw : bound <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm := by
      dsimp only [bound]
      unfold fixedWidthOpenIndexAtomicCoordinateScale
        fixedWidthOpenIndexPublicCoordinateScale
      omega
    exact hraw.trans hscale
  have hboundSyntax : bound <= syntaxBound := by
    dsimp only [syntaxBound]
    unfold fixedWidthOpenIndexUniversalSyntaxPolynomial
    omega
  have hbodyRaw := fixedWidthBitBody_code_le_fixed valuation tableTerm widthTerm
    indexTerm valueTerm scale hscale
  have hbodySyntax : (binaryFormulaCode body).length <= syntaxBound := by
    dsimp only [body, syntaxBound]
    unfold fixedWidthOpenIndexUniversalSyntaxPolynomial
    omega
  have hclosedLe : boundedUniversalClosedFormulaEnvelope syntaxBound <=
      formulaBound := by
    dsimp only [syntaxBound, formulaBound]
    unfold fixedWidthOpenIndexUniversalClosedFormulaPolynomial
      fixedWidthOpenIndexUniversalFormulaPolynomial
    omega
  have hcontextLe : fixedWidthOpenIndexUniversalContextCodePolynomial scale <=
      formulaBound := by
    dsimp only [formulaBound]
    unfold fixedWidthOpenIndexUniversalClosedFormulaPolynomial
      fixedWidthOpenIndexUniversalFormulaPolynomial
    omega
  have hshiftedSum := fixedWidthOpenIndexOuterContextFormulaCodeSum_le_fixed
    valuation tableTerm widthTerm indexTerm valueTerm scale hscale htable hwidth
      hindex hvalue
  have hshiftedBound : FormulaCodeBound shiftedGamma formulaBound := by
    intro formula hformula
    have hmember :=
      formulaCode_le_contextualHybridUniversalFormulaCodeSum hformula
    exact hmember.trans (hshiftedSum.trans hcontextLe)
  have hshiftedCard : shiftedGamma.card <= 1 := by
    dsimp only [shiftedGamma, Gamma, outerVariables, outerFormula, body]
    exact fixedWidthUniversalShiftedOuterContext_card_le_one_of_openIndex
      valuation tableTerm widthTerm indexTerm valueTerm htable hwidth hindex
        hvalue
  have htargetCode : (binaryFormulaCode targetFormula).length <= formulaBound := by
    have hfree := binaryFormulaCode_free_length_le body
    dsimp only [targetFormula, formulaBound]
    unfold fixedWidthOpenIndexUniversalClosedFormulaPolynomial
      fixedWidthOpenIndexUniversalFormulaPolynomial
    dsimp only [syntaxBound] at hbodySyntax
    omega
  have hnegatedFiniteBound :=
    negatedFiniteBoundFormula_code_le_boundedUniversal bound syntaxBound
      hboundSyntax
  have hdoubleNegatedFiniteBound :=
    doubleNegatedFiniteBoundFormula_code_le_boundedUniversal bound syntaxBound
      hboundSyntax
  have hnegatedCases :=
    negatedFiniteEqualityCases_code_le_boundedUniversal bound syntaxBound
      (by omega)
  have hfiniteExhaustion :=
    finiteExhaustionFormula_code_le_boundedUniversal bound syntaxBound
      hboundSyntax
  have hnegatedFiniteExhaustion :=
    negatedFiniteExhaustionFormula_code_le_boundedUniversal bound syntaxBound
      hboundSyntax
  have hfiniteContextBound : FormulaCodeBound finiteContext formulaBound := by
    dsimp only [finiteContext]
    unfold contextualFiniteBoundContext
    exact hshiftedBound.insert (hnegatedFiniteBound.trans hclosedLe)
  have hfiniteContextCard : finiteContext.card <= 4 := by
    have hstep := Finset.card_insert_le (∼finiteBoundFormula bound) shiftedGamma
    dsimp only [finiteContext]
    unfold contextualFiniteBoundContext
    omega
  have hlower : lowerBoundContradictionFullPayloadCost bound targetFormula <=
      smallContextAssemblyEnvelope formulaBound := by
    exact lowerBoundContradictionFullPayloadCost_le_openIndexUniversal bound
      targetFormula formulaBound htargetCode
      ((finiteBoundFormula_code_le_boundedUniversal bound syntaxBound
        hboundSyntax).trans hclosedLe)
      (hnegatedFiniteBound.trans hclosedLe)
      (hdoubleNegatedFiniteBound.trans hclosedLe)
  have hweakContextBound : FormulaCodeBound
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula bound (&0)) finiteContext))
      formulaBound :=
    (hfiniteContextBound.insert
      (hdoubleNegatedFiniteBound.trans hclosedLe)).insert htargetCode
  have hweakContextCard :
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula bound (&0)) finiteContext)).card <=
          8 := by
    have hfirst := Finset.card_insert_le
      (∼finiteLowerBoundFormula bound (&0)) finiteContext
    have hsecond := Finset.card_insert_le targetFormula
      (insert (∼finiteLowerBoundFormula bound (&0)) finiteContext)
    omega
  have hweak := weakeningFullAssemblyCost_le_small
    (insert targetFormula
      (insert (∼finiteLowerBoundFormula bound (&0)) finiteContext))
    formulaBound hweakContextCard hweakContextBound
  have heliminate := eliminateDisjunctionAssumptionFullAssemblyCost_le_small
    finiteContext targetFormula (finiteEqualityCases (&0) bound)
      (finiteLowerBoundFormula bound (&0)) formulaBound hfiniteContextCard
      hfiniteContextBound htargetCode (hnegatedCases.trans hclosedLe)
      (hdoubleNegatedFiniteBound.trans hclosedLe) (by
        simpa only [finiteExhaustionFormula, finiteLowerBoundFormula] using
          hnegatedFiniteExhaustion.trans hclosedLe)
  have hcut := cutClosedAssumptionFullAssemblyCost_le_openIndexUniversal
    finiteContext (finiteExhaustionFormula bound (&0)) targetFormula
      formulaBound hfiniteContextCard hfiniteContextBound
      (hfiniteExhaustion.trans hclosedLe)
      (hnegatedFiniteExhaustion.trans hclosedLe) htargetCode
  have hexhaustion :=
    finiteExhaustionAtEigenvariableStructuralPayloadBound_le_polynomial bound
      syntaxBound hboundSyntax
  have hcase : caseResource <= caseBound := by
    dsimp only [caseResource, caseBound]
    exact fixedWidthBitBranchesResource_le_fixed_of_eq valuation tableTerm
      widthTerm indexTerm valueTerm _ _ scale rfl rfl hscale htable hwidth
        hindex hvalue
  change contextualBranchesUnderBoundPayloadEnvelope shiftedGamma bound
      targetFormula caseResource <=
    caseBound + cumulativeFiniteExhaustionPayloadPolynomial syntaxBound +
      boundedUniversalFiniteExhaustionSpecializationEnvelope syntaxBound +
      4 * localBound
  exact contextualBranchesUnderBoundPayloadEnvelope_le_components shiftedGamma
    bound targetFormula caseResource caseBound
      (cumulativeFiniteExhaustionPayloadPolynomial syntaxBound)
      (boundedUniversalFiniteExhaustionSpecializationEnvelope syntaxBound)
      localBound hcase hexhaustion hlower hweak heliminate hcut

theorem fixedWidthContextualBranchesResource_le_fixed_of_eq
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (resource target scale : Nat)
    (hresource : resource =
      fixedWidthOpenIndexContextualBranchesEqualityExposedPayloadPolynomial
        valuation tableTerm widthTerm indexTerm valueTerm)
    (htarget : target =
      fixedWidthOpenIndexContextualBranchesFixedPayloadPolynomial scale)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    Nat.le resource target := by
  rw [hresource, htarget]
  exact fixedWidthContextualBranchesEqualityExposedPayloadPolynomial_le_fixed
    valuation tableTerm widthTerm indexTerm valueTerm scale hscale htable hwidth
      hindex hvalue

#print axioms cutClosedAssumptionFullAssemblyCost_le_openIndexUniversal
#print axioms
  fixedWidthContextualBranchesEqualityExposedPayloadPolynomial_le_fixed
#print axioms fixedWidthContextualBranchesResource_le_fixed_of_eq

end FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexContextualBranchesFixedBounds
