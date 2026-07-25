import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

/-!
# Fixed assembly of contextual bounded-universal branches

The theorem packages finite exhaustion, weakening, disjunction elimination,
and cut once their shared syntax and context bounds have been established.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactPAContextualBranchesFixedAssembly

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABoundedUniversalCompilerBounds
open FoundationCompactPABoundedUniversalCompiler
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAFiniteExhaustionSuccessor
open FoundationCompactPANegativeEqualityBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

def contextualBranchesFixedAssemblyEnvelope
    (syntaxCode formulaCode caseBound : Nat) : Nat :=
  caseBound +
    cumulativeFiniteExhaustionPayloadPolynomial syntaxCode +
    boundedUniversalFiniteExhaustionSpecializationEnvelope syntaxCode +
    4 * smallContextAssemblyEnvelope formulaCode

theorem contextualBranchesUnderBoundPayloadEnvelope_le_fixedAssembly
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (bound syntaxCode formulaCode caseResource caseBound : Nat)
    (targetFormula : LO.FirstOrder.ArithmeticProposition)
    (hboundSyntax : bound <= syntaxCode)
    (hclosedLe :
      boundedUniversalClosedFormulaEnvelope syntaxCode <= formulaCode)
    (htargetCode :
      (binaryFormulaCode targetFormula).length <= formulaCode)
    (hGammaCard : Gamma.card <= 1)
    (hGammaBound : FormulaCodeBound Gamma formulaCode)
    (hcase : caseResource <= caseBound) :
    contextualBranchesUnderBoundPayloadEnvelope Gamma bound targetFormula
        caseResource <=
      contextualBranchesFixedAssemblyEnvelope syntaxCode formulaCode
        caseBound := by
  let finiteContext := contextualFiniteBoundContext Gamma bound
  let localBound := smallContextAssemblyEnvelope formulaCode
  have hnegatedFiniteBound :=
    negatedFiniteBoundFormula_code_le_boundedUniversal bound syntaxCode
      hboundSyntax
  have hdoubleNegatedFiniteBound :=
    doubleNegatedFiniteBoundFormula_code_le_boundedUniversal bound syntaxCode
      hboundSyntax
  have hnegatedCases :=
    negatedFiniteEqualityCases_code_le_boundedUniversal bound syntaxCode
      (by omega)
  have hfiniteExhaustion :=
    finiteExhaustionFormula_code_le_boundedUniversal bound syntaxCode
      hboundSyntax
  have hnegatedFiniteExhaustion :=
    negatedFiniteExhaustionFormula_code_le_boundedUniversal bound syntaxCode
      hboundSyntax
  have hfiniteContextBound :
      FormulaCodeBound finiteContext formulaCode := by
    dsimp only [finiteContext]
    unfold contextualFiniteBoundContext
    exact hGammaBound.insert (hnegatedFiniteBound.trans hclosedLe)
  have hfiniteContextCard : finiteContext.card <= 4 := by
    have hinsert := Finset.card_insert_le
      (∼finiteBoundFormula bound) Gamma
    dsimp only [finiteContext]
    unfold contextualFiniteBoundContext
    omega
  have hlower :
      lowerBoundContradictionFullPayloadCost bound targetFormula <=
        localBound := by
    exact lowerBoundContradictionFullPayloadCost_le_completed bound
      targetFormula formulaCode htargetCode
      ((finiteBoundFormula_code_le_boundedUniversal bound syntaxCode
        hboundSyntax).trans hclosedLe)
      (hnegatedFiniteBound.trans hclosedLe)
      (hdoubleNegatedFiniteBound.trans hclosedLe)
  have hweakContextBound : FormulaCodeBound
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula bound (&0)) finiteContext))
      formulaCode :=
    (hfiniteContextBound.insert
      (hdoubleNegatedFiniteBound.trans hclosedLe)).insert htargetCode
  have hweakContextCard :
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula bound (&0))
          finiteContext)).card <= 8 := by
    have hfirst := Finset.card_insert_le
      (∼finiteLowerBoundFormula bound (&0)) finiteContext
    have hsecond := Finset.card_insert_le targetFormula
      (insert (∼finiteLowerBoundFormula bound (&0)) finiteContext)
    omega
  have hweak := weakeningFullAssemblyCost_le_small
    (insert targetFormula
      (insert (∼finiteLowerBoundFormula bound (&0)) finiteContext))
    formulaCode hweakContextCard hweakContextBound
  have heliminate := eliminateDisjunctionAssumptionFullAssemblyCost_le_small
    finiteContext targetFormula (finiteEqualityCases (&0) bound)
      (finiteLowerBoundFormula bound (&0)) formulaCode hfiniteContextCard
      hfiniteContextBound htargetCode (hnegatedCases.trans hclosedLe)
      (hdoubleNegatedFiniteBound.trans hclosedLe) (by
        simpa only [finiteExhaustionFormula, finiteLowerBoundFormula] using
          hnegatedFiniteExhaustion.trans hclosedLe)
  have hcut := cutClosedAssumptionFullAssemblyCost_le_completed
    finiteContext (finiteExhaustionFormula bound (&0)) targetFormula
      formulaCode hfiniteContextCard hfiniteContextBound
      (hfiniteExhaustion.trans hclosedLe)
      (hnegatedFiniteExhaustion.trans hclosedLe) htargetCode
  have hexhaustion :=
    finiteExhaustionAtEigenvariableStructuralPayloadBound_le_polynomial bound
      syntaxCode hboundSyntax
  unfold contextualBranchesFixedAssemblyEnvelope
  exact contextualBranchesUnderBoundPayloadEnvelope_le_components_completed
    Gamma bound targetFormula caseResource caseBound
    (cumulativeFiniteExhaustionPayloadPolynomial syntaxCode)
    (boundedUniversalFiniteExhaustionSpecializationEnvelope syntaxCode)
    localBound hcase hexhaustion hlower hweak heliminate hcut

#print axioms
  contextualBranchesUnderBoundPayloadEnvelope_le_fixedAssembly

end FoundationCompactPAContextualBranchesFixedAssembly
