import integration.FoundationCompactNumericListedDirectNatListConsRowsTailBranchTreeFixedBound
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodySyntaxUniformBound
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

/-! # Fully fixed contextual branch resource for the cons-tail universal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 260000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailContextualBranchesFixed

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPABoundedUniversalCompilerBounds
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAFiniteExhaustionSuccessor
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPANegativeEqualityBounds
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailBranchTreeUniformBound
open FoundationCompactNumericListedDirectNatListConsRowsTailBranchTreeFixedBound
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyPolynomialResources
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodySyntaxUniformBound

def natListConsRowsTailContextualBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxCode :=
    natListConsRowsTailUniversalSyntaxFixedPolynomial numericBound bitBound
  let formulaCode :=
    natListConsRowsTailUniversalFormulaFixedPolynomial numericBound bitBound
  natListConsRowsTailBranchesFullyFixedPayloadPolynomial numericBound bitBound +
    cumulativeFiniteExhaustionPayloadPolynomial syntaxCode +
    boundedUniversalFiniteExhaustionSpecializationEnvelope syntaxCode +
    4 * smallContextAssemblyEnvelope formulaCode

theorem compactAdditiveNatListConsRowsTailContextualBranchesResource_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCountSuccessor : sourceCount + 1 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    contextualBranchesUnderBoundPayloadEnvelope ∅ sourceCount
        (Rewriting.free
          (compactAdditiveNatListConsRowsTailBody tokenTable width tokenCount
            sourceBoundary targetBoundary))
        (hybridBranchesStructuralPayloadEnvelope sourceCount (∅ : Finset Nat)
          (compactAdditiveNatListConsRowsTailUniformBranches tokenTable width
            tokenCount sourceBoundary sourceCount targetBoundary rows)) <=
      natListConsRowsTailContextualBranchesFullyFixedPayloadPolynomial
        numericBound bitBound := by
  let body := compactAdditiveNatListConsRowsTailBody tokenTable width
    tokenCount sourceBoundary targetBoundary
  let targetFormula := Rewriting.free body
  let syntaxCode :=
    natListConsRowsTailUniversalSyntaxFixedPolynomial numericBound bitBound
  let formulaCode :=
    natListConsRowsTailUniversalFormulaFixedPolynomial numericBound bitBound
  let caseResource := hybridBranchesStructuralPayloadEnvelope sourceCount
    (∅ : Finset Nat)
    (compactAdditiveNatListConsRowsTailUniformBranches tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary rows)
  let caseBound :=
    natListConsRowsTailBranchesFullyFixedPayloadPolynomial numericBound bitBound
  let finiteContext := contextualFiniteBoundContext
    (∅ : Finset LO.FirstOrder.ArithmeticProposition) sourceCount
  let localBound := smallContextAssemblyEnvelope formulaCode
  have hsourceCount : sourceCount <= numericBound := by omega
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hbody : (binaryFormulaCode body).length <=
      natListConsRowsTailUniversalBodyFormulaCodePolynomial numericBound
        bitBound := by
    dsimp only [body]
    exact compactAdditiveNatListConsRowsTailBody_code_length_le_uniform
      tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound htokenCount htokenTableSize hwidthSize htokenCountSize
      hsourceBoundarySize htargetBoundarySize
  have hboundSyntax : sourceCount <= syntaxCode := by
    unfold syntaxCode natListConsRowsTailUniversalSyntaxFixedPolynomial
    omega
  have hclosedLe : boundedUniversalClosedFormulaEnvelope syntaxCode <=
      formulaCode := by
    unfold formulaCode natListConsRowsTailUniversalFormulaFixedPolynomial
    dsimp only [syntaxCode]
    omega
  have htargetCode : (binaryFormulaCode targetFormula).length <=
      formulaCode := by
    have hfree := binaryFormulaCode_free_length_le body
    dsimp only [targetFormula]
    exact hfree.trans (by
      unfold formulaCode natListConsRowsTailUniversalFormulaFixedPolynomial
      omega)
  have hnegatedFiniteBound :=
    negatedFiniteBoundFormula_code_le_boundedUniversal sourceCount syntaxCode
      hboundSyntax
  have hdoubleNegatedFiniteBound :=
    doubleNegatedFiniteBoundFormula_code_le_boundedUniversal sourceCount
      syntaxCode hboundSyntax
  have hnegatedCases :=
    negatedFiniteEqualityCases_code_le_boundedUniversal sourceCount syntaxCode
      (by omega)
  have hfiniteExhaustion :=
    finiteExhaustionFormula_code_le_boundedUniversal sourceCount syntaxCode
      hboundSyntax
  have hnegatedFiniteExhaustion :=
    negatedFiniteExhaustionFormula_code_le_boundedUniversal sourceCount
      syntaxCode hboundSyntax
  have hfiniteContextBound : FormulaCodeBound finiteContext formulaCode := by
    dsimp only [finiteContext]
    unfold contextualFiniteBoundContext
    exact (show FormulaCodeBound
      (∅ : Finset LO.FirstOrder.ArithmeticProposition) formulaCode by
        intro formula hformula
        simp at hformula).insert (hnegatedFiniteBound.trans hclosedLe)
  have hfiniteContextCard : finiteContext.card <= 4 := by
    dsimp only [finiteContext]
    simp [contextualFiniteBoundContext]
  have hlower :
      lowerBoundContradictionFullPayloadCost sourceCount targetFormula <=
        localBound := by
    exact lowerBoundContradictionFullPayloadCost_le_completed sourceCount
      targetFormula formulaCode htargetCode
      ((finiteBoundFormula_code_le_boundedUniversal sourceCount syntaxCode
        hboundSyntax).trans hclosedLe)
      (hnegatedFiniteBound.trans hclosedLe)
      (hdoubleNegatedFiniteBound.trans hclosedLe)
  have hweakContextBound : FormulaCodeBound
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula sourceCount (&0)) finiteContext))
      formulaCode :=
    (hfiniteContextBound.insert
      (hdoubleNegatedFiniteBound.trans hclosedLe)).insert htargetCode
  have hweakContextCard :
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula sourceCount (&0))
          finiteContext)).card <= 8 := by
    have hfirst := Finset.card_insert_le
      (∼finiteLowerBoundFormula sourceCount (&0)) finiteContext
    have hsecond := Finset.card_insert_le targetFormula
      (insert (∼finiteLowerBoundFormula sourceCount (&0)) finiteContext)
    omega
  have hweak := weakeningFullAssemblyCost_le_small
    (insert targetFormula
      (insert (∼finiteLowerBoundFormula sourceCount (&0)) finiteContext))
    formulaCode hweakContextCard hweakContextBound
  have heliminate := eliminateDisjunctionAssumptionFullAssemblyCost_le_small
    finiteContext targetFormula (finiteEqualityCases (&0) sourceCount)
      (finiteLowerBoundFormula sourceCount (&0)) formulaCode
      hfiniteContextCard hfiniteContextBound htargetCode
      (hnegatedCases.trans hclosedLe)
      (hdoubleNegatedFiniteBound.trans hclosedLe) (by
        simpa only [finiteExhaustionFormula, finiteLowerBoundFormula] using
          hnegatedFiniteExhaustion.trans hclosedLe)
  have hcut := cutClosedAssumptionFullAssemblyCost_le_completed
    finiteContext (finiteExhaustionFormula sourceCount (&0)) targetFormula
      formulaCode hfiniteContextCard hfiniteContextBound
      (hfiniteExhaustion.trans hclosedLe)
      (hnegatedFiniteExhaustion.trans hclosedLe) htargetCode
  have hexhaustion :=
    finiteExhaustionAtEigenvariableStructuralPayloadBound_le_polynomial
      sourceCount syntaxCode hboundSyntax
  have hcase : caseResource <= caseBound := by
    dsimp only [caseResource, caseBound]
    exact
      compactAdditiveNatListConsRowsTailUniformBranches_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        numericBound bitBound rows hwidth htokenCount hsourceCountSuccessor
        htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  change contextualBranchesUnderBoundPayloadEnvelope ∅ sourceCount
      targetFormula caseResource <= _
  unfold natListConsRowsTailContextualBranchesFullyFixedPayloadPolynomial
  dsimp only [syntaxCode, formulaCode, caseBound, localBound]
  exact contextualBranchesUnderBoundPayloadEnvelope_le_components_completed ∅
    sourceCount targetFormula caseResource caseBound
    (cumulativeFiniteExhaustionPayloadPolynomial syntaxCode)
    (boundedUniversalFiniteExhaustionSpecializationEnvelope syntaxCode)
    localBound hcase hexhaustion hlower hweak heliminate hcut

#print axioms
  compactAdditiveNatListConsRowsTailContextualBranchesResource_le_fullyFixed

end FoundationCompactNumericListedDirectNatListConsRowsTailContextualBranchesFixed
