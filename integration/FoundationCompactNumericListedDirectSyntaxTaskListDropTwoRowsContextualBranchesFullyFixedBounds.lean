import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsBranchesFullyFixedBounds

/-!
# Fully fixed contextual branches for syntax-task drop two

This layer pays finite exhaustion and the surrounding context operations after
the exact drop-two row branches have been replaced by their fixed resource.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsContextualBranchesFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABoundedUniversalCompilerBounds
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
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
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalShellSyntaxFixedBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsUniformBranchFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsUniversalBodyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

def taskDropTwoContextualBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxCode :=
    taskDropTwoUniversalSyntaxFixedPolynomial numericBound bitBound
  let formulaCode :=
    taskDropTwoUniversalFormulaFixedPolynomial numericBound bitBound
  taskDropTwoBranchesFullyFixedPayloadPolynomial numericBound bitBound +
    cumulativeFiniteExhaustionPayloadPolynomial syntaxCode +
    boundedUniversalFiniteExhaustionSpecializationEnvelope syntaxCode +
    4 * smallContextAssemblyEnvelope formulaCode

theorem
    compactAdditiveSyntaxTaskListDropTwoRowsContextualBranchesResource_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 2)
    (rows : (index : Fin targetCount) ->
      CompactAdditiveSyntaxTaskListDropRowData tokenTable width tokenCount
        sourceBoundary targetBoundary 2 index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    contextualBranchesUnderBoundPayloadEnvelope ∅ targetCount
        (Rewriting.free
          (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable
            width tokenCount sourceBoundary targetBoundary 2))
        (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchesTransparentEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary targetCount
          2 rows) <=
      taskDropTwoContextualBranchesFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let body :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 2
  let targetFormula := Rewriting.free body
  let syntaxCode :=
    taskDropTwoUniversalSyntaxFixedPolynomial numericBound bitBound
  let formulaCode :=
    taskDropTwoUniversalFormulaFixedPolynomial numericBound bitBound
  let caseResource :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchesTransparentEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      2 rows
  let caseBound :=
    taskDropTwoBranchesFullyFixedPayloadPolynomial numericBound bitBound
  let finiteContext := contextualFiniteBoundContext
    (∅ : Finset LO.FirstOrder.ArithmeticProposition) targetCount
  let localBound := smallContextAssemblyEnvelope formulaCode
  have htargetCount : targetCount <= numericBound := by
    rw [hgraph.2.1] at hsourceCount
    omega
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hbody : (binaryFormulaCode body).length <=
      taskDropTwoUniversalBodyFormulaCodePolynomial numericBound bitBound := by
    dsimp only [body]
    exact compactAdditiveSyntaxTaskListDropTwoRowsBody_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound htokenCount htokenTableSize hwidthSize htokenCountSize
      hsourceBoundarySize htargetBoundarySize
  have hboundSyntax : targetCount <= syntaxCode := by
    unfold syntaxCode taskDropTwoUniversalSyntaxFixedPolynomial
    omega
  have hbodySyntax : (binaryFormulaCode body).length <= syntaxCode := by
    exact hbody.trans (by
      unfold syntaxCode taskDropTwoUniversalSyntaxFixedPolynomial
      omega)
  have hclosedLe : boundedUniversalClosedFormulaEnvelope syntaxCode <=
      formulaCode := by
    unfold formulaCode taskDropTwoUniversalFormulaFixedPolynomial
    dsimp only [syntaxCode]
    omega
  have htargetCode : (binaryFormulaCode targetFormula).length <=
      formulaCode := by
    have hfree := binaryFormulaCode_free_length_le body
    dsimp only [targetFormula]
    exact hfree.trans (by
      unfold formulaCode taskDropTwoUniversalFormulaFixedPolynomial
      omega)
  have hnegatedFiniteBound :=
    negatedFiniteBoundFormula_code_le_boundedUniversal targetCount syntaxCode
      hboundSyntax
  have hdoubleNegatedFiniteBound :=
    doubleNegatedFiniteBoundFormula_code_le_boundedUniversal targetCount
      syntaxCode hboundSyntax
  have hnegatedCases :=
    negatedFiniteEqualityCases_code_le_boundedUniversal targetCount syntaxCode
      (by omega)
  have hfiniteExhaustion :=
    finiteExhaustionFormula_code_le_boundedUniversal targetCount syntaxCode
      hboundSyntax
  have hnegatedFiniteExhaustion :=
    negatedFiniteExhaustionFormula_code_le_boundedUniversal targetCount
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
      lowerBoundContradictionFullPayloadCost targetCount targetFormula <=
        localBound := by
    exact lowerBoundContradictionFullPayloadCost_le_completed targetCount
      targetFormula formulaCode htargetCode
      ((finiteBoundFormula_code_le_boundedUniversal targetCount syntaxCode
        hboundSyntax).trans hclosedLe)
      (hnegatedFiniteBound.trans hclosedLe)
      (hdoubleNegatedFiniteBound.trans hclosedLe)
  have hweakContextBound : FormulaCodeBound
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula targetCount (&0)) finiteContext))
      formulaCode :=
    (hfiniteContextBound.insert
      (hdoubleNegatedFiniteBound.trans hclosedLe)).insert htargetCode
  have hweakContextCard :
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula targetCount (&0))
          finiteContext)).card <= 8 := by
    have hfirst := Finset.card_insert_le
      (∼finiteLowerBoundFormula targetCount (&0)) finiteContext
    have hsecond := Finset.card_insert_le targetFormula
      (insert (∼finiteLowerBoundFormula targetCount (&0)) finiteContext)
    omega
  have hweak := weakeningFullAssemblyCost_le_small
    (insert targetFormula
      (insert (∼finiteLowerBoundFormula targetCount (&0)) finiteContext))
    formulaCode hweakContextCard hweakContextBound
  have heliminate := eliminateDisjunctionAssumptionFullAssemblyCost_le_small
    finiteContext targetFormula (finiteEqualityCases (&0) targetCount)
      (finiteLowerBoundFormula targetCount (&0)) formulaCode
      hfiniteContextCard hfiniteContextBound htargetCode
      (hnegatedCases.trans hclosedLe)
      (hdoubleNegatedFiniteBound.trans hclosedLe) (by
        simpa only [finiteExhaustionFormula, finiteLowerBoundFormula] using
          hnegatedFiniteExhaustion.trans hclosedLe)
  have hcut := cutClosedAssumptionFullAssemblyCost_le_completed
    finiteContext (finiteExhaustionFormula targetCount (&0)) targetFormula
      formulaCode hfiniteContextCard hfiniteContextBound
      (hfiniteExhaustion.trans hclosedLe)
      (hnegatedFiniteExhaustion.trans hclosedLe) htargetCode
  have hexhaustion :=
    finiteExhaustionAtEigenvariableStructuralPayloadBound_le_polynomial
      targetCount syntaxCode hboundSyntax
  have hcase : caseResource <= caseBound := by
    dsimp only [caseResource, caseBound]
    exact
      compactAdditiveSyntaxTaskListDropTwoRowsBranchesTransparentEnvelope_le_fullyFixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount numericBound bitBound hgraph rows hwidth htokenCount
        hsourceCount htokenTableSize hsourceBoundarySize htargetBoundarySize
        hnumericSize
  change contextualBranchesUnderBoundPayloadEnvelope ∅ targetCount
      targetFormula caseResource <= _
  unfold taskDropTwoContextualBranchesFullyFixedPayloadPolynomial
  dsimp only [syntaxCode, formulaCode, caseBound, localBound]
  exact contextualBranchesUnderBoundPayloadEnvelope_le_components_completed ∅
    targetCount targetFormula caseResource caseBound
    (cumulativeFiniteExhaustionPayloadPolynomial syntaxCode)
    (boundedUniversalFiniteExhaustionSpecializationEnvelope syntaxCode)
    localBound hcase hexhaustion hlower hweak heliminate hcut

#print axioms
  compactAdditiveSyntaxTaskListDropTwoRowsContextualBranchesResource_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsContextualBranchesFullyFixedBounds
