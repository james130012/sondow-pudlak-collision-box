import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsBranchesFullyFixedBounds

/-!
# Fully fixed contextual branches for syntax-task same rows

This layer pays finite exhaustion and the surrounding context operations after
the exact row branches have been replaced by their fixed resource.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListSameRowsContextualBranchesFullyFixedBounds

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
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsUniformBranchFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsUniversalBodyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

def taskSameRowsContextualBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxCode :=
    taskSameRowsUniversalSyntaxFixedPolynomial numericBound bitBound
  let formulaCode :=
    taskSameRowsUniversalFormulaFixedPolynomial numericBound bitBound
  taskSameRowsBranchesFullyFixedPayloadPolynomial numericBound bitBound +
    cumulativeFiniteExhaustionPayloadPolynomial syntaxCode +
    boundedUniversalFiniteExhaustionSpecializationEnvelope syntaxCode +
    4 * smallContextAssemblyEnvelope formulaCode

theorem
    compactAdditiveSyntaxTaskListSameRowsContextualBranchesResource_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListSameRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    contextualBranchesUnderBoundPayloadEnvelope ∅ sourceCount
        (Rewriting.free
          (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width
            tokenCount sourceBoundary targetBoundary))
        (compactAdditiveSyntaxTaskListSameRowsBranchesTransparentEnvelope
          tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary rows) <=
      taskSameRowsContextualBranchesFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let body := compactAdditiveSyntaxTaskListSameRowsBody tokenTable width
    tokenCount sourceBoundary targetBoundary
  let targetFormula := Rewriting.free body
  let syntaxCode :=
    taskSameRowsUniversalSyntaxFixedPolynomial numericBound bitBound
  let formulaCode :=
    taskSameRowsUniversalFormulaFixedPolynomial numericBound bitBound
  let caseResource :=
    compactAdditiveSyntaxTaskListSameRowsBranchesTransparentEnvelope tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary rows
  let caseBound :=
    taskSameRowsBranchesFullyFixedPayloadPolynomial numericBound bitBound
  let finiteContext := contextualFiniteBoundContext
    (∅ : Finset LO.FirstOrder.ArithmeticProposition) sourceCount
  let localBound := smallContextAssemblyEnvelope formulaCode
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hbody : (binaryFormulaCode body).length <=
      taskSameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound := by
    dsimp only [body]
    exact compactAdditiveSyntaxTaskListSameRowsBody_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound htokenCount htokenTableSize hwidthSize htokenCountSize
      hsourceBoundarySize htargetBoundarySize
  have hboundSyntax : sourceCount <= syntaxCode := by
    unfold syntaxCode taskSameRowsUniversalSyntaxFixedPolynomial
    omega
  have hbodySyntax : (binaryFormulaCode body).length <= syntaxCode := by
    exact hbody.trans (by
      unfold syntaxCode taskSameRowsUniversalSyntaxFixedPolynomial
      omega)
  have hclosedLe : boundedUniversalClosedFormulaEnvelope syntaxCode <=
      formulaCode := by
    unfold formulaCode taskSameRowsUniversalFormulaFixedPolynomial
    dsimp only [syntaxCode]
    omega
  have htargetCode : (binaryFormulaCode targetFormula).length <=
      formulaCode := by
    have hfree := binaryFormulaCode_free_length_le body
    dsimp only [targetFormula]
    exact hfree.trans (by
      unfold formulaCode taskSameRowsUniversalFormulaFixedPolynomial
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
      compactAdditiveSyntaxTaskListSameRowsBranchesTransparentEnvelope_le_fullyFixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        numericBound bitBound rows hwidth htokenCount hsourceCount
        htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  change contextualBranchesUnderBoundPayloadEnvelope ∅ sourceCount
      targetFormula caseResource <= _
  unfold taskSameRowsContextualBranchesFullyFixedPayloadPolynomial
  dsimp only [syntaxCode, formulaCode, caseBound, localBound]
  exact contextualBranchesUnderBoundPayloadEnvelope_le_components_completed ∅
    sourceCount targetFormula caseResource caseBound
    (cumulativeFiniteExhaustionPayloadPolynomial syntaxCode)
    (boundedUniversalFiniteExhaustionSpecializationEnvelope syntaxCode)
    localBound hcase hexhaustion hlower hweak heliminate hcut

#print axioms
  compactAdditiveSyntaxTaskListSameRowsContextualBranchesResource_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListSameRowsContextualBranchesFullyFixedBounds
