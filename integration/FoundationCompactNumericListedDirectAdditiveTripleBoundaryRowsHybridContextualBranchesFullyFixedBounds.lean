import integration.FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridBranchesFullyFixedBounds

/-!
# Fully fixed contextual hybrid branches for triple-boundary rows

This pays finite exhaustion and the surrounding contextual proof operations
after the actual hybrid row tree has received its fixed resource bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridContextualBranchesFullyFixedBounds

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
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsPublicBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectFixedPolynomialBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

def tripleBoundaryRowsHybridContextualBranchesFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxCode :=
    tripleBoundaryRowDirectUniversalSyntaxFixedPolynomial numericBound bitBound
  let formulaCode :=
    tripleBoundaryRowDirectUniversalFormulaFixedPolynomial numericBound bitBound
  tripleBoundaryRowsHybridBranchesFixedPayloadPolynomial numericBound bitBound +
    cumulativeFiniteExhaustionPayloadPolynomial syntaxCode +
    boundedUniversalFiniteExhaustionSpecializationEnvelope syntaxCode +
    4 * smallContextAssemblyEnvelope formulaCode

theorem
    compactAdditiveTripleBoundaryRowsHybridContextualBranchesResource_le_fullyFixed
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    contextualBranchesUnderBoundPayloadEnvelope ∅ count
        (Rewriting.free
          (compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable))
        (compactAdditiveTripleBoundaryRowsBranchesTransparentStructuralEnvelope
          tokenCount count boundaryTable rows) <=
      tripleBoundaryRowsHybridContextualBranchesFixedPayloadPolynomial
        numericBound bitBound := by
  let body := compactAdditiveTripleBoundaryRowsBody tokenCount boundaryTable
  let targetFormula := Rewriting.free body
  let syntaxCode :=
    tripleBoundaryRowDirectUniversalSyntaxFixedPolynomial numericBound bitBound
  let formulaCode :=
    tripleBoundaryRowDirectUniversalFormulaFixedPolynomial numericBound bitBound
  let caseResource :=
    compactAdditiveTripleBoundaryRowsBranchesTransparentStructuralEnvelope
      tokenCount count boundaryTable rows
  let caseBound :=
    tripleBoundaryRowsHybridBranchesFixedPayloadPolynomial
      numericBound bitBound
  let finiteContext := contextualFiniteBoundContext
    (∅ : Finset LO.FirstOrder.ArithmeticProposition) count
  let localBound := smallContextAssemblyEnvelope formulaCode
  have hbody : (binaryFormulaCode body).length <=
      tripleBoundaryRowUniversalBodyFormulaCodePolynomial numericBound bitBound :=
    compactAdditiveTripleBoundaryRowsBody_code_length_le_fixed tokenCount
      boundaryTable numericBound bitBound htokenCount htableSize hnumericSize
  have hboundSyntax : count <= syntaxCode := by
    unfold syntaxCode tripleBoundaryRowDirectUniversalSyntaxFixedPolynomial
    omega
  have hbodySyntax : (binaryFormulaCode body).length <= syntaxCode := by
    exact hbody.trans (by
      unfold syntaxCode tripleBoundaryRowDirectUniversalSyntaxFixedPolynomial
      omega)
  have hclosedLe : boundedUniversalClosedFormulaEnvelope syntaxCode <=
      formulaCode := by
    unfold formulaCode tripleBoundaryRowDirectUniversalFormulaFixedPolynomial
    dsimp only [syntaxCode]
    omega
  have htargetCode : (binaryFormulaCode targetFormula).length <=
      formulaCode := by
    have hfree := binaryFormulaCode_free_length_le body
    dsimp only [targetFormula]
    exact hfree.trans (by
      unfold formulaCode tripleBoundaryRowDirectUniversalFormulaFixedPolynomial
      dsimp only [syntaxCode]
      omega)
  have hnegatedFiniteBound :=
    negatedFiniteBoundFormula_code_le_boundedUniversal count syntaxCode
      hboundSyntax
  have hdoubleNegatedFiniteBound :=
    doubleNegatedFiniteBoundFormula_code_le_boundedUniversal count syntaxCode
      hboundSyntax
  have hnegatedCases :=
    negatedFiniteEqualityCases_code_le_boundedUniversal count syntaxCode
      (by omega)
  have hfiniteExhaustion :=
    finiteExhaustionFormula_code_le_boundedUniversal count syntaxCode
      hboundSyntax
  have hnegatedFiniteExhaustion :=
    negatedFiniteExhaustionFormula_code_le_boundedUniversal count syntaxCode
      hboundSyntax
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
      lowerBoundContradictionFullPayloadCost count targetFormula <=
        localBound := by
    exact lowerBoundContradictionFullPayloadCost_le_completed count
      targetFormula formulaCode htargetCode
      ((finiteBoundFormula_code_le_boundedUniversal count syntaxCode
        hboundSyntax).trans hclosedLe)
      (hnegatedFiniteBound.trans hclosedLe)
      (hdoubleNegatedFiniteBound.trans hclosedLe)
  have hweakContextBound : FormulaCodeBound
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula count (&0)) finiteContext))
      formulaCode :=
    (hfiniteContextBound.insert
      (hdoubleNegatedFiniteBound.trans hclosedLe)).insert htargetCode
  have hweakContextCard :
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula count (&0))
          finiteContext)).card <= 8 := by
    have hfirst := Finset.card_insert_le
      (∼finiteLowerBoundFormula count (&0)) finiteContext
    have hsecond := Finset.card_insert_le targetFormula
      (insert (∼finiteLowerBoundFormula count (&0)) finiteContext)
    omega
  have hweak := weakeningFullAssemblyCost_le_small
    (insert targetFormula
      (insert (∼finiteLowerBoundFormula count (&0)) finiteContext))
    formulaCode hweakContextCard hweakContextBound
  have heliminate := eliminateDisjunctionAssumptionFullAssemblyCost_le_small
    finiteContext targetFormula (finiteEqualityCases (&0) count)
      (finiteLowerBoundFormula count (&0)) formulaCode
      hfiniteContextCard hfiniteContextBound htargetCode
      (hnegatedCases.trans hclosedLe)
      (hdoubleNegatedFiniteBound.trans hclosedLe) (by
        simpa only [finiteExhaustionFormula, finiteLowerBoundFormula] using
          hnegatedFiniteExhaustion.trans hclosedLe)
  have hcut := cutClosedAssumptionFullAssemblyCost_le_completed
    finiteContext (finiteExhaustionFormula count (&0)) targetFormula
      formulaCode hfiniteContextCard hfiniteContextBound
      (hfiniteExhaustion.trans hclosedLe)
      (hnegatedFiniteExhaustion.trans hclosedLe) htargetCode
  have hexhaustion :=
    finiteExhaustionAtEigenvariableStructuralPayloadBound_le_polynomial
      count syntaxCode hboundSyntax
  have hcase : caseResource <= caseBound := by
    dsimp only [caseResource, caseBound]
    exact
      compactAdditiveTripleBoundaryRowsBranchesTransparentStructuralEnvelope_le_fullyFixed
        tokenCount count boundaryTable numericBound bitBound rows htokenCount
        hcount htableSize hnumericSize
  change contextualBranchesUnderBoundPayloadEnvelope ∅ count
      targetFormula caseResource <= _
  unfold tripleBoundaryRowsHybridContextualBranchesFixedPayloadPolynomial
  dsimp only [syntaxCode, formulaCode, caseBound, localBound]
  exact contextualBranchesUnderBoundPayloadEnvelope_le_components_completed ∅
    count targetFormula caseResource caseBound
    (cumulativeFiniteExhaustionPayloadPolynomial syntaxCode)
    (boundedUniversalFiniteExhaustionSpecializationEnvelope syntaxCode)
    localBound hcase hexhaustion hlower hweak heliminate hcut

#print axioms
  compactAdditiveTripleBoundaryRowsHybridContextualBranchesResource_le_fullyFixed

end FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridContextualBranchesFullyFixedBounds
