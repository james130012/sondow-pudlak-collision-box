import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedUniformResourceBranchTree
import integration.FoundationCompactNumericListedDirectParserSyntaxExactFuelDirectBoundEqualityFixedBounds

/-! # Exact-fuel adjacent-row universal with a uniform witness resource -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelUniformResourceDirectUniversal

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversal
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedUniformResourceBranches
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedUniformResourceBranchTree
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserSyntaxExactFuelDirectBoundEqualityFixedBounds

def compactParserSyntaxAdjacentRowsBoundedExactFuelUniformDirectUniversalResource
    (tokenTable width tokenCount stateBoundary stateCount inputCount
      formulaValueBound uniformValueBound numericBound bitBound : Nat) : Nat :=
  let fuel := compactParserSyntaxExactFuel inputCount
  let body :=
    compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
      tokenCount stateBoundary stateCount formulaValueBound
  let branchPolynomial :=
    explicitDirectUniversalBranchesPayloadPolynomial fuel body
      (compactParserSyntaxAdjacentRowsBoundedUniformDirectBranchResource
        tokenCount uniformValueBound numericBound bitBound)
  compileContextualTermBoundedUniversalPayloadEnvelope ∅ fuel
    (Rew.bShift (compactParserSyntaxExactFuelTerm inputCount)) body
    (compactParserSyntaxExactFuelDirectBoundEqualityFixedPayloadPolynomial
      numericBound)
    (contextualBranchesUnderBoundPayloadEnvelope ∅ fuel
      (Rewriting.free body) branchPolynomial)

noncomputable def
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelUniformDirectUniversalContext
    (tokenTable width tokenCount stateBoundary stateCount inputCount
      formulaValueBound uniformValueBound numericBound bitBound : Nat)
    (hformulaValue : formulaValueBound <= uniformValueBound)
    (hrows : ∀ rowIndex < compactParserSyntaxExactFuel inputCount,
      CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
        stateBoundary stateCount rowIndex formulaValueBound)
    (hfuel : compactParserSyntaxExactFuel inputCount <= numericBound)
    (hvalueBound : formulaValueBound <= numericBound)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    CertifiedPAContextProof ∅
      ((compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
        tokenCount stateBoundary stateCount formulaValueBound).ballLT
          (compactParserSyntaxExactFuelTerm inputCount)) := by
  let fuel := compactParserSyntaxExactFuel inputCount
  let body := compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable
    width tokenCount stateBoundary stateCount formulaValueBound
  let branches :=
    compactParserSyntaxAdjacentRowsBoundedUniformFullyDirectBranches tokenTable
      width tokenCount stateBoundary stateCount fuel formulaValueBound
      uniformValueBound numericBound bitBound hformulaValue hrows hfuel
      hvalueBound hwidth hwidthBit htokenCount hstateCount htokenTableSize
      hstateBoundarySize hareaNumeric hareaBit hnumericSize hbitPositive
  let boundEquality :=
    compactParserSyntaxExactFuelDirectBoundEquality inputCount
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) fuel
    (Rew.bShift (compactParserSyntaxExactFuelTerm inputCount)) body boundEquality
    branches
  exact CertifiedPAContextProof.cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (compactParserSyntaxExactFuelTerm inputCount)) body) =
        body.ballLT (compactParserSyntaxExactFuelTerm inputCount)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

theorem
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelUniformDirectUniversalContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount inputCount
      formulaValueBound uniformValueBound numericBound bitBound : Nat)
    (hformulaValue : formulaValueBound <= uniformValueBound)
    (hrows : ∀ rowIndex < compactParserSyntaxExactFuel inputCount,
      CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
        stateBoundary stateCount rowIndex formulaValueBound)
    (hfuel : compactParserSyntaxExactFuel inputCount <= numericBound)
    (hvalueBound : formulaValueBound <= numericBound)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compileCompactParserSyntaxAdjacentRowsBoundedExactFuelUniformDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount inputCount
      formulaValueBound uniformValueBound numericBound bitBound hformulaValue
      hrows hfuel hvalueBound hwidth hwidthBit htokenCount hstateCount
      htokenTableSize hstateBoundarySize hareaNumeric hareaBit hnumericSize
      hbitPositive).payloadLength <=
    compactParserSyntaxAdjacentRowsBoundedExactFuelUniformDirectUniversalResource
      tokenTable width tokenCount stateBoundary stateCount inputCount
      formulaValueBound uniformValueBound numericBound bitBound := by
  let fuel := compactParserSyntaxExactFuel inputCount
  let body := compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable
    width tokenCount stateBoundary stateCount formulaValueBound
  let branches :=
    compactParserSyntaxAdjacentRowsBoundedUniformFullyDirectBranches tokenTable
      width tokenCount stateBoundary stateCount fuel formulaValueBound
      uniformValueBound numericBound bitBound hformulaValue hrows hfuel
      hvalueBound hwidth hwidthBit htokenCount hstateCount htokenTableSize
      hstateBoundarySize hareaNumeric hareaBit hnumericSize hbitPositive
  let boundEquality := compactParserSyntaxExactFuelDirectBoundEquality inputCount
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) fuel
    (Rew.bShift (compactParserSyntaxExactFuelTerm inputCount)) body boundEquality
    branches
  let leafResource :=
    compactParserSyntaxAdjacentRowsBoundedUniformDirectBranchResource tokenCount
      uniformValueBound numericBound bitBound
  let branchPolynomial :=
    explicitDirectUniversalBranchesPayloadPolynomial fuel body leafResource
  have hinputCount : inputCount <= numericBound := by
    have hself : inputCount <= compactParserSyntaxExactFuel inputCount := by
      unfold compactParserSyntaxExactFuel
      nlinarith
    exact hself.trans hfuel
  have hbound : boundEquality.payloadLength <=
      compactParserSyntaxExactFuelDirectBoundEqualityFixedPayloadPolynomial
        numericBound :=
    (compactParserSyntaxExactFuelDirectBoundEquality_payloadLength_le inputCount).trans
      (compactParserSyntaxExactFuelDirectBoundEqualityResource_le_fixed inputCount
        numericBound hinputCount hfuel)
  have hbranchesStructural :=
    compactParserSyntaxAdjacentRowsBoundedUniformFullyDirectBranches_structuralPayloadBound_le
      tokenTable width tokenCount stateBoundary stateCount fuel formulaValueBound
      uniformValueBound numericBound bitBound hformulaValue hrows hfuel
      hvalueBound hwidth hwidthBit htokenCount hstateCount htokenTableSize
      hstateBoundarySize hareaNumeric hareaBit hnumericSize hbitPositive
  have henvelopePolynomial :=
    compactParserSyntaxAdjacentRowsBoundedUniformBranchesStructuralEnvelope_le_polynomial
      tokenTable width tokenCount stateBoundary stateCount fuel formulaValueBound
      uniformValueBound numericBound bitBound
  have hbranchesCore :
      branches.structuralPayloadBound fuel <= branchPolynomial :=
    hbranchesStructural.trans henvelopePolynomial
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅ fuel
    (Rewriting.free body) branchPolynomial
  have hbranches :
      branches.compileUnderBoundAssumptionStructuralPayloadBound <=
        branchResource := by
    unfold branchResource contextualBranchesUnderBoundPayloadEnvelope
      CertifiedContextFiniteUniversalBranches.compileUnderBoundAssumptionStructuralPayloadBound
      CertifiedContextFiniteUniversalBranches.underExhaustionStructuralPayloadBound
    dsimp only [body, branchPolynomial, leafResource] at hbranchesCore ⊢
    simp only [Finset.image_empty] at hbranchesCore ⊢
    omega
  have hstructural :=
    compileContextualTermBoundedUniversal_payloadLength_le_structural
      (Gamma := ∅) fuel
      (Rew.bShift (compactParserSyntaxExactFuelTerm inputCount)) body
      boundEquality branches
  have htotal :=
    compileContextualTermBoundedUniversalStructuralPayloadBound_le_envelope
      (Gamma := ∅) fuel
      (Rew.bShift (compactParserSyntaxExactFuelTerm inputCount)) body
      boundEquality branches
      (compactParserSyntaxExactFuelDirectBoundEqualityFixedPayloadPolynomial
        numericBound)
      branchResource hbound hbranches
  unfold
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelUniformDirectUniversalContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change direct.payloadLength <= _
  exact hstructural.trans (htotal.trans (by rfl))

#print axioms
  compileCompactParserSyntaxAdjacentRowsBoundedExactFuelUniformDirectUniversalContext_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelUniformResourceDirectUniversal
