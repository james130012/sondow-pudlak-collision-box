import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversal
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedUniversalBodyFixedBounds
import integration.FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
import integration.FoundationCompactPAContextualBranchesFixedAssembly

/-! # Fixed polynomial shell for the exact-fuel adjacent-row universal -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedUniversalPolynomial

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualBranchesFixedAssembly
open FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranches
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversal
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedUniversalBodyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserSyntaxExactFuelFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxExactFuelDirectBoundEqualityFixedBounds

def compactParserSyntaxExactAdjacentUniversalBodyCodePolynomial
    (bitBound : Nat) : Nat :=
  compactParserSyntaxAdjacentRowsBoundedUniversalBodyCodePolynomial bitBound

def compactParserSyntaxExactAdjacentUniversalSyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound +
    compactParserSyntaxExactAdjacentUniversalBodyCodePolynomial bitBound

def compactParserSyntaxExactAdjacentUniversalFormulaPolynomial
    (numericBound bitBound : Nat) : Nat :=
  boundedUniversalClosedFormulaEnvelope
      (compactParserSyntaxExactAdjacentUniversalSyntaxPolynomial numericBound
        bitBound) +
    2 * compactParserSyntaxExactAdjacentUniversalBodyCodePolynomial bitBound

def compactParserSyntaxExactAdjacentUniversalLocalPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (compactParserSyntaxExactAdjacentUniversalFormulaPolynomial numericBound
      bitBound)

def compactParserSyntaxExactAdjacentUniversalCasePolynomial
    (leafBound numericBound bitBound : Nat) : Nat :=
  (numericBound + 1) *
    (leafBound +
      3 * compactParserSyntaxExactAdjacentUniversalLocalPayloadPolynomial
        numericBound bitBound)

def compactParserSyntaxExactAdjacentUniversalBranchAssemblyPolynomial
    (leafBound numericBound bitBound : Nat) : Nat :=
  contextualBranchesFixedAssemblyEnvelope
    (compactParserSyntaxExactAdjacentUniversalSyntaxPolynomial numericBound
      bitBound)
    (compactParserSyntaxExactAdjacentUniversalFormulaPolynomial numericBound
      bitBound)
    (compactParserSyntaxExactAdjacentUniversalCasePolynomial leafBound
      numericBound bitBound)

def compactParserSyntaxExactAdjacentUniversalShellBitPolynomial
    (numericBound bitBound : Nat) : Nat :=
  bitBound +
    compactParserSyntaxExactFuelTermFixedCodePolynomial numericBound + 1

def compactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedUniversalPolynomial
    (tokenCount valueBound numericBound bitBound : Nat) : Nat :=
  let leafBound :=
    compactParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchResource
      tokenCount valueBound numericBound bitBound
  closedShortUniversalShellFixedPayloadPolynomial numericBound
    (compactParserSyntaxExactAdjacentUniversalShellBitPolynomial numericBound
      bitBound)
    (compactParserSyntaxExactAdjacentUniversalSyntaxPolynomial numericBound
      bitBound)
    (compactParserSyntaxExactAdjacentUniversalBodyCodePolynomial bitBound)
    (compactParserSyntaxExactAdjacentUniversalBranchAssemblyPolynomial
      leafBound numericBound bitBound)
    (compactParserSyntaxExactFuelDirectBoundEqualityFixedPayloadPolynomial
      numericBound)

private theorem explicitDirectUniversalBranchesPayloadPolynomial_le_fixed
    (body : ArithmeticSemiformula Nat 1)
    (fuel leafBound numericBound bitBound : Nat)
    (hfuel : fuel <= numericBound)
    (hbody : (binaryFormulaCode body).length <=
      compactParserSyntaxExactAdjacentUniversalBodyCodePolynomial bitBound) :
    explicitDirectUniversalBranchesPayloadPolynomial fuel body leafBound <=
      compactParserSyntaxExactAdjacentUniversalCasePolynomial leafBound
        numericBound bitBound := by
  let actualSyntax := explicitDirectUniversalSyntaxResource fuel body
  let fixedSyntax :=
    compactParserSyntaxExactAdjacentUniversalSyntaxPolynomial numericBound
      bitBound
  let actualFormula := explicitDirectUniversalFormulaEnvelope fuel body
  let fixedFormula :=
    compactParserSyntaxExactAdjacentUniversalFormulaPolynomial numericBound
      bitBound
  let actualLocal := explicitDirectUniversalLocalPayloadEnvelope fuel body
  let fixedLocal :=
    compactParserSyntaxExactAdjacentUniversalLocalPayloadPolynomial
      numericBound bitBound
  have hsyntax : actualSyntax <= fixedSyntax := by
    dsimp only [actualSyntax, fixedSyntax]
    unfold explicitDirectUniversalSyntaxResource
      compactParserSyntaxExactAdjacentUniversalSyntaxPolynomial
    omega
  have hclosed := boundedUniversalClosedFormulaEnvelope_mono_completed hsyntax
  have hformula : actualFormula <= fixedFormula := by
    change boundedUniversalClosedFormulaEnvelope actualSyntax +
        2 * (binaryFormulaCode body).length <=
      boundedUniversalClosedFormulaEnvelope fixedSyntax +
        2 * compactParserSyntaxExactAdjacentUniversalBodyCodePolynomial
          bitBound
    exact Nat.add_le_add hclosed (Nat.mul_le_mul_left 2 hbody)
  have hlocal : actualLocal <= fixedLocal := by
    dsimp only [actualLocal, fixedLocal]
    unfold explicitDirectUniversalLocalPayloadEnvelope
      compactParserSyntaxExactAdjacentUniversalLocalPayloadPolynomial
    exact smallContextAssemblyEnvelope_mono_uniform hformula
  unfold explicitDirectUniversalBranchesPayloadPolynomial
    compactParserSyntaxExactAdjacentUniversalCasePolynomial
  apply Nat.mul_le_mul
  · omega
  · exact Nat.add_le_add_left (Nat.mul_le_mul_left 3 hlocal) leafBound

theorem
    compactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversalResource_le_polynomial
    (tokenTable width tokenCount stateBoundary stateCount inputCount valueBound
      numericBound bitBound : Nat)
    (hinputCount : inputCount <= numericBound)
    (hfuel : compactParserSyntaxExactFuel inputCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hstateCountSize : Nat.size stateCount <= bitBound)
    (hvalueBoundSize : Nat.size valueBound <= bitBound) :
    compactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversalResource
        tokenTable width tokenCount stateBoundary stateCount inputCount
          valueBound numericBound bitBound <=
      compactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedUniversalPolynomial
        tokenCount valueBound numericBound bitBound := by
  let fuel := compactParserSyntaxExactFuel inputCount
  let body := compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable
    width tokenCount stateBoundary stateCount valueBound
  let leafBound :=
    compactParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchResource
      tokenCount valueBound numericBound bitBound
  let bodyCode :=
    compactParserSyntaxExactAdjacentUniversalBodyCodePolynomial bitBound
  let syntaxCode :=
    compactParserSyntaxExactAdjacentUniversalSyntaxPolynomial numericBound
      bitBound
  let formulaCode :=
    compactParserSyntaxExactAdjacentUniversalFormulaPolynomial numericBound
      bitBound
  let caseBound :=
    compactParserSyntaxExactAdjacentUniversalCasePolynomial leafBound
      numericBound bitBound
  let branchBound :=
    compactParserSyntaxExactAdjacentUniversalBranchAssemblyPolynomial
      leafBound numericBound bitBound
  let equalityBound :=
    compactParserSyntaxExactFuelDirectBoundEqualityFixedPayloadPolynomial
      numericBound
  let shellBit :=
    compactParserSyntaxExactAdjacentUniversalShellBitPolynomial numericBound
      bitBound
  have hbody : (binaryFormulaCode body).length <= bodyCode := by
    dsimp only [body, bodyCode,
      compactParserSyntaxExactAdjacentUniversalBodyCodePolynomial]
    exact
      compactParserSyntaxAdjacentRowsBoundedUniversalBody_code_length_le_fixed
        tokenTable width tokenCount stateBoundary stateCount valueBound bitBound
        htokenTableSize hwidthSize htokenCountSize hstateBoundarySize
        hstateCountSize hvalueBoundSize
  let caseResource :=
    explicitDirectUniversalBranchesPayloadPolynomial fuel body leafBound
  have hcase : caseResource <= caseBound := by
    exact explicitDirectUniversalBranchesPayloadPolynomial_le_fixed body fuel
      leafBound numericBound bitBound hfuel hbody
  have hsyntax : fuel <= syntaxCode := by
    dsimp only [syntaxCode]
    unfold compactParserSyntaxExactAdjacentUniversalSyntaxPolynomial
    omega
  have hclosed : boundedUniversalClosedFormulaEnvelope syntaxCode <=
      formulaCode := by
    change boundedUniversalClosedFormulaEnvelope syntaxCode <=
      boundedUniversalClosedFormulaEnvelope syntaxCode + 2 * bodyCode
    omega
  have htargetRaw := binaryFormulaCode_free_length_le body
  have htarget : (binaryFormulaCode (Rewriting.free body)).length <=
      formulaCode := by
    have htargetTight :
        (binaryFormulaCode (Rewriting.free body)).length <= 2 * bodyCode :=
      htargetRaw.trans (Nat.mul_le_mul_left 2 hbody)
    change (binaryFormulaCode (Rewriting.free body)).length <=
      boundedUniversalClosedFormulaEnvelope syntaxCode + 2 * bodyCode
    omega
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅ fuel
    (Rewriting.free body) caseResource
  have hbranch : branchResource <= branchBound := by
    dsimp only [branchResource, branchBound]
    exact contextualBranchesUnderBoundPayloadEnvelope_le_fixedAssembly ∅ fuel
      syntaxCode formulaCode caseResource caseBound (Rewriting.free body)
      hsyntax hclosed htarget (by simp) (by
        intro formula hformula
        simp at hformula) hcase
  let exactTerm := compactParserSyntaxExactFuelTerm inputCount
  let boundTerm := Rew.bShift exactTerm
  have hexactCode : (binaryTermCode exactTerm).length <=
      compactParserSyntaxExactFuelTermFixedCodePolynomial numericBound := by
    dsimp only [exactTerm]
    exact compactParserSyntaxExactFuelTerm_code_length_le_fixed inputCount
      numericBound hinputCount
  have hexactSymbols := termSymbolCount_le_binaryTermCode_length exactTerm
  have hshift := binaryTermCode_bShift_length_le_add_symbols exactTerm
  have hshellBase :
      compactParserSyntaxExactFuelTermFixedCodePolynomial numericBound <=
        binaryNumeralTermCodeEnvelope shellBit := by
    have hbudget : 1 <= binaryNumeralStepBudget := by
      have htrue := four_le_binaryTermCode_length
        (binaryNumeralBitTerm true arithmeticZeroTerm)
      unfold binaryNumeralStepBudget
      omega
    have hpolyLeShell :
        compactParserSyntaxExactFuelTermFixedCodePolynomial numericBound <=
          shellBit := by
      dsimp only [shellBit]
      unfold compactParserSyntaxExactAdjacentUniversalShellBitPolynomial
      omega
    have hshellLeBudget :
        shellBit <= binaryNumeralStepBudget * shellBit := by
      simpa only [Nat.one_mul, Nat.mul_one, Nat.mul_comm] using
        Nat.mul_le_mul_right shellBit hbudget
    unfold binaryNumeralTermCodeEnvelope
    omega
  have hboundTerm : (binaryTermCode boundTerm).length <=
      3 * binaryNumeralTermCodeEnvelope shellBit := by
    dsimp only [boundTerm]
    omega
  have hshell :=
    compileContextualTermBoundedUniversalPayloadEnvelope_termCode_le_fixed_of_context
      body ∅ boundTerm fuel numericBound shellBit syntaxCode bodyCode
      equalityBound branchResource equalityBound branchBound hfuel hboundTerm
      hsyntax hbody (Nat.le_refl _) hbranch (by simp) (by
        intro formula hformula
        simp at hformula) (by
        intro formula hformula
        simp at hformula)
  simpa only [
    compactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversalResource,
    compactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedUniversalPolynomial,
    fuel, body, leafBound, bodyCode, syntaxCode, formulaCode, caseBound,
    branchBound, equalityBound, shellBit, caseResource, branchResource,
    exactTerm, boundTerm] using hshell

#print axioms
  compactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversalResource_le_polynomial

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedUniversalPolynomial
