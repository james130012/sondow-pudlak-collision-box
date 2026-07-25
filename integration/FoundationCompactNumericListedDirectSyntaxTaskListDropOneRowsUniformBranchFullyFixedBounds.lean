import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsTerminalPayloadFixedBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity04Bounds

/-!
# Fully fixed four-witness branch for syntax-task drop one
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsUniformBranchFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity04Bounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsTerminalSyntaxFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsTerminalPayloadFixedBounds

private abbrev dropOneZeroValuationBranch : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation

private theorem valuationContextFormulaCodeSum_le_dropOneBranchFixed
    (valuation : Nat -> Nat) {arity : Nat}
    (formula : ArithmeticSemiformula Nat arity)
    (numericBound : Nat)
    (hvariables : formula.freeVariables ⊆ {0})
    (hvaluation : valuation 0 <= numericBound) :
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
        (valuationContext formula.freeVariables valuation) <=
      taskDropOneTerminalContextCodePolynomial numericBound := by
  have hcard : formula.freeVariables.card <= 1 :=
    (Finset.card_le_card hvariables).trans (by simp)
  have hvalues : forall index, index ∈ formula.freeVariables ->
      valuation index <= numericBound := by
    intro index hindex
    have hsingleton := hvariables hindex
    simp only [Finset.mem_singleton] at hsingleton
    subst index
    exact hvaluation
  have htermCodes : forall index, index ∈ formula.freeVariables ->
      (binaryTermCode (&index : ValuationTerm)).length <=
        (binaryTermCode (&0 : ValuationTerm)).length := by
    intro index hindex
    have hsingleton := hvariables hindex
    simp only [Finset.mem_singleton] at hsingleton
    subst index
    exact le_rfl
  have hraw := valuationContext_formulaCodeSum_le_uniform
    formula.freeVariables valuation 1 numericBound
      (binaryTermCode (&0 : ValuationTerm)).length hcard hvalues htermCodes
  simpa only [
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum,
    FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum,
    taskDropOneTerminalContextCodePolynomial] using hraw

def taskDropOneUniformBranchFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity04
    (taskDropOneTerminalContextCodePolynomial numericBound)
    numericBound
    (taskDropOneTerminalFormulaCodePolynomial bitBound)
    (taskDropOneTerminalFullyFixedPayloadPolynomial numericBound bitBound)

theorem
    compactAdditiveSyntaxTaskListDropOneRowsBranchStructuralPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary targetBoundary index
      numericBound bitBound : Nat)
    (data : CompactAdditiveSyntaxTaskListDropRowData tokenTable width
      tokenCount sourceBoundary targetBoundary 1 index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceNextIndex : 1 + index + 1 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary 1 index
        data <=
      taskDropOneUniformBranchFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let valuation := extendValuation index dropOneZeroValuationBranch
  let body :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchTerminal tokenTable
      width tokenCount sourceBoundary targetBoundary 1
  let values : Fin 4 -> Nat :=
    ![data.targetRight, data.targetLeft, data.sourceRight, data.sourceLeft]
  have hvalues : forall coordinate, values coordinate <= tokenCount := by
    intro coordinate
    fin_cases coordinate
    · exact data.targetRight_le
    · exact data.targetLeft_le
    · exact data.sourceRight_le
    · exact data.sourceLeft_le
  have hindex : index <= numericBound := by omega
  have hvaluation : valuation 0 <= numericBound := by
    change index <= numericBound
    exact hindex
  have hbodyVariables : body.freeVariables ⊆ {0} := by
    dsimp only [body]
    rw [compactAdditiveSyntaxTaskListDropOneRowsBranchTerminal_eq_explicit]
    exact taskDropOneBranchTerminalExplicit_freeVariables_subset_singleton
      tokenTable width tokenCount sourceBoundary targetBoundary
  have hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext body.freeVariables valuation) <=
        taskDropOneTerminalContextCodePolynomial numericBound := by
    exact valuationContextFormulaCodeSum_le_dropOneBranchFixed valuation body
      numericBound hbodyVariables hvaluation
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hbody :
      (binaryFormulaCode body).length <=
        taskDropOneTerminalFormulaCodePolynomial bitBound := by
    dsimp only [body]
    rw [compactAdditiveSyntaxTaskListDropOneRowsBranchTerminal_eq_explicit]
    exact taskDropOneBranchTerminalExplicit_code_length_le_fixed tokenTable
      width tokenCount sourceBoundary targetBoundary bitBound htokenTableSize
      hwidthSize htokenCountSize hsourceBoundarySize htargetBoundarySize
  have hterminal :=
    compactAdditiveSyntaxTaskListDropOneRowsTerminalStructuralPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount sourceBoundary targetBoundary index
      numericBound bitBound data hwidth htokenCount hsourceNextIndex
      htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  have hfixed :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity04
      (terminalSmall :=
        compactAdditiveSyntaxTaskListDropFixedNumeralRowsTerminalStructuralPayloadEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary 1 index
          data)
      (terminalLarge :=
        taskDropOneTerminalFullyFixedPayloadPolynomial numericBound bitBound)
      valuation (taskDropOneTerminalContextCodePolynomial numericBound)
      tokenCount numericBound
      (taskDropOneTerminalFormulaCodePolynomial bitBound)
      body values hvalues htokenCount hbody hcontext hterminal
  simpa only [
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchStructuralPayloadEnvelope,
    taskDropOneUniformBranchFullyFixedPayloadPolynomial, valuation, body,
    values, dropOneZeroValuationBranch] using hfixed

def taskDropOneAllBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound *
    taskDropOneUniformBranchFullyFixedPayloadPolynomial numericBound bitBound

theorem
    compactAdditiveSyntaxTaskListDropOneRowsBranchPayloadResourceSum_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      numericBound bitBound : Nat)
    (rows : (index : Fin targetCount) ->
      CompactAdditiveSyntaxTaskListDropRowData tokenTable width tokenCount
        sourceBoundary targetBoundary 1 index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hshiftedCount : 1 + targetCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchPayloadResourceSum
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        1 rows <=
      taskDropOneAllBranchesFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let resource :=
    taskDropOneUniformBranchFullyFixedPayloadPolynomial numericBound bitBound
  have htargetCount : targetCount <= numericBound := by omega
  have hsum :
      (∑ index : Fin targetCount,
        compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchStructuralPayloadEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary 1 index
          (rows index)) <=
        ∑ _index : Fin targetCount, resource := by
    apply Finset.sum_le_sum
    intro index _
    have hsourceNextIndex :
        1 + index.val + 1 <= numericBound := by
      have hindex : index.val + 1 <= targetCount :=
        Nat.succ_le_of_lt index.isLt
      omega
    exact
      compactAdditiveSyntaxTaskListDropOneRowsBranchStructuralPayloadEnvelope_le_fullyFixed
        tokenTable width tokenCount sourceBoundary targetBoundary index
        numericBound bitBound (rows index) hwidth htokenCount
        hsourceNextIndex htokenTableSize hsourceBoundarySize
        htargetBoundarySize hnumericSize
  have hsum' :
      (∑ index : Fin targetCount,
        compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchStructuralPayloadEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary 1 index
          (rows index)) <= targetCount * resource := by
    simpa [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul] using hsum
  have hcount :
      targetCount * resource <= numericBound * resource :=
    Nat.mul_le_mul_right resource htargetCount
  unfold
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchPayloadResourceSum
    taskDropOneAllBranchesFullyFixedPayloadPolynomial
  simpa only [resource] using hsum'.trans hcount

#print axioms
  compactAdditiveSyntaxTaskListDropOneRowsBranchStructuralPayloadEnvelope_le_fullyFixed
#print axioms
  compactAdditiveSyntaxTaskListDropOneRowsBranchPayloadResourceSum_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsUniformBranchFullyFixedBounds
