import integration.FoundationCompactNumericListedDirectNatListDropThreeRowsTerminalSyntaxFixedBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity04Bounds

/-!
# Fully fixed branch resources for drop-one natural-list rows

The checked graph supplies every row datum and index bound.  One four-witness
branch is bounded uniformly, then all target rows are summed under the shared
numeric coordinate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListDropThreeRowsUniformBranchFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity04Bounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactNumericListedDirectNatListDropRows
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectNatListDropThreeRowsIndexSemanticFixedBounds
open FoundationCompactNumericListedDirectNatListDropThreeRowsTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectNatListDropThreeRowsTerminalSyntaxFixedBounds

def dropThreeRowsUniformBranchFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity04
    (dropThreeRowsTerminalContextCodePolynomial numericBound)
    numericBound
    (dropThreeRowsBranchTerminalFormulaCodePolynomial bitBound)
    (dropThreeRowsTerminalFullyFixedPayloadPolynomial numericBound bitBound)

private theorem
    valuationContextFormulaCodeSum_le_dropThreeSingletonBranchFixed
    (valuation : Nat -> Nat) {arity : Nat}
    (formula : ArithmeticSemiformula Nat arity)
    (numericBound : Nat)
    (hvariables : formula.freeVariables ⊆ {0})
    (hvaluation : valuation 0 <= numericBound) :
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
        (valuationContext formula.freeVariables valuation) <=
      dropThreeRowsTerminalContextCodePolynomial numericBound := by
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
    dropThreeRowsTerminalContextCodePolynomial] using hraw

theorem
    compactAdditiveNatListDropThreeRowsBranchStructuralPayloadEnvelope_le_fullyUniform
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 3)
    (index : Fin targetCount)
    (data : CompactAdditiveNatListDropRowData tokenTable width tokenCount
      sourceBoundary targetBoundary 3 index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary 3 index data <=
      dropThreeRowsUniformBranchFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let valuation := dropThreeRowsValuation index
  let body :=
    compactAdditiveNatListDropFixedNumeralRowsBranchTerminal tokenTable width
      tokenCount sourceBoundary targetBoundary 3
  let values : Fin 4 -> Nat :=
    ![data.targetRight, data.targetLeft, data.sourceRight, data.sourceLeft]
  have hvalues : forall coordinate, values coordinate <= tokenCount := by
    intro coordinate
    fin_cases coordinate
    · exact data.targetRight_le
    · exact data.targetLeft_le
    · exact data.sourceRight_le
    · exact data.sourceLeft_le
  have hindices := dropThreeRowsIndexSemanticBounds_of_graph tokenTable width
    tokenCount sourceBoundary sourceCount targetBoundary targetCount
    numericBound bitBound hgraph index hsourceCount hnumericSize
  have hvaluation : valuation 0 <= numericBound := by
    change index.val <= numericBound
    exact hindices.targetIndexValue
  have hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext body.freeVariables valuation) <=
        dropThreeRowsTerminalContextCodePolynomial numericBound := by
    exact valuationContextFormulaCodeSum_le_dropThreeSingletonBranchFixed
      valuation body numericBound
      (compactAdditiveNatListDropThreeRowsBranchTerminal_freeVariables_subset_singleton
        tokenTable width tokenCount sourceBoundary targetBoundary)
      hvaluation
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hbody :
      (binaryFormulaCode body).length <=
        dropThreeRowsBranchTerminalFormulaCodePolynomial bitBound := by
    dsimp only [body]
    exact compactAdditiveNatListDropThreeRowsBranchTerminal_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary bitBound
      htokenTableSize hwidthSize htokenCountSize hsourceBoundarySize
      htargetBoundarySize
  have hterminal :=
    compactAdditiveNatListDropThreeRowsTerminalStructuralPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound hgraph index data hwidth htokenCount
      hsourceCount htokenTableSize hsourceBoundarySize htargetBoundarySize
      hnumericSize
  have hfixed :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity04
      (terminalSmall :=
        compactAdditiveNatListDropFixedNumeralRowsTerminalStructuralPayloadEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary 3 index data)
      (terminalLarge :=
        dropThreeRowsTerminalFullyFixedPayloadPolynomial numericBound bitBound)
      valuation
      (dropThreeRowsTerminalContextCodePolynomial numericBound)
      tokenCount numericBound
      (dropThreeRowsBranchTerminalFormulaCodePolynomial bitBound)
      body values hvalues htokenCount hbody hcontext hterminal
  unfold
    compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelope
    dropThreeRowsUniformBranchFullyFixedPayloadPolynomial
  change
    explicitBoundedWitnessHybridStructuralPayloadEnvelope valuation tokenCount
        body values
        (compactAdditiveNatListDropFixedNumeralRowsTerminalStructuralPayloadEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary 3 index
          data) <=
      explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity04
        (dropThreeRowsTerminalContextCodePolynomial numericBound)
        numericBound
        (dropThreeRowsBranchTerminalFormulaCodePolynomial bitBound)
        (dropThreeRowsTerminalFullyFixedPayloadPolynomial numericBound bitBound)
  exact hfixed

#print axioms
  compactAdditiveNatListDropThreeRowsBranchStructuralPayloadEnvelope_le_fullyUniform

def dropThreeRowsAllBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound *
    dropThreeRowsUniformBranchFullyFixedPayloadPolynomial numericBound bitBound

theorem
    compactAdditiveNatListDropThreeRowsBranchPayloadResourceSum_le_fullyUniform
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 3)
    (rows : (index : Fin targetCount) ->
      CompactAdditiveNatListDropRowData tokenTable width tokenCount
        sourceBoundary targetBoundary 3 index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListDropFixedNumeralRowsBranchPayloadResourceSum
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        3 rows <=
      dropThreeRowsAllBranchesFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let resource :=
    dropThreeRowsUniformBranchFullyFixedPayloadPolynomial numericBound bitBound
  have htargetCount : targetCount <= numericBound := by
    rw [hgraph.2.1] at hsourceCount
    omega
  have hsum :
      (∑ index : Fin targetCount,
        compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary 3 index
          (rows index)) <=
        ∑ _index : Fin targetCount, resource := by
    apply Finset.sum_le_sum
    intro index _
    exact
      compactAdditiveNatListDropThreeRowsBranchStructuralPayloadEnvelope_le_fullyUniform
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount numericBound bitBound hgraph index (rows index) hwidth
        htokenCount hsourceCount htokenTableSize hsourceBoundarySize
        htargetBoundarySize hnumericSize
  have hsum' :
      (∑ index : Fin targetCount,
        compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary 3 index
          (rows index)) <= targetCount * resource := by
    simpa [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul] using hsum
  have hcountResource :
      targetCount * resource <= numericBound * resource :=
    Nat.mul_le_mul_right resource htargetCount
  unfold compactAdditiveNatListDropFixedNumeralRowsBranchPayloadResourceSum
    dropThreeRowsAllBranchesFullyFixedPayloadPolynomial
  simpa only [resource] using hsum'.trans hcountResource

#print axioms
  compactAdditiveNatListDropThreeRowsBranchPayloadResourceSum_le_fullyUniform

end FoundationCompactNumericListedDirectNatListDropThreeRowsUniformBranchFullyFixedBounds
