import integration.FoundationCompactNumericListedDirectNatListSameRowsUniversalBodyFixedBounds

/-!
# Fully fixed row-branch resource for equal natural-list rows

The released outer row variable doubles the terminal formula-code bound.  The
four witness compiler is then instantiated directly with fixed context, body,
and terminal resources, eliminating all concrete row coordinates.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListSameRowsUniformBranchFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity04Bounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsFixedPolynomialBounds

private abbrev sameRowsZeroValuationBranchFixed : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate.zeroValuation

def sameRowsBranchTerminalFormulaCodePolynomial (bitBound : Nat) : Nat :=
  2 * sameRowsUniversalTerminalFormulaCodePolynomial bitBound

def sameRowsUniformBranchFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity04
    (sameRowsTerminalContextFormulaCodeSumEnvelope numericBound)
    numericBound
    (sameRowsBranchTerminalFormulaCodePolynomial bitBound)
    (sameRowsTerminalFullyFixedPayloadPolynomial numericBound bitBound)

theorem compactAdditiveNatListSameRowsBranchTerminal_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListSameRowsBranchTerminal tokenTable width tokenCount
        sourceBoundary targetBoundary)).length <=
      sameRowsBranchTerminalFormulaCodePolynomial bitBound := by
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hterminal :=
    compactAdditiveNatListSameRowsTerminal_code_length_le_fixed tokenTable
      width tokenCount sourceBoundary targetBoundary bitBound htokenTableSize
      hwidthSize htokenCountSize hsourceBoundarySize htargetBoundarySize
  have hfree := binaryFormulaCode_free_length_le
    (compactAdditiveNatListSameRowsTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary)
  rw [compactAdditiveNatListSameRowsTerminal_free_alignment] at hfree
  unfold sameRowsBranchTerminalFormulaCodePolynomial
  exact hfree.trans (Nat.mul_le_mul_left 2 hterminal)

private theorem valuationContextFormulaCodeSum_le_sameRowsSingletonBranchFixed
    (valuation : Nat -> Nat) {arity : Nat}
    (formula : ArithmeticSemiformula Nat arity)
    (numericBound : Nat)
    (hvariables : formula.freeVariables ⊆ {0})
    (hvaluation : valuation 0 <= numericBound) :
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
        (valuationContext formula.freeVariables valuation) <=
      sameRowsTerminalContextFormulaCodeSumEnvelope numericBound := by
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
    sameRowsTerminalContextFormulaCodeSumEnvelope] using hraw

theorem
    compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope_le_fullyUniform
    (tokenTable width tokenCount sourceBoundary targetBoundary index
      numericBound bitBound : Nat)
    (data : CompactAdditiveNatListSameRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope tokenTable
        width tokenCount sourceBoundary targetBoundary index data <=
      sameRowsUniformBranchFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let valuation := extendValuation index sameRowsZeroValuationBranchFixed
  let body := compactAdditiveNatListSameRowsBranchTerminal tokenTable width
    tokenCount sourceBoundary targetBoundary
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
  have hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext body.freeVariables valuation) <=
        sameRowsTerminalContextFormulaCodeSumEnvelope numericBound := by
    exact
      valuationContextFormulaCodeSum_le_sameRowsSingletonBranchFixed valuation
        body numericBound
        (compactAdditiveNatListSameRowsBranchTerminal_freeVariables_subset_singleton
          tokenTable width tokenCount sourceBoundary targetBoundary)
        hvaluation
  have hbody :=
    compactAdditiveNatListSameRowsBranchTerminal_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound hwidth htokenCount htokenTableSize hsourceBoundarySize
      htargetBoundarySize hnumericSize
  have hterminal :=
    compactAdditiveNatListSameRowsTerminalStructuralPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount sourceBoundary targetBoundary index
      numericBound bitBound data hwidth htokenCount hindexSuccessor
      htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  have hfixed :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity04
      (terminalSmall :=
        compactAdditiveNatListSameRowsTerminalStructuralPayloadEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary index data)
      (terminalLarge :=
        sameRowsTerminalFullyFixedPayloadPolynomial numericBound bitBound)
      valuation
      (sameRowsTerminalContextFormulaCodeSumEnvelope numericBound)
      tokenCount numericBound
      (sameRowsBranchTerminalFormulaCodePolynomial bitBound)
      body values hvalues htokenCount hbody hcontext hterminal
  simpa only [compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope,
    sameRowsUniformBranchFullyFixedPayloadPolynomial, valuation, body, values,
    sameRowsZeroValuationBranchFixed] using hfixed

def sameRowsAllBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound *
    sameRowsUniformBranchFullyFixedPayloadPolynomial numericBound bitBound

theorem compactAdditiveNatListSameRowsBranchPayloadResourceSum_le_fullyUniform
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListSameRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListSameRowsBranchPayloadResourceSum tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows <=
      sameRowsAllBranchesFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let resource :=
    sameRowsUniformBranchFullyFixedPayloadPolynomial numericBound bitBound
  have hsum :
      (∑ index : Fin sourceCount,
        compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope tokenTable
          width tokenCount sourceBoundary targetBoundary index
          (rows index)) <=
        ∑ _index : Fin sourceCount, resource := by
    apply Finset.sum_le_sum
    intro index _
    have hindexSuccessor : index.val + 1 <= numericBound :=
      (Nat.succ_le_of_lt index.isLt).trans hsourceCount
    exact
      compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope_le_fullyUniform
        tokenTable width tokenCount sourceBoundary targetBoundary index
        numericBound bitBound (rows index) hwidth htokenCount hindexSuccessor
        htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  have hcountResource :
      sourceCount * resource <= numericBound * resource :=
    Nat.mul_le_mul_right resource hsourceCount
  have hsum' :
      (∑ index : Fin sourceCount,
        compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope tokenTable
          width tokenCount sourceBoundary targetBoundary index
          (rows index)) <= sourceCount * resource := by
    simpa [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul] using hsum
  unfold compactAdditiveNatListSameRowsBranchPayloadResourceSum
    sameRowsAllBranchesFullyFixedPayloadPolynomial
  simpa only [resource] using hsum'.trans hcountResource

#print axioms
  compactAdditiveNatListSameRowsBranchTerminal_code_length_le_fixed
#print axioms
  compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope_le_fullyUniform
#print axioms
  compactAdditiveNatListSameRowsBranchPayloadResourceSum_le_fullyUniform

end FoundationCompactNumericListedDirectNatListSameRowsUniformBranchFullyFixedBounds
