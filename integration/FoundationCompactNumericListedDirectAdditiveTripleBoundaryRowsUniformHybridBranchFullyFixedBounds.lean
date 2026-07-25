import integration.FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectFixedPolynomialBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-!
# Fully fixed hybrid branches for additive triple-boundary rows

The original hybrid certificate is bounded on the actual checked row data.
This avoids the older public envelope that enumerates every pair of values.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 50000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformHybridBranchFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsPublicBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsFixedWidthEntryBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsDirectUniformContextBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectFixedPolynomialBounds

private abbrev tripleZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate.zeroValuation

def tripleBoundaryRowUniformHybridBranchFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02
    (tripleBoundaryTerminalContextFormulaCodeSumEnvelope numericBound)
    numericBound
    (tripleBoundaryRowDirectTerminalFormulaCodePolynomial bitBound)
    (tripleBoundaryTerminalFullyUniformPayloadPolynomial numericBound bitBound)

theorem
    compactAdditiveTripleBoundaryRowsExplicitBranchEnvelope_le_fullyFixed
    (tokenCount boundaryTable index numericBound bitBound : Nat)
    (data : CompactAdditiveTripleBoundaryRowData
      tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    explicitBoundedWitnessHybridStructuralPayloadEnvelope
        (extendValuation index tripleZeroValuation) tokenCount
        (compactAdditiveTripleBoundaryRowsBranchTerminal
          tokenCount boundaryTable)
        (![data.right, data.left] : Fin 2 -> Nat)
        (compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelope
          tokenCount boundaryTable index data) <=
      tripleBoundaryRowUniformHybridBranchFixedPayloadPolynomial
        numericBound bitBound := by
  let valuation := extendValuation index tripleZeroValuation
  let body :=
    compactAdditiveTripleBoundaryRowsBranchTerminal tokenCount boundaryTable
  let values : Fin 2 -> Nat := ![data.right, data.left]
  have hvalues : forall coordinate, values coordinate <= tokenCount := by
    intro coordinate
    fin_cases coordinate
    · exact data.right_le
    · exact data.left_le
  have hindex : index <= numericBound := by omega
  have htokenSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hbody :
      (binaryFormulaCode body).length <=
        tripleBoundaryRowDirectTerminalFormulaCodePolynomial bitBound := by
    dsimp only [body]
    exact compactAdditiveTripleBoundaryRowsBranchTerminal_code_length_le_fixed
      tokenCount boundaryTable bitBound htokenSize htableSize
  have hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext body.freeVariables valuation) <=
        tripleBoundaryTerminalContextFormulaCodeSumEnvelope numericBound := by
    dsimp only [body, valuation]
    exact
      compactAdditiveTripleBoundaryRowsBranchTerminal_contextCodeSum_le
        tokenCount boundaryTable index numericBound hindex
  have hterminal :=
    compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelope_le_fullyUniform
      tokenCount boundaryTable index numericBound bitBound data htokenCount
      hindexSuccessor htableSize hnumericSize
  have hfixed :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity02
      (terminalSmall :=
        compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelope
          tokenCount boundaryTable index data)
      (terminalLarge :=
        tripleBoundaryTerminalFullyUniformPayloadPolynomial
          numericBound bitBound)
      valuation
      (tripleBoundaryTerminalContextFormulaCodeSumEnvelope numericBound)
      tokenCount numericBound
      (tripleBoundaryRowDirectTerminalFormulaCodePolynomial bitBound)
      body values hvalues htokenCount hbody hcontext hterminal
  simpa only [tripleBoundaryRowUniformHybridBranchFixedPayloadPolynomial,
    valuation, body, values] using hfixed

def tripleBoundaryRowsAllHybridBranchesFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound *
    tripleBoundaryRowUniformHybridBranchFixedPayloadPolynomial
      numericBound bitBound

theorem
    compactAdditiveTripleBoundaryRowsBranchStructuralPayloadResourceSum_le_fullyFixed
    (tokenCount count boundaryTable numericBound bitBound : Nat)
    (rows : (index : Fin count) ->
      CompactAdditiveTripleBoundaryRowData tokenCount boundaryTable index)
    (htokenCount : tokenCount <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveTripleBoundaryRowsBranchStructuralPayloadResourceSum
        tokenCount count boundaryTable rows <=
      tripleBoundaryRowsAllHybridBranchesFixedPayloadPolynomial
        numericBound bitBound := by
  let resource :=
    tripleBoundaryRowUniformHybridBranchFixedPayloadPolynomial
      numericBound bitBound
  have hsum :
      (∑ index : Fin count,
        compactAdditiveTripleBoundaryRowsBranchStructuralPayloadEnvelope
          tokenCount boundaryTable index (rows index)) <=
        ∑ _index : Fin count, resource := by
    apply Finset.sum_le_sum
    intro index _
    have hindexSuccessor : index.val + 1 <= numericBound := by
      have hindex : index.val + 1 <= count :=
        Nat.succ_le_of_lt index.isLt
      omega
    change
      explicitBoundedWitnessHybridStructuralPayloadEnvelope
          (extendValuation index tripleZeroValuation) tokenCount
          (compactAdditiveTripleBoundaryRowsBranchTerminal
            tokenCount boundaryTable)
          (![(rows index).right, (rows index).left] : Fin 2 -> Nat)
          (compactAdditiveTripleBoundaryRowsTerminalStructuralPayloadEnvelope
            tokenCount boundaryTable index (rows index)) <= resource
    exact
      compactAdditiveTripleBoundaryRowsExplicitBranchEnvelope_le_fullyFixed
        tokenCount boundaryTable index numericBound bitBound (rows index)
        htokenCount hindexSuccessor htableSize hnumericSize
  have hsum' :
      (∑ index : Fin count,
        compactAdditiveTripleBoundaryRowsBranchStructuralPayloadEnvelope
          tokenCount boundaryTable index (rows index)) <=
        count * resource := by
    simpa [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul] using hsum
  have htotal : count * resource <= numericBound * resource :=
    Nat.mul_le_mul_right resource hcount
  unfold compactAdditiveTripleBoundaryRowsBranchStructuralPayloadResourceSum
    tripleBoundaryRowsAllHybridBranchesFixedPayloadPolynomial
  simpa only [resource] using hsum'.trans htotal

#print axioms
  compactAdditiveTripleBoundaryRowsExplicitBranchEnvelope_le_fullyFixed
#print axioms
  compactAdditiveTripleBoundaryRowsBranchStructuralPayloadResourceSum_le_fullyFixed

end FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformHybridBranchFullyFixedBounds
