import integration.FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicFullyFixedBounds
import integration.FoundationCompactPAClosedDirectContextTransport
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities

/-! # Closed-form public fixed transform-step proof at any valuation -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicFullyFixedClosedBounds

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAClosedDirectContextTransport
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStepRowsFormulaFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicFullyFixedBounds

noncomputable def compactFormulaTransformStepRowsPublicFullyFixedClosedBoundAtValuation
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformStepRows tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount) :
    ExplicitDirectFormulaBound valuation
      (compactFormulaTransformStepRowsClosedFormula tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount)
      (compactFormulaTransformStepRowsPublicFullyFixedPayloadPolynomial
        tokenTable width tokenCount current next mode stepWitness consumedCount
        mappedHead witnessStart witnessFinish witnessCount) := by
  let explicitBound :=
    compactFormulaTransformStepRowsPublicFullyFixedBoundOfGraph tokenTable width
      tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount hgraph
  have halignment :
      compactFormulaTransformStepRowsExplicitFormula tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount =
        compactFormulaTransformStepRowsClosedFormula tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount :=
    (compactFormulaTransformStepRowsClosedFormula_alignment tokenTable width
      tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount).symm
  let closedAtZero := castValuationContextProof halignment explicitBound.proof
  have hclosed := compactFormulaTransformStepRowsClosedFormula_closed
    tokenTable width tokenCount current next mode stepWitness consumedCount
    mappedHead witnessStart witnessFinish witnessCount
  let proof := transportClosedDirectProofAtValuation
    (target := valuation) closedAtZero hclosed
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = closedAtZero.payloadLength by
    exact transportClosedDirectProofAtValuation_payloadLength_eq
      (target := valuation) closedAtZero hclosed]
  rw [show closedAtZero.payloadLength = explicitBound.proof.payloadLength by
    exact castValuationContextProof_payloadLength_eq halignment
      explicitBound.proof]
  exact explicitBound.payloadLength_le

theorem
    compactFormulaTransformStepRowsPublicFullyFixedClosedBoundAtValuation_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformStepRows tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount) :
    (compactFormulaTransformStepRowsPublicFullyFixedClosedBoundAtValuation
      valuation tokenTable width tokenCount current next mode stepWitness
      consumedCount mappedHead witnessStart witnessFinish witnessCount
      hgraph).proof.payloadLength <=
      compactFormulaTransformStepRowsPublicFullyFixedPayloadPolynomial
        tokenTable width tokenCount current next mode stepWitness consumedCount
        mappedHead witnessStart witnessFinish witnessCount :=
  (compactFormulaTransformStepRowsPublicFullyFixedClosedBoundAtValuation
    valuation tokenTable width tokenCount current next mode stepWitness
    consumedCount mappedHead witnessStart witnessFinish witnessCount
    hgraph).payloadLength_le

#print axioms
  compactFormulaTransformStepRowsPublicFullyFixedClosedBoundAtValuation
#print axioms
  compactFormulaTransformStepRowsPublicFullyFixedClosedBoundAtValuation_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicFullyFixedClosedBounds
