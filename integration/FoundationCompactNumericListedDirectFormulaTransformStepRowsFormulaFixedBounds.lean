import integration.FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Fixed complete syntax for one formula-transform step -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000

namespace FoundationCompactNumericListedDirectFormulaTransformStepRowsFormulaFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate

def compactFormulaTransformStepRowsClosedTerms
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    Fin 38 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm current.start,
    shortBinaryNumeralTerm current.finish,
    shortBinaryNumeralTerm current.parserFinish,
    shortBinaryNumeralTerm current.parserTokensFinish,
    shortBinaryNumeralTerm current.parserTasksFinish,
    shortBinaryNumeralTerm current.parserTokensBoundary,
    shortBinaryNumeralTerm current.parserTokensCount,
    shortBinaryNumeralTerm current.parserTasksBoundary,
    shortBinaryNumeralTerm current.parserTasksCount,
    shortBinaryNumeralTerm current.outputBoundary,
    shortBinaryNumeralTerm current.outputCount,
    shortBinaryNumeralTerm next.start,
    shortBinaryNumeralTerm next.finish,
    shortBinaryNumeralTerm next.parserFinish,
    shortBinaryNumeralTerm next.parserTokensFinish,
    shortBinaryNumeralTerm next.parserTasksFinish,
    shortBinaryNumeralTerm next.parserTokensBoundary,
    shortBinaryNumeralTerm next.parserTokensCount,
    shortBinaryNumeralTerm next.parserTasksBoundary,
    shortBinaryNumeralTerm next.parserTasksCount,
    shortBinaryNumeralTerm next.outputBoundary,
    shortBinaryNumeralTerm next.outputCount,
    shortBinaryNumeralTerm mode,
    shortBinaryNumeralTerm stepWitness.slot0,
    shortBinaryNumeralTerm stepWitness.slot1,
    shortBinaryNumeralTerm stepWitness.slot2,
    shortBinaryNumeralTerm stepWitness.slot3,
    shortBinaryNumeralTerm stepWitness.slot4,
    shortBinaryNumeralTerm stepWitness.slot5,
    shortBinaryNumeralTerm stepWitness.slot6,
    shortBinaryNumeralTerm consumedCount,
    shortBinaryNumeralTerm mappedHead,
    shortBinaryNumeralTerm witnessStart,
    shortBinaryNumeralTerm witnessFinish,
    shortBinaryNumeralTerm witnessCount]

theorem compactFormulaTransformStepRowsClosedTerms_eq_environment
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (coordinate : Fin 38) :
    compactFormulaTransformStepRowsClosedTerms tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount coordinate =
      shortBinaryNumeralTerm
        (compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount coordinate) := by
  fin_cases coordinate <;>
    rfl

def compactFormulaTransformStepRowsFullFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  let source : LO.FirstOrder.ArithmeticSemiformula Nat 38 :=
    Rewriting.emb (ξ := Nat) compactFormulaTransformStepRowsDef.val
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 0
    (binaryNumeralTermCodeEnvelope bitBound) (binaryFormulaCode source).length

def compactFormulaTransformStepRowsOuterSyntaxPolynomial
    (bitBound : Nat) : Nat :=
  compactFormulaTransformStepRowsFullFormulaCodePolynomial bitBound + 1

theorem compactFormulaTransformStepRowsOuterSyntaxPolynomial_positive
    (bitBound : Nat) :
    1 <= compactFormulaTransformStepRowsOuterSyntaxPolynomial bitBound := by
  unfold compactFormulaTransformStepRowsOuterSyntaxPolynomial
  omega

theorem compactFormulaTransformStepRowsClosedFormula_code_length_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount
      bitBound : Nat)
    (henvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount coordinate) <= bitBound) :
    (binaryFormulaCode
      (compactFormulaTransformStepRowsClosedFormula tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount)).length <=
      compactFormulaTransformStepRowsFullFormulaCodePolynomial bitBound := by
  let terms := compactFormulaTransformStepRowsClosedTerms tokenTable width
    tokenCount current next mode stepWitness consumedCount mappedHead
    witnessStart witnessFinish witnessCount
  let source : LO.FirstOrder.ArithmeticSemiformula Nat 38 :=
    Rewriting.emb (ξ := Nat) compactFormulaTransformStepRowsDef.val
  have hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <=
        binaryNumeralTermCodeEnvelope bitBound := by
    intro coordinate
    dsimp only [terms]
    rw [compactFormulaTransformStepRowsClosedTerms_eq_environment]
    exact binaryNumeralTerm_code_length_le_envelope _ bitBound
      (henvironmentSize coordinate)
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 (binaryNumeralTermCodeEnvelope bitBound)
      (binaryFormulaCode source).length terms source hterms le_rfl
  unfold compactFormulaTransformStepRowsClosedFormula
    compactFormulaTransformStepRowsFullFormulaCodePolynomial
  simpa only [sourceSubstitutionQpow, terms, source,
    compactFormulaTransformStepRowsClosedTerms] using hraw

theorem compactFormulaTransformStepRowsExplicitFormula_code_length_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount
      bitBound : Nat)
    (henvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformStepRowsEnvironment tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount coordinate) <= bitBound) :
    (binaryFormulaCode
      (compactFormulaTransformStepRowsExplicitFormula tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount)).length <=
      compactFormulaTransformStepRowsOuterSyntaxPolynomial bitBound := by
  have hraw :=
    compactFormulaTransformStepRowsClosedFormula_code_length_le_fixed
      tokenTable width tokenCount current next mode stepWitness consumedCount
      mappedHead witnessStart witnessFinish witnessCount bitBound
      henvironmentSize
  rw [compactFormulaTransformStepRowsClosedFormula_alignment] at hraw
  unfold compactFormulaTransformStepRowsOuterSyntaxPolynomial
  omega

theorem compactFormulaTransformStepRowsClosedFormula_closed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    (compactFormulaTransformStepRowsClosedFormula tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount).freeVariables = ∅ := by
  unfold compactFormulaTransformStepRowsClosedFormula
  change
    ((Rewriting.emb (ξ := Nat) compactFormulaTransformStepRowsDef.val) ⇜
      compactFormulaTransformStepRowsClosedTerms tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount).freeVariables = ∅
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  rw [compactFormulaTransformStepRowsClosedTerms_eq_environment]
  exact shortBinaryNumeralTerm_freeVariables_eq_empty _

theorem compactFormulaTransformStepRowsExplicitFormula_closed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    (compactFormulaTransformStepRowsExplicitFormula tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount).freeVariables = ∅ := by
  rw [← compactFormulaTransformStepRowsClosedFormula_alignment]
  exact compactFormulaTransformStepRowsClosedFormula_closed tokenTable width
    tokenCount current next mode stepWitness consumedCount mappedHead
    witnessStart witnessFinish witnessCount

#print axioms compactFormulaTransformStepRowsClosedFormula_code_length_le_fixed
#print axioms compactFormulaTransformStepRowsExplicitFormula_closed

end FoundationCompactNumericListedDirectFormulaTransformStepRowsFormulaFixedBounds
