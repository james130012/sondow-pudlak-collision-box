import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedFixedCorePublicDirectCompiler
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity14

/-! # Fixed-core public compiler for the fourteen current-state witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedFixedCorePublicDirectCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity14
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedFixedCorePublicDirectCompiler
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicCodeBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds

noncomputable def
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicDirectPayloadEnvelopeOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound) : Nat :=
  let data := compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound hcurrent
  let witness := data.witness
  let innerResource :=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexFixedCorePublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
  explicitBoundedWitnessDirectPublicPayloadEnvelope 14
    (compactFormulaTransformAdjacentPublicContextCodeBound valuation rowIndexTerm)
    valueBound
    (compactFormulaTransformAdjacentCurrentRawTerminalPublicCodeEnvelope tokenTable
      width tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
      witnessFinish witnessCount valueBound)
    innerResource

noncomputable def
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicDirectBoundOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound) :
    ExplicitDirectFormulaBound valuation
      (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound)
      (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicDirectPayloadEnvelopeOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        hcurrent) := by
  let data := compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound hcurrent
  let witness := data.witness
  let values := adjacentCurrentBoundedWitnessValues witness
  let rawBody := compactFormulaTransformAdjacentCurrentBoundedRawTerminal
    tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
    witnessStart witnessFinish witnessCount valueBound
  let bodyCodeBound :=
    compactFormulaTransformAdjacentCurrentRawTerminalPublicCodeEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound
  let contextCodeBound :=
    compactFormulaTransformAdjacentPublicContextCodeBound valuation rowIndexTerm
  have hbody : (binaryFormulaCode rawBody).length <= bodyCodeBound :=
    compactFormulaTransformAdjacentCurrentRawTerminal_code_length_le_public
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound
  have hcontext : formulaCodeSum
      (valuationContext rawBody.freeVariables valuation) <= contextCodeBound :=
    compactFormulaTransformAdjacentCurrentRawTerminal_context_le_public
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
  let innerDirect :=
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexFixedCorePublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.values_le data.next
  let innerResource :=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexFixedCorePublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
  have hinner : innerDirect.payloadLength <= innerResource :=
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexFixedCorePublicDirectOfGraph_payloadLength_le
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.values_le data.next
  let rawTerminal := castValuationContextProof
    (compactFormulaTransformAdjacentCurrentBoundedRawTerminal_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound witness).symm innerDirect
  have hrawTerminal : rawTerminal.payloadLength <= innerResource := by
    change (castValuationContextProof
      (compactFormulaTransformAdjacentCurrentBoundedRawTerminal_alignment
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound witness).symm
      innerDirect).payloadLength <= _
    rw [castValuationContextProof_payloadLength_eq]
    exact hinner
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 14 rawBody
  let compilation := compileExplicitBoundedWitnessDirectPublicWithResource
    contextCodeBound valueBound bodyCodeBound rawBody values data.values_le
      hbody hcontext innerResource rawTerminal hrawTerminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity14
      contextCodeBound valueBound bodyCodeBound rawBody values data.values_le
      hbody hcontext innerResource rawTerminal hrawTerminal
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound :=
    (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound).symm
  let proof := castValuationContextProof hformula rawProof
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = rawProof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula rawProof]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  simpa only [
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicDirectPayloadEnvelopeOfGraph,
    data, witness, innerResource, rawBody, bodyCodeBound, contextCodeBound,
    sourceFormula, compilation, rawProof] using hcoordinates.2

noncomputable def
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicDirectOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound) :=
  (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicDirectBoundOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound hcurrent).proof

theorem
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicDirectOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound) :
    (compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hcurrent).payloadLength <=
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hcurrent :=
  (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicDirectBoundOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound hcurrent).payloadLength_le

noncomputable def
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicAllRowsFiniteDirectPayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) : Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 14
    (compactFormulaTransformAdjacentPublicContextCodeBound valuation rowIndexTerm)
    valueBound
    (compactFormulaTransformAdjacentCurrentRawTerminalPublicCodeEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound)
    (compactFormulaTransformAdjacentNextBoundedAtValuationIndexFixedCorePublicAllRowsFiniteDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound)

noncomputable def
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicFiniteStepDirectPayloadEnvelopeOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (_hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound) : Nat :=
  compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicAllRowsFiniteDirectPayloadEnvelope
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound

noncomputable def
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicFiniteStepDirectBoundOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hindexVariables : rowIndexTerm.freeVariables ⊆ {0})
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound) :
    ExplicitDirectFormulaBound valuation
      (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound)
      (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicFiniteStepDirectPayloadEnvelopeOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        hcurrent) := by
  let data := compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound hcurrent
  let witness := data.witness
  let values := adjacentCurrentBoundedWitnessValues witness
  let rawBody := compactFormulaTransformAdjacentCurrentBoundedRawTerminal
    tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
    witnessStart witnessFinish witnessCount valueBound
  let bodyCodeBound :=
    compactFormulaTransformAdjacentCurrentRawTerminalPublicCodeEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound
  let contextCodeBound :=
    compactFormulaTransformAdjacentPublicContextCodeBound valuation rowIndexTerm
  have hbody : (binaryFormulaCode rawBody).length <= bodyCodeBound :=
    compactFormulaTransformAdjacentCurrentRawTerminal_code_length_le_public
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound
  have hcontext : formulaCodeSum
      (valuationContext rawBody.freeVariables valuation) <= contextCodeBound :=
    compactFormulaTransformAdjacentCurrentRawTerminal_context_le_public
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
  let innerDirect :=
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexFixedCorePublicFiniteStepDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.values_le hindexVariables data.next
  let innerResource :=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexFixedCorePublicAllRowsFiniteDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound
  have hinner : innerDirect.payloadLength <= innerResource :=
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexFixedCorePublicFiniteStepDirectOfGraph_payloadLength_le_allRowsFinite
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.values_le hindexVariables data.next
  let rawTerminal := castValuationContextProof
    (compactFormulaTransformAdjacentCurrentBoundedRawTerminal_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound witness).symm innerDirect
  have hrawTerminal : rawTerminal.payloadLength <= innerResource := by
    change (castValuationContextProof
      (compactFormulaTransformAdjacentCurrentBoundedRawTerminal_alignment
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound witness).symm
      innerDirect).payloadLength <= _
    rw [castValuationContextProof_payloadLength_eq]
    exact hinner
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 14 rawBody
  let compilation := compileExplicitBoundedWitnessDirectPublicWithResource
    contextCodeBound valueBound bodyCodeBound rawBody values data.values_le
      hbody hcontext innerResource rawTerminal hrawTerminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity14
      contextCodeBound valueBound bodyCodeBound rawBody values data.values_le
      hbody hcontext innerResource rawTerminal hrawTerminal
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound :=
    (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound).symm
  let proof := castValuationContextProof hformula rawProof
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = rawProof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula rawProof]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  simpa only [
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicFiniteStepDirectPayloadEnvelopeOfGraph,
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicAllRowsFiniteDirectPayloadEnvelope,
    data, witness, innerResource, rawBody, bodyCodeBound, contextCodeBound,
    sourceFormula, compilation, rawProof] using hcoordinates.2

noncomputable def
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicFiniteStepDirectOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hindexVariables : rowIndexTerm.freeVariables ⊆ {0})
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound) :=
  (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicFiniteStepDirectBoundOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound hindexVariables
    hcurrent).proof

theorem
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicFiniteStepDirectOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hindexVariables : rowIndexTerm.freeVariables ⊆ {0})
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound) :
    (compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicFiniteStepDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hindexVariables
      hcurrent).payloadLength <=
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicFiniteStepDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hcurrent :=
  (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicFiniteStepDirectBoundOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound hindexVariables
    hcurrent).payloadLength_le

theorem
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicFiniteStepDirectOfGraph_payloadLength_le_allRowsFinite
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hindexVariables : rowIndexTerm.freeVariables ⊆ {0})
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound) :
    (compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicFiniteStepDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hindexVariables
      hcurrent).payloadLength <=
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicAllRowsFiniteDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound := by
  simpa only [
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicFiniteStepDirectPayloadEnvelopeOfGraph] using
    (compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicFiniteStepDirectOfGraph_payloadLength_le
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hindexVariables
      hcurrent)

#print axioms
  compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicDirectOfGraph_payloadLength_le
#print axioms
  compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicFiniteStepDirectOfGraph_payloadLength_le
#print axioms
  compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFixedCorePublicFiniteStepDirectOfGraph_payloadLength_le_allRowsFinite

end FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedFixedCorePublicDirectCompiler
