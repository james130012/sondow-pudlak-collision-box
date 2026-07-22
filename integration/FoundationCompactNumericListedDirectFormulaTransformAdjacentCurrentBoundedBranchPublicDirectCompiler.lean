import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedBranchPublicDirectCompiler
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity14

/-! # Branch-sensitive public compiler for the fourteen current-state witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedBranchPublicDirectCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity14
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedBranchPublicDirectCompiler
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicCodeBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds

noncomputable def
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexBranchPublicDirectPayloadEnvelopeOfGraph
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
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexBranchPublicDirectPayloadEnvelopeOfGraph
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
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexBranchPublicDirectOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound).freeVariables
        valuation)
      (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound) := by
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
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexBranchPublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.values_le data.next
  let innerResource :=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexBranchPublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
  have hinner : innerDirect.payloadLength <= innerResource :=
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexBranchPublicDirectOfGraph_payloadLength_le
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
  exact castValuationContextProof hformula rawProof

theorem
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexBranchPublicDirectOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound) :
    (compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexBranchPublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hcurrent).payloadLength <=
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexBranchPublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hcurrent := by
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
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexBranchPublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.values_le data.next
  let innerResource :=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexBranchPublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
  have hinner : innerDirect.payloadLength <= innerResource :=
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexBranchPublicDirectOfGraph_payloadLength_le
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
  change (castValuationContextProof hformula rawProof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  exact hcoordinates.2

#print axioms
  compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexBranchPublicDirectOfGraph_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedBranchPublicDirectCompiler
