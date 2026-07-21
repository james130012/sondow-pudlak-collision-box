import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedUniformDirectCompiler
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformArity14

/-!
# Uniform direct compiler for the fourteen current-state witnesses

The terminal is the uniform next-state proof.  The outer current-state witness
block is compiled with a public resource independent of its concrete
fourteen-coordinate vector.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedUniformDirectCompiler

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectUniformCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformArity14
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedUniformDirectCompiler

noncomputable def
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexUniformDirectPayloadEnvelopeOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound) : Nat :=
  let data := compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound hcurrent
  let witness := data.witness
  let innerResource :=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexUniformDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
  explicitBoundedWitnessDirectUniformPayloadEnvelope valuation valueBound
    (compactFormulaTransformAdjacentCurrentBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound)
    innerResource

noncomputable def
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexUniformDirectOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound).freeVariables valuation)
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
  let innerDirect :=
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexUniformDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
  let innerResource :=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexUniformDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
  have hinner : innerDirect.payloadLength <= innerResource :=
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexUniformDirectOfGraph_payloadLength_le
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
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
  let compilation := compileExplicitBoundedWitnessDirectUniformWithResource
    valueBound rawBody values data.values_le innerResource rawTerminal hrawTerminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectUniformWithResource_coordinates_arity14
      valueBound rawBody values data.values_le innerResource rawTerminal hrawTerminal
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
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexUniformDirectOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound) :
    (compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexUniformDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hcurrent).payloadLength <=
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexUniformDirectPayloadEnvelopeOfGraph
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
  let innerDirect :=
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexUniformDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
  let innerResource :=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexUniformDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
  have hinner : innerDirect.payloadLength <= innerResource :=
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexUniformDirectOfGraph_payloadLength_le
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
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
  let compilation := compileExplicitBoundedWitnessDirectUniformWithResource
    valueBound rawBody values data.values_le innerResource rawTerminal hrawTerminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectUniformWithResource_coordinates_arity14
      valueBound rawBody values data.values_le innerResource rawTerminal hrawTerminal
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
  compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexUniformDirectOfGraph_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedUniformDirectCompiler
