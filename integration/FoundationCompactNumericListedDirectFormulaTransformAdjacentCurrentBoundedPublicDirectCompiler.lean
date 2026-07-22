import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedPublicDirectCompiler
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity14

/-! # Public direct compiler for the fourteen current-state witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedPublicDirectCompiler

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
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedPublicDirectCompiler
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicCodeBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds

noncomputable def
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph
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
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
  explicitBoundedWitnessDirectPublicPayloadEnvelope 14
    (compactFormulaTransformAdjacentPublicContextCodeBound
      valuation rowIndexTerm)
    valueBound
    (compactFormulaTransformAdjacentCurrentRawTerminalPublicCodeEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound)
    innerResource

noncomputable def
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm) mode
      witnessStart witnessFinish witnessCount valueBound) : Nat :=
  let data := compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound hcurrent
  let witness := data.witness
  let innerResource :=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
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

theorem
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph_eq_publicFinite
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm) mode
      witnessStart witnessFinish witnessCount valueBound)
    (hindexVariables : rowIndexTerm.freeVariables ⊆ {0}) :
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound hcurrent =
      compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound hcurrent := by
  unfold
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
  simp only [
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph_eq_publicFinite
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound
      (compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph valuation
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound hcurrent).witness.coordinates
      (compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph valuation
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound hcurrent).witness.size
      (compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph valuation
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound hcurrent).next
      hindexVariables]

noncomputable def
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicDirectOfGraph
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
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.values_le data.next
  let innerResource :=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
  have hinner : innerDirect.payloadLength <= innerResource :=
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le
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
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound) :
    (compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hcurrent).payloadLength <=
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph
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
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.values_le data.next
  let innerResource :=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound witness.coordinates
      witness.size data.next
  have hinner : innerDirect.payloadLength <= innerResource :=
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le
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

theorem
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le_publicFinite
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm) mode
      witnessStart witnessFinish witnessCount valueBound)
    (hindexVariables : rowIndexTerm.freeVariables ⊆ {0}) :
    (compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hcurrent).payloadLength <=
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hcurrent := by
  rw [←
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph_eq_publicFinite
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hcurrent
      hindexVariables]
  exact
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hcurrent

#print axioms
  compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le
#print axioms
  compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le_publicFinite

end FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedPublicDirectCompiler
