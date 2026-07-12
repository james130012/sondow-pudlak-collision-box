import integration.FoundationCompactNumericListedDirectBinaryNatStreamStepFormula
import integration.FoundationCompactNumericListedDirectTracePackedStreamStateLayouts

/-!
# Installation of the direct stream-step graph into trace state tables

Every adjacent pair in a valid binary-natural stream trace receives explicit
state coordinates and one Delta-zero step witness.  The generic result is then
installed in both packed streams of a complete public-verifier trace.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStreamStepInstallation

open FoundationCompactAdditiveTokenCodec
open FoundationCompactBinaryNatStreamMachine
open FoundationCompactPackedTokenStreamDirectTrace
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectTraceComponentTableau
open FoundationCompactNumericListedDirectBinaryNatStreamStateLayout
open FoundationCompactNumericListedDirectBinaryNatStreamStateListLayout
open FoundationCompactNumericListedDirectTracePackedStreamStateLayouts
open FoundationCompactNumericListedDirectBinaryNatStreamStepRows
open FoundationCompactNumericListedDirectBinaryNatStreamStepFormula

theorem BinaryNatStreamLocalTraceValid.getI_step
    {fuel : Nat} {start : BinaryNatStreamState}
    {states : List BinaryNatStreamState}
    (hvalid : BinaryNatStreamLocalTraceValid fuel start states)
    {stepIndex : Nat} (hstepIndex : stepIndex < fuel) :
    states.getI (stepIndex + 1) =
      binaryNatStreamStep (states.getI stepIndex) := by
  have hcurrentIndex : stepIndex < states.length := by
    rw [hvalid.1]
    omega
  have hnextIndex : stepIndex + 1 < states.length := by
    rw [hvalid.1]
    omega
  have htransition := hvalid.2.2 stepIndex hstepIndex
  have htransition' :
      states[stepIndex + 1] = binaryNatStreamStep states[stepIndex] := by
    simpa [binaryNatStreamTraceState?, binaryNatStreamStepOption,
      hcurrentIndex, hnextIndex] using htransition
  rw [List.getI_eq_getElem _ hnextIndex,
    List.getI_eq_getElem _ hcurrentIndex]
  exact htransition'

def CompactBinaryNatStreamStateListAdjacentStepGraphRows
    (tokenTable width tokenCount stateBoundary : Nat)
    (states : List BinaryNatStreamState) : Prop :=
  ∀ index < states.length - 1,
    ∃ currentLeft, currentLeft ≤ tokenCount ∧
    ∃ currentRight, currentRight ≤ tokenCount ∧
    ∃ nextLeft, nextLeft ≤ tokenCount ∧
    ∃ nextRight, nextRight ≤ tokenCount ∧
      CompactFixedWidthEntry
        stateBoundary tokenCount index currentLeft ∧
      CompactFixedWidthEntry
        stateBoundary tokenCount (index + 1) currentRight ∧
      CompactFixedWidthEntry
        stateBoundary tokenCount (index + 1) nextLeft ∧
      CompactFixedWidthEntry
        stateBoundary tokenCount (index + 2) nextRight ∧
      ∃ currentCoordinates nextCoordinates witness,
        currentCoordinates.start = currentLeft ∧
        currentCoordinates.finish = currentRight ∧
        nextCoordinates.start = nextLeft ∧
        nextCoordinates.finish = nextRight ∧
        CompactBinaryNatStreamStateFixedLayout
          tokenTable width tokenCount currentCoordinates
            (states.getI index) ∧
        CompactBinaryNatStreamStateFixedLayout
          tokenTable width tokenCount nextCoordinates
            (states.getI (index + 1)) ∧
        CompactBinaryNatStreamStepGraphRows
          tokenTable width tokenCount
            currentCoordinates nextCoordinates witness

theorem stateListAdjacentStepGraphRows_of_localTrace
    {tokenTable width tokenCount stateBoundary fuel : Nat}
    {start : BinaryNatStreamState}
    {states : List BinaryNatStreamState}
    (hrows : CompactBinaryNatStreamStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hvalid : BinaryNatStreamLocalTraceValid fuel start states) :
    CompactBinaryNatStreamStateListAdjacentStepGraphRows
      tokenTable width tokenCount stateBoundary states := by
  intro index hindex
  have hstepIndex : index < fuel := by
    rw [hvalid.1] at hindex
    omega
  have hcurrentIndex : index < states.length := by
    rw [hvalid.1]
    omega
  have hnextIndex : index + 1 < states.length := by
    rw [hvalid.1]
    omega
  rcases hrows index hcurrentIndex with
    ⟨currentLeft, hcurrentLeft,
      currentRight, hcurrentRight,
      hcurrentLeftEntry, hcurrentRightEntry, hcurrentLayout⟩
  rcases hrows (index + 1) hnextIndex with
    ⟨nextLeft, hnextLeft,
      nextRight, hnextRight,
      hnextLeftEntry, hnextRightEntry, hnextLayout⟩
  rcases
      (compactBinaryNatStreamStateDirectLayout_iff_fixedCoordinates
        tokenTable width tokenCount currentLeft currentRight
          (states.getI index)).mp hcurrentLayout with
    ⟨currentCoordinates, hcurrentStart, hcurrentFinish, hcurrentFixed⟩
  rcases
      (compactBinaryNatStreamStateDirectLayout_iff_fixedCoordinates
        tokenTable width tokenCount nextLeft nextRight
          (states.getI (index + 1))).mp hnextLayout with
    ⟨nextCoordinates, hnextStart, hnextFinish, hnextFixed⟩
  have hstep : states.getI (index + 1) =
      binaryNatStreamStep (states.getI index) :=
    BinaryNatStreamLocalTraceValid.getI_step hvalid hstepIndex
  rcases (exists_stepGraphRows_iff_step
      hcurrentFixed hnextFixed).mpr hstep with
    ⟨witness, hwitness⟩
  exact ⟨currentLeft, hcurrentLeft,
    currentRight, hcurrentRight,
    nextLeft, hnextLeft, nextRight, hnextRight,
    hcurrentLeftEntry, hcurrentRightEntry,
    hnextLeftEntry, hnextRightEntry,
    currentCoordinates, nextCoordinates, witness,
    hcurrentStart, hcurrentFinish, hnextStart, hnextFinish,
    hcurrentFixed, hnextFixed, hwitness⟩

theorem compactNumericListedDirectTrace_packedStream_step_graph_rows
    (code formulaCode : Nat) (trace : CompactNumericListedDirectTrace)
    (hvalid : CompactNumericListedDirectTraceValid
      code formulaCode trace) :
    let components := compactNumericListedDirectTraceComponentTokens trace
    let tokens := compactNumericListedDirectTraceTokens trace
    let width := (compactBinaryNatPayloadBits tokens).length
    let boundaries := compactAdditiveComponentBoundaries components
    let proofStart := boundaries.getI 1 +
      (compactAdditiveEncode
        (compactNumericDirectTraceCertifiedStreamTrace trace).1).length
    let formulaStart := boundaries.getI 3 +
      (compactAdditiveEncode
        (compactNumericDirectTraceFormulaStreamTrace trace).1).length
    ∃ proofStateBoundaryTable formulaStateBoundaryTable,
      CompactAdditiveStructuredListLayout
          (compactFixedWidthTableCode width tokens)
          width tokens.length proofStart
          (compactNumericDirectTraceCertifiedStreamTrace trace).2.length
          (boundaries.getI 2) proofStateBoundaryTable ∧
        CompactBinaryNatStreamStateListAdjacentStepGraphRows
          (compactFixedWidthTableCode width tokens)
          width tokens.length proofStateBoundaryTable
          (compactNumericDirectTraceCertifiedStreamTrace trace).2 ∧
        Nat.size proofStateBoundaryTable ≤
          ((compactNumericDirectTraceCertifiedStreamTrace trace).2.length + 1) *
            tokens.length ∧
        CompactAdditiveStructuredListLayout
          (compactFixedWidthTableCode width tokens)
          width tokens.length formulaStart
          (compactNumericDirectTraceFormulaStreamTrace trace).2.length
          (boundaries.getI 4) formulaStateBoundaryTable ∧
        CompactBinaryNatStreamStateListAdjacentStepGraphRows
          (compactFixedWidthTableCode width tokens)
          width tokens.length formulaStateBoundaryTable
          (compactNumericDirectTraceFormulaStreamTrace trace).2 ∧
        Nat.size formulaStateBoundaryTable ≤
          ((compactNumericDirectTraceFormulaStreamTrace trace).2.length + 1) *
            tokens.length := by
  let components := compactNumericListedDirectTraceComponentTokens trace
  let tokens := compactNumericListedDirectTraceTokens trace
  let width := (compactBinaryNatPayloadBits tokens).length
  let boundaries := compactAdditiveComponentBoundaries components
  let proofStart := boundaries.getI 1 +
    (compactAdditiveEncode
      (compactNumericDirectTraceCertifiedStreamTrace trace).1).length
  let formulaStart := boundaries.getI 3 +
    (compactAdditiveEncode
      (compactNumericDirectTraceFormulaStreamTrace trace).1).length
  rcases compactNumericListedDirectTrace_packedStream_state_layouts trace with
    ⟨proofStateBoundaryTable, formulaStateBoundaryTable,
      hproofLayout, hproofRows, hproofSize,
      hformulaLayout, hformulaRows, hformulaSize⟩
  have hcertifiedValid : CompactPackedTokenStreamDirectTraceValid
      code (compactNumericDirectTraceCertifiedTokens trace)
        (compactNumericDirectTraceCertifiedStreamTrace trace) :=
    hvalid.1
  have hformulaValid : CompactPackedTokenStreamDirectTraceValid
      formulaCode (compactNumericDirectTraceFormulaTokens trace)
        (compactNumericDirectTraceFormulaStreamTrace trace) :=
    hvalid.2.1
  have hproofSteps := stateListAdjacentStepGraphRows_of_localTrace
    hproofRows hcertifiedValid.2.1
  have hformulaSteps := stateListAdjacentStepGraphRows_of_localTrace
    hformulaRows hformulaValid.2.1
  exact ⟨proofStateBoundaryTable, formulaStateBoundaryTable,
    hproofLayout, hproofSteps, hproofSize,
    hformulaLayout, hformulaSteps, hformulaSize⟩

#print axioms BinaryNatStreamLocalTraceValid.getI_step
#print axioms stateListAdjacentStepGraphRows_of_localTrace
#print axioms compactNumericListedDirectTrace_packedStream_step_graph_rows

end FoundationCompactNumericListedDirectBinaryNatStreamStepInstallation
