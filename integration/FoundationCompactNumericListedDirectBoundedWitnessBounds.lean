import integration.FoundationCompactNumericListedDirectBoundedProofWitness
import integration.FoundationCompactNumericListedDirectWitnessBounds

/-!
# Public size bounds for all twenty bounded direct witnesses
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBoundedWitnessBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedPublicVerifier
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierAcceptedBoundedTraceTable
open FoundationCompactNumericListedDirectProofPredicate
open FoundationCompactNumericListedDirectBoundedProofWitness
open FoundationCompactNumericListedDirectWitnessBounds

def directBoundedWitnessStreamWeight (bound : Nat) : Nat :=
  compactNumericDecodedTokenListWeightBound bound

def directBoundedWitnessFuelLimit (bound : Nat) : Nat :=
  compactNumericVerifierPublicFuelWeightBound
    (directBoundedWitnessStreamWeight bound)

def directBoundedWitnessCoordinateLimit (bound : Nat) : Nat :=
  compactNumericVerifierAcceptedCoordinateSizeBound
    (directBoundedWitnessStreamWeight bound)

def directBoundedWitnessTraceWidthLimit (bound : Nat) : Nat :=
  directBoundedWitnessFuelLimit bound *
    (compactNumericVerifierStepWitnessColumnCount *
      directBoundedWitnessCoordinateLimit bound)

def directBoundedWitnessTraceTableLimit (bound : Nat) : Nat :=
  directBoundedWitnessFuelLimit bound *
      compactNumericVerifierStepWitnessColumnCount *
    (directBoundedWitnessFuelLimit bound *
      (compactNumericVerifierStepWitnessColumnCount *
        directBoundedWitnessCoordinateLimit bound))

def directBoundedWitnessTraceValueLimit (bound : Nat) : Nat :=
  directBoundedWitnessTraceWidthLimit bound + 1

def directBoundedWitness_toNonTraceCanonical
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    CompactListedPADirectNonTraceCanonicalWitness bound formulaCode :=
  { witness := bounded.witness
    proofTokens := bounded.proofTokens
    certificateTokens := bounded.certificateTokens
    formulaTokens := bounded.formulaTokens
    proofCode_eq := bounded.proofCode_eq
    formulaCode_eq := bounded.formulaCode_eq
    inputTokenCount_eq := bounded.inputTokenCount_eq
    inputWidth_eq := bounded.inputWidth_eq
    inputTable_eq := bounded.inputTable_eq
    inputOffsetTable_eq := bounded.inputOffsetTable_eq
    sourceTokenCount_eq := bounded.sourceTokenCount_eq
    sourceWidth_eq := bounded.sourceWidth_eq
    sourceTable_eq := bounded.sourceTable_eq
    proofStart_eq := bounded.proofStart_eq
    proofFinish_eq := bounded.proofFinish_eq
    certificateStart_eq := bounded.certificateStart_eq
    certificateFinish_eq := bounded.certificateFinish_eq
    split_eq := bounded.split_eq
    formulaTokenCount_eq := bounded.formulaTokenCount_eq
    formulaWidth_eq := bounded.formulaWidth_eq
    formulaTable_eq := bounded.formulaTable_eq
    formulaOffsetTable_eq := bounded.formulaOffsetTable_eq }

theorem directBoundedWitness_nonTrace_sizeBounds
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    DirectWitnessNonTraceSizeBounds bounded.witness
      (Nat.size formulaCode) :=
  directNonTraceCanonicalWitness_sizeBounds
    (directBoundedWitness_toNonTraceCanonical bounded)

theorem directBoundedWitness_nonTraceBitWeight_le
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    directWitnessNonTraceBitWeight bounded.witness <=
      directWitnessNonTraceBitWeightPolynomial
        bound (Nat.size formulaCode) := by
  have hbounds := directBoundedWitness_nonTrace_sizeBounds bounded
  rcases hbounds with
    ⟨hproofCode, hinputTokenCount, hinputTable, hinputOffsetTable,
      hinputWidth, hsourceTable, hsourceWidth, hsourceTokenCount,
      hproofStart, hproofFinish, hcertificateStart, hcertificateFinish,
      hsplit, hformulaTokenCount, hformulaTable, hformulaOffsetTable,
      hformulaWidth⟩
  apply compactAdditiveTokenWeight_le_of_sizeBounds
  constructor
  · exact hproofCode
  constructor
  · exact hinputTokenCount
  constructor
  · exact hinputTable
  constructor
  · exact hinputOffsetTable
  constructor
  · exact hinputWidth
  constructor
  · exact hsourceTable
  constructor
  · exact hsourceWidth
  constructor
  · exact hsourceTokenCount
  constructor
  · exact hproofStart
  constructor
  · exact hproofFinish
  constructor
  · exact hcertificateStart
  constructor
  · exact hcertificateFinish
  constructor
  · exact hsplit
  constructor
  · exact hformulaTokenCount
  constructor
  · exact hformulaTable
  constructor
  · exact hformulaOffsetTable
  constructor
  · exact hformulaWidth
  · exact List.Forall₂.nil

structure DirectWitnessTraceSizeBounds
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) : Prop where
  traceWidth : Nat.size witness.traceWidth <=
    directBoundedWitnessTraceWidthLimit bound
  traceTable : Nat.size witness.traceTable <=
    directBoundedWitnessTraceTableLimit bound
  traceValueBound : Nat.size witness.traceValueBound <=
    directBoundedWitnessTraceValueLimit bound

theorem directBoundedWitness_trace_sizeBounds
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    DirectWitnessTraceSizeBounds bounded.witness := by
  have hraw := bounded.traceCoordinates_size_le
  have hfuel : compactNumericVerifierFuelBound bounded.proofTokens
      bounded.certificateTokens <=
      compactNumericVerifierPublicFuelWeightBound bounded.streamWeight :=
    compactNumericVerifierFuelBound_le_weightBound
      bounded.proofWeight bounded.certificateWeight
  let columnCount := compactNumericVerifierStepWitnessColumnCount
  let coordinateBound :=
    compactNumericVerifierAcceptedCoordinateSizeBound bounded.streamWeight
  let fuel := compactNumericVerifierFuelBound bounded.proofTokens
    bounded.certificateTokens
  let publicFuel :=
    compactNumericVerifierPublicFuelWeightBound bounded.streamWeight
  have hwidthScale :
      fuel * (columnCount * coordinateBound) <=
        publicFuel * (columnCount * coordinateBound) :=
    Nat.mul_le_mul_right (columnCount * coordinateBound) hfuel
  have houter : fuel * columnCount <= publicFuel * columnCount :=
    Nat.mul_le_mul_right columnCount hfuel
  have hinner : fuel * (columnCount * coordinateBound) <=
      publicFuel * (columnCount * coordinateBound) := hwidthScale
  have htableScale :
      fuel * columnCount * (fuel * (columnCount * coordinateBound)) <=
        publicFuel * columnCount *
          (publicFuel * (columnCount * coordinateBound)) :=
    Nat.mul_le_mul houter hinner
  have hwidth : bounded.witness.traceWidth <=
      publicFuel * (columnCount * coordinateBound) :=
    hraw.1.trans hwidthScale
  have htable : Nat.size bounded.witness.traceTable <=
      publicFuel * columnCount *
        (publicFuel * (columnCount * coordinateBound)) :=
    hraw.2.1.trans htableScale
  have hvalue : Nat.size bounded.witness.traceValueBound <=
      publicFuel * (columnCount * coordinateBound) + 1 :=
    hraw.2.2.trans (Nat.add_le_add_right hwidthScale 1)
  refine
    { traceWidth := ?_
      traceTable := ?_
      traceValueBound := ?_ }
  · have hsize := nat_size_le_self bounded.witness.traceWidth
    have h := hsize.trans hwidth
    simpa [directBoundedWitnessTraceWidthLimit,
      directBoundedWitnessFuelLimit,
      directBoundedWitnessCoordinateLimit,
      directBoundedWitnessStreamWeight, columnCount, coordinateBound,
      publicFuel, bounded.streamWeight_eq] using h
  · simpa [directBoundedWitnessTraceTableLimit,
      directBoundedWitnessFuelLimit,
      directBoundedWitnessCoordinateLimit,
      directBoundedWitnessStreamWeight, columnCount, coordinateBound,
      publicFuel, bounded.streamWeight_eq] using htable
  · simpa [directBoundedWitnessTraceValueLimit,
      directBoundedWitnessTraceWidthLimit,
      directBoundedWitnessFuelLimit,
      directBoundedWitnessCoordinateLimit,
      directBoundedWitnessStreamWeight, columnCount, coordinateBound,
      publicFuel, bounded.streamWeight_eq] using hvalue

def directBoundedWitnessBitWeightPolynomial
    (bound formulaCodeSize : Nat) : Nat :=
  directWitnessNonTraceBitWeightPolynomial bound formulaCodeSize +
    (directBoundedWitnessTraceWidthLimit bound + 1) +
    (directBoundedWitnessTraceTableLimit bound + 1) +
    (directBoundedWitnessTraceValueLimit bound + 1)

theorem directWitnessBitWeight_eq_nonTrace_add_trace
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    directWitnessBitWeight witness =
      directWitnessNonTraceBitWeight witness +
        (Nat.size witness.traceWidth + 1) +
        (Nat.size witness.traceTable + 1) +
        (Nat.size witness.traceValueBound + 1) := by
  simp only [directWitnessBitWeight, directWitnessValues,
    directWitnessNonTraceBitWeight, directWitnessNonTraceValues,
    compactAdditiveTokenWeight_cons, compactAdditiveTokenWeight_nil]
  omega

theorem directBoundedWitness_bitWeight_le
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    directWitnessBitWeight bounded.witness <=
      directBoundedWitnessBitWeightPolynomial
        bound (Nat.size formulaCode) := by
  rw [directWitnessBitWeight_eq_nonTrace_add_trace]
  have hnontrace := directBoundedWitness_nonTraceBitWeight_le bounded
  have htrace := directBoundedWitness_trace_sizeBounds bounded
  unfold directBoundedWitnessBitWeightPolynomial
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add hnontrace
        (Nat.add_le_add_right htrace.traceWidth 1))
      (Nat.add_le_add_right htrace.traceTable 1))
    (Nat.add_le_add_right htrace.traceValueBound 1)

theorem directBoundedWitness_exists_with_bitWeight_le_of_public
    {bound proofCode formulaCode : Nat}
    (hbound : packedPayloadLength proofCode <= bound)
    (hpublic :
      compactNumericListedPublicVerifier proofCode formulaCode = true) :
    exists witness : CompactListedPADirectWitness bound formulaCode,
      directWitnessBitWeight witness <=
        directBoundedWitnessBitWeightPolynomial
          bound (Nat.size formulaCode) := by
  rcases directBoundedWitness_nonempty_of_public hbound hpublic with
    ⟨bounded⟩
  exact ⟨bounded.witness, directBoundedWitness_bitWeight_le bounded⟩

#print axioms directBoundedWitness_nonTrace_sizeBounds
#print axioms directBoundedWitness_trace_sizeBounds
#print axioms directBoundedWitness_bitWeight_le
#print axioms directBoundedWitness_exists_with_bitWeight_le_of_public

end FoundationCompactNumericListedDirectBoundedWitnessBounds
