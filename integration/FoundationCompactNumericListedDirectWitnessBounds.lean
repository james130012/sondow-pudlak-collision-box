import integration.FoundationCompactNumericListedDirectProofPredicate
import integration.FoundationCompactNumericListedDirectTraceBounds
import integration.FoundationCompactNumericListedDirectTraceNatListSlices

/-!
# Honest bit weight for the twenty direct proof witnesses

The weight counts every witness by binary payload size plus one structural
unit.  It is the resource to be bounded before the twenty existential
introductions in the quantitative PA compiler.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectWitnessBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedPublicVerifier
open FoundationCompactNumericListedDirectProofPredicate
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectTraceNatListSlices

def directWitnessValues
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    List Nat :=
  [witness.proofCode,
    witness.inputTokenCount, witness.inputTable,
    witness.inputOffsetTable, witness.inputWidth,
    witness.sourceTable, witness.sourceWidth, witness.sourceTokenCount,
    witness.proofStart, witness.proofFinish,
    witness.certificateStart, witness.certificateFinish, witness.split,
    witness.traceWidth, witness.traceTable, witness.traceValueBound,
    witness.formulaTokenCount, witness.formulaTable,
    witness.formulaOffsetTable, witness.formulaWidth]

def directWitnessBitWeight
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) : Nat :=
  compactAdditiveTokenWeight (directWitnessValues witness)

def directWitnessNonTraceValues
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    List Nat :=
  [witness.proofCode,
    witness.inputTokenCount, witness.inputTable,
    witness.inputOffsetTable, witness.inputWidth,
    witness.sourceTable, witness.sourceWidth, witness.sourceTokenCount,
    witness.proofStart, witness.proofFinish,
    witness.certificateStart, witness.certificateFinish, witness.split,
    witness.formulaTokenCount, witness.formulaTable,
    witness.formulaOffsetTable, witness.formulaWidth]

def directWitnessNonTraceBitWeight
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) : Nat :=
  compactAdditiveTokenWeight (directWitnessNonTraceValues witness)

@[simp] theorem directWitnessNonTraceValues_length
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    (directWitnessNonTraceValues witness).length = 17 := by
  rfl

theorem compactBinaryNatPayloadBits_length_eq_tokenBitLength
    (tokens : List Nat) :
    (compactBinaryNatPayloadBits tokens).length =
      compactAdditiveTokenBitLength tokens := by
  rfl

theorem compactBinaryNatPayloadBits_additiveNatLists_length
    (left right : List Nat) :
    (compactBinaryNatPayloadBits
      (compactAdditiveEncode left ++ compactAdditiveEncode right)).length =
      (compactBinaryNatPayloadBits (left ++ right)).length +
        2 * Nat.size left.length + 2 * Nat.size right.length + 4 := by
  rw [compactBinaryNatPayloadBits_length_eq_tokenBitLength,
    compactBinaryNatPayloadBits_length_eq_tokenBitLength]
  rw [compactAdditiveEncode_natList_eq,
    compactAdditiveEncode_natList_eq]
  simp only [compactAdditiveTokenBitLength_append,
    compactAdditiveTokenBitLength_cons]
  omega

theorem nat_size_le_self (value : Nat) : Nat.size value <= value := by
  exact natSize_le_of_le (Nat.le_refl value)

@[simp] theorem directWitnessValues_length
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    (directWitnessValues witness).length = 20 := by
  rfl

theorem nat_size_le_compactAdditiveTokenWeight_of_mem
    {value : Nat} {values : List Nat}
    (hmem : value ∈ values) :
    Nat.size value <= compactAdditiveTokenWeight values := by
  induction values with
  | nil => simp at hmem
  | cons head tail inductionHypothesis =>
      rw [compactAdditiveTokenWeight_cons]
      rcases List.mem_cons.mp hmem with hsame | htail
      · subst value
        omega
      · have hbound := inductionHypothesis htail
        omega

theorem directWitnessField_size_le_bitWeight
    {bound formulaCode value : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode)
    (hmem : value ∈ directWitnessValues witness) :
    Nat.size value <= directWitnessBitWeight witness :=
  nat_size_le_compactAdditiveTokenWeight_of_mem hmem

theorem directWitnessInputWidth_le_bound
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    witness.inputWidth <= bound :=
  witness.matrix.1

theorem directWitnessProofCode_size_le_bitWeight
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    Nat.size witness.proofCode <= directWitnessBitWeight witness := by
  apply directWitnessField_size_le_bitWeight witness
  simp [directWitnessValues]

theorem directWitnessTraceTable_size_le_bitWeight
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    Nat.size witness.traceTable <= directWitnessBitWeight witness := by
  apply directWitnessField_size_le_bitWeight witness
  simp [directWitnessValues]

theorem directWitnessFormulaTable_size_le_bitWeight
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    Nat.size witness.formulaTable <= directWitnessBitWeight witness := by
  apply directWitnessField_size_le_bitWeight witness
  simp [directWitnessValues]

structure DirectWitnessNonTraceSizeBounds
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode)
    (formulaCodeSize : Nat) : Prop where
  proofCode : Nat.size witness.proofCode <= bound + 1
  inputTokenCount : Nat.size witness.inputTokenCount <= bound
  inputTable : Nat.size witness.inputTable <= bound * bound
  inputOffsetTable : Nat.size witness.inputOffsetTable <=
    (bound + 1) * bound
  inputWidth : Nat.size witness.inputWidth <= bound
  sourceTable : Nat.size witness.sourceTable <=
    (bound + 2) * (5 * bound + 4)
  sourceWidth : Nat.size witness.sourceWidth <= 5 * bound + 4
  sourceTokenCount : Nat.size witness.sourceTokenCount <= bound + 2
  proofStart : Nat.size witness.proofStart <= 0
  proofFinish : Nat.size witness.proofFinish <= bound + 1
  certificateStart : Nat.size witness.certificateStart <= bound + 1
  certificateFinish : Nat.size witness.certificateFinish <= bound + 2
  split : Nat.size witness.split <= bound
  formulaTokenCount : Nat.size witness.formulaTokenCount <= formulaCodeSize
  formulaTable : Nat.size witness.formulaTable <=
    formulaCodeSize * formulaCodeSize
  formulaOffsetTable : Nat.size witness.formulaOffsetTable <=
    (formulaCodeSize + 1) * formulaCodeSize
  formulaWidth : Nat.size witness.formulaWidth <= formulaCodeSize

/-- The canonical-coordinate data used by the seventeen non-trace bounds.
It deliberately omits the trace fields, so bounded and canonical trace
selectors share exactly the same non-trace audit. -/
structure CompactListedPADirectNonTraceCanonicalWitness
    (bound formulaCode : Nat) where
  witness : CompactListedPADirectWitness bound formulaCode
  proofTokens : List Nat
  certificateTokens : List Nat
  formulaTokens : List Nat
  proofCode_eq : witness.proofCode =
    compactAdditivePackedCode (proofTokens ++ certificateTokens)
  formulaCode_eq : formulaCode = compactAdditivePackedCode formulaTokens
  inputTokenCount_eq : witness.inputTokenCount =
    (proofTokens ++ certificateTokens).length
  inputWidth_eq : witness.inputWidth =
    (compactBinaryNatPayloadBits
      (proofTokens ++ certificateTokens)).length
  inputTable_eq : witness.inputTable =
    compactFixedWidthTableCode witness.inputWidth
      (proofTokens ++ certificateTokens)
  inputOffsetTable_eq : witness.inputOffsetTable =
    compactFixedWidthTableCode witness.inputWidth
      (compactBinaryNatTokenOffsets (proofTokens ++ certificateTokens))
  sourceTokenCount_eq : witness.sourceTokenCount =
    (compactAdditiveEncode proofTokens ++
      compactAdditiveEncode certificateTokens).length
  sourceWidth_eq : witness.sourceWidth =
    (compactBinaryNatPayloadBits
      (compactAdditiveEncode proofTokens ++
        compactAdditiveEncode certificateTokens)).length
  sourceTable_eq : witness.sourceTable =
    compactFixedWidthTableCode witness.sourceWidth
      (compactAdditiveEncode proofTokens ++
        compactAdditiveEncode certificateTokens)
  proofStart_eq : witness.proofStart = 0
  proofFinish_eq : witness.proofFinish =
    (compactAdditiveEncode proofTokens).length
  certificateStart_eq : witness.certificateStart =
    (compactAdditiveEncode proofTokens).length
  certificateFinish_eq : witness.certificateFinish =
    (compactAdditiveEncode proofTokens ++
      compactAdditiveEncode certificateTokens).length
  split_eq : witness.split = proofTokens.length
  formulaTokenCount_eq : witness.formulaTokenCount = formulaTokens.length
  formulaWidth_eq : witness.formulaWidth =
    (compactBinaryNatPayloadBits formulaTokens).length
  formulaTable_eq : witness.formulaTable =
    compactFixedWidthTableCode witness.formulaWidth formulaTokens
  formulaOffsetTable_eq : witness.formulaOffsetTable =
    compactFixedWidthTableCode witness.formulaWidth
      (compactBinaryNatTokenOffsets formulaTokens)

def directCanonicalWitness_toNonTraceCanonical
    {bound formulaCode : Nat}
    (canonical : CompactListedPADirectCanonicalWitness bound formulaCode) :
    CompactListedPADirectNonTraceCanonicalWitness bound formulaCode :=
  { witness := canonical.witness
    proofTokens := canonical.proofTokens
    certificateTokens := canonical.certificateTokens
    formulaTokens := canonical.formulaTokens
    proofCode_eq := canonical.proofCode_eq
    formulaCode_eq := canonical.formulaCode_eq
    inputTokenCount_eq := canonical.inputTokenCount_eq
    inputWidth_eq := canonical.inputWidth_eq
    inputTable_eq := canonical.inputTable_eq
    inputOffsetTable_eq := canonical.inputOffsetTable_eq
    sourceTokenCount_eq := canonical.sourceTokenCount_eq
    sourceWidth_eq := canonical.sourceWidth_eq
    sourceTable_eq := canonical.sourceTable_eq
    proofStart_eq := canonical.proofStart_eq
    proofFinish_eq := canonical.proofFinish_eq
    certificateStart_eq := canonical.certificateStart_eq
    certificateFinish_eq := canonical.certificateFinish_eq
    split_eq := canonical.split_eq
    formulaTokenCount_eq := canonical.formulaTokenCount_eq
    formulaWidth_eq := canonical.formulaWidth_eq
    formulaTable_eq := canonical.formulaTable_eq
    formulaOffsetTable_eq := canonical.formulaOffsetTable_eq }

def directWitnessNonTraceSizeLimits
    (bound formulaCodeSize : Nat) : List Nat :=
  [bound + 1,
    bound,
    bound * bound,
    (bound + 1) * bound,
    bound,
    (bound + 2) * (5 * bound + 4),
    5 * bound + 4,
    bound + 2,
    0,
    bound + 1,
    bound + 1,
    bound + 2,
    bound,
    formulaCodeSize,
    formulaCodeSize * formulaCodeSize,
    (formulaCodeSize + 1) * formulaCodeSize,
    formulaCodeSize]

/-- Fixed seventeen-coordinate polynomial budget.  The fixed list makes the
coordinatewise origin of every summand explicit without forcing the kernel to
reassociate one large addition term. -/
def directWitnessNonTraceBitWeightPolynomial
    (bound formulaCodeSize : Nat) : Nat :=
  ((directWitnessNonTraceSizeLimits bound formulaCodeSize).map
    fun limit => limit + 1).sum

theorem compactAdditiveTokenWeight_le_of_sizeBounds
    {values limits : List Nat}
    (hbounds : List.Forall₂
      (fun value limit => Nat.size value <= limit) values limits) :
    compactAdditiveTokenWeight values <=
      (limits.map fun limit => limit + 1).sum := by
  induction hbounds with
  | nil => simp
  | cons hhead _ inductionHypothesis =>
      rw [compactAdditiveTokenWeight_cons]
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (Nat.add_le_add_right hhead 1) inductionHypothesis

theorem directNonTraceCanonicalWitness_sizeBounds
    {bound formulaCode : Nat}
    (canonical :
      CompactListedPADirectNonTraceCanonicalWitness bound formulaCode) :
    DirectWitnessNonTraceSizeBounds canonical.witness
      (Nat.size formulaCode) := by
  have hinputWidth : canonical.witness.inputWidth <= bound :=
    directWitnessInputWidth_le_bound canonical.witness
  have hinputCount : canonical.witness.inputTokenCount <= bound := by
    have hcount := compactBinaryNatToken_count_le_payloadLength
      (canonical.proofTokens ++ canonical.certificateTokens)
    rw [← canonical.inputTokenCount_eq,
      ← canonical.inputWidth_eq] at hcount
    exact hcount.trans hinputWidth
  have hproofLength : canonical.proofTokens.length <= bound := by
    calc
      canonical.proofTokens.length <=
          (canonical.proofTokens ++ canonical.certificateTokens).length := by
        simp
      _ = canonical.witness.inputTokenCount :=
        canonical.inputTokenCount_eq.symm
      _ <= bound := hinputCount
  have hcertificateLength : canonical.certificateTokens.length <= bound := by
    calc
      canonical.certificateTokens.length <=
          (canonical.proofTokens ++ canonical.certificateTokens).length := by
        simp
      _ = canonical.witness.inputTokenCount :=
        canonical.inputTokenCount_eq.symm
      _ <= bound := hinputCount
  have hsourceCount : canonical.witness.sourceTokenCount <= bound + 2 := by
    rw [canonical.sourceTokenCount_eq,
      List.length_append,
      compactAdditiveEncode_natList_length,
      compactAdditiveEncode_natList_length]
    have hinputLength :
        canonical.proofTokens.length + canonical.certificateTokens.length <=
          bound := by
      calc
        canonical.proofTokens.length + canonical.certificateTokens.length =
            (canonical.proofTokens ++ canonical.certificateTokens).length := by
          simp
        _ = canonical.witness.inputTokenCount :=
          canonical.inputTokenCount_eq.symm
        _ <= bound := hinputCount
    omega
  have hsourceWidth : canonical.witness.sourceWidth <= 5 * bound + 4 := by
    rw [canonical.sourceWidth_eq,
      compactBinaryNatPayloadBits_additiveNatLists_length,
      ← canonical.inputWidth_eq]
    have hproofSize := nat_size_le_self canonical.proofTokens.length
    have hcertificateSize :=
      nat_size_le_self canonical.certificateTokens.length
    omega
  have hformulaCodeSize :
      Nat.size formulaCode = canonical.witness.formulaWidth + 1 := by
    calc
      Nat.size formulaCode =
          Nat.size (compactAdditivePackedCode canonical.formulaTokens) := by
        exact congrArg Nat.size canonical.formulaCode_eq
      _ = compactAdditiveTokenBitLength canonical.formulaTokens + 1 :=
        compactAdditivePackedCode_size canonical.formulaTokens
      _ = (compactBinaryNatPayloadBits canonical.formulaTokens).length + 1 := by
        rw [compactBinaryNatPayloadBits_length_eq_tokenBitLength]
      _ = canonical.witness.formulaWidth + 1 := by
        rw [canonical.formulaWidth_eq]
  have hformulaWidth : canonical.witness.formulaWidth <=
      Nat.size formulaCode := by
    omega
  have hformulaCount : canonical.witness.formulaTokenCount <=
      Nat.size formulaCode := by
    rw [canonical.formulaTokenCount_eq]
    have hcount := compactBinaryNatToken_count_le_payloadLength
      canonical.formulaTokens
    rw [← canonical.formulaWidth_eq] at hcount
    exact hcount.trans hformulaWidth
  refine
    { proofCode := ?_
      inputTokenCount := (nat_size_le_self _).trans hinputCount
      inputTable := ?_
      inputOffsetTable := ?_
      inputWidth := (nat_size_le_self _).trans hinputWidth
      sourceTable := ?_
      sourceWidth := (nat_size_le_self _).trans hsourceWidth
      sourceTokenCount := (nat_size_le_self _).trans hsourceCount
      proofStart := ?_
      proofFinish := ?_
      certificateStart := ?_
      certificateFinish := ?_
      split := ?_
      formulaTokenCount := (nat_size_le_self _).trans hformulaCount
      formulaTable := ?_
      formulaOffsetTable := ?_
      formulaWidth := (nat_size_le_self _).trans hformulaWidth }
  · rw [canonical.proofCode_eq, compactAdditivePackedCode_size,
      ← compactBinaryNatPayloadBits_length_eq_tokenBitLength,
      ← canonical.inputWidth_eq]
    omega
  · rw [canonical.inputTable_eq]
    have htable := compactFixedWidthTableCode_size_le
      canonical.witness.inputWidth
      (canonical.proofTokens ++ canonical.certificateTokens)
    have hproduct := Nat.mul_le_mul hinputCount hinputWidth
    rw [← canonical.inputTokenCount_eq] at htable
    exact htable.trans hproduct
  · rw [canonical.inputOffsetTable_eq]
    have htable := compactFixedWidthTableCode_size_le
      canonical.witness.inputWidth
      (compactBinaryNatTokenOffsets
        (canonical.proofTokens ++ canonical.certificateTokens))
    rw [compactBinaryNatTokenOffsets_length,
      ← canonical.inputTokenCount_eq] at htable
    have hproduct := Nat.mul_le_mul (Nat.add_le_add_right hinputCount 1)
      hinputWidth
    exact htable.trans hproduct
  · rw [canonical.sourceTable_eq]
    have htable := compactFixedWidthTableCode_size_le
      canonical.witness.sourceWidth
      (compactAdditiveEncode canonical.proofTokens ++
        compactAdditiveEncode canonical.certificateTokens)
    rw [← canonical.sourceTokenCount_eq] at htable
    exact htable.trans (Nat.mul_le_mul hsourceCount hsourceWidth)
  · rw [canonical.proofStart_eq]
    rfl
  · rw [canonical.proofFinish_eq,
      compactAdditiveEncode_natList_length]
    exact (nat_size_le_self _).trans (by omega)
  · rw [canonical.certificateStart_eq,
      compactAdditiveEncode_natList_length]
    exact (nat_size_le_self _).trans (by omega)
  · rw [canonical.certificateFinish_eq]
    have hfinish :
        (compactAdditiveEncode canonical.proofTokens ++
          compactAdditiveEncode canonical.certificateTokens).length <=
            bound + 2 := by
      calc
        (compactAdditiveEncode canonical.proofTokens ++
            compactAdditiveEncode canonical.certificateTokens).length =
            canonical.witness.sourceTokenCount :=
          canonical.sourceTokenCount_eq.symm
        _ <= bound + 2 := hsourceCount
    exact (nat_size_le_self _).trans hfinish
  · rw [canonical.split_eq]
    exact (nat_size_le_self _).trans hproofLength
  · rw [canonical.formulaTable_eq]
    have htable := compactFixedWidthTableCode_size_le
      canonical.witness.formulaWidth
      canonical.formulaTokens
    rw [← canonical.formulaTokenCount_eq] at htable
    exact htable.trans (Nat.mul_le_mul hformulaCount hformulaWidth)
  · rw [canonical.formulaOffsetTable_eq]
    have htable := compactFixedWidthTableCode_size_le
      canonical.witness.formulaWidth
      (compactBinaryNatTokenOffsets canonical.formulaTokens)
    rw [compactBinaryNatTokenOffsets_length,
      ← canonical.formulaTokenCount_eq] at htable
    exact htable.trans
      (Nat.mul_le_mul (Nat.add_le_add_right hformulaCount 1)
        hformulaWidth)

theorem directCanonicalWitness_nonTrace_sizeBounds
    {bound formulaCode : Nat}
    (canonical :
      CompactListedPADirectCanonicalWitness bound formulaCode) :
    DirectWitnessNonTraceSizeBounds canonical.witness
      (Nat.size formulaCode) :=
  directNonTraceCanonicalWitness_sizeBounds
    (directCanonicalWitness_toNonTraceCanonical canonical)

theorem directCanonicalWitness_nonTraceBitWeight_le
    {bound formulaCode : Nat}
    (canonical :
      CompactListedPADirectCanonicalWitness bound formulaCode) :
    directWitnessNonTraceBitWeight canonical.witness <=
      directWitnessNonTraceBitWeightPolynomial
        bound (Nat.size formulaCode) := by
  have hbounds := directCanonicalWitness_nonTrace_sizeBounds canonical
  rcases hbounds with
    ⟨hproofCode, hinputTokenCount, hinputTable, hinputOffsetTable,
      hinputWidth, hsourceTable, hsourceWidth, hsourceTokenCount,
      hproofStart, hproofFinish, hcertificateStart, hcertificateFinish,
      hsplit, hformulaTokenCount, hformulaTable, hformulaOffsetTable,
      hformulaWidth⟩
  have hpointwise : List.Forall₂
      (fun value limit => Nat.size value <= limit)
      (directWitnessNonTraceValues canonical.witness)
      (directWitnessNonTraceSizeLimits bound (Nat.size formulaCode)) := by
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
  have hsum := compactAdditiveTokenWeight_le_of_sizeBounds hpointwise
  simpa only [directWitnessNonTraceBitWeight,
    directWitnessNonTraceBitWeightPolynomial] using hsum

def directWitnessPublicResource
    (bound formulaCode : Nat) : Nat :=
  bound + Nat.size formulaCode + 1

theorem directWitness_exists_with_inputWidth_le_bound
    {bound proofCode formulaCode : Nat}
    (hbound : packedPayloadLength proofCode <= bound)
    (hpublic :
      compactNumericListedPublicVerifier proofCode formulaCode = true) :
    ∃ witness : CompactListedPADirectWitness bound formulaCode,
      witness.inputWidth <= bound := by
  rcases directWitness_nonempty_of_public hbound hpublic with ⟨witness⟩
  exact ⟨witness, directWitnessInputWidth_le_bound witness⟩

#print axioms directWitnessField_size_le_bitWeight
#print axioms directWitnessInputWidth_le_bound
#print axioms directCanonicalWitness_nonTrace_sizeBounds
#print axioms directCanonicalWitness_nonTraceBitWeight_le
#print axioms directWitness_exists_with_inputWidth_le_bound

end FoundationCompactNumericListedDirectWitnessBounds
