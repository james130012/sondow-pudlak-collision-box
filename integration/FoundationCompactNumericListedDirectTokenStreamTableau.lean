import integration.FoundationCompactNumericListedDirectArithmeticPrimitives
import Mathlib.Data.Nat.Bitwise

/-!
# Direct arithmetic tableau for a binary-natural token stream

The payload is segmented by a pair of flat fixed-width tables: one stores token
values and one stores cumulative bit offsets.  The local formula is bounded,
and the canonical witnesses have quadratic bit area in the payload length.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectTokenStreamTableau

open FoundationCompactNumericListedDirectArithmeticPrimitives

@[simp] theorem foundationNatLE_iff_standard (left right : Nat) :
    @LE.le Nat LO.FirstOrder.Arithmetic.instLE_foundation left right ↔
      @LE.le Nat instLENat left right := by
  change (left = right ∨ left < right) ↔ left ≤ right
  omega

/-- Direct row-by-row semantics for one complete token stream. -/
def CompactBinaryNatTokenStreamTableau
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    Prop :=
  sentinel = 2 ^ payloadLength ∧
    tokenCount ≤ payloadLength + 1 ∧
    CompactFixedWidthEntry offsetTable payloadLength 0 0 ∧
    CompactFixedWidthEntry offsetTable payloadLength tokenCount
      payloadLength ∧
    ∀ index < tokenCount,
      ∃ token, token ≤ sentinel ∧
      ∃ offset, offset ≤ sentinel ∧
      ∃ next, next ≤ sentinel ∧
        CompactFixedWidthEntry tokenTable payloadLength index token ∧
        CompactFixedWidthEntry offsetTable payloadLength index offset ∧
        CompactFixedWidthEntry offsetTable payloadLength (index + 1) next ∧
        CompactBinaryNatTokenSegment payload offset token next

/-- Handwritten bounded arithmetic graph for the complete token stream. -/
def compactBinaryNatTokenStreamTableauDef : 𝚺₀.Semisentence 6 := .mkSigma
  “payload payloadLength sentinel tokenCount tokenTable offsetTable.
    !expDef sentinel payloadLength ∧
    tokenCount ≤ payloadLength + 1 ∧
    !(compactFixedWidthEntryDef) offsetTable payloadLength 0 0 ∧
    !(compactFixedWidthEntryDef) offsetTable payloadLength tokenCount payloadLength ∧
    ∀ index < tokenCount,
      ∃ token <⁺ sentinel,
      ∃ offset <⁺ sentinel,
      ∃ next <⁺ sentinel,
        !(compactFixedWidthEntryDef) tokenTable payloadLength index token ∧
        !(compactFixedWidthEntryDef) offsetTable payloadLength index offset ∧
        !(compactFixedWidthEntryDef) offsetTable payloadLength (index + 1) next ∧
        !(compactBinaryNatTokenSegmentDef) payload offset token next”

@[simp] theorem compactBinaryNatTokenStreamTableauDef_spec
    (payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat) :
    compactBinaryNatTokenStreamTableauDef.val.Evalb
        ![payload, payloadLength, sentinel, tokenCount, tokenTable,
          offsetTable] ↔
      CompactBinaryNatTokenStreamTableau
        payload payloadLength sentinel tokenCount tokenTable offsetTable := by
  simp [compactBinaryNatTokenStreamTableauDef,
    CompactBinaryNatTokenStreamTableau,
    foundationNatLE_iff_standard]

theorem compactBinaryNatTokenStreamTableauDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactBinaryNatTokenStreamTableauDef.val := by
  simp [compactBinaryNatTokenStreamTableauDef]

def compactBinaryNatTokenWidth (token : Nat) : Nat :=
  2 * Nat.size token + 2

def compactBinaryNatPayloadBits (tokens : List Nat) : List Bool :=
  tokens.flatMap FoundationSuccinctFiniteConsistencyTarget.binaryNatCode

def compactBinaryNatPayloadValue (tokens : List Nat) : Nat :=
  FoundationCompactVerifierBitCostPrimitives.natOfBitsList
    (compactBinaryNatPayloadBits tokens)

/-- Cumulative start offsets, including the final payload endpoint. -/
def compactBinaryNatTokenOffsets : List Nat → List Nat
  | [] => [0]
  | token :: tokens =>
      0 :: (compactBinaryNatTokenOffsets tokens).map
        (fun offset => compactBinaryNatTokenWidth token + offset)

@[simp] theorem compactBinaryNatTokenWidth_eq_code_length (token : Nat) :
    compactBinaryNatTokenWidth token =
      (FoundationSuccinctFiniteConsistencyTarget.binaryNatCode token).length := by
  rw [FoundationCompactCanonicalDecodeLength.binaryNatCode_length]
  rfl

@[simp] theorem compactBinaryNatPayloadBits_nil :
    compactBinaryNatPayloadBits [] = [] := by
  rfl

@[simp] theorem compactBinaryNatPayloadBits_cons
    (token : Nat) (tokens : List Nat) :
    compactBinaryNatPayloadBits (token :: tokens) =
      FoundationSuccinctFiniteConsistencyTarget.binaryNatCode token ++
        compactBinaryNatPayloadBits tokens := by
  rfl

@[simp] theorem compactBinaryNatTokenOffsets_length (tokens : List Nat) :
    (compactBinaryNatTokenOffsets tokens).length = tokens.length + 1 := by
  induction tokens with
  | nil => simp [compactBinaryNatTokenOffsets]
  | cons token tokens ih =>
      simp [compactBinaryNatTokenOffsets, ih]

@[simp] theorem compactBinaryNatTokenOffsets_getI_zero (tokens : List Nat) :
    (compactBinaryNatTokenOffsets tokens).getI 0 = 0 := by
  cases tokens <;> rfl

theorem compactBinaryNatTokenOffsets_getI_succ
    (token : Nat) (tokens : List Nat) (index : Nat)
    (hindex : index < (compactBinaryNatTokenOffsets tokens).length) :
    (compactBinaryNatTokenOffsets (token :: tokens)).getI (index + 1) =
      compactBinaryNatTokenWidth token +
        (compactBinaryNatTokenOffsets tokens).getI index := by
  simp only [compactBinaryNatTokenOffsets, List.getI_cons_succ]
  rw [List.getI_eq_getElem _ (by simpa using hindex)]
  rw [List.getI_eq_getElem _ hindex]
  simp

@[simp] theorem compactBinaryNatPayloadBits_length (tokens : List Nat) :
    (compactBinaryNatPayloadBits tokens).length =
      (compactBinaryNatTokenOffsets tokens).getI tokens.length := by
  induction tokens with
  | nil => simp [compactBinaryNatTokenOffsets]
  | cons token tokens ih =>
      rw [compactBinaryNatPayloadBits_cons, List.length_append]
      rw [← compactBinaryNatTokenWidth_eq_code_length]
      rw [show (token :: tokens).length = tokens.length + 1 by simp]
      rw [compactBinaryNatTokenOffsets_getI_succ]
      · rw [← ih]
      · simp

def compactEscapedNatBits (bits : List Bool) : List Bool :=
  bits.flatMap fun bit => [true, bit]

@[simp] theorem compactEscapedNatBits_length (bits : List Bool) :
    (compactEscapedNatBits bits).length = 2 * bits.length := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      simp [compactEscapedNatBits]
      omega

theorem compactEscapedNatBits_getI_marker
    (bits : List Bool) (index : Nat) (hindex : index < bits.length) :
    (compactEscapedNatBits bits).getI (2 * index) = true := by
  induction bits generalizing index with
  | nil => simp at hindex
  | cons bit bits ih =>
      cases index with
      | zero => rfl
      | succ index =>
          have hindex' : index < bits.length := by simpa using hindex
          change ([true, bit] ++ compactEscapedNatBits bits).getI
              (2 * (index + 1)) = true
          have hposition : 2 * (index + 1) = 2 + 2 * index := by
            omega
          rw [hposition, List.getI_append_right]
          · simpa using ih index hindex'
          · simp

theorem compactEscapedNatBits_getI_data
    (bits : List Bool) (index : Nat) (hindex : index < bits.length) :
    (compactEscapedNatBits bits).getI (2 * index + 1) =
      bits.getI index := by
  induction bits generalizing index with
  | nil => simp at hindex
  | cons bit bits ih =>
      cases index with
      | zero => rfl
      | succ index =>
          have hindex' : index < bits.length := by simpa using hindex
          change ([true, bit] ++ compactEscapedNatBits bits).getI
              (2 * (index + 1) + 1) = bits.getI index
          have hposition :
              2 * (index + 1) + 1 = 2 + (2 * index + 1) := by
            omega
          rw [hposition, List.getI_append_right]
          · simpa using ih index hindex'
          · simp

theorem binaryNatCode_getI_marker
    (token index : Nat) (hindex : index < Nat.size token) :
    (FoundationSuccinctFiniteConsistencyTarget.binaryNatCode token).getI
        (2 * index) = true := by
  rw [show FoundationSuccinctFiniteConsistencyTarget.binaryNatCode token =
      compactEscapedNatBits token.bits ++ [false, false] by rfl]
  rw [List.getI_append _ _ _]
  · exact compactEscapedNatBits_getI_marker token.bits index
      (by simpa [Nat.size_eq_bits_len] using hindex)
  · simp [Nat.size_eq_bits_len] at hindex ⊢
    omega

theorem binaryNatCode_getI_data
    (token index : Nat) (hindex : index < Nat.size token) :
    (FoundationSuccinctFiniteConsistencyTarget.binaryNatCode token).getI
        (2 * index + 1) = token.testBit index := by
  rw [show FoundationSuccinctFiniteConsistencyTarget.binaryNatCode token =
      compactEscapedNatBits token.bits ++ [false, false] by rfl]
  rw [List.getI_append _ _ _]
  · rw [compactEscapedNatBits_getI_data token.bits index
      (by simpa [Nat.size_eq_bits_len] using hindex)]
    exact (Nat.testBit_eq_inth token index).symm
  · simp [Nat.size_eq_bits_len] at hindex ⊢
    omega

@[simp] theorem binaryNatCode_getI_terminator_zero (token : Nat) :
    (FoundationSuccinctFiniteConsistencyTarget.binaryNatCode token).getI
        (2 * Nat.size token) = false := by
  rw [show FoundationSuccinctFiniteConsistencyTarget.binaryNatCode token =
      compactEscapedNatBits token.bits ++ [false, false] by rfl]
  rw [List.getI_append_right]
  · simp [Nat.size_eq_bits_len]
  · simp [Nat.size_eq_bits_len]

@[simp] theorem binaryNatCode_getI_terminator_one (token : Nat) :
    (FoundationSuccinctFiniteConsistencyTarget.binaryNatCode token).getI
        (2 * Nat.size token + 1) = false := by
  rw [show FoundationSuccinctFiniteConsistencyTarget.binaryNatCode token =
      compactEscapedNatBits token.bits ++ [false, false] by rfl]
  rw [List.getI_append_right]
  · simp [Nat.size_eq_bits_len]
  · simp [Nat.size_eq_bits_len]

theorem compactBinaryNatTokenSegment_head
    (token : Nat) (tokens : List Nat) :
    CompactBinaryNatTokenSegment
      (compactBinaryNatPayloadValue (token :: tokens))
      0 token (compactBinaryNatTokenWidth token) := by
  refine ⟨by simp [compactBinaryNatTokenWidth], ?_, ?_, ?_⟩
  · intro index hindex
    constructor
    · rw [compactBinaryNatPayloadValue,
        natOfBitsList_testBit_eq_getI,
        compactBinaryNatPayloadBits_cons]
      rw [List.getI_append _ _ _]
      · simpa using binaryNatCode_getI_marker token index hindex
      · rw [FoundationCompactCanonicalDecodeLength.binaryNatCode_length]
        omega
    · rw [compactBinaryNatPayloadValue,
        natOfBitsList_testBit_eq_getI,
        compactBinaryNatPayloadBits_cons]
      rw [List.getI_append _ _ _]
      · simpa using binaryNatCode_getI_data token index hindex
      · rw [FoundationCompactCanonicalDecodeLength.binaryNatCode_length]
        omega
  · rw [compactBinaryNatPayloadValue,
      natOfBitsList_testBit_eq_getI,
      compactBinaryNatPayloadBits_cons]
    rw [List.getI_append _ _ _]
    · simp
    · rw [FoundationCompactCanonicalDecodeLength.binaryNatCode_length]
      omega
  · rw [compactBinaryNatPayloadValue,
      natOfBitsList_testBit_eq_getI,
      compactBinaryNatPayloadBits_cons]
    rw [List.getI_append _ _ _]
    · simp
    · rw [FoundationCompactCanonicalDecodeLength.binaryNatCode_length]
      omega

theorem natOfBitsList_append_testBit_right
    (headBits tailBits : List Bool) (index : Nat) :
    (FoundationCompactVerifierBitCostPrimitives.natOfBitsList
        (headBits ++ tailBits)).testBit (headBits.length + index) =
      (FoundationCompactVerifierBitCostPrimitives.natOfBitsList tailBits).testBit
        index := by
  rw [natOfBitsList_testBit_eq_getI,
    natOfBitsList_testBit_eq_getI]
  rw [List.getI_append_right]
  · simp
  · omega

theorem compactBinaryNatTokenSegment_prepend
    (headBits tailBits : List Bool) (offset token next : Nat)
    (hsegment : CompactBinaryNatTokenSegment
      (FoundationCompactVerifierBitCostPrimitives.natOfBitsList tailBits)
      offset token next) :
    CompactBinaryNatTokenSegment
      (FoundationCompactVerifierBitCostPrimitives.natOfBitsList
        (headBits ++ tailBits))
      (headBits.length + offset) token (headBits.length + next) := by
  rcases hsegment with ⟨hnext, hbits, hzero, hone⟩
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro index hindex
    rcases hbits index hindex with ⟨hmarker, hdata⟩
    constructor
    · simpa [Nat.add_assoc] using
        (natOfBitsList_append_testBit_right headBits tailBits
          (offset + 2 * index)).trans hmarker
    · simpa [Nat.add_assoc] using
        (natOfBitsList_append_testBit_right headBits tailBits
          (offset + 2 * index + 1)).trans hdata
  · simpa [Nat.add_assoc] using
      (natOfBitsList_append_testBit_right headBits tailBits
        (offset + 2 * Nat.size token)).trans hzero
  · simpa [Nat.add_assoc] using
      (natOfBitsList_append_testBit_right headBits tailBits
        (offset + 2 * Nat.size token + 1)).trans hone

theorem compactBinaryNatPayloadValue_segment
    (tokens : List Nat) (index : Nat) (hindex : index < tokens.length) :
    CompactBinaryNatTokenSegment
      (compactBinaryNatPayloadValue tokens)
      ((compactBinaryNatTokenOffsets tokens).getI index)
      (tokens.getI index)
      ((compactBinaryNatTokenOffsets tokens).getI (index + 1)) := by
  induction tokens generalizing index with
  | nil => simp at hindex
  | cons token tokens ih =>
      cases index with
      | zero =>
          rw [compactBinaryNatTokenOffsets_getI_succ
            token tokens 0 (by simp)]
          simpa [compactBinaryNatTokenOffsets] using
            compactBinaryNatTokenSegment_head token tokens
      | succ index =>
          have hindex' : index < tokens.length := by
            simpa using hindex
          have htail := ih index hindex'
          have hshifted := compactBinaryNatTokenSegment_prepend
            (FoundationSuccinctFiniteConsistencyTarget.binaryNatCode token)
            (compactBinaryNatPayloadBits tokens)
            ((compactBinaryNatTokenOffsets tokens).getI index)
            (tokens.getI index)
            ((compactBinaryNatTokenOffsets tokens).getI (index + 1))
            (by simpa [compactBinaryNatPayloadValue] using htail)
          have hcurrentIndex :
              index < (compactBinaryNatTokenOffsets tokens).length := by
            rw [compactBinaryNatTokenOffsets_length]
            omega
          have hnextIndex :
              index + 1 < (compactBinaryNatTokenOffsets tokens).length := by
            rw [compactBinaryNatTokenOffsets_length]
            omega
          rw [compactBinaryNatTokenOffsets_getI_succ
            token tokens index hcurrentIndex]
          rw [show index + 1 + 1 = (index + 1) + 1 by rfl]
          rw [compactBinaryNatTokenOffsets_getI_succ
            token tokens (index + 1) hnextIndex]
          simpa [compactBinaryNatPayloadValue,
            compactBinaryNatPayloadBits_cons,
            compactBinaryNatTokenWidth_eq_code_length] using hshifted

theorem compactBinaryNatToken_count_le_payloadLength (tokens : List Nat) :
    tokens.length ≤ (compactBinaryNatPayloadBits tokens).length := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
      rw [compactBinaryNatPayloadBits_cons, List.length_append]
      rw [FoundationCompactCanonicalDecodeLength.binaryNatCode_length]
      simp only [List.length_cons]
      omega

theorem compactBinaryNatToken_size_le_payloadLength
    (tokens : List Nat) (token : Nat) (htoken : token ∈ tokens) :
    Nat.size token ≤ (compactBinaryNatPayloadBits tokens).length := by
  induction tokens with
  | nil => simp at htoken
  | cons head tokens ih =>
      rw [compactBinaryNatPayloadBits_cons, List.length_append]
      rw [FoundationCompactCanonicalDecodeLength.binaryNatCode_length]
      rcases List.mem_cons.mp htoken with rfl | htoken
      · omega
      · have htail := ih htoken
        omega

theorem compactBinaryNatTokenOffsets_mem_le_payloadLength
    (tokens : List Nat) (offset : Nat)
    (hoffset : offset ∈ compactBinaryNatTokenOffsets tokens) :
    offset ≤ (compactBinaryNatPayloadBits tokens).length := by
  induction tokens generalizing offset with
  | nil =>
      simp [compactBinaryNatTokenOffsets] at hoffset
      simp [hoffset]
  | cons token tokens ih =>
      simp only [compactBinaryNatTokenOffsets, List.mem_cons,
        List.mem_map] at hoffset
      rcases hoffset with rfl | ⟨tailOffset, htailOffset, rfl⟩
      · simp
      · rw [compactBinaryNatPayloadBits_cons, List.length_append]
        rw [← compactBinaryNatTokenWidth_eq_code_length]
        have htail := ih tailOffset htailOffset
        omega

theorem compactBinaryNatTokenOffsets_size_le_payloadLength
    (tokens : List Nat) (offset : Nat)
    (hoffset : offset ∈ compactBinaryNatTokenOffsets tokens) :
    Nat.size offset ≤ (compactBinaryNatPayloadBits tokens).length := by
  rw [Nat.size_le]
  exact lt_of_le_of_lt
    (compactBinaryNatTokenOffsets_mem_le_payloadLength
      tokens offset hoffset)
    (compactBinaryNatPayloadBits tokens).length.lt_two_pow_self

/-- Every genuine flat token stream has canonical polynomial-size token and
offset tables satisfying the handwritten bounded formula. -/
theorem compactBinaryNatTokenStreamTableau_canonical
    (tokens : List Nat) :
    let payloadLength := (compactBinaryNatPayloadBits tokens).length
    CompactBinaryNatTokenStreamTableau
      (compactBinaryNatPayloadValue tokens)
      payloadLength (2 ^ payloadLength) tokens.length
      (compactFixedWidthTableCode payloadLength tokens)
      (compactFixedWidthTableCode payloadLength
        (compactBinaryNatTokenOffsets tokens)) := by
  let payloadLength := (compactBinaryNatPayloadBits tokens).length
  have htokenSizes : ∀ token ∈ tokens, Nat.size token ≤ payloadLength := by
    intro token htoken
    exact compactBinaryNatToken_size_le_payloadLength tokens token htoken
  have hoffsetSizes : ∀ offset ∈ compactBinaryNatTokenOffsets tokens,
      Nat.size offset ≤ payloadLength := by
    intro offset hoffset
    exact compactBinaryNatTokenOffsets_size_le_payloadLength
      tokens offset hoffset
  have hoffsetZero := compactFixedWidthTableCode_entry payloadLength
    (compactBinaryNatTokenOffsets tokens) 0
    (by simp) hoffsetSizes
  have hoffsetFinal := compactFixedWidthTableCode_entry payloadLength
    (compactBinaryNatTokenOffsets tokens) tokens.length
    (by simp) hoffsetSizes
  have hfinalValue :
      (compactBinaryNatTokenOffsets tokens).getI tokens.length =
        payloadLength := by
    exact (compactBinaryNatPayloadBits_length tokens).symm
  rw [compactBinaryNatTokenOffsets_getI_zero] at hoffsetZero
  rw [hfinalValue] at hoffsetFinal
  refine ⟨rfl, by
    exact (compactBinaryNatToken_count_le_payloadLength tokens).trans
      (Nat.le_succ payloadLength), ?_, ?_, ?_⟩
  · exact hoffsetZero
  · exact hoffsetFinal
  · intro index hindex
    have htokenMem : tokens.getI index ∈ tokens := by
      rw [List.getI_eq_getElem _ hindex]
      exact List.getElem_mem hindex
    have hcurrentIndex :
        index < (compactBinaryNatTokenOffsets tokens).length := by
      rw [compactBinaryNatTokenOffsets_length]
      omega
    have hnextIndex :
        index + 1 < (compactBinaryNatTokenOffsets tokens).length := by
      rw [compactBinaryNatTokenOffsets_length]
      omega
    have hcurrentMem :
        (compactBinaryNatTokenOffsets tokens).getI index ∈
          compactBinaryNatTokenOffsets tokens := by
      rw [List.getI_eq_getElem _ hcurrentIndex]
      exact List.getElem_mem hcurrentIndex
    have hnextMem :
        (compactBinaryNatTokenOffsets tokens).getI (index + 1) ∈
          compactBinaryNatTokenOffsets tokens := by
      rw [List.getI_eq_getElem _ hnextIndex]
      exact List.getElem_mem hnextIndex
    refine ⟨tokens.getI index, ?_,
      (compactBinaryNatTokenOffsets tokens).getI index, ?_,
      (compactBinaryNatTokenOffsets tokens).getI (index + 1), ?_,
      compactFixedWidthTableCode_entry payloadLength tokens index hindex
        htokenSizes,
      compactFixedWidthTableCode_entry payloadLength
        (compactBinaryNatTokenOffsets tokens) index hcurrentIndex
        hoffsetSizes,
      compactFixedWidthTableCode_entry payloadLength
        (compactBinaryNatTokenOffsets tokens) (index + 1) hnextIndex
        hoffsetSizes,
      compactBinaryNatPayloadValue_segment tokens index hindex⟩
    · exact Nat.le_of_lt <| Nat.size_le.mp <| htokenSizes _ htokenMem
    · exact Nat.le_of_lt <| lt_of_le_of_lt
        (compactBinaryNatTokenOffsets_mem_le_payloadLength
          tokens _ hcurrentMem) payloadLength.lt_two_pow_self
    · exact Nat.le_of_lt <| lt_of_le_of_lt
        (compactBinaryNatTokenOffsets_mem_le_payloadLength
          tokens _ hnextMem) payloadLength.lt_two_pow_self

theorem compactBinaryNatTokenStreamTableau_canonical_size_bounds
    (tokens : List Nat) :
    let payloadLength := (compactBinaryNatPayloadBits tokens).length
    Nat.size (compactFixedWidthTableCode payloadLength tokens) ≤
        tokens.length * payloadLength ∧
      Nat.size (compactFixedWidthTableCode payloadLength
        (compactBinaryNatTokenOffsets tokens)) ≤
        (tokens.length + 1) * payloadLength := by
  let payloadLength := (compactBinaryNatPayloadBits tokens).length
  constructor
  · exact compactFixedWidthTableCode_size_le payloadLength tokens
  · have hbound := compactFixedWidthTableCode_size_le payloadLength
      (compactBinaryNatTokenOffsets tokens)
    rw [compactBinaryNatTokenOffsets_length] at hbound
    exact hbound

#print axioms compactBinaryNatTokenStreamTableauDef_spec
#print axioms compactBinaryNatTokenStreamTableauDef_sigmaZero
#print axioms compactBinaryNatPayloadValue_segment
#print axioms compactBinaryNatTokenStreamTableau_canonical
#print axioms compactBinaryNatTokenStreamTableau_canonical_size_bounds

end FoundationCompactNumericListedDirectTokenStreamTableau
