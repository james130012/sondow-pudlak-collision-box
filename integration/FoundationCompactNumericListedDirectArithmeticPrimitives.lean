import integration.FoundationCompactNumericListedDirectTraceBounds
import Foundation.FirstOrder.Arithmetic.Exponential.Log

/-!
# Direct arithmetic primitives for the compact listed trace

This module starts the handwritten arithmetic graph from Foundation's bounded
binary-length formula.  It does not use the generic RE projection or `rfind`
representation route.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectArithmeticPrimitives

/-- Foundation's model-theoretic binary length agrees with the exact
`Nat.size` coordinate used by the public verifier and all trace bounds. -/
theorem binaryLength_nat_eq_size (n : Nat) :
    LO.FirstOrder.Arithmetic.binaryLength n = Nat.size n := by
  induction n using Nat.binaryRec' with
  | zero => simp [LO.FirstOrder.Arithmetic.binaryLength]
  | bit bit n hn ih =>
      have hnonzero : Nat.bit bit n ≠ 0 :=
        Nat.bit_ne_zero_iff.mpr hn
      rw [Nat.size_bit hnonzero]
      cases bit with
      | false =>
          have hnpos : 0 < n := by
            exact Nat.pos_of_ne_zero (by simpa [Nat.bit] using hnonzero)
          have hlength :=
            LO.FirstOrder.Arithmetic.length_two_mul_of_pos
              (V := Nat) hnpos
          change LO.FirstOrder.Arithmetic.binaryLength (2 * n) =
            LO.FirstOrder.Arithmetic.binaryLength n + 1 at hlength
          simpa [Nat.bit, ih] using hlength
      | true =>
          have hlength :=
            LO.FirstOrder.Arithmetic.length_two_mul_add_one
              (V := Nat) n
          change LO.FirstOrder.Arithmetic.binaryLength (2 * n + 1) =
            LO.FirstOrder.Arithmetic.binaryLength n + 1 at hlength
          simpa [Nat.bit, ih] using hlength

/-- Direct bounded arithmetic graph for the honest binary code length. -/
def compactNatSizeDef : 𝚺₀.Semisentence 2 :=
  LO.FirstOrder.Arithmetic.lengthDef

@[simp] theorem compactNatSizeDef_spec (size value : Nat) :
    compactNatSizeDef.val.Evalb ![size, value] ↔
      size = Nat.size value := by
  simp [compactNatSizeDef]
  change size = LO.FirstOrder.Arithmetic.binaryLength value ↔
    size = Nat.size value
  rw [binaryLength_nat_eq_size]

theorem compactNatSizeDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNatSizeDef.val := by
  simp [compactNatSizeDef]

@[simp] theorem arithmeticExp_nat (n : Nat) :
    LO.Exp.exp n = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [LO.FirstOrder.Arithmetic.exp_succ, ih, pow_succ]
      omega

theorem natOfBitsList_lt_two_pow_length (bits : List Bool) :
    FoundationCompactVerifierBitCostPrimitives.natOfBitsList bits <
      2 ^ bits.length := by
  induction bits with
  | nil => simp [FoundationCompactVerifierBitCostPrimitives.natOfBitsList]
  | cons bit bits ih =>
      cases bit <;>
        simp [FoundationCompactVerifierBitCostPrimitives.natOfBitsList,
          Nat.bit, pow_succ] <;> omega

theorem packBinaryString_eq_payload_add_sentinel (bits : List Bool) :
    FoundationSuccinctFiniteConsistencyTarget.packBinaryString bits =
      FoundationCompactVerifierBitCostPrimitives.natOfBitsList bits +
        2 ^ bits.length := by
  induction bits with
  | nil =>
      simp [FoundationSuccinctFiniteConsistencyTarget.packBinaryString,
        FoundationCompactVerifierBitCostPrimitives.natOfBitsList]
  | cons bit bits ih =>
      cases bit <;>
        simp [FoundationSuccinctFiniteConsistencyTarget.packBinaryString,
          FoundationCompactVerifierBitCostPrimitives.natOfBitsList,
          Nat.bit, ih, pow_succ] <;> omega

/-- A packed bit string is represented by its low-bit value and its exact
length.  The terminal sentinel is the single power of two above that payload. -/
def compactPackedPayloadDef : 𝚺₀.Semisentence 3 := .mkSigma
  “payloadValue payloadLength code.
    ∃ sentinel <⁺ code,
      !expDef sentinel payloadLength ∧
      payloadValue < sentinel ∧
      code = payloadValue + sentinel”

@[simp] theorem compactPackedPayloadDef_spec
    (payloadValue payloadLength code : Nat) :
    compactPackedPayloadDef.val.Evalb
        ![payloadValue, payloadLength, code] ↔
      payloadValue < 2 ^ payloadLength ∧
        code = payloadValue + 2 ^ payloadLength := by
  simp [compactPackedPayloadDef]
  intro _ hcode
  rw [hcode]
  exact @le_add_self Nat
    LO.ORingStructure.toAdd
    LO.FirstOrder.Arithmetic.instLE_foundation
    LO.FirstOrder.Arithmetic.instCanonicallyOrderedAdd_foundation
    (2 ^ payloadLength) payloadValue

@[simp] theorem compactPackedPayloadDef_pack_iff
    (bits : List Bool) (code : Nat) :
    compactPackedPayloadDef.val.Evalb
        ![FoundationCompactVerifierBitCostPrimitives.natOfBitsList bits,
          bits.length, code] ↔
      code = FoundationSuccinctFiniteConsistencyTarget.packBinaryString bits := by
  rw [compactPackedPayloadDef_spec]
  simp only [natOfBitsList_lt_two_pow_length, true_and]
  rw [packBinaryString_eq_payload_add_sentinel]

theorem compactPackedPayloadDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactPackedPayloadDef.val := by
  simp [compactPackedPayloadDef]

private def foundationNatMul (left right : Nat) : Nat :=
  @Mul.mul Nat LO.ORingStructure.toMul left right

private def foundationNatAdd (left right : Nat) : Nat :=
  @Add.add Nat LO.ORingStructure.toAdd left right

@[simp] private theorem foundationNatMul_eq (left right : Nat) :
    foundationNatMul left right = left * right := by
  rfl

@[simp] private theorem foundationNatAdd_eq (left right : Nat) :
    foundationNatAdd left right = left + right := by
  rfl

/-- Foundation's arithmetic bit relation is exactly Lean's standard natural
number bit test. -/
theorem arithmeticBit_nat_iff_testBit (index value : Nat) :
    LO.FirstOrder.Arithmetic.Bit index value ↔
      value.testBit index = true := by
  induction value using Nat.binaryRec' generalizing index with
  | zero =>
      have hzero := LO.FirstOrder.Arithmetic.not_mem_zero
        (V := Nat) index
      change ¬ LO.FirstOrder.Arithmetic.Bit index 0 at hzero
      simp [hzero]
  | bit bit value hn ih =>
      cases index with
      | zero =>
          cases bit with
          | false =>
              have hzero := LO.FirstOrder.Arithmetic.zero_not_mem
                (V := Nat) value
              change ¬ LO.FirstOrder.Arithmetic.Bit 0
                (foundationNatMul 2 value) at hzero
              simp only [foundationNatMul_eq] at hzero
              change LO.FirstOrder.Arithmetic.Bit 0 (2 * value) ↔
                (Nat.bit false value).testBit 0 = true
              rw [Nat.testBit_bit_zero]
              simpa using hzero
          | true =>
              have hone := LO.FirstOrder.Arithmetic.zero_mem_double_add_one
                (V := Nat) value
              change LO.FirstOrder.Arithmetic.Bit 0
                (foundationNatAdd (foundationNatMul 2 value) 1) at hone
              simp only [foundationNatMul_eq, foundationNatAdd_eq] at hone
              change LO.FirstOrder.Arithmetic.Bit 0 (2 * value + 1) ↔
                (Nat.bit true value).testBit 0 = true
              rw [Nat.testBit_bit_zero]
              simpa using hone
      | succ index =>
          cases bit with
          | false =>
              have hsucc := LO.FirstOrder.Arithmetic.succ_mem_two_mul_iff
                (V := Nat) (i := index) (a := value)
              change LO.FirstOrder.Arithmetic.Bit (index + 1)
                  (foundationNatMul 2 value) ↔
                LO.FirstOrder.Arithmetic.Bit index value at hsucc
              simp only [foundationNatMul_eq] at hsucc
              change LO.FirstOrder.Arithmetic.Bit (index + 1) (2 * value) ↔
                (Nat.bit false value).testBit (index + 1) = true
              rw [hsucc, ih, Nat.testBit_bit_succ]
          | true =>
              have hsucc :=
                LO.FirstOrder.Arithmetic.succ_mem_two_mul_succ_iff
                  (V := Nat) (i := index) (a := value)
              change LO.FirstOrder.Arithmetic.Bit (index + 1)
                  (foundationNatAdd (foundationNatMul 2 value) 1) ↔
                LO.FirstOrder.Arithmetic.Bit index value at hsucc
              simp only [foundationNatMul_eq, foundationNatAdd_eq] at hsucc
              change LO.FirstOrder.Arithmetic.Bit (index + 1)
                  (2 * value + 1) ↔
                (Nat.bit true value).testBit (index + 1) = true
              rw [hsucc, ih, Nat.testBit_bit_succ]

theorem arithmeticMem_nat_iff_testBit (index value : Nat) :
    index ∈ value ↔ value.testBit index = true := by
  rw [LO.FirstOrder.Arithmetic.mem_iff_bit,
    arithmeticBit_nat_iff_testBit]

/-- One self-delimiting `binaryNatCode` segment starts at `offset`, contains
one `(marker,data)` pair for every token bit, and ends at `next` after `00`. -/
def CompactBinaryNatTokenSegment
    (payload offset token next : Nat) : Prop :=
  let size := Nat.size token
  next = offset + 2 * size + 2 ∧
    (∀ index < size,
      payload.testBit (offset + 2 * index) = true ∧
      payload.testBit (offset + 2 * index + 1) =
        token.testBit index) ∧
    payload.testBit (offset + 2 * size) = false ∧
    payload.testBit (offset + 2 * size + 1) = false

/-- Direct bounded arithmetic graph of one self-delimiting natural-number
token inside a packed payload. -/
def compactBinaryNatTokenSegmentDef : 𝚺₀.Semisentence 4 := .mkSigma
  “payload offset token next.
    ∃ size <⁺ token,
      !(compactNatSizeDef) size token ∧
      next = offset + 2 * size + 2 ∧
      (∀ index < size,
        (offset + 2 * index) ∈ payload ∧
        ((offset + 2 * index + 1) ∈ payload ↔ index ∈ token)) ∧
      (offset + 2 * size) ∉ payload ∧
      (offset + 2 * size + 1) ∉ payload”

@[simp] theorem compactBinaryNatTokenSegmentDef_spec
    (payload offset token next : Nat) :
    compactBinaryNatTokenSegmentDef.val.Evalb
        ![payload, offset, token, next] ↔
      CompactBinaryNatTokenSegment payload offset token next := by
  have hsize :
      @LE.le Nat LO.FirstOrder.Arithmetic.instLE_foundation
        (Nat.size token) token := by
    have hlength := LO.FirstOrder.Arithmetic.length_le (V := Nat) token
    have hlength_eq : (‖token‖ : Nat) =
        LO.FirstOrder.Arithmetic.binaryLength token := rfl
    rw [hlength_eq, binaryLength_nat_eq_size] at hlength
    exact hlength
  simp [compactBinaryNatTokenSegmentDef,
    CompactBinaryNatTokenSegment, arithmeticMem_nat_iff_testBit,
    hsize]
  rfl

theorem compactBinaryNatTokenSegmentDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactBinaryNatTokenSegmentDef.val := by
  simp [compactBinaryNatTokenSegmentDef]

/-- A value occupies one `width`-bit row of a flat binary tableau. -/
def CompactFixedWidthEntry
    (table width index value : Nat) : Prop :=
  Nat.size value ≤ width ∧
    ∀ bitIndex < width,
      table.testBit (index * width + bitIndex) =
        value.testBit bitIndex

/-- Direct bounded graph for random access to one row of a flat fixed-width
tableau. -/
def compactFixedWidthEntryDef : 𝚺₀.Semisentence 4 := .mkSigma
  “table width index value.
    ∃ size <⁺ value,
      !(compactNatSizeDef) size value ∧
      size ≤ width ∧
      ∀ bitIndex < width,
        ((index * width + bitIndex) ∈ table ↔ bitIndex ∈ value)”

@[simp] theorem compactFixedWidthEntryDef_spec
    (table width index value : Nat) :
    compactFixedWidthEntryDef.val.Evalb
        ![table, width, index, value] ↔
      CompactFixedWidthEntry table width index value := by
  have hsize :
      @LE.le Nat LO.FirstOrder.Arithmetic.instLE_foundation
        (Nat.size value) value := by
    have hlength := LO.FirstOrder.Arithmetic.length_le (V := Nat) value
    have hlength_eq : (‖value‖ : Nat) =
        LO.FirstOrder.Arithmetic.binaryLength value := rfl
    rw [hlength_eq, binaryLength_nat_eq_size] at hlength
    exact hlength
  simp [compactFixedWidthEntryDef, CompactFixedWidthEntry,
    arithmeticMem_nat_iff_testBit, hsize]

theorem compactFixedWidthEntryDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFixedWidthEntryDef.val := by
  simp [compactFixedWidthEntryDef]

theorem natOfBitsList_testBit_eq_getI
    (bits : List Bool) (index : Nat) :
    (FoundationCompactVerifierBitCostPrimitives.natOfBitsList bits).testBit
        index = bits.getI index := by
  induction bits generalizing index with
  | nil => simp [FoundationCompactVerifierBitCostPrimitives.natOfBitsList]
  | cons bit bits ih =>
      cases index with
      | zero =>
          simp [FoundationCompactVerifierBitCostPrimitives.natOfBitsList]
      | succ index =>
          simp only [FoundationCompactVerifierBitCostPrimitives.natOfBitsList]
          rw [Nat.testBit_bit_succ]
          simpa using ih index

def compactFixedWidthBits (width value : Nat) : List Bool :=
  (List.range width).map value.testBit

def compactFixedWidthTableBits
    (width : Nat) (values : List Nat) : List Bool :=
  values.flatMap (compactFixedWidthBits width)

/-- Canonical row-major tableau code.  It has no terminal sentinel because its
row count and width are carried separately by the surrounding formula. -/
def compactFixedWidthTableCode
    (width : Nat) (values : List Nat) : Nat :=
  FoundationCompactVerifierBitCostPrimitives.natOfBitsList
    (compactFixedWidthTableBits width values)

@[simp] theorem compactFixedWidthBits_length (width value : Nat) :
    (compactFixedWidthBits width value).length = width := by
  simp [compactFixedWidthBits]

@[simp] theorem compactFixedWidthBits_getI
    (width value bitIndex : Nat) (hbitIndex : bitIndex < width) :
    (compactFixedWidthBits width value).getI bitIndex =
      value.testBit bitIndex := by
  rw [List.getI_eq_getElem _ (by simpa using hbitIndex)]
  simp [compactFixedWidthBits]

theorem compactFixedWidthTableBits_getI
    (width : Nat) (values : List Nat)
    (index bitIndex : Nat)
    (hindex : index < values.length)
    (hbitIndex : bitIndex < width) :
    (compactFixedWidthTableBits width values).getI
        (index * width + bitIndex) =
      (values.getI index).testBit bitIndex := by
  induction values generalizing index with
  | nil => simp at hindex
  | cons value values ih =>
      cases index with
      | zero =>
          simp only [Nat.zero_mul, Nat.zero_add]
          rw [show compactFixedWidthTableBits width (value :: values) =
              compactFixedWidthBits width value ++
                compactFixedWidthTableBits width values by
            rfl]
          rw [List.getI_append _ _ _ (by simpa using hbitIndex)]
          simp [compactFixedWidthBits_getI, hbitIndex]
      | succ index =>
          have hindex' : index < values.length := by
            simpa using hindex
          rw [show compactFixedWidthTableBits width (value :: values) =
              compactFixedWidthBits width value ++
                compactFixedWidthTableBits width values by
            rfl]
          have hposition :
              (index + 1) * width + bitIndex =
                width + (index * width + bitIndex) := by
            simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm]
          rw [hposition]
          rw [List.getI_append_right]
          · simpa using ih index hindex'
          · simp

theorem compactFixedWidthTableCode_testBit
    (width : Nat) (values : List Nat)
    (index bitIndex : Nat)
    (hindex : index < values.length)
    (hbitIndex : bitIndex < width) :
    (compactFixedWidthTableCode width values).testBit
        (index * width + bitIndex) =
      (values.getI index).testBit bitIndex := by
  rw [compactFixedWidthTableCode, natOfBitsList_testBit_eq_getI]
  exact compactFixedWidthTableBits_getI
    width values index bitIndex hindex hbitIndex

@[simp] theorem compactFixedWidthTableBits_length
    (width : Nat) (values : List Nat) :
    (compactFixedWidthTableBits width values).length =
      values.length * width := by
  induction values with
  | nil => simp [compactFixedWidthTableBits]
  | cons value values ih =>
      simp [compactFixedWidthTableBits, Nat.add_mul]
      omega

theorem compactFixedWidthTableCode_entry
    (width : Nat) (values : List Nat) (index : Nat)
    (hindex : index < values.length)
    (hvalues : ∀ value ∈ values, Nat.size value ≤ width) :
    CompactFixedWidthEntry
      (compactFixedWidthTableCode width values)
      width index (values.getI index) := by
  refine ⟨?_, ?_⟩
  · apply hvalues
    rw [List.getI_eq_getElem _ hindex]
    exact List.getElem_mem hindex
  · intro bitIndex hbitIndex
    exact compactFixedWidthTableCode_testBit
      width values index bitIndex hindex hbitIndex

theorem compactFixedWidthTableCode_size_le
    (width : Nat) (values : List Nat) :
    Nat.size (compactFixedWidthTableCode width values) ≤
      values.length * width := by
  rw [Nat.size_le]
  simpa [compactFixedWidthTableCode] using
    natOfBitsList_lt_two_pow_length
      (compactFixedWidthTableBits width values)

#print axioms binaryLength_nat_eq_size
#print axioms compactNatSizeDef_spec
#print axioms compactNatSizeDef_sigmaZero
#print axioms arithmeticExp_nat
#print axioms natOfBitsList_lt_two_pow_length
#print axioms packBinaryString_eq_payload_add_sentinel
#print axioms compactPackedPayloadDef_spec
#print axioms compactPackedPayloadDef_pack_iff
#print axioms compactPackedPayloadDef_sigmaZero
#print axioms arithmeticBit_nat_iff_testBit
#print axioms compactBinaryNatTokenSegmentDef_spec
#print axioms compactBinaryNatTokenSegmentDef_sigmaZero
#print axioms compactFixedWidthEntryDef_spec
#print axioms compactFixedWidthEntryDef_sigmaZero
#print axioms compactFixedWidthTableCode_testBit
#print axioms compactFixedWidthTableCode_entry
#print axioms compactFixedWidthTableCode_size_le

end FoundationCompactNumericListedDirectArithmeticPrimitives
