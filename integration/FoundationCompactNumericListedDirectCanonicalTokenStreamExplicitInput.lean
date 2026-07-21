import integration.FoundationCompactNumericListedDirectCanonicalFormulaTableRowWitnesses

/-!
# Explicit input data for a canonical token-stream tableau

The three row witnesses are functions of the row index.  No witness is
extracted from the existential row clause of the semantic tableau theorem.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

namespace FoundationCompactNumericListedDirectCanonicalTokenStreamExplicitInput

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectCanonicalFormulaTableRowWitnesses

/-- Data and proof fields consumed by the explicit token-tableau compiler.
The public-size fields are retained for the later polynomial compression. -/
structure ExplicitTokenStreamTableauInput
    (payload payloadLength sentinel tokenCount tokenTable offsetTable
      publicSize : Nat) : Type where
  sentinel_eq : sentinel = 2 ^ payloadLength
  tokenCount_le : tokenCount <= payloadLength + 1
  offsetZero : CompactFixedWidthEntry offsetTable payloadLength 0 0
  offsetLast :
    CompactFixedWidthEntry offsetTable payloadLength tokenCount payloadLength
  tokenAt : Nat -> Nat
  offsetAt : Nat -> Nat
  nextAt : Nat -> Nat
  token_le : forall index, index < tokenCount -> tokenAt index <= sentinel
  offset_le : forall index, index < tokenCount -> offsetAt index <= sentinel
  next_le : forall index, index < tokenCount -> nextAt index <= sentinel
  token_size_le :
    forall index, index < tokenCount -> Nat.size (tokenAt index) <= publicSize
  offset_size_le :
    forall index, index < tokenCount -> Nat.size (offsetAt index) <= publicSize
  next_size_le :
    forall index, index < tokenCount -> Nat.size (nextAt index) <= publicSize
  tokenEntry : forall index, index < tokenCount ->
    CompactFixedWidthEntry tokenTable payloadLength index (tokenAt index)
  offsetEntry : forall index, index < tokenCount ->
    CompactFixedWidthEntry offsetTable payloadLength index (offsetAt index)
  nextEntry : forall index, index < tokenCount ->
    CompactFixedWidthEntry offsetTable payloadLength (index + 1) (nextAt index)
  segment : forall index, index < tokenCount ->
    CompactBinaryNatTokenSegment payload (offsetAt index)
      (tokenAt index) (nextAt index)

private theorem canonicalRow_token_le
    (tokens : List Nat) (formulaCode index : Nat)
    (hcode : formulaCode = compactAdditivePackedCode tokens)
    (hindex : index < tokens.length) :
    let width := (compactBinaryNatPayloadBits tokens).length
    tokens.getI index <= 2 ^ width := by
  simpa using
    (compactNumericListedDirectCanonicalFormulaTable_rowWitnesses
      tokens formulaCode index hcode hindex).1

private theorem canonicalRow_offset_le
    (tokens : List Nat) (formulaCode index : Nat)
    (hcode : formulaCode = compactAdditivePackedCode tokens)
    (hindex : index < tokens.length) :
    let width := (compactBinaryNatPayloadBits tokens).length
    (compactBinaryNatTokenOffsets tokens).getI index <= 2 ^ width := by
  simpa using
    (compactNumericListedDirectCanonicalFormulaTable_rowWitnesses
      tokens formulaCode index hcode hindex).2.1

private theorem canonicalRow_next_le
    (tokens : List Nat) (formulaCode index : Nat)
    (hcode : formulaCode = compactAdditivePackedCode tokens)
    (hindex : index < tokens.length) :
    let width := (compactBinaryNatPayloadBits tokens).length
    (compactBinaryNatTokenOffsets tokens).getI (index + 1) <= 2 ^ width := by
  simpa using
    (compactNumericListedDirectCanonicalFormulaTable_rowWitnesses
      tokens formulaCode index hcode hindex).2.2.1

private theorem canonicalRow_token_size_le
    (tokens : List Nat) (formulaCode index : Nat)
    (hcode : formulaCode = compactAdditivePackedCode tokens)
    (hindex : index < tokens.length) :
    Nat.size (tokens.getI index) <= Nat.size formulaCode := by
  simpa using
    (compactNumericListedDirectCanonicalFormulaTable_rowWitnesses
      tokens formulaCode index hcode hindex).2.2.2.1

private theorem canonicalRow_offset_size_le
    (tokens : List Nat) (formulaCode index : Nat)
    (hcode : formulaCode = compactAdditivePackedCode tokens)
    (hindex : index < tokens.length) :
    Nat.size ((compactBinaryNatTokenOffsets tokens).getI index) <=
      Nat.size formulaCode := by
  simpa using
    (compactNumericListedDirectCanonicalFormulaTable_rowWitnesses
      tokens formulaCode index hcode hindex).2.2.2.2.1

private theorem canonicalRow_next_size_le
    (tokens : List Nat) (formulaCode index : Nat)
    (hcode : formulaCode = compactAdditivePackedCode tokens)
    (hindex : index < tokens.length) :
    Nat.size ((compactBinaryNatTokenOffsets tokens).getI (index + 1)) <=
      Nat.size formulaCode := by
  simpa using
    (compactNumericListedDirectCanonicalFormulaTable_rowWitnesses
      tokens formulaCode index hcode hindex).2.2.2.2.2.1

private theorem canonicalRow_tokenEntry
    (tokens : List Nat) (formulaCode index : Nat)
    (hcode : formulaCode = compactAdditivePackedCode tokens)
    (hindex : index < tokens.length) :
    let width := (compactBinaryNatPayloadBits tokens).length
    CompactFixedWidthEntry (compactFixedWidthTableCode width tokens)
      width index (tokens.getI index) := by
  simpa using
    (compactNumericListedDirectCanonicalFormulaTable_rowWitnesses
      tokens formulaCode index hcode hindex).2.2.2.2.2.2.1

private theorem canonicalRow_offsetEntry
    (tokens : List Nat) (formulaCode index : Nat)
    (hcode : formulaCode = compactAdditivePackedCode tokens)
    (hindex : index < tokens.length) :
    let width := (compactBinaryNatPayloadBits tokens).length
    let offsets := compactBinaryNatTokenOffsets tokens
    CompactFixedWidthEntry (compactFixedWidthTableCode width offsets)
      width index (offsets.getI index) := by
  simpa using
    (compactNumericListedDirectCanonicalFormulaTable_rowWitnesses
      tokens formulaCode index hcode hindex).2.2.2.2.2.2.2.1

private theorem canonicalRow_nextEntry
    (tokens : List Nat) (formulaCode index : Nat)
    (hcode : formulaCode = compactAdditivePackedCode tokens)
    (hindex : index < tokens.length) :
    let width := (compactBinaryNatPayloadBits tokens).length
    let offsets := compactBinaryNatTokenOffsets tokens
    CompactFixedWidthEntry (compactFixedWidthTableCode width offsets)
      width (index + 1) (offsets.getI (index + 1)) := by
  simpa using
    (compactNumericListedDirectCanonicalFormulaTable_rowWitnesses
      tokens formulaCode index hcode hindex).2.2.2.2.2.2.2.2.1

private theorem canonicalRow_segment
    (tokens : List Nat) (formulaCode index : Nat)
    (hcode : formulaCode = compactAdditivePackedCode tokens)
    (hindex : index < tokens.length) :
    let offsets := compactBinaryNatTokenOffsets tokens
    CompactBinaryNatTokenSegment (compactBinaryNatPayloadValue tokens)
      (offsets.getI index) (tokens.getI index)
      (offsets.getI (index + 1)) := by
  simpa using
    (compactNumericListedDirectCanonicalFormulaTable_rowWitnesses
      tokens formulaCode index hcode hindex).2.2.2.2.2.2.2.2.2

/-- Canonical list-derived input.  All data fields are definitions, while the
semantic fields are projections of direct row theorems. -/
noncomputable def canonicalTokenStreamExplicitInput
    (tokens : List Nat) (formulaCode : Nat)
    (hcode : formulaCode = compactAdditivePackedCode tokens) :
    let width := (compactBinaryNatPayloadBits tokens).length
    let offsets := compactBinaryNatTokenOffsets tokens
    ExplicitTokenStreamTableauInput
      (compactBinaryNatPayloadValue tokens) width (2 ^ width) tokens.length
      (compactFixedWidthTableCode width tokens)
      (compactFixedWidthTableCode width offsets)
      (Nat.size formulaCode) := by
  let width := (compactBinaryNatPayloadBits tokens).length
  let offsets := compactBinaryNatTokenOffsets tokens
  let canonical := compactBinaryNatTokenStreamTableau_canonical tokens
  exact {
    sentinel_eq := canonical.1
    tokenCount_le := canonical.2.1
    offsetZero := canonical.2.2.1
    offsetLast := canonical.2.2.2.1
    tokenAt := fun index => tokens.getI index
    offsetAt := fun index => offsets.getI index
    nextAt := fun index => offsets.getI (index + 1)
    token_le := fun index hindex =>
      canonicalRow_token_le tokens formulaCode index hcode hindex
    offset_le := fun index hindex =>
      canonicalRow_offset_le tokens formulaCode index hcode hindex
    next_le := fun index hindex =>
      canonicalRow_next_le tokens formulaCode index hcode hindex
    token_size_le := fun index hindex =>
      canonicalRow_token_size_le tokens formulaCode index hcode hindex
    offset_size_le := fun index hindex =>
      canonicalRow_offset_size_le tokens formulaCode index hcode hindex
    next_size_le := fun index hindex =>
      canonicalRow_next_size_le tokens formulaCode index hcode hindex
    tokenEntry := fun index hindex =>
      canonicalRow_tokenEntry tokens formulaCode index hcode hindex
    offsetEntry := fun index hindex =>
      canonicalRow_offsetEntry tokens formulaCode index hcode hindex
    nextEntry := fun index hindex =>
      canonicalRow_nextEntry tokens formulaCode index hcode hindex
    segment := fun index hindex =>
      canonicalRow_segment tokens formulaCode index hcode hindex }

#print axioms canonicalTokenStreamExplicitInput

end FoundationCompactNumericListedDirectCanonicalTokenStreamExplicitInput
