import integration.FoundationCompactCanonicalDecodeLength
import integration.FoundationCompactListedPackedBitTokenSynchronization
import Mathlib.Computability.Primrec.List

/-!
# Additive token codecs for direct verifier traces

The default `Encodable (List α)` nests `Nat.pair` once per list cell.  That is
primitive recursive, but its immediate bit-size recurrence can double at each
cell.  The codecs here instead serialize typed values to a flat `List Nat`.
The existing self-delimiting `binaryNatCode` then gives additive bit length.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactAdditiveTokenCodec

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCanonicalDecodeLength
open FoundationCompactListedVerifierArithmeticInput
open FoundationCompactBinaryNatStreamMachine
open FoundationCompactListedPackedBitTokenSynchronization

/-- A typed prefix codec into a flat stream of natural-number tokens. -/
class CompactAdditiveTokenCodec (α : Type*) [Primcodable α] where
  encode : α → List Nat
  decode : List Nat → Option (α × List Nat)
  decode_encode_append : ∀ value suffix,
    decode (encode value ++ suffix) = some (value, suffix)
  encode_primrec : Primrec encode
  decode_primrec : Primrec decode

def compactAdditiveEncode {α : Type*} [Primcodable α]
    [CompactAdditiveTokenCodec α] (value : α) : List Nat :=
  CompactAdditiveTokenCodec.encode value

def compactAdditiveDecode {α : Type*} [Primcodable α]
    [CompactAdditiveTokenCodec α] (tokens : List Nat) :
    Option (α × List Nat) :=
  CompactAdditiveTokenCodec.decode tokens

theorem compactAdditiveDecode_encode_append
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (value : α) (suffix : List Nat) :
    compactAdditiveDecode (compactAdditiveEncode value ++ suffix) =
      some (value, suffix) :=
  CompactAdditiveTokenCodec.decode_encode_append value suffix

theorem compactAdditiveEncode_primrec
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α] :
    Primrec (@compactAdditiveEncode α _ _) :=
  CompactAdditiveTokenCodec.encode_primrec

theorem compactAdditiveDecode_primrec
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α] :
    Primrec (@compactAdditiveDecode α _ _) :=
  CompactAdditiveTokenCodec.decode_primrec

/-- Bit length after each token is written with the existing self-delimiting
`binaryNatCode`. -/
def compactAdditiveTokenBitLength (tokens : List Nat) : Nat :=
  (tokens.flatMap binaryNatCode).length

@[simp] theorem compactAdditiveTokenBitLength_nil :
    compactAdditiveTokenBitLength [] = 0 := by
  simp [compactAdditiveTokenBitLength]

@[simp] theorem compactAdditiveTokenBitLength_cons
    (token : Nat) (tokens : List Nat) :
    compactAdditiveTokenBitLength (token :: tokens) =
      2 * Nat.size token + 2 + compactAdditiveTokenBitLength tokens := by
  simp [compactAdditiveTokenBitLength, binaryNatCode_length]

@[simp] theorem compactAdditiveTokenBitLength_append
    (left right : List Nat) :
    compactAdditiveTokenBitLength (left ++ right) =
      compactAdditiveTokenBitLength left +
        compactAdditiveTokenBitLength right := by
  simp [compactAdditiveTokenBitLength, List.flatMap_append]

def compactNatAdditiveEncode (value : Nat) : List Nat :=
  [value]

def compactNatAdditiveDecode (tokens : List Nat) :
    Option (Nat × List Nat) :=
  match tokens with
  | [] => none
  | value :: suffix => some (value, suffix)

theorem compactNatAdditiveDecode_encode_append
    (value : Nat) (suffix : List Nat) :
    compactNatAdditiveDecode
        (compactNatAdditiveEncode value ++ suffix) =
      some (value, suffix) := by
  rfl

theorem compactNatAdditiveEncode_primrec :
    Primrec compactNatAdditiveEncode := by
  exact Primrec.list_cons.comp Primrec.id (Primrec.const [])

theorem compactNatAdditiveDecode_primrec :
    Primrec compactNatAdditiveDecode := by
  have hcons : Primrec₂
      (fun (_tokens : List Nat) (headTail : Nat × List Nat) =>
        some (headTail.1, headTail.2)) :=
    Primrec.option_some.comp₂ Primrec₂.right
  exact
    (Primrec.list_casesOn
      (f := fun tokens : List Nat => tokens)
      (g := fun _tokens : List Nat => none)
      (h := fun _tokens headTail => some (headTail.1, headTail.2))
      Primrec.id (Primrec.const none) hcons).of_eq fun tokens => by
        cases tokens <;> rfl

instance compactNatAdditiveTokenCodec : CompactAdditiveTokenCodec Nat where
  encode := compactNatAdditiveEncode
  decode := compactNatAdditiveDecode
  decode_encode_append := compactNatAdditiveDecode_encode_append
  encode_primrec := compactNatAdditiveEncode_primrec
  decode_primrec := compactNatAdditiveDecode_primrec

@[simp] theorem compactAdditiveEncode_nat (value : Nat) :
    compactAdditiveEncode value = [value] :=
  rfl

@[simp] theorem compactAdditiveDecode_nat (tokens : List Nat) :
    compactAdditiveDecode (α := Nat) tokens =
      compactNatAdditiveDecode tokens :=
  rfl

@[simp] theorem compactAdditiveTokenBitLength_encode_nat (value : Nat) :
    compactAdditiveTokenBitLength (compactAdditiveEncode value) =
      2 * Nat.size value + 2 := by
  simp

def compactBoolAdditiveEncode (value : Bool) : List Nat :=
  [if value then 1 else 0]

def compactBoolAdditiveDecodeCons (headTail : Nat × List Nat) :
    Option (Bool × List Nat) :=
  if headTail.1 = 0 then
    some (false, headTail.2)
  else if headTail.1 = 1 then
    some (true, headTail.2)
  else
    none

def compactBoolAdditiveDecode (tokens : List Nat) :
    Option (Bool × List Nat) :=
  match tokens with
  | [] => none
  | tag :: suffix => compactBoolAdditiveDecodeCons (tag, suffix)

theorem compactBoolAdditiveDecode_encode_append
    (value : Bool) (suffix : List Nat) :
    compactBoolAdditiveDecode
        (compactBoolAdditiveEncode value ++ suffix) =
      some (value, suffix) := by
  cases value <;> rfl

theorem compactBoolAdditiveEncode_primrec :
    Primrec compactBoolAdditiveEncode := by
  have hvalue : Primrec (fun value : Bool =>
      if value then 1 else 0) :=
    Primrec.encode.of_eq fun value => by
      cases value <;> rfl
  exact Primrec.list_cons.comp hvalue (Primrec.const [])

theorem compactBoolAdditiveDecodeCons_primrec :
    Primrec compactBoolAdditiveDecodeCons := by
  have htag : Primrec (fun headTail : Nat × List Nat => headTail.1) :=
    Primrec.fst
  have hsuffix : Primrec (fun headTail : Nat × List Nat => headTail.2) :=
    Primrec.snd
  have htagZero : PrimrecPred (fun headTail : Nat × List Nat =>
      headTail.1 = 0) :=
    Primrec.eq.comp htag (Primrec.const 0)
  have htagOne : PrimrecPred (fun headTail : Nat × List Nat =>
      headTail.1 = 1) :=
    Primrec.eq.comp htag (Primrec.const 1)
  have hfalse : Primrec (fun headTail : Nat × List Nat =>
      some (false, headTail.2)) :=
    Primrec.option_some.comp <|
      Primrec.pair (Primrec.const false) hsuffix
  have htrue : Primrec (fun headTail : Nat × List Nat =>
      some (true, headTail.2)) :=
    Primrec.option_some.comp <|
      Primrec.pair (Primrec.const true) hsuffix
  exact
    (Primrec.ite htagZero hfalse
      (Primrec.ite htagOne htrue (Primrec.const none))).of_eq
        fun headTail => by
          simp [compactBoolAdditiveDecodeCons]

theorem compactBoolAdditiveDecode_primrec :
    Primrec compactBoolAdditiveDecode := by
  have hcons : Primrec₂
      (fun (_tokens : List Nat) (headTail : Nat × List Nat) =>
        compactBoolAdditiveDecodeCons headTail) :=
    compactBoolAdditiveDecodeCons_primrec.comp₂ Primrec₂.right
  exact
    (Primrec.list_casesOn
      (f := fun tokens : List Nat => tokens)
      (g := fun _tokens : List Nat => none)
      (h := fun _tokens headTail =>
        compactBoolAdditiveDecodeCons headTail)
      Primrec.id (Primrec.const none) hcons).of_eq fun tokens => by
        cases tokens <;> rfl

instance compactBoolAdditiveTokenCodec : CompactAdditiveTokenCodec Bool where
  encode := compactBoolAdditiveEncode
  decode := compactBoolAdditiveDecode
  decode_encode_append := compactBoolAdditiveDecode_encode_append
  encode_primrec := compactBoolAdditiveEncode_primrec
  decode_primrec := compactBoolAdditiveDecode_primrec

@[simp] theorem compactAdditiveEncode_bool (value : Bool) :
    compactAdditiveEncode value = [if value then 1 else 0] :=
  rfl

theorem compactAdditiveTokenBitLength_encode_bool_le (value : Bool) :
    compactAdditiveTokenBitLength (compactAdditiveEncode value) <= 4 := by
  cases value <;> decide

def compactOptionAdditiveEncode
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α] :
    Option α → List Nat
  | none => [0]
  | some value => 1 :: compactAdditiveEncode value

def compactOptionAdditiveDecodeCons
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (headTail : Nat × List Nat) : Option (Option α × List Nat) :=
  if headTail.1 = 0 then
    some (none, headTail.2)
  else if headTail.1 = 1 then
    (compactAdditiveDecode (α := α) headTail.2).map fun parsed =>
      (some parsed.1, parsed.2)
  else
    none

def compactOptionAdditiveDecode
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (tokens : List Nat) : Option (Option α × List Nat) :=
  match tokens with
  | [] => none
  | tag :: suffix => compactOptionAdditiveDecodeCons (α := α) (tag, suffix)

theorem compactOptionAdditiveDecode_encode_append
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (value : Option α) (suffix : List Nat) :
    compactOptionAdditiveDecode
        (compactOptionAdditiveEncode value ++ suffix) =
      some (value, suffix) := by
  cases value with
  | none => rfl
  | some value =>
      simp [compactOptionAdditiveEncode, compactOptionAdditiveDecode,
        compactOptionAdditiveDecodeCons,
        compactAdditiveDecode_encode_append]

theorem compactOptionAdditiveEncode_primrec
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α] :
    Primrec (@compactOptionAdditiveEncode α _ _) := by
  have hsome : Primrec₂
      (fun (_option : Option α) (value : α) =>
        1 :: compactAdditiveEncode value) :=
    Primrec.list_cons.comp₂ (Primrec₂.const 1)
      (compactAdditiveEncode_primrec.comp₂ Primrec₂.right)
  exact
    (Primrec.option_casesOn Primrec.id (Primrec.const [0]) hsome).of_eq
      fun value => by cases value <;> rfl

theorem compactOptionAdditiveDecodeCons_primrec
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α] :
    Primrec (@compactOptionAdditiveDecodeCons α _ _) := by
  let Input := Nat × List Nat
  have htag : Primrec (fun input : Input => input.1) := Primrec.fst
  have hsuffix : Primrec (fun input : Input => input.2) := Primrec.snd
  have htagZero : PrimrecPred (fun input : Input => input.1 = 0) :=
    Primrec.eq.comp htag (Primrec.const 0)
  have htagOne : PrimrecPred (fun input : Input => input.1 = 1) :=
    Primrec.eq.comp htag (Primrec.const 1)
  have hnone : Primrec (fun input : Input =>
      some ((none : Option α), input.2)) :=
    Primrec.option_some.comp <|
      Primrec.pair (Primrec.const none) hsuffix
  have hdecoded : Primrec (fun input : Input =>
      compactAdditiveDecode (α := α) input.2) :=
    compactAdditiveDecode_primrec.comp hsuffix
  have hwrapped : Primrec₂
      (fun (_input : Input) (parsed : α × List Nat) =>
        ((some parsed.1 : Option α), parsed.2)) :=
    Primrec₂.pair.comp₂
      (Primrec.option_some.comp₂
        (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  have hsome : Primrec (fun input : Input =>
      (compactAdditiveDecode (α := α) input.2).map fun parsed =>
        ((some parsed.1 : Option α), parsed.2)) :=
    Primrec.option_map hdecoded hwrapped
  exact
    (Primrec.ite htagZero hnone
      (Primrec.ite htagOne hsome (Primrec.const none))).of_eq
        fun input => by
          simp [compactOptionAdditiveDecodeCons]

theorem compactOptionAdditiveDecode_primrec
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α] :
    Primrec (@compactOptionAdditiveDecode α _ _) := by
  have hcons : Primrec₂
      (fun (_tokens : List Nat) (headTail : Nat × List Nat) =>
        compactOptionAdditiveDecodeCons (α := α) headTail) :=
    compactOptionAdditiveDecodeCons_primrec.comp₂ Primrec₂.right
  exact
    (Primrec.list_casesOn
      (f := fun tokens : List Nat => tokens)
      (g := fun _tokens : List Nat => none)
      (h := fun _tokens headTail =>
        compactOptionAdditiveDecodeCons (α := α) headTail)
      Primrec.id (Primrec.const none) hcons).of_eq fun tokens => by
        cases tokens <;> rfl

instance compactOptionAdditiveTokenCodec
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α] :
    CompactAdditiveTokenCodec (Option α) where
  encode := compactOptionAdditiveEncode
  decode := compactOptionAdditiveDecode
  decode_encode_append := compactOptionAdditiveDecode_encode_append
  encode_primrec := compactOptionAdditiveEncode_primrec
  decode_primrec := compactOptionAdditiveDecode_primrec

@[simp] theorem compactAdditiveEncode_option_none
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α] :
    compactAdditiveEncode (none : Option α) = [0] :=
  rfl

@[simp] theorem compactAdditiveEncode_option_some
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (value : α) :
    compactAdditiveEncode (some value) =
      1 :: compactAdditiveEncode value :=
  rfl

@[simp] theorem compactAdditiveTokenBitLength_encode_option_none
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α] :
    compactAdditiveTokenBitLength
        (compactAdditiveEncode (none : Option α)) = 2 := by
  simp

@[simp] theorem compactAdditiveTokenBitLength_encode_option_some
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (value : α) :
    compactAdditiveTokenBitLength (compactAdditiveEncode (some value)) =
      4 + compactAdditiveTokenBitLength (compactAdditiveEncode value) := by
  simp

def compactProdAdditiveEncode
    {α β : Type*} [Primcodable α] [Primcodable β]
    [CompactAdditiveTokenCodec α] [CompactAdditiveTokenCodec β]
    (value : α × β) : List Nat :=
  compactAdditiveEncode value.1 ++ compactAdditiveEncode value.2

def compactProdAdditiveDecodeAfter
    {α β : Type*} [Primcodable α] [Primcodable β]
    [CompactAdditiveTokenCodec α] [CompactAdditiveTokenCodec β]
    (first : α × List Nat) : Option ((α × β) × List Nat) :=
  (compactAdditiveDecode (α := β) first.2).map fun second =>
    ((first.1, second.1), second.2)

def compactProdAdditiveDecode
    {α β : Type*} [Primcodable α] [Primcodable β]
    [CompactAdditiveTokenCodec α] [CompactAdditiveTokenCodec β]
    (tokens : List Nat) : Option ((α × β) × List Nat) :=
  (compactAdditiveDecode (α := α) tokens).bind
    compactProdAdditiveDecodeAfter

theorem compactProdAdditiveDecode_encode_append
    {α β : Type*} [Primcodable α] [Primcodable β]
    [CompactAdditiveTokenCodec α] [CompactAdditiveTokenCodec β]
    (value : α × β) (suffix : List Nat) :
    compactProdAdditiveDecode
        (compactProdAdditiveEncode value ++ suffix) =
      some (value, suffix) := by
  rcases value with ⟨left, right⟩
  simp [compactProdAdditiveEncode, compactProdAdditiveDecode,
    compactProdAdditiveDecodeAfter, List.append_assoc,
    compactAdditiveDecode_encode_append]

theorem compactProdAdditiveEncode_primrec
    {α β : Type*} [Primcodable α] [Primcodable β]
    [CompactAdditiveTokenCodec α] [CompactAdditiveTokenCodec β] :
    Primrec (@compactProdAdditiveEncode α β _ _ _ _) := by
  exact Primrec.list_append.comp
    (compactAdditiveEncode_primrec.comp Primrec.fst)
    (compactAdditiveEncode_primrec.comp Primrec.snd)

theorem compactProdAdditiveDecodeAfter_primrec
    {α β : Type*} [Primcodable α] [Primcodable β]
    [CompactAdditiveTokenCodec α] [CompactAdditiveTokenCodec β] :
    Primrec (@compactProdAdditiveDecodeAfter α β _ _ _ _) := by
  let Input := α × List Nat
  have hdecoded : Primrec (fun input : Input =>
      compactAdditiveDecode (α := β) input.2) :=
    compactAdditiveDecode_primrec.comp Primrec.snd
  have hwrapped : Primrec₂
      (fun (input : Input) (second : β × List Nat) =>
        ((input.1, second.1), second.2)) :=
    Primrec₂.pair.comp₂
      (Primrec₂.pair.comp₂
        (Primrec.fst.comp₂ Primrec₂.left)
        (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.option_map hdecoded hwrapped).of_eq fun input => by
      rfl

theorem compactProdAdditiveDecode_primrec
    {α β : Type*} [Primcodable α] [Primcodable β]
    [CompactAdditiveTokenCodec α] [CompactAdditiveTokenCodec β] :
    Primrec (@compactProdAdditiveDecode α β _ _ _ _) := by
  have hfirst : Primrec (fun tokens : List Nat =>
      compactAdditiveDecode (α := α) tokens) :=
    compactAdditiveDecode_primrec
  have hafter : Primrec₂
      (fun (_tokens : List Nat) (first : α × List Nat) =>
        compactProdAdditiveDecodeAfter (β := β) first) :=
    compactProdAdditiveDecodeAfter_primrec.comp₂ Primrec₂.right
  exact
    (Primrec.option_bind hfirst hafter).of_eq fun tokens => by
      rfl

instance compactProdAdditiveTokenCodec
    {α β : Type*} [Primcodable α] [Primcodable β]
    [CompactAdditiveTokenCodec α] [CompactAdditiveTokenCodec β] :
    CompactAdditiveTokenCodec (α × β) where
  encode := compactProdAdditiveEncode
  decode := compactProdAdditiveDecode
  decode_encode_append := compactProdAdditiveDecode_encode_append
  encode_primrec := compactProdAdditiveEncode_primrec
  decode_primrec := compactProdAdditiveDecode_primrec

@[simp] theorem compactAdditiveEncode_prod
    {α β : Type*} [Primcodable α] [Primcodable β]
    [CompactAdditiveTokenCodec α] [CompactAdditiveTokenCodec β]
    (value : α × β) :
    compactAdditiveEncode value =
      compactAdditiveEncode value.1 ++ compactAdditiveEncode value.2 :=
  rfl

@[simp] theorem compactAdditiveTokenBitLength_encode_prod
    {α β : Type*} [Primcodable α] [Primcodable β]
    [CompactAdditiveTokenCodec α] [CompactAdditiveTokenCodec β]
    (value : α × β) :
    compactAdditiveTokenBitLength (compactAdditiveEncode value) =
      compactAdditiveTokenBitLength (compactAdditiveEncode value.1) +
        compactAdditiveTokenBitLength (compactAdditiveEncode value.2) := by
  simp

abbrev CompactAdditiveDecodeManyState (α : Type*) :=
  Option (List α × List Nat)

def compactAdditiveDecodeManyAdvance
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (current : List α × List Nat) : CompactAdditiveDecodeManyState α :=
  (compactAdditiveDecode (α := α) current.2).map fun parsed =>
    (parsed.1 :: current.1, parsed.2)

def compactAdditiveDecodeManyStep
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (state : CompactAdditiveDecodeManyState α) :
    CompactAdditiveDecodeManyState α :=
  state.bind compactAdditiveDecodeManyAdvance

def compactAdditiveDecodeMany
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (count : Nat) (tokens : List Nat) : Option (List α × List Nat) :=
  let final :=
    (compactAdditiveDecodeManyStep (α := α)^[count])
      (some ([], tokens))
  final.map fun current => (current.1.reverse, current.2)

theorem compactAdditiveDecodeManyAdvance_primrec
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α] :
    Primrec (@compactAdditiveDecodeManyAdvance α _ _) := by
  let Input := List α × List Nat
  have hdecoded : Primrec (fun input : Input =>
      compactAdditiveDecode (α := α) input.2) :=
    compactAdditiveDecode_primrec.comp Primrec.snd
  have hnext : Primrec₂
      (fun (input : Input) (parsed : α × List Nat) =>
        (parsed.1 :: input.1, parsed.2)) :=
    Primrec₂.pair.comp₂
      (Primrec.list_cons.comp₂
        (Primrec.fst.comp₂ Primrec₂.right)
        (Primrec.fst.comp₂ Primrec₂.left))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.option_map hdecoded hnext).of_eq fun input => by
      rfl

theorem compactAdditiveDecodeManyStep_primrec
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α] :
    Primrec (@compactAdditiveDecodeManyStep α _ _) := by
  exact Primrec.option_bind₁ compactAdditiveDecodeManyAdvance_primrec

theorem compactAdditiveDecodeMany_primrec
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α] :
    Primrec₂ (@compactAdditiveDecodeMany α _ _) := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  have hcount : Primrec (fun input : Input => input.1) := Primrec.fst
  have hinitial : Primrec (fun input : Input =>
      (some ([], input.2) : CompactAdditiveDecodeManyState α)) :=
    Primrec.option_some.comp <|
      Primrec.pair (Primrec.const []) Primrec.snd
  have hstep : Primrec₂
      (fun (_input : Input) (state : CompactAdditiveDecodeManyState α) =>
        compactAdditiveDecodeManyStep state) :=
    compactAdditiveDecodeManyStep_primrec.comp₂ Primrec₂.right
  have hfinal : Primrec (fun input : Input =>
      (compactAdditiveDecodeManyStep (α := α)^[input.1])
        (some ([], input.2))) :=
    Primrec.nat_iterate hcount hinitial hstep
  have houtput : Primrec₂
      (fun (_input : Input) (current : List α × List Nat) =>
        (current.1.reverse, current.2)) :=
    Primrec₂.pair.comp₂
      (Primrec.list_reverse.comp₂
        (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.option_map hfinal houtput).of_eq fun input => by
      rfl

theorem compactAdditiveDecodeManyStep_encode_head
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (accumulator : List α) (value : α) (suffix : List Nat) :
    compactAdditiveDecodeManyStep
        (some (accumulator,
          compactAdditiveEncode value ++ suffix)) =
      some (value :: accumulator, suffix) := by
  simp [compactAdditiveDecodeManyStep,
    compactAdditiveDecodeManyAdvance,
    compactAdditiveDecode_encode_append]

theorem compactAdditiveDecodeMany_run_encode_append
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (values accumulator : List α) (suffix : List Nat) :
    (compactAdditiveDecodeManyStep (α := α)^[values.length])
        (some (accumulator,
          values.flatMap compactAdditiveEncode ++ suffix)) =
      some (values.reverse ++ accumulator, suffix) := by
  induction values generalizing accumulator with
  | nil => simp
  | cons value values ih =>
      simp only [List.length_cons, List.flatMap_cons]
      rw [Function.iterate_succ_apply]
      rw [List.append_assoc]
      rw [compactAdditiveDecodeManyStep_encode_head]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem compactAdditiveDecodeMany_encode_append
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (values : List α) (suffix : List Nat) :
    compactAdditiveDecodeMany values.length
        (values.flatMap compactAdditiveEncode ++ suffix) =
      some (values, suffix) := by
  simp [compactAdditiveDecodeMany,
    compactAdditiveDecodeMany_run_encode_append]

def compactListAdditiveEncode
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (values : List α) : List Nat :=
  values.length :: values.flatMap compactAdditiveEncode

def compactListAdditiveDecode
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (tokens : List Nat) : Option (List α × List Nat) :=
  match tokens with
  | [] => none
  | count :: suffix => compactAdditiveDecodeMany count suffix

theorem compactListAdditiveDecode_encode_append
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (values : List α) (suffix : List Nat) :
    compactListAdditiveDecode
        (compactListAdditiveEncode values ++ suffix) =
      some (values, suffix) := by
  simp [compactListAdditiveEncode, compactListAdditiveDecode,
    compactAdditiveDecodeMany_encode_append]

theorem compactListAdditiveEncode_primrec
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α] :
    Primrec (@compactListAdditiveEncode α _ _) := by
  have hpayload : Primrec (fun values : List α =>
      values.flatMap compactAdditiveEncode) :=
    Primrec.list_flatMap Primrec.id
      (compactAdditiveEncode_primrec.comp₂ Primrec₂.right)
  exact Primrec.list_cons.comp Primrec.list_length hpayload

theorem compactListAdditiveDecode_primrec
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α] :
    Primrec (@compactListAdditiveDecode α _ _) := by
  have hcons : Primrec₂
      (fun (_tokens : List Nat) (headTail : Nat × List Nat) =>
        compactAdditiveDecodeMany (α := α) headTail.1 headTail.2) :=
    compactAdditiveDecodeMany_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_casesOn
      (f := fun tokens : List Nat => tokens)
      (g := fun _tokens : List Nat => none)
      (h := fun _tokens headTail =>
        compactAdditiveDecodeMany (α := α) headTail.1 headTail.2)
      Primrec.id (Primrec.const none) hcons).of_eq fun tokens => by
        cases tokens <;> rfl

instance compactListAdditiveTokenCodec
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α] :
    CompactAdditiveTokenCodec (List α) where
  encode := compactListAdditiveEncode
  decode := compactListAdditiveDecode
  decode_encode_append := compactListAdditiveDecode_encode_append
  encode_primrec := compactListAdditiveEncode_primrec
  decode_primrec := compactListAdditiveDecode_primrec

@[simp] theorem compactAdditiveEncode_list
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (values : List α) :
    compactAdditiveEncode values =
      values.length :: values.flatMap compactAdditiveEncode :=
  rfl

theorem compactAdditiveTokenBitLength_flatMap_encode
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (values : List α) :
    compactAdditiveTokenBitLength
        (values.flatMap compactAdditiveEncode) =
      (values.map fun value =>
        compactAdditiveTokenBitLength
          (compactAdditiveEncode value)).sum := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp [ih]

@[simp] theorem compactAdditiveTokenBitLength_encode_list
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (values : List α) :
    compactAdditiveTokenBitLength (compactAdditiveEncode values) =
      2 * Nat.size values.length + 2 +
        (values.map fun value =>
          compactAdditiveTokenBitLength
            (compactAdditiveEncode value)).sum := by
  simp [compactAdditiveTokenBitLength_flatMap_encode]

def compactAdditivePackedBits (tokens : List Nat) : List Bool :=
  tokens.flatMap binaryNatCode

def compactAdditivePackedCode (tokens : List Nat) : Nat :=
  packBinaryString (compactAdditivePackedBits tokens)

theorem binaryNatCode_primrec : Primrec binaryNatCode := by
  have hbitPair : Primrec₂
      (fun (_value : Nat) (bit : Bool) => [true, bit]) :=
    Primrec.list_cons.comp₂ (Primrec₂.const true)
      (Primrec.list_cons.comp₂ Primrec₂.right (Primrec₂.const []))
  have hpairs : Primrec (fun value : Nat =>
      value.bits.flatMap fun bit => [true, bit]) :=
    Primrec.list_flatMap natBits_primrec hbitPair
  exact
    (Primrec.list_append.comp hpairs (Primrec.const [false, false])).of_eq
      fun value => by
        rfl

theorem packBinaryString_primrec : Primrec packBinaryString := by
  have hstep : Primrec₂
      (fun (_bits : List Bool) (bitCode : Bool × Nat) =>
        Nat.bit bitCode.1 bitCode.2) :=
    natBit_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldr Primrec.id (Primrec.const 1) hstep).of_eq
      fun bits => by
        induction bits with
        | nil => rfl
        | cons bit bits ih =>
            change Nat.bit bit
                (List.foldr (fun bit state => Nat.bit bit state) 1 bits) =
              Nat.bit bit (packBinaryString bits)
            exact congrArg (Nat.bit bit) ih

theorem compactAdditivePackedBits_primrec :
    Primrec compactAdditivePackedBits := by
  exact Primrec.list_flatMap Primrec.id
    (binaryNatCode_primrec.comp₂ Primrec₂.right)

theorem compactAdditivePackedCode_primrec :
    Primrec compactAdditivePackedCode :=
  packBinaryString_primrec.comp compactAdditivePackedBits_primrec

@[simp] theorem compactAdditivePackedCode_size (tokens : List Nat) :
    Nat.size (compactAdditivePackedCode tokens) =
      compactAdditiveTokenBitLength tokens + 1 := by
  simp [compactAdditivePackedCode, compactAdditivePackedBits,
    compactAdditiveTokenBitLength]

theorem compactPackedTokenStream_additivePackedCode
    (tokens : List Nat) :
    compactPackedTokenStream (compactAdditivePackedCode tokens) =
      some tokens := by
  simp [compactAdditivePackedCode, compactAdditivePackedBits,
    compactPackedTokenStream, packedPayloadBits_packBinaryString,
    binaryNatStreamTokens_eq_decodeBinaryNatStream,
    decodeBinaryNatStream_flatMap_binaryNatCode]

#print axioms compactNatAdditiveDecode_encode_append
#print axioms compactNatAdditiveEncode_primrec
#print axioms compactNatAdditiveDecode_primrec
#print axioms compactAdditiveTokenBitLength_encode_nat
#print axioms compactBoolAdditiveDecode_encode_append
#print axioms compactBoolAdditiveEncode_primrec
#print axioms compactBoolAdditiveDecode_primrec
#print axioms compactAdditiveTokenBitLength_encode_bool_le
#print axioms compactOptionAdditiveDecode_encode_append
#print axioms compactOptionAdditiveEncode_primrec
#print axioms compactOptionAdditiveDecode_primrec
#print axioms compactAdditiveTokenBitLength_encode_option_some
#print axioms compactProdAdditiveDecode_encode_append
#print axioms compactProdAdditiveEncode_primrec
#print axioms compactProdAdditiveDecode_primrec
#print axioms compactAdditiveTokenBitLength_encode_prod
#print axioms compactAdditiveDecodeMany_primrec
#print axioms compactAdditiveDecodeMany_encode_append
#print axioms compactListAdditiveDecode_encode_append
#print axioms compactListAdditiveEncode_primrec
#print axioms compactListAdditiveDecode_primrec
#print axioms compactAdditiveTokenBitLength_encode_list
#print axioms binaryNatCode_primrec
#print axioms packBinaryString_primrec
#print axioms compactAdditivePackedCode_primrec
#print axioms compactAdditivePackedCode_size
#print axioms compactPackedTokenStream_additivePackedCode

end FoundationCompactAdditiveTokenCodec
