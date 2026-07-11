import integration.FoundationCompactListedGuardedAxiomCost
import Mathlib.Computability.Primrec.List

/-!
# Primitive-recursive input layer for the guarded listed verifier

The public verifier receives two sentinel-terminated binary strings packed as
natural numbers.  This file fixes that exact input coordinate at the arithmetic
layer: `Nat.bits` is proved primitive recursive, and peeling the terminal
sentinel is proved primitive recursive and inverse to the existing
`packBinaryString` encoder.  No proof-system or growth assumption enters here.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

namespace FoundationCompactListedVerifierArithmeticInput

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactVerifierBitCostPrimitives

/-- Strong-recursion step for the little-endian binary expansion of a natural.
The list of previous values has length `n` and contains the binary expansions
at all smaller inputs. -/
def natBitsStrongStep
    (_ : Nat) (previous : List (List Bool)) : Option (List Bool) :=
  let n := previous.length
  if n = 0 then
    some []
  else
    previous[n.div2]?.map fun tail => n.bodd :: tail

theorem natBitsStrongStep_primrec : Primrec₂ natBitsStrongStep := by
  apply Primrec₂.mk
  let Input := Nat × List (List Bool)
  have hprevious : Primrec (fun input : Input => input.2) :=
    Primrec.snd
  have hn : Primrec (fun input : Input => input.2.length) :=
    Primrec.list_length.comp hprevious
  have hzero : PrimrecPred (fun input : Input => input.2.length = 0) :=
    Primrec.eq.comp hn (Primrec.const 0)
  have hindex : Primrec (fun input : Input => input.2.length.div2) :=
    Primrec.nat_div2.comp hn
  have htail : Primrec (fun input : Input =>
      input.2[input.2.length.div2]?) :=
    Primrec.list_getElem?.comp hprevious hindex
  have hbodd : Primrec (fun input : Input => input.2.length.bodd) :=
    Primrec.nat_bodd.comp hn
  have hcons : Primrec₂ (fun (input : Input) (tail : List Bool) =>
      input.2.length.bodd :: tail) :=
    Primrec.list_cons.comp₂
      ((hbodd.comp Primrec.fst).to₂)
      Primrec₂.right
  have hnext : Primrec (fun input : Input =>
      input.2[input.2.length.div2]?.map fun tail =>
        input.2.length.bodd :: tail) :=
    Primrec.option_map htail hcons
  exact
    (Primrec.ite hzero (Primrec.const (some [])) hnext).of_eq
      fun input => by
        simp only [natBitsStrongStep]

theorem natBits_ne_nil_of_ne_zero {n : Nat} (hn : Not (n = 0)) :
    Not (n.bits = []) := by
  intro hbits
  apply hn
  apply natBits_injective
  simpa using hbits

theorem natBits_cons_div2 (n : Nat) (hn : Not (n = 0)) :
    n.bits = n.bodd :: n.div2.bits := by
  rw [Nat.bodd_eq_bits_head, Nat.div2_bits_eq_tail]
  exact (List.cons_head!_tail (natBits_ne_nil_of_ne_zero hn)).symm

theorem natBits_primrec : Primrec Nat.bits := by
  let f : Nat -> Nat -> List Bool := fun _ n => n.bits
  have hf : Primrec₂ f := by
    apply Primrec.nat_strong_rec f natBitsStrongStep_primrec
    intro dummy n
    by_cases hn : n = 0
    · subst n
      simp [natBitsStrongStep, f]
    · have hdiv : n.div2 < n := by
        simpa [Nat.div2] using
          (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega : 1 < 2))
      let previous : List (List Bool) :=
        List.map (fun k => k.bits) (List.range n)
      have hlookup :
          previous[n.div2]? = some n.div2.bits := by
        dsimp only [previous]
        rw [List.getElem?_map, List.getElem?_range hdiv]
        rfl
      change natBitsStrongStep dummy previous = some n.bits
      simp only [natBitsStrongStep, previous, List.length_map,
        List.length_range, hn, ↓reduceIte, hlookup, Option.map_some]
      exact congrArg some (natBits_cons_div2 n hn).symm
  exact (hf.comp (Primrec.const 0) Primrec.id).of_eq fun _ => rfl

/-- Primitive-recursive implementation of `List.dropLast`, expressed through
operations already covered by Mathlib's primitive-recursion library. -/
def primitiveDropLast {alpha : Type*} (values : List alpha) : List alpha :=
  values.reverse.tail.reverse

theorem primitiveDropLast_eq_dropLast {alpha : Type*}
    (values : List alpha) :
    primitiveDropLast values = values.dropLast := by
  induction values using List.reverseRecOn with
  | nil => simp [primitiveDropLast]
  | append_singleton values value =>
      simp [primitiveDropLast]

theorem primitiveDropLast_primrec {alpha : Type*} [Primcodable alpha] :
    Primrec (@primitiveDropLast alpha) := by
  exact Primrec.list_reverse.comp
    (Primrec.list_tail.comp Primrec.list_reverse)

theorem listDropLast_primrec {alpha : Type*} [Primcodable alpha] :
    Primrec (@List.dropLast alpha) := by
  exact primitiveDropLast_primrec.of_eq primitiveDropLast_eq_dropLast

theorem listGetLast?_primrec {alpha : Type*} [Primcodable alpha] :
    Primrec (@List.getLast? alpha) := by
  exact
    (Primrec.list_head?.comp Primrec.list_reverse).of_eq fun values =>
      List.getLast?_eq_head?_reverse.symm

/-- The exact sentinel check and payload peel used by both packed public
decoders, written without any typed syntax object. -/
def packedPayloadBits (code : Nat) : Option (List Bool) :=
  if code.bits.getLast? = some true then
    some code.bits.dropLast
  else
    none

theorem packedPayloadBits_primrec : Primrec packedPayloadBits := by
  have hlast : Primrec (fun code : Nat => code.bits.getLast?) :=
    listGetLast?_primrec.comp natBits_primrec
  have hsentinel : PrimrecPred (fun code : Nat =>
      code.bits.getLast? = some true) :=
    Primrec.eq.comp hlast (Primrec.const (some true))
  have hpayload : Primrec (fun code : Nat =>
      some code.bits.dropLast) :=
    Primrec.option_some.comp (listDropLast_primrec.comp natBits_primrec)
  exact
    (Primrec.ite hsentinel hpayload (Primrec.const none)).of_eq
      fun code => by simp only [packedPayloadBits]

theorem packedPayloadBits_packBinaryString (bits : List Bool) :
    packedPayloadBits (packBinaryString bits) = some bits := by
  simp [packedPayloadBits]

theorem packedPayloadBits_eq_some_iff
    (code : Nat) (payload : List Bool) :
    packedPayloadBits code = some payload <->
      packBinaryString payload = code := by
  constructor
  · intro hpeel
    by_cases hlast : code.bits.getLast? = some true
    · simp only [packedPayloadBits, hlast, if_pos] at hpeel
      have hpayload : code.bits.dropLast = payload := Option.some.inj hpeel
      have hbits : payload ++ [true] = code.bits := by
        rw [<- hpayload]
        exact List.dropLast_append_getLast? true (by simpa [hlast])
      apply natBits_injective
      simpa [hbits]
    · simp [packedPayloadBits, hlast] at hpeel
  · intro hpack
    subst code
    exact packedPayloadBits_packBinaryString payload

theorem packedPayloadTrace_result_eq_packedPayloadBits (code : Nat) :
    (FoundationCompactListedCertifiedDecoderCost.packedPayloadTrace code).1 =
      packedPayloadBits code := by
  simp [FoundationCompactListedCertifiedDecoderCost.packedPayloadTrace_result,
    packedPayloadBits]

/-! ## Primitive-recursive natural-prefix decoder -/

abbrev BinaryNatDecodeResult := Option (Nat × List Bool)

/-- A right-fold state stores the raw suffix, the decoder result at that
suffix, and the decoder result one position farther right.  The third field is
exactly what the escaped `true :: bit` branch needs. -/
abbrev BinaryNatDecodeFoldState :=
  List Bool × BinaryNatDecodeResult × BinaryNatDecodeResult

def binaryNatDecodeFalseBranch
    (state : BinaryNatDecodeFoldState) : BinaryNatDecodeFoldState :=
  let tail := state.1
  let decoded :=
    if tail.head? = some false then
      some (0, tail.tail)
    else
      none
  (false :: tail, decoded, state.2.1)

def binaryNatDecodeTrueBranch
    (state : BinaryNatDecodeFoldState) : BinaryNatDecodeFoldState :=
  let tail := state.1
  let decoded := tail.head?.bind fun payloadBit =>
    state.2.2.map fun result =>
      (Nat.bit payloadBit result.1, result.2)
  (true :: tail, decoded, state.2.1)

def binaryNatDecodeFoldStep
    (bit : Bool) (state : BinaryNatDecodeFoldState) :
    BinaryNatDecodeFoldState :=
  bif bit then
    binaryNatDecodeTrueBranch state
  else
    binaryNatDecodeFalseBranch state

def binaryNatDecodeInitialState : BinaryNatDecodeFoldState :=
  ([], none, none)

def primitiveDecodeBinaryNat (bits : List Bool) : BinaryNatDecodeResult :=
  (bits.foldr binaryNatDecodeFoldStep binaryNatDecodeInitialState).2.1

theorem natBit_primrec : Primrec₂ Nat.bit := by
  apply Primrec₂.mk
  have hdouble : Primrec (fun input : Bool × Nat => 2 * input.2) :=
    Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd
  exact
    (Primrec.cond Primrec.fst (Primrec.succ.comp hdouble) hdouble).of_eq
      fun input => by cases input.1 <;> simp [Nat.bit]

theorem binaryNatDecodeFalseBranch_primrec :
    Primrec binaryNatDecodeFalseBranch := by
  have htail : Primrec (fun state : BinaryNatDecodeFoldState => state.1) :=
    Primrec.fst
  have hdecodedTail : Primrec
      (fun state : BinaryNatDecodeFoldState => state.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hhead : Primrec
      (fun state : BinaryNatDecodeFoldState => state.1.head?) :=
    Primrec.list_head?.comp htail
  have hcondition : PrimrecPred
      (fun state : BinaryNatDecodeFoldState =>
        state.1.head? = some false) :=
    Primrec.eq.comp hhead (Primrec.const (some false))
  have hrest : Primrec
      (fun state : BinaryNatDecodeFoldState => state.1.tail) :=
    Primrec.list_tail.comp htail
  have hsuccess : Primrec
      (fun state : BinaryNatDecodeFoldState =>
        some (0, state.1.tail)) :=
    Primrec.option_some.comp
      (Primrec.pair (Primrec.const 0) hrest)
  have hdecoded : Primrec
      (fun state : BinaryNatDecodeFoldState =>
        if state.1.head? = some false then
          some (0, state.1.tail)
        else
          none) :=
    Primrec.ite hcondition hsuccess (Primrec.const none)
  have hprefixed : Primrec
      (fun state : BinaryNatDecodeFoldState => false :: state.1) :=
    Primrec.list_cons.comp (Primrec.const false) htail
  exact
    (Primrec.pair hprefixed (Primrec.pair hdecoded hdecodedTail)).of_eq
      fun state => by simp [binaryNatDecodeFalseBranch]

theorem binaryNatDecodeTrueBranch_primrec :
    Primrec binaryNatDecodeTrueBranch := by
  have htail : Primrec (fun state : BinaryNatDecodeFoldState => state.1) :=
    Primrec.fst
  have hdecodedTail : Primrec
      (fun state : BinaryNatDecodeFoldState => state.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hdecodedTailTail : Primrec
      (fun state : BinaryNatDecodeFoldState => state.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hhead : Primrec
      (fun state : BinaryNatDecodeFoldState => state.1.head?) :=
    Primrec.list_head?.comp htail
  have hresult : Primrec₂
      (fun (input : BinaryNatDecodeFoldState × Bool)
          (result : Nat × List Bool) =>
        (Nat.bit input.2 result.1, result.2)) := by
    have hbit : Primrec₂
        (fun (input : BinaryNatDecodeFoldState × Bool)
            (result : Nat × List Bool) =>
          Nat.bit input.2 result.1) :=
      natBit_primrec.comp₂
        (Primrec.snd.comp Primrec.fst).to₂
        (Primrec.fst.comp Primrec.snd).to₂
    exact Primrec₂.pair.comp₂ hbit
      (Primrec.snd.comp Primrec.snd).to₂
  have hmapped : Primrec
      (fun input : BinaryNatDecodeFoldState × Bool =>
        input.1.2.2.map fun result =>
          (Nat.bit input.2 result.1, result.2)) :=
    Primrec.option_map
      (hdecodedTailTail.comp Primrec.fst) hresult
  have hdecoded : Primrec
      (fun state : BinaryNatDecodeFoldState =>
        state.1.head?.bind fun payloadBit =>
          state.2.2.map fun result =>
            (Nat.bit payloadBit result.1, result.2)) :=
    Primrec.option_bind hhead
      ((hmapped.comp
        (Primrec.pair Primrec.fst Primrec.snd)).to₂)
  have hprefixed : Primrec
      (fun state : BinaryNatDecodeFoldState => true :: state.1) :=
    Primrec.list_cons.comp (Primrec.const true) htail
  exact
    (Primrec.pair hprefixed (Primrec.pair hdecoded hdecodedTail)).of_eq
      fun state => by simp [binaryNatDecodeTrueBranch]

theorem binaryNatDecodeFoldStep_primrec :
    Primrec₂ binaryNatDecodeFoldStep := by
  apply Primrec₂.mk
  exact
    (Primrec.cond Primrec.fst
      (binaryNatDecodeTrueBranch_primrec.comp Primrec.snd)
      (binaryNatDecodeFalseBranch_primrec.comp Primrec.snd)).of_eq
      fun input => by cases input.1 <;> rfl

theorem primitiveDecodeBinaryNat_primrec :
    Primrec primitiveDecodeBinaryNat := by
  have hstep : Primrec
      (fun input : Bool × BinaryNatDecodeFoldState =>
        binaryNatDecodeFoldStep input.1 input.2) :=
    binaryNatDecodeFoldStep_primrec
  have hfold : Primrec (fun bits : List Bool =>
      bits.foldr binaryNatDecodeFoldStep binaryNatDecodeInitialState) :=
    Primrec.list_foldr Primrec.id
      (Primrec.const binaryNatDecodeInitialState)
      ((hstep.comp Primrec.snd).to₂)
  exact
    ((Primrec.fst.comp Primrec.snd).comp hfold).of_eq
      fun bits => by rfl

theorem binaryNatDecodeFold_invariant (bits : List Bool) :
    bits.foldr binaryNatDecodeFoldStep binaryNatDecodeInitialState =
      (bits, decodeBinaryNat bits, decodeBinaryNat bits.tail) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      rw [List.foldr_cons, ih]
      cases bit <;> cases bits with
      | nil => rfl
      | cons second rest =>
          cases second <;>
            simp [binaryNatDecodeFoldStep,
              binaryNatDecodeFalseBranch,
              binaryNatDecodeTrueBranch, decodeBinaryNat,
              Option.map_eq_bind]

theorem primitiveDecodeBinaryNat_eq_decodeBinaryNat (bits : List Bool) :
    primitiveDecodeBinaryNat bits = decodeBinaryNat bits := by
  rw [primitiveDecodeBinaryNat, binaryNatDecodeFold_invariant]

theorem decodeBinaryNat_primrec : Primrec decodeBinaryNat := by
  exact primitiveDecodeBinaryNat_primrec.of_eq
    primitiveDecodeBinaryNat_eq_decodeBinaryNat

#print axioms natBits_primrec
#print axioms packedPayloadBits_primrec
#print axioms packedPayloadBits_eq_some_iff
#print axioms packedPayloadTrace_result_eq_packedPayloadBits
#print axioms decodeBinaryNat_primrec
#print axioms primitiveDecodeBinaryNat_eq_decodeBinaryNat

end FoundationCompactListedVerifierArithmeticInput
