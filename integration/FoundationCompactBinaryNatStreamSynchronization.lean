import integration.FoundationCompactBinaryNatStreamMachine
import integration.FoundationCompactVerifierStructuralBound

/-!
# Exact synchronization of binary-natural bits and natural tokens

`decodeBinaryNat` accepts noncanonical encodings with redundant high zero
bits.  Consequently, a successful bit stream must not be identified with the
canonical re-encoding of its token list.  The relation below records the exact
bit suffix after each decoded natural.  It is the invariant needed to connect
the bit-level typed decoders to the primitive-recursive token machines without
assuming canonical input.
-/

namespace FoundationCompactBinaryNatStreamSynchronization

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNatStreamMachine
open FoundationCompactVerifierStructuralBound

/-- `BinaryNatTokensDecode tokens bits suffix` says that repeated uses of the
actual project decoder read exactly `tokens` from `bits` and leave exactly
`suffix`.  No canonicity condition is imposed on the consumed bits. -/
inductive BinaryNatTokensDecode :
    List Nat -> List Bool -> List Bool -> Prop
  | nil (suffix : List Bool) :
      BinaryNatTokensDecode [] suffix suffix
  | cons {token : Nat} {tokens : List Nat}
      {bits middle suffix : List Bool}
      (head : decodeBinaryNat bits = some (token, middle))
      (tail : BinaryNatTokensDecode tokens middle suffix) :
      BinaryNatTokensDecode (token :: tokens) bits suffix

theorem binaryNatTokensDecode_append
    {left right : List Nat} {bits middle suffix : List Bool}
    (hleft : BinaryNatTokensDecode left bits middle)
    (hright : BinaryNatTokensDecode right middle suffix) :
    BinaryNatTokensDecode (left ++ right) bits suffix := by
  induction hleft with
  | nil => simpa using hright
  | cons hhead _ ih =>
      exact .cons hhead (ih hright)

theorem binaryNatTokensDecode_split_append
    (left right : List Nat) {bits suffix : List Bool}
    (hdecode : BinaryNatTokensDecode (left ++ right) bits suffix) :
    exists middle,
      BinaryNatTokensDecode left bits middle /\
        BinaryNatTokensDecode right middle suffix := by
  induction left generalizing bits with
  | nil =>
      exact ⟨bits, .nil bits, by simpa using hdecode⟩
  | cons token left ih =>
      cases hdecode with
      | cons hhead htail =>
          obtain ⟨middle, hleft, hright⟩ := ih htail
          exact ⟨middle, .cons hhead hleft, hright⟩

theorem binaryNatTokensDecode_append_iff
    (left right : List Nat) (bits suffix : List Bool) :
    BinaryNatTokensDecode (left ++ right) bits suffix <->
      exists middle,
        BinaryNatTokensDecode left bits middle /\
          BinaryNatTokensDecode right middle suffix := by
  constructor
  · exact binaryNatTokensDecode_split_append left right
  · rintro ⟨middle, hleft, hright⟩
    exact binaryNatTokensDecode_append hleft hright

theorem binaryNatTokensDecode_deterministic
    {tokens : List Nat} {bits suffix₁ suffix₂ : List Bool}
    (h₁ : BinaryNatTokensDecode tokens bits suffix₁)
    (h₂ : BinaryNatTokensDecode tokens bits suffix₂) :
    suffix₁ = suffix₂ := by
  induction h₁ generalizing suffix₂ with
  | nil =>
      cases h₂
      rfl
  | cons hhead _ ih =>
      cases h₂ with
      | cons hhead₂ htail₂ =>
          rw [hhead] at hhead₂
          cases hhead₂
          exact ih htail₂

theorem binaryNatTokensDecode_length
    {tokens : List Nat} {bits suffix : List Bool}
    (hdecode : BinaryNatTokensDecode tokens bits suffix) :
    tokens.length + suffix.length <= bits.length := by
  induction hdecode with
  | nil => simp
  | cons hhead _ ih =>
      have hconsumed := decodeBinaryNat_consumes_two hhead
      simp only [List.length_cons]
      omega

theorem binaryNatTokensDecode_canonical_append
    (tokens : List Nat) (suffix : List Bool) :
    BinaryNatTokensDecode tokens
      (tokens.flatMap binaryNatCode ++ suffix) suffix := by
  induction tokens with
  | nil => simp only [List.flatMap_nil, List.nil_append]
           exact .nil suffix
  | cons token tokens ih =>
      simp only [List.flatMap_cons, List.append_assoc]
      exact .cons
        (decodeBinaryNat_binaryNatCode_append token
          (tokens.flatMap binaryNatCode ++ suffix)) ih

theorem decodeBinaryNatStreamFuel_sound
    {fuel : Nat} {bits : List Bool} {tokens : List Nat}
    (hdecode : decodeBinaryNatStreamFuel fuel bits = some tokens) :
    BinaryNatTokensDecode tokens bits [] := by
  induction fuel generalizing bits tokens with
  | zero => simp [decodeBinaryNatStreamFuel] at hdecode
  | succ fuel ih =>
      cases bits with
      | nil =>
          simp [decodeBinaryNatStreamFuel] at hdecode
          subst tokens
          exact .nil []
      | cons bit bits =>
          cases hhead : decodeBinaryNat (bit :: bits) with
          | none =>
              simp [decodeBinaryNatStreamFuel, hhead] at hdecode
          | some result =>
              rcases result with ⟨token, suffix⟩
              cases htail : decodeBinaryNatStreamFuel fuel suffix with
              | none =>
                  simp [decodeBinaryNatStreamFuel, hhead, htail] at hdecode
              | some tailTokens =>
                  simp [decodeBinaryNatStreamFuel, hhead, htail] at hdecode
                  subst tokens
                  exact .cons hhead (ih htail)

theorem decodeBinaryNatStreamFuel_complete
    {fuel : Nat} {tokens : List Nat} {bits : List Bool}
    (hdecode : BinaryNatTokensDecode tokens bits [])
    (hfuel : tokens.length < fuel) :
    decodeBinaryNatStreamFuel fuel bits = some tokens := by
  induction tokens generalizing bits fuel with
  | nil =>
      cases hdecode
      cases fuel <;> simp_all [decodeBinaryNatStreamFuel]
  | cons token tokens ih =>
      cases hdecode with
      | cons hhead htail =>
          cases fuel with
          | zero => simp at hfuel
          | succ fuel =>
              have hbits : bits ≠ [] := by
                intro hempty
                subst bits
                simp [decodeBinaryNat] at hhead
              rw [decodeBinaryNatStreamFuel_succ_of_decode
                fuel bits token _ hbits hhead]
              have htailFuel : tokens.length < fuel := by
                simpa using hfuel
              rw [ih htail htailFuel]
              rfl

theorem decodeBinaryNatStream_success_iff
    (bits : List Bool) (tokens : List Nat) :
    decodeBinaryNatStream bits = some tokens <->
      BinaryNatTokensDecode tokens bits [] := by
  constructor
  · intro hdecode
    exact decodeBinaryNatStreamFuel_sound hdecode
  · intro hdecode
    unfold decodeBinaryNatStream
    apply decodeBinaryNatStreamFuel_complete hdecode
    have hlength := binaryNatTokensDecode_length hdecode
    omega

/-- A full successful tokenization has a real bit boundary at every token-list
split, even when some naturals use noncanonical bit encodings. -/
theorem decodeBinaryNatStream_split_append
    (bits : List Bool) (leading trailing : List Nat)
    (hdecode : decodeBinaryNatStream bits = some (leading ++ trailing)) :
    exists middleBits,
      BinaryNatTokensDecode leading bits middleBits /\
        decodeBinaryNatStream middleBits = some trailing := by
  have hall := (decodeBinaryNatStream_success_iff
    bits (leading ++ trailing)).1 hdecode
  obtain ⟨middleBits, hleading, htrailing⟩ :=
    binaryNatTokensDecode_split_append leading trailing hall
  exact ⟨middleBits, hleading,
    (decodeBinaryNatStream_success_iff middleBits trailing).2 htrailing⟩

#print axioms binaryNatTokensDecode_append_iff
#print axioms binaryNatTokensDecode_deterministic
#print axioms decodeBinaryNatStream_success_iff
#print axioms decodeBinaryNatStream_split_append

end FoundationCompactBinaryNatStreamSynchronization
