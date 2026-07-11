import integration.FoundationCompactListedVerifierArithmeticInput

/-!
# Primitive-recursive binary-natural token stream machine

Every compact proof component is a concatenation of self-delimiting
`binaryNatCode` tokens.  This file turns the bit payload into a deterministic
token stream by a bounded iterator.  Running, failed, and successful states are
distinct, and the machine is proved extensionally equal to repeated use of the
project's existing `decodeBinaryNat` parser.
-/

namespace FoundationCompactBinaryNatStreamMachine

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactListedVerifierArithmeticInput

abbrev BinaryNatStreamStatus := Option (Option (List Nat))

abbrev BinaryNatStreamState :=
  List Bool × List Nat × BinaryNatStreamStatus

def binaryNatStreamStateOutput
    (state : BinaryNatStreamState) : Option (List Nat) :=
  state.2.2.getD none

def binaryNatStreamRunningStep
    (state : BinaryNatStreamState) : BinaryNatStreamState :=
  if state.1 = [] then
    ([], state.2.1, some (some state.2.1.reverse))
  else
    match decodeBinaryNat state.1 with
    | none => (state.1, state.2.1, some none)
    | some result => (result.2, result.1 :: state.2.1, none)

def binaryNatStreamStep
    (state : BinaryNatStreamState) : BinaryNatStreamState :=
  if state.2.2.isSome then
    state
  else
    binaryNatStreamRunningStep state

def binaryNatStreamInitialState (bits : List Bool) :
    BinaryNatStreamState :=
  (bits, [], none)

def binaryNatStreamRun (bits : List Bool) : BinaryNatStreamState :=
  (binaryNatStreamStep^[bits.length + 1])
    (binaryNatStreamInitialState bits)

def binaryNatStreamTokens (bits : List Bool) : Option (List Nat) :=
  binaryNatStreamStateOutput (binaryNatStreamRun bits)

def decodeBinaryNatStreamFuel :
    Nat -> List Bool -> Option (List Nat)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, bits =>
      match decodeBinaryNat bits with
      | none => none
      | some result =>
          (decodeBinaryNatStreamFuel fuel result.2).map fun tokens =>
            result.1 :: tokens

def decodeBinaryNatStream (bits : List Bool) : Option (List Nat) :=
  decodeBinaryNatStreamFuel (bits.length + 1) bits

theorem binaryNatStreamStateOutput_primrec :
    Primrec binaryNatStreamStateOutput := by
  have hstatus : Primrec
      (fun state : BinaryNatStreamState => state.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact
    (Primrec.option_getD.comp hstatus (Primrec.const none)).of_eq
      fun state => by rfl

theorem binaryNatStreamRunningStep_primrec :
    Primrec binaryNatStreamRunningStep := by
  have hbits : Primrec (fun state : BinaryNatStreamState => state.1) :=
    Primrec.fst
  have htokens : Primrec
      (fun state : BinaryNatStreamState => state.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hempty : PrimrecPred
      (fun state : BinaryNatStreamState => state.1 = []) :=
    Primrec.eq.comp hbits (Primrec.const [])
  have hreverse : Primrec
      (fun state : BinaryNatStreamState => state.2.1.reverse) :=
    Primrec.list_reverse.comp htokens
  have hsuccessStatus : Primrec
      (fun state : BinaryNatStreamState =>
        some (some state.2.1.reverse)) :=
    Primrec.option_some.comp (Primrec.option_some.comp hreverse)
  have hsuccess : Primrec
      (fun state : BinaryNatStreamState =>
        ([], state.2.1, some (some state.2.1.reverse))) :=
    Primrec.pair (Primrec.const ([] : List Bool))
      (Primrec.pair htokens hsuccessStatus)
  have hfailedStatus : Primrec
      (fun _state : BinaryNatStreamState =>
        (some none : BinaryNatStreamStatus)) :=
    Primrec.const (some none)
  have hfailure : Primrec
      (fun state : BinaryNatStreamState =>
        (state.1, state.2.1, some none)) :=
    Primrec.pair hbits (Primrec.pair htokens hfailedStatus)
  have hdecode : Primrec
      (fun state : BinaryNatStreamState => decodeBinaryNat state.1) :=
    decodeBinaryNat_primrec.comp hbits
  have hadvance : Primrec₂
      (fun (state : BinaryNatStreamState)
          (result : Nat × List Bool) =>
        (result.2, result.1 :: state.2.1,
          (none : BinaryNatStreamStatus))) := by
    have hremaining : Primrec₂
        (fun (_state : BinaryNatStreamState)
            (result : Nat × List Bool) => result.2) :=
      (Primrec.snd.comp Primrec.snd).to₂
    have htoken : Primrec₂
        (fun (_state : BinaryNatStreamState)
            (result : Nat × List Bool) => result.1) :=
      (Primrec.fst.comp Primrec.snd).to₂
    have hacc : Primrec₂
        (fun (state : BinaryNatStreamState)
            (_result : Nat × List Bool) => state.2.1) :=
      ((htokens.comp Primrec.fst).to₂)
    have hcons : Primrec₂
        (fun (state : BinaryNatStreamState)
            (result : Nat × List Bool) => result.1 :: state.2.1) :=
      Primrec.list_cons.comp₂ htoken hacc
    exact Primrec₂.pair.comp₂ hremaining
      (Primrec₂.pair.comp₂ hcons
        (Primrec₂.const (none : BinaryNatStreamStatus)))
  have hdecodedCase : Primrec (fun state : BinaryNatStreamState =>
      match decodeBinaryNat state.1 with
      | none => (state.1, state.2.1, some none)
      | some result =>
          (result.2, result.1 :: state.2.1,
            (none : BinaryNatStreamStatus))) :=
    (Primrec.option_casesOn hdecode hfailure hadvance).of_eq
      fun state => by
        cases hresult : decodeBinaryNat state.1 <;> simp [hresult]
  exact
    (Primrec.ite hempty hsuccess hdecodedCase).of_eq fun state => by
      simp only [binaryNatStreamRunningStep]

theorem binaryNatStreamStep_primrec :
    Primrec binaryNatStreamStep := by
  have hstatus : Primrec
      (fun state : BinaryNatStreamState => state.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hdone : Primrec
      (fun state : BinaryNatStreamState => state.2.2.isSome) :=
    Primrec.option_isSome.comp hstatus
  exact
    (Primrec.cond hdone Primrec.id
      binaryNatStreamRunningStep_primrec).of_eq fun state => by
        cases hstatusValue : state.2.2 <;>
          simp [binaryNatStreamStep, hstatusValue]

theorem binaryNatStreamInitialState_primrec :
    Primrec binaryNatStreamInitialState := by
  exact
    (Primrec.pair Primrec.id
      (Primrec.pair (Primrec.const [])
        (Primrec.const (none : BinaryNatStreamStatus)))).of_eq
      fun bits => by rfl

theorem binaryNatStreamRun_primrec : Primrec binaryNatStreamRun := by
  have hcount : Primrec (fun bits : List Bool => bits.length + 1) :=
    Primrec.succ.comp Primrec.list_length
  have hstep : Primrec₂
      (fun (_bits : List Bool) (state : BinaryNatStreamState) =>
        binaryNatStreamStep state) :=
    (binaryNatStreamStep_primrec.comp Primrec.snd).to₂
  exact
    (Primrec.nat_iterate hcount binaryNatStreamInitialState_primrec
      hstep).of_eq fun bits => by rfl

theorem binaryNatStreamTokens_primrec :
    Primrec binaryNatStreamTokens := by
  exact
    (binaryNatStreamStateOutput_primrec.comp
      binaryNatStreamRun_primrec).of_eq fun bits => by rfl

theorem binaryNatStreamStep_done
    (bits : List Bool) (tokens : List Nat)
    (result : Option (List Nat)) :
    binaryNatStreamStep (bits, tokens, some result) =
      (bits, tokens, some result) := by
  simp [binaryNatStreamStep]

theorem binaryNatStreamStep_iterate_done
    (fuel : Nat) (bits : List Bool) (tokens : List Nat)
    (result : Option (List Nat)) :
    (binaryNatStreamStep^[fuel]) (bits, tokens, some result) =
      (bits, tokens, some result) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply,
        binaryNatStreamStep_done, ih]

theorem binaryNatStreamRunFuel_spec
    (fuel : Nat) (bits : List Bool) (tokensRev : List Nat) :
    binaryNatStreamStateOutput
        ((binaryNatStreamStep^[fuel]) (bits, tokensRev, none)) =
      (decodeBinaryNatStreamFuel fuel bits).map fun tokens =>
        tokensRev.reverse ++ tokens := by
  induction fuel generalizing bits tokensRev with
  | zero => simp [binaryNatStreamStateOutput, decodeBinaryNatStreamFuel]
  | succ fuel ih =>
      rw [Function.iterate_succ_apply]
      cases bits with
      | nil =>
          rw [binaryNatStreamStep]
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            binaryNatStreamRunningStep, if_pos, binaryNatStreamStep_iterate_done]
          simp [binaryNatStreamStateOutput, decodeBinaryNatStreamFuel]
      | cons bit bits =>
          cases hdecode : decodeBinaryNat (bit :: bits) with
          | none =>
              rw [binaryNatStreamStep]
              simp only [Option.isSome_none, Bool.false_eq_true,
                ↓reduceIte, binaryNatStreamRunningStep,
                List.cons_ne_nil, if_false, hdecode,
                binaryNatStreamStep_iterate_done]
              simp [binaryNatStreamStateOutput,
                decodeBinaryNatStreamFuel, hdecode]
          | some result =>
              rcases result with ⟨token, suffix⟩
              rw [binaryNatStreamStep]
              simp only [Option.isSome_none, Bool.false_eq_true,
                ↓reduceIte, binaryNatStreamRunningStep,
                List.cons_ne_nil, if_false, hdecode]
              rw [ih suffix (token :: tokensRev)]
              cases htail : decodeBinaryNatStreamFuel fuel suffix <;>
                simp [decodeBinaryNatStreamFuel, hdecode,
                  htail, List.reverse_cons, List.append_assoc]

theorem binaryNatStreamTokens_eq_decodeBinaryNatStream
    (bits : List Bool) :
    binaryNatStreamTokens bits = decodeBinaryNatStream bits := by
  unfold binaryNatStreamTokens binaryNatStreamRun
    binaryNatStreamInitialState decodeBinaryNatStream
  simpa using
    (binaryNatStreamRunFuel_spec (bits.length + 1) bits [])

theorem decodeBinaryNatStream_primrec :
    Primrec decodeBinaryNatStream := by
  exact binaryNatStreamTokens_primrec.of_eq
    binaryNatStreamTokens_eq_decodeBinaryNatStream

theorem decodeBinaryNatStreamFuel_succ_of_decode
    (fuel : Nat) (bits : List Bool) (token : Nat)
    (suffix : List Bool) (hbits : Not (bits = []))
    (hdecode : decodeBinaryNat bits = some (token, suffix)) :
    decodeBinaryNatStreamFuel (fuel + 1) bits =
      (decodeBinaryNatStreamFuel fuel suffix).map fun tokens =>
        token :: tokens := by
  cases bits with
  | nil => exact (hbits rfl).elim
  | cons bit bits => simp [decodeBinaryNatStreamFuel, hdecode]

theorem decodeBinaryNatStreamFuel_flatMap_binaryNatCode
    (tokens : List Nat) (fuel : Nat)
    (hfuel : tokens.length < fuel) :
    decodeBinaryNatStreamFuel fuel
        (tokens.flatMap binaryNatCode) = some tokens := by
  induction tokens generalizing fuel with
  | nil =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel => simp [decodeBinaryNatStreamFuel]
  | cons token tokens ih =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          have htailFuel : tokens.length < fuel := by
            simpa using hfuel
          simp only [List.flatMap_cons]
          rw [decodeBinaryNatStreamFuel_succ_of_decode fuel
            (binaryNatCode token ++ tokens.flatMap binaryNatCode)
            token (tokens.flatMap binaryNatCode)
            (by simp [binaryNatCode])
            (decodeBinaryNat_binaryNatCode_append token
              (tokens.flatMap binaryNatCode))]
          simp [ih fuel htailFuel]

theorem tokenCount_le_binaryNatStreamLength (tokens : List Nat) :
    tokens.length <= (tokens.flatMap binaryNatCode).length := by
  induction tokens with
  | nil => simp
  | cons token tokens ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      simp only [binaryNatCode, List.length_append, List.length_cons,
        List.length_nil]
      omega

theorem decodeBinaryNatStream_flatMap_binaryNatCode
    (tokens : List Nat) :
    decodeBinaryNatStream (tokens.flatMap binaryNatCode) = some tokens := by
  apply decodeBinaryNatStreamFuel_flatMap_binaryNatCode
  have hle := tokenCount_le_binaryNatStreamLength tokens
  omega

#print axioms binaryNatStreamStep_primrec
#print axioms binaryNatStreamTokens_primrec
#print axioms binaryNatStreamTokens_eq_decodeBinaryNatStream
#print axioms decodeBinaryNatStream_primrec
#print axioms decodeBinaryNatStream_flatMap_binaryNatCode

end FoundationCompactBinaryNatStreamMachine
