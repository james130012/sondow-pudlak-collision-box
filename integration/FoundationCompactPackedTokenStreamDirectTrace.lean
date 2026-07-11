import integration.FoundationCompactListedPackedBitTokenSynchronization
import Mathlib.Computability.Primrec.List

/-!
# Direct local traces for packed binary-natural token streams

This module opens the bounded iterator inside `compactPackedTokenStream`.
The witness records the peeled payload and a local initial/step/final tableau
for `binaryNatStreamStep`.  It uses no minimization or witness search.
-/

namespace FoundationCompactPackedTokenStreamDirectTrace

open FoundationCompactListedVerifierArithmeticInput
open FoundationCompactBinaryNatStreamMachine
open FoundationCompactListedPackedBitTokenSynchronization

def binaryNatStreamStateAt
    (start : BinaryNatStreamState) (stepIndex : Nat) :
    BinaryNatStreamState :=
  (binaryNatStreamStep^[stepIndex]) start

theorem binaryNatStreamStateAt_primrec :
    Primrec₂ binaryNatStreamStateAt := by
  apply Primrec₂.mk
  have hstep : Primrec₂
      (fun (_input : BinaryNatStreamState × Nat)
          (state : BinaryNatStreamState) =>
        binaryNatStreamStep state) := by
    apply Primrec₂.mk
    exact binaryNatStreamStep_primrec.comp Primrec.snd
  exact
    (Primrec.nat_iterate Primrec.snd Primrec.fst hstep).of_eq
      fun input => by rfl

def binaryNatStreamStateTrace
    (fuel : Nat) (start : BinaryNatStreamState) :
    List BinaryNatStreamState :=
  (List.range (fuel + 1)).map fun stepIndex =>
    binaryNatStreamStateAt start stepIndex

theorem binaryNatStreamStateTrace_primrec :
    Primrec₂ binaryNatStreamStateTrace := by
  apply Primrec₂.mk
  let Input := Nat × BinaryNatStreamState
  have hindices : Primrec (fun input : Input =>
      List.range (input.1 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.fst)
  have hstate : Primrec₂
      (fun (input : Input) (stepIndex : Nat) =>
        binaryNatStreamStateAt input.2 stepIndex) :=
    binaryNatStreamStateAt_primrec.comp₂
      (Primrec.snd.comp Primrec₂.left) Primrec₂.right
  exact
    (Primrec.list_map hindices hstate).of_eq fun input => by rfl

def binaryNatStreamTraceState?
    (states : List BinaryNatStreamState) (stepIndex : Nat) :
    Option BinaryNatStreamState :=
  states[stepIndex]?

theorem binaryNatStreamTraceState?_primrec :
    Primrec₂ binaryNatStreamTraceState? :=
  Primrec.list_getElem?

def binaryNatStreamStepOption
    (state : Option BinaryNatStreamState) :
    Option BinaryNatStreamState :=
  state.map binaryNatStreamStep

theorem binaryNatStreamStepOption_primrec :
    Primrec binaryNatStreamStepOption := by
  refine (Primrec.option_map Primrec.id ?_).of_eq fun state => by rfl
  apply Primrec₂.mk
  exact binaryNatStreamStep_primrec.comp Primrec.snd

@[simp] theorem binaryNatStreamStateTrace_length
    (fuel : Nat) (start : BinaryNatStreamState) :
    (binaryNatStreamStateTrace fuel start).length = fuel + 1 := by
  simp [binaryNatStreamStateTrace]

theorem binaryNatStreamStateTrace_getElem?
    (fuel stepIndex : Nat) (start : BinaryNatStreamState)
    (hstepIndex : stepIndex <= fuel) :
    binaryNatStreamTraceState?
        (binaryNatStreamStateTrace fuel start) stepIndex =
      some (binaryNatStreamStateAt start stepIndex) := by
  simp [binaryNatStreamTraceState?, binaryNatStreamStateTrace,
    hstepIndex]

theorem binaryNatStreamStateTrace_final
    (fuel : Nat) (start : BinaryNatStreamState) :
    binaryNatStreamTraceState?
        (binaryNatStreamStateTrace fuel start) fuel =
      some ((binaryNatStreamStep^[fuel]) start) := by
  simpa [binaryNatStreamStateAt] using
    binaryNatStreamStateTrace_getElem? fuel fuel start (by rfl)

def BinaryNatStreamCanonicalTraceValid
    (fuel : Nat) (start : BinaryNatStreamState)
    (states : List BinaryNatStreamState) : Prop :=
  states = binaryNatStreamStateTrace fuel start

theorem binaryNatStreamCanonicalTraceValid_primrec :
    PrimrecPred (fun input :
        (Nat × BinaryNatStreamState) × List BinaryNatStreamState =>
      BinaryNatStreamCanonicalTraceValid
        input.1.1 input.1.2 input.2) := by
  have hcanonical : Primrec (fun input :
      (Nat × BinaryNatStreamState) × List BinaryNatStreamState =>
      binaryNatStreamStateTrace input.1.1 input.1.2) :=
    binaryNatStreamStateTrace_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst)
  exact
    (Primrec.eq.comp Primrec.snd hcanonical).of_eq fun input => by
      simp [BinaryNatStreamCanonicalTraceValid]

def BinaryNatStreamLocalTraceValid
    (fuel : Nat) (start : BinaryNatStreamState)
    (states : List BinaryNatStreamState) : Prop :=
  states.length = fuel + 1 ∧
    binaryNatStreamTraceState? states 0 = some start ∧
    ∀ stepIndex < fuel,
      binaryNatStreamTraceState? states (stepIndex + 1) =
        binaryNatStreamStepOption
          (binaryNatStreamTraceState? states stepIndex)

abbrev BinaryNatStreamLocalTraceInput :=
  (Nat × BinaryNatStreamState) × List BinaryNatStreamState

def BinaryNatStreamTransitionAt
    (stepIndex : Nat) (input : BinaryNatStreamLocalTraceInput) : Prop :=
  binaryNatStreamTraceState? input.2 (stepIndex + 1) =
    binaryNatStreamStepOption
      (binaryNatStreamTraceState? input.2 stepIndex)

theorem binaryNatStreamTransitionAt_primrec :
    PrimrecRel BinaryNatStreamTransitionAt := by
  have hindex : Primrec
      (fun pair : Nat × BinaryNatStreamLocalTraceInput => pair.1) :=
    Primrec.fst
  have hstates : Primrec
      (fun pair : Nat × BinaryNatStreamLocalTraceInput => pair.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hcurrent : Primrec
      (fun pair : Nat × BinaryNatStreamLocalTraceInput =>
        binaryNatStreamTraceState? pair.2.2 pair.1) :=
    binaryNatStreamTraceState?_primrec.comp hstates hindex
  have hnextIndex : Primrec
      (fun pair : Nat × BinaryNatStreamLocalTraceInput => pair.1 + 1) :=
    Primrec.succ.comp hindex
  have hnext : Primrec
      (fun pair : Nat × BinaryNatStreamLocalTraceInput =>
        binaryNatStreamTraceState? pair.2.2 (pair.1 + 1)) :=
    binaryNatStreamTraceState?_primrec.comp hstates hnextIndex
  have hstepped : Primrec
      (fun pair : Nat × BinaryNatStreamLocalTraceInput =>
        binaryNatStreamStepOption
          (binaryNatStreamTraceState? pair.2.2 pair.1)) :=
    binaryNatStreamStepOption_primrec.comp hcurrent
  exact
    (Primrec.eq.comp hnext hstepped).of_eq fun pair => by
      simp [BinaryNatStreamTransitionAt]

theorem binaryNatStreamStateTrace_localValid
    (fuel : Nat) (start : BinaryNatStreamState) :
    BinaryNatStreamLocalTraceValid fuel start
      (binaryNatStreamStateTrace fuel start) := by
  refine ⟨binaryNatStreamStateTrace_length fuel start, ?_, ?_⟩
  · simpa [binaryNatStreamStateAt] using
      binaryNatStreamStateTrace_getElem? fuel 0 start (Nat.zero_le fuel)
  · intro stepIndex hstepIndex
    rw [binaryNatStreamStateTrace_getElem? fuel (stepIndex + 1)
      start (by omega)]
    rw [binaryNatStreamStateTrace_getElem? fuel stepIndex
      start (Nat.le_of_lt hstepIndex)]
    simp [binaryNatStreamStateAt, binaryNatStreamStepOption,
      Function.iterate_succ_apply']

theorem binaryNatStreamLocalTraceValid_stateAt
    {fuel : Nat} {start : BinaryNatStreamState}
    {states : List BinaryNatStreamState}
    (hvalid : BinaryNatStreamLocalTraceValid fuel start states)
    {stepIndex : Nat} (hstepIndex : stepIndex <= fuel) :
    binaryNatStreamTraceState? states stepIndex =
      some (binaryNatStreamStateAt start stepIndex) := by
  induction stepIndex with
  | zero =>
      simpa [binaryNatStreamStateAt] using hvalid.2.1
  | succ stepIndex ih =>
      have hlt : stepIndex < fuel := by omega
      have hprevious := ih (by omega)
      rw [show stepIndex + 1 = stepIndex.succ by omega,
        hvalid.2.2 stepIndex hlt, hprevious]
      simp [binaryNatStreamStateAt, binaryNatStreamStepOption,
        Function.iterate_succ_apply']

theorem binaryNatStreamLocalTraceValid_eq_canonical
    {fuel : Nat} {start : BinaryNatStreamState}
    {states : List BinaryNatStreamState}
    (hvalid : BinaryNatStreamLocalTraceValid fuel start states) :
    states = binaryNatStreamStateTrace fuel start := by
  apply List.ext_getElem?
  intro stepIndex
  by_cases hstepIndex : stepIndex <= fuel
  · change
      binaryNatStreamTraceState? states stepIndex =
        binaryNatStreamTraceState?
          (binaryNatStreamStateTrace fuel start) stepIndex
    rw [binaryNatStreamLocalTraceValid_stateAt hvalid hstepIndex]
    rw [binaryNatStreamStateTrace_getElem?
      fuel stepIndex start hstepIndex]
  · have hstatesLength : states.length = fuel + 1 := hvalid.1
    have hcanonicalLength := binaryNatStreamStateTrace_length fuel start
    have houtside : fuel + 1 <= stepIndex := by omega
    rw [List.getElem?_eq_none (by omega : states.length <= stepIndex)]
    rw [List.getElem?_eq_none (by omega :
      (binaryNatStreamStateTrace fuel start).length <= stepIndex)]

theorem binaryNatStreamLocalTraceValid_iff_canonical
    (fuel : Nat) (start : BinaryNatStreamState)
    (states : List BinaryNatStreamState) :
    BinaryNatStreamLocalTraceValid fuel start states ↔
      BinaryNatStreamCanonicalTraceValid fuel start states := by
  constructor
  · exact binaryNatStreamLocalTraceValid_eq_canonical
  · intro hvalid
    rw [hvalid]
    exact binaryNatStreamStateTrace_localValid fuel start

theorem binaryNatStreamLocalTraceValid_primrec :
    PrimrecPred (fun input : BinaryNatStreamLocalTraceInput =>
      BinaryNatStreamLocalTraceValid input.1.1 input.1.2 input.2) := by
  exact binaryNatStreamCanonicalTraceValid_primrec.of_eq fun input =>
    (binaryNatStreamLocalTraceValid_iff_canonical
      input.1.1 input.1.2 input.2).symm

abbrev CompactPackedTokenStreamDirectTrace :=
  List Bool × List BinaryNatStreamState

def CompactPackedTokenStreamDirectTraceValid
    (code : Nat) (tokens : List Nat)
    (trace : CompactPackedTokenStreamDirectTrace) : Prop :=
  let payload := trace.1
  let states := trace.2
  let fuel := payload.length + 1
  let start := binaryNatStreamInitialState payload
  packedPayloadBits code = some payload ∧
    BinaryNatStreamLocalTraceValid fuel start states ∧
    (binaryNatStreamTraceState? states fuel).map
        binaryNatStreamStateOutput = some (some tokens)

theorem compactPackedTokenStreamDirectTraceValid_primrec :
    PrimrecPred (fun input :
        (Nat × List Nat) × CompactPackedTokenStreamDirectTrace =>
      CompactPackedTokenStreamDirectTraceValid
        input.1.1 input.1.2 input.2) := by
  let Input :=
    (Nat × List Nat) × CompactPackedTokenStreamDirectTrace
  have hcode : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have htokens : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hpayload : Primrec (fun input : Input => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hstates : Primrec (fun input : Input => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hfuel : Primrec (fun input : Input => input.2.1.length + 1) :=
    Primrec.succ.comp (Primrec.list_length.comp hpayload)
  have hstart : Primrec (fun input : Input =>
      binaryNatStreamInitialState input.2.1) :=
    binaryNatStreamInitialState_primrec.comp hpayload
  have hpayloadEq : PrimrecPred (fun input : Input =>
      packedPayloadBits input.1.1 = some input.2.1) :=
    Primrec.eq.comp
      (packedPayloadBits_primrec.comp hcode)
      (Primrec.option_some.comp hpayload)
  have hlocal : PrimrecPred (fun input : Input =>
      BinaryNatStreamLocalTraceValid
        (input.2.1.length + 1)
        (binaryNatStreamInitialState input.2.1) input.2.2) :=
    binaryNatStreamLocalTraceValid_primrec.comp <|
      Primrec.pair (Primrec.pair hfuel hstart) hstates
  have hfinalState : Primrec (fun input : Input =>
      binaryNatStreamTraceState? input.2.2 (input.2.1.length + 1)) :=
    binaryNatStreamTraceState?_primrec.comp hstates hfuel
  have hfinalOutput : Primrec (fun input : Input =>
      (binaryNatStreamTraceState?
        input.2.2 (input.2.1.length + 1)).map
          binaryNatStreamStateOutput) :=
    Primrec.option_map hfinalState
      (binaryNatStreamStateOutput_primrec.comp Primrec₂.right)
  have htarget : Primrec (fun input : Input =>
      some (some input.1.2)) :=
    Primrec.option_some.comp
      (Primrec.option_some.comp htokens)
  have hfinal : PrimrecPred (fun input : Input =>
      (binaryNatStreamTraceState?
        input.2.2 (input.2.1.length + 1)).map
          binaryNatStreamStateOutput = some (some input.1.2)) :=
    Primrec.eq.comp hfinalOutput htarget
  exact
    (hpayloadEq.and (hlocal.and hfinal)).of_eq fun input => by
      simp only [CompactPackedTokenStreamDirectTraceValid]

theorem compactPackedTokenStream_eq_some_iff_exists_directTrace
    (code : Nat) (tokens : List Nat) :
    compactPackedTokenStream code = some tokens ↔
      ∃ trace : CompactPackedTokenStreamDirectTrace,
        CompactPackedTokenStreamDirectTraceValid code tokens trace := by
  constructor
  · intro hstream
    cases hpayload : packedPayloadBits code with
    | none =>
        simp [compactPackedTokenStream, hpayload] at hstream
    | some payload =>
        let fuel := payload.length + 1
        let start := binaryNatStreamInitialState payload
        let states := binaryNatStreamStateTrace fuel start
        have htokens : binaryNatStreamTokens payload = some tokens := by
          simpa [compactPackedTokenStream, hpayload] using hstream
        refine ⟨(payload, states), ?_⟩
        simp only [CompactPackedTokenStreamDirectTraceValid]
        refine ⟨hpayload,
          binaryNatStreamStateTrace_localValid fuel start, ?_⟩
        change
          (binaryNatStreamTraceState?
            (binaryNatStreamStateTrace fuel start) fuel).map
              binaryNatStreamStateOutput = some (some tokens)
        rw [binaryNatStreamStateTrace_final]
        simpa [fuel, start, binaryNatStreamTokens,
          binaryNatStreamRun] using htokens
  · rintro ⟨trace, htrace⟩
    let payload := trace.1
    let states := trace.2
    let fuel := payload.length + 1
    let start := binaryNatStreamInitialState payload
    change
      packedPayloadBits code = some payload ∧
        BinaryNatStreamLocalTraceValid fuel start states ∧
        (binaryNatStreamTraceState? states fuel).map
          binaryNatStreamStateOutput = some (some tokens) at htrace
    rcases htrace with ⟨hpayload, hstates, hfinal⟩
    have hstatesEq : states = binaryNatStreamStateTrace fuel start :=
      binaryNatStreamLocalTraceValid_eq_canonical hstates
    rw [hstatesEq] at hfinal
    change
      (binaryNatStreamTraceState?
        (binaryNatStreamStateTrace fuel start) fuel).map
          binaryNatStreamStateOutput = some (some tokens) at hfinal
    rw [binaryNatStreamStateTrace_final] at hfinal
    have htokens : binaryNatStreamTokens payload = some tokens := by
      simpa [fuel, start, binaryNatStreamTokens,
        binaryNatStreamRun] using hfinal
    simp [compactPackedTokenStream, hpayload, htokens]

#print axioms binaryNatStreamStateAt_primrec
#print axioms binaryNatStreamStateTrace_primrec
#print axioms binaryNatStreamTransitionAt_primrec
#print axioms binaryNatStreamLocalTraceValid_primrec
#print axioms compactPackedTokenStreamDirectTraceValid_primrec
#print axioms compactPackedTokenStream_eq_some_iff_exists_directTrace

end FoundationCompactPackedTokenStreamDirectTrace
