import integration.FoundationEfficientPAProofPredicateArithmetic
import Mathlib.Computability.Primrec.List

/-!
# Arithmetic representation of the efficient PA proof predicate

This file proves computability of the concrete postfix verifier and then uses
Foundation's representation theorem to obtain an exact Sigma-one formula.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

namespace FoundationEfficientPAProofPredicateRepresentation

open FoundationSuccinctFiniteConsistencyTarget
open FoundationEfficientPAProofPredicateArithmetic
open Primrec

theorem taggedValue_primrec : Primrec₂ taggedValue := by
  exact Primrec₂.natPair.of_eq fun _ _ ↦ rfl

theorem decodeTaggedValue_primrec : Primrec₂ decodeTaggedValue := by
  apply Primrec₂.mk
  simp only [decodeTaggedValue]
  exact Primrec.ite
    (Primrec.eq.comp
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
      Primrec.fst)
    (Primrec.option_some.comp
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
    (Primrec.const none)

theorem pushTerm_primrec : Primrec₂ pushTerm := by
  exact
    (Primrec.list_cons.comp₂
      (taggedValue_primrec.comp₂
        (Primrec₂.const termValueTag) Primrec₂.left)
      Primrec₂.right).of_eq fun _ _ ↦ rfl

theorem pushFormula_primrec : Primrec₂ pushFormula := by
  exact
    (Primrec.list_cons.comp₂
      (taggedValue_primrec.comp₂
        (Primrec₂.const formulaValueTag) Primrec₂.left)
      Primrec₂.right).of_eq fun _ _ ↦ rfl

theorem pushSequent_primrec : Primrec₂ pushSequent := by
  exact
    (Primrec.list_cons.comp₂
      (taggedValue_primrec.comp₂
        (Primrec₂.const sequentValueTag) Primrec₂.left)
      Primrec₂.right).of_eq fun _ _ ↦ rfl

theorem pushProof_primrec :
    Primrec₂ (fun p : Nat × Nat ↦ pushProof p.1 p.2) := by
  apply Primrec₂.mk
  exact Primrec.list_cons.comp
    (taggedValue_primrec.comp
      (Primrec.const proofValueTag)
      (Primrec₂.natPair.comp
        (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.fst)))
    Primrec.snd

def tagMatches (tag value : Nat) : Bool :=
  decide (value.unpair.1 = tag)

theorem tagMatches_primrec : Primrec₂ tagMatches := by
  exact
    (Primrec.eq.decide.comp₂
      ((Primrec.fst.comp Primrec.unpair).comp₂ Primrec₂.right)
      Primrec₂.left).of_eq fun _ _ ↦ rfl

theorem taggedListAll_primrec :
    Primrec₂ (fun (tag : Nat) (values : List Nat) ↦
      values.all (tagMatches tag)) := by
  have hstep :
      Primrec₂ (fun (input : Nat × List Nat)
        (state : Nat × Bool) ↦
          tagMatches input.1 state.1 && state.2) :=
    Primrec.and.comp₂
      (tagMatches_primrec.comp₂
        ((Primrec.fst.comp Primrec.fst).to₂)
        ((Primrec.fst.comp Primrec.snd).to₂))
      ((Primrec.snd.comp Primrec.snd).to₂)
  refine
    (Primrec.list_foldr
      (f := fun input : Nat × List Nat ↦ input.2)
      (g := fun _ : Nat × List Nat ↦ true)
      (h := fun input (state : Nat × Bool) ↦
        tagMatches input.1 state.1 && state.2)
      Primrec.snd (Primrec.const true) hstep).of_eq ?_
  rintro ⟨tag, values⟩
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [Prod.fst, Prod.snd] at ih
      simp only [List.foldr_cons, List.all_cons, ih]

theorem mapUnpairRight_primrec :
    Primrec (fun values : List Nat ↦
      values.map fun value ↦ value.unpair.2) := by
  exact
    (Primrec.list_map Primrec.id
      ((Primrec.snd.comp Primrec.unpair).comp
        Primrec.snd).to₂).of_eq fun _ ↦ rfl

theorem decodeTaggedList_primrec : Primrec₂ decodeTaggedList := by
  apply Primrec₂.mk
  refine
    (Primrec.cond
      (taggedListAll_primrec.comp Primrec.fst Primrec.snd)
      (Primrec.option_some.comp
        (mapUnpairRight_primrec.comp Primrec.snd))
      (Primrec.const none)).of_eq ?_
  rintro ⟨tag, values⟩
  change
    (bif values.all (tagMatches tag) then
      some (values.map fun value ↦ value.unpair.2)
    else none) = decodeTaggedList tag values
  unfold decodeTaggedList
  change
    (bif values.all (tagMatches tag) then
      some (values.map fun value ↦ value.unpair.2)
    else none) =
    (if values.all (tagMatches tag) then
      some (values.map fun value ↦ value.unpair.2)
    else none)
  cases values.all (tagMatches tag) <;> rfl

theorem popTagged_primrec : Primrec₂ popTagged := by
  have hstep :
      Primrec₂ (fun (input : Nat × List Nat)
        (state : Nat × List Nat) ↦ do
          let payload ← decodeTaggedValue input.1 state.1
          pure (payload, state.2)) := by
    apply Primrec₂.mk
    have hdecode :
        Primrec (fun q :
          (Nat × List Nat) × (Nat × List Nat) ↦
            decodeTaggedValue q.1.1 q.2.1) :=
      decodeTaggedValue_primrec.comp
        (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd)
    have htail :
        Primrec₂ (fun
          (q : (Nat × List Nat) × (Nat × List Nat))
          (_ : Nat) ↦ q.2.2) :=
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).to₂
    exact
      (Primrec.option_map hdecode
        (Primrec₂.pair.comp₂ Primrec₂.right htail)).of_eq
          fun q ↦ by
            cases decodeTaggedValue q.1.1 q.2.1 <;> rfl
  refine
    (Primrec.list_casesOn
      (f := fun input : Nat × List Nat ↦ input.2)
      (g := fun _ : Nat × List Nat ↦ none)
      (h := fun input state ↦ do
        let payload ← decodeTaggedValue input.1 state.1
        pure (payload, state.2))
      Primrec.snd (Primrec.const none) hstep).of_eq ?_
  rintro ⟨tag, stack⟩
  cases stack <;> rfl

theorem popManyTagged_primrec :
    Primrec₂ (fun input : Nat × Nat ↦
      popManyTagged input.1 input.2) := by
  apply Primrec₂.mk
  let Input := (Nat × Nat) × List Nat
  have htag : Primrec (fun input : Input ↦ input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hcount : Primrec (fun input : Input ↦ input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hstack : Primrec (fun input : Input ↦ input.2) :=
    Primrec.snd
  have hfront : Primrec (fun input : Input ↦
      input.2.take input.1.2) :=
    Primrec.list_take.comp hcount hstack
  have hdrop : Primrec (fun input : Input ↦
      input.2.drop input.1.2) :=
    Primrec.list_drop.comp hcount hstack
  have hlength : Primrec (fun input : Input ↦
      (input.2.take input.1.2).length) :=
    Primrec.list_length.comp hfront
  have heq : PrimrecPred (fun input : Input ↦
      (input.2.take input.1.2).length = input.1.2) :=
    Primrec.eq.comp hlength hcount
  have hguard : Primrec (fun input : Input ↦
      if (input.2.take input.1.2).length = input.1.2 then
        some ()
      else
        none) :=
    Primrec.ite heq (Primrec.const (some ())) (Primrec.const none)
  have hdecode : Primrec (fun input : Input ↦
      decodeTaggedList input.1.1 (input.2.take input.1.2)) :=
    decodeTaggedList_primrec.comp htag hfront
  have hpair : Primrec₂ (fun (input : Input) (payloads : List Nat) ↦
      (payloads, input.2.drop input.1.2)) :=
    Primrec₂.pair.comp₂ Primrec₂.right
      ((hdrop.comp Primrec.fst).to₂)
  have hbody : Primrec (fun input : Input ↦
      (decodeTaggedList input.1.1
        (input.2.take input.1.2)).map
          fun payloads ↦
            (payloads, input.2.drop input.1.2)) :=
    Primrec.option_map hdecode hpair
  refine
    (Primrec.option_bind hguard
      ((hbody.comp Primrec.fst).to₂)).of_eq ?_
  rintro ⟨⟨tag, count⟩, stack⟩
  by_cases hlengthEq : (stack.take count).length = count
  · have hle : count ≤ stack.length := by
      simpa using hlengthEq
    cases hdecodeValue :
        decodeTaggedList tag (stack.take count) <;>
      simp [popManyTagged, hlengthEq, hle, hdecodeValue]
  · have hnotLe : ¬count ≤ stack.length := by
      simpa using hlengthEq
    simp [popManyTagged, hlengthEq, hnotLe]

theorem rawVectorCode_primrec : Primrec rawVectorCode := by
  have hstep :
      Primrec₂ (fun (_ : List Nat) (state : Nat × Nat) ↦
        Nat.pair state.1 state.2 + 1) :=
    Primrec.succ.comp₂
      (Primrec₂.natPair.comp₂
        ((Primrec.fst.comp Primrec.snd).to₂)
        ((Primrec.snd.comp Primrec.snd).to₂))
  refine
    (Primrec.list_foldr
      (f := fun values : List Nat ↦ values)
      (g := fun _ : List Nat ↦ 0)
      (h := fun (_ : List Nat) (state : Nat × Nat) ↦
        Nat.pair state.1 state.2 + 1)
      Primrec.id (Primrec.const 0) hstep).of_eq ?_
  intro values
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.foldr_cons]
      rw [ih]
      rfl

theorem natPow_primrec : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) :=
  Primrec₂.unpaired'.mp Nat.Primrec.pow

theorem rawSequentCode_primrec : Primrec rawSequentCode := by
  have hstep :
      Primrec₂ (fun (_ : List Nat) (state : Nat × Nat) ↦
        state.1 + 2 ^ state.2) :=
    Primrec.nat_add.comp₂
      ((Primrec.fst.comp Primrec.snd).to₂)
      (natPow_primrec.comp₂ (Primrec₂.const 2)
        ((Primrec.snd.comp Primrec.snd).to₂))
  exact
    (Primrec.list_foldl
      (f := fun values : List Nat ↦ values)
      (g := fun _ : List Nat ↦ 0)
      (h := fun (_ : List Nat) (state : Nat × Nat) ↦
        state.1 + 2 ^ state.2)
      Primrec.id (Primrec.const 0) hstep).of_eq fun _ ↦ rfl

def postfixBranch0 (payload : Nat) (stack : List Nat) :
    Option (List Nat) :=
  some (pushTerm (Nat.pair 0 payload + 1) stack)

def postfixBranch1 (payload : Nat) (stack : List Nat) :
    Option (List Nat) :=
  some (pushTerm (Nat.pair 1 payload + 1) stack)

def postfixVectorBranch
    (sourceTag resultTag rawTag payload : Nat)
    (stack : List Nat) : Option (List Nat) := do
  let arity := payload.unpair.1
  let symbolCode := payload.unpair.2
  let (arguments, stack) ←
    popManyTagged sourceTag arity stack
  let raw :=
    Nat.pair rawTag
      (Nat.pair arity
        (Nat.pair symbolCode
          (rawVectorCode arguments.reverse))) + 1
  pure (taggedValue resultTag raw :: stack)

def postfixBranch2 :=
  postfixVectorBranch termValueTag termValueTag 2

def postfixBranch3 :=
  postfixVectorBranch termValueTag formulaValueTag 0

def postfixBranch4 :=
  postfixVectorBranch termValueTag formulaValueTag 1

def postfixBranch5 (_payload : Nat) (stack : List Nat) :
    Option (List Nat) :=
  some (pushFormula (Nat.pair 2 0 + 1) stack)

def postfixBranch6 (_payload : Nat) (stack : List Nat) :
    Option (List Nat) :=
  some (pushFormula (Nat.pair 3 0 + 1) stack)

def postfixUnaryFormulaBranch
    (rawTag _payload : Nat) (stack : List Nat) :
    Option (List Nat) := do
  let (body, stack) ← popTagged formulaValueTag stack
  pure (pushFormula (Nat.pair rawTag body + 1) stack)

def postfixBranch9 := postfixUnaryFormulaBranch 6
def postfixBranch10 := postfixUnaryFormulaBranch 7

def postfixBinaryFormulaBranch
    (rawTag _payload : Nat) (stack : List Nat) :
    Option (List Nat) := do
  let (right, stack) ← popTagged formulaValueTag stack
  let (left, stack) ← popTagged formulaValueTag stack
  pure
    (pushFormula
      (Nat.pair rawTag (Nat.pair left right) + 1) stack)

def postfixBranch7 := postfixBinaryFormulaBranch 4
def postfixBranch8 := postfixBinaryFormulaBranch 5

def postfixBranch11 (payload : Nat) (stack : List Nat) :
    Option (List Nat) := do
  let (formulas, stack) ←
    popManyTagged formulaValueTag payload stack
  pure (pushSequent (rawSequentCode formulas.reverse) stack)

def postfixFormulaSequentProofBranch
    (ruleTag _payload : Nat) (stack : List Nat) :
    Option (List Nat) := do
  let (formula, stack) ← popTagged formulaValueTag stack
  let (sequent, stack) ← popTagged sequentValueTag stack
  let raw :=
    Nat.pair sequent (Nat.pair ruleTag formula) + 1
  pure (pushProof raw sequent stack)

def postfixBranch12 := postfixFormulaSequentProofBranch 0
def postfixBranch13 := postfixFormulaSequentProofBranch 9

def postfixBranch14 (_payload : Nat) (stack : List Nat) :
    Option (List Nat) := do
  let (sequent, stack) ← popTagged sequentValueTag stack
  pure
    (pushProof
      (Nat.pair sequent (Nat.pair 1 0) + 1)
      sequent stack)

def postfixUnaryProofBranch
    (ruleTag _payload : Nat) (stack : List Nat) :
    Option (List Nat) := do
  let (premise, stack) ← popTagged proofValueTag stack
  let (sequent, stack) ← popTagged sequentValueTag stack
  let raw :=
    Nat.pair sequent (Nat.pair ruleTag premise.unpair.1) + 1
  pure (pushProof raw sequent stack)

def postfixBranch19 := postfixUnaryProofBranch 6
def postfixBranch20 := postfixUnaryProofBranch 7

def postfixBranch17 (_payload : Nat) (stack : List Nat) :
    Option (List Nat) := do
  let (premise, stack) ← popTagged proofValueTag stack
  let (formula, stack) ← popTagged formulaValueTag stack
  let (sequent, stack) ← popTagged sequentValueTag stack
  pure
    (pushProof
      (rawProofAll sequent formula premise.unpair.1)
      sequent stack)

def popTaggedPatternStep
    (state : Option (List Nat × List Nat)) (tag : Nat) :
    Option (List Nat × List Nat) := do
  let (payloads, stack) ← state
  let (payload, stack) ← popTagged tag stack
  pure (payload :: payloads, stack)

def popTaggedPattern (tags stack : List Nat) :
    Option (List Nat × List Nat) :=
  (tags.foldl popTaggedPatternStep (some ([], stack))).map
    fun result ↦ (result.1.reverse, result.2)

def postfixOneProofTwoSyntaxBranch
    (ruleTag firstTag secondTag _payload : Nat)
    (stack : List Nat) : Option (List Nat) := do
  let (values, stack) ←
    popTaggedPattern
      [proofValueTag, firstTag, secondTag, sequentValueTag] stack
  let premise := values.getD 0 0
  let first := values.getD 1 0
  let second := values.getD 2 0
  let sequent := values.getD 3 0
  let raw :=
    Nat.pair sequent
      (Nat.pair ruleTag
        (Nat.pair second
          (Nat.pair first premise.unpair.1))) + 1
  pure (pushProof raw sequent stack)

def postfixBranch16 :=
  postfixOneProofTwoSyntaxBranch 3 formulaValueTag formulaValueTag

def postfixBranch18 :=
  postfixOneProofTwoSyntaxBranch 5 termValueTag formulaValueTag

theorem postfixBranch0_primrec : Primrec₂ postfixBranch0 := by
  exact
    (Primrec.option_some.comp₂
      (pushTerm_primrec.comp₂
        (Primrec.succ.comp₂
          (Primrec₂.natPair.comp₂
            (Primrec₂.const 0) Primrec₂.left))
        Primrec₂.right)).of_eq fun _ _ ↦ rfl

theorem postfixBranch1_primrec : Primrec₂ postfixBranch1 := by
  exact
    (Primrec.option_some.comp₂
      (pushTerm_primrec.comp₂
        (Primrec.succ.comp₂
          (Primrec₂.natPair.comp₂
            (Primrec₂.const 1) Primrec₂.left))
        Primrec₂.right)).of_eq fun _ _ ↦ rfl

theorem postfixVectorBranch_primrec
    (sourceTag resultTag rawTag : Nat) :
    Primrec₂ (postfixVectorBranch sourceTag resultTag rawTag) := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  let Popped := List Nat × List Nat
  have hpayload : Primrec (fun input : Input ↦ input.1) :=
    Primrec.fst
  have harity : Primrec (fun input : Input ↦ input.1.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hsymbol : Primrec (fun input : Input ↦ input.1.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have hpopInput : Primrec (fun input : Input ↦
      (sourceTag, input.1.unpair.1)) :=
    Primrec.pair (Primrec.const sourceTag) harity
  have hpop : Primrec (fun input : Input ↦
      popManyTagged sourceTag input.1.unpair.1 input.2) :=
    popManyTagged_primrec.comp hpopInput Primrec.snd
  have harguments : Primrec₂ (fun (_ : Input) (popped : Popped) ↦
      popped.1) :=
    (Primrec.fst.comp Primrec.snd).to₂
  have htail : Primrec₂ (fun (_ : Input) (popped : Popped) ↦
      popped.2) :=
    (Primrec.snd.comp Primrec.snd).to₂
  have hvector : Primrec₂ (fun (_ : Input) (popped : Popped) ↦
      rawVectorCode popped.1.reverse) :=
    (rawVectorCode_primrec.comp
      (Primrec.list_reverse.comp
        (Primrec.fst.comp Primrec.snd))).to₂
  have harity₂ : Primrec₂ (fun (input : Input) (_ : Popped) ↦
      input.1.unpair.1) :=
    (harity.comp Primrec.fst).to₂
  have hsymbol₂ : Primrec₂ (fun (input : Input) (_ : Popped) ↦
      input.1.unpair.2) :=
    (hsymbol.comp Primrec.fst).to₂
  have hsymbolVector : Primrec₂ (fun (input : Input) (popped : Popped) ↦
      Nat.pair input.1.unpair.2
        (rawVectorCode popped.1.reverse)) :=
    Primrec₂.natPair.comp₂ hsymbol₂ hvector
  have harityRest : Primrec₂ (fun (input : Input) (popped : Popped) ↦
      Nat.pair input.1.unpair.1
        (Nat.pair input.1.unpair.2
          (rawVectorCode popped.1.reverse))) :=
    Primrec₂.natPair.comp₂ harity₂ hsymbolVector
  have hraw : Primrec₂ (fun (input : Input) (popped : Popped) ↦
      Nat.pair rawTag
        (Nat.pair input.1.unpair.1
          (Nat.pair input.1.unpair.2
            (rawVectorCode popped.1.reverse))) + 1) :=
    Primrec.succ.comp₂
      (Primrec₂.natPair.comp₂
        (Primrec₂.const rawTag) harityRest)
  have hresult : Primrec₂ (fun (input : Input) (popped : Popped) ↦
      taggedValue resultTag
        (Nat.pair rawTag
          (Nat.pair input.1.unpair.1
            (Nat.pair input.1.unpair.2
              (rawVectorCode popped.1.reverse))) + 1) :: popped.2) :=
    Primrec.list_cons.comp₂
      (taggedValue_primrec.comp₂
        (Primrec₂.const resultTag) hraw)
      htail
  exact
    (Primrec.option_map hpop hresult).of_eq fun input ↦ by
      cases hpopValue :
          popManyTagged sourceTag input.1.unpair.1 input.2 <;>
        simp [postfixVectorBranch, hpopValue]

theorem postfixBranch2_primrec : Primrec₂ postfixBranch2 := by
  exact postfixVectorBranch_primrec termValueTag termValueTag 2

theorem postfixBranch3_primrec : Primrec₂ postfixBranch3 := by
  exact postfixVectorBranch_primrec termValueTag formulaValueTag 0

theorem postfixBranch4_primrec : Primrec₂ postfixBranch4 := by
  exact postfixVectorBranch_primrec termValueTag formulaValueTag 1

theorem postfixBranch5_primrec : Primrec₂ postfixBranch5 := by
  exact
    (Primrec.option_some.comp₂
      (pushFormula_primrec.comp₂
        (Primrec₂.const (Nat.pair 2 0 + 1))
        Primrec₂.right)).of_eq fun _ _ ↦ rfl

theorem postfixBranch6_primrec : Primrec₂ postfixBranch6 := by
  exact
    (Primrec.option_some.comp₂
      (pushFormula_primrec.comp₂
        (Primrec₂.const (Nat.pair 3 0 + 1))
        Primrec₂.right)).of_eq fun _ _ ↦ rfl

theorem postfixUnaryFormulaBranch_primrec (rawTag : Nat) :
    Primrec₂ (postfixUnaryFormulaBranch rawTag) := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  let Popped := Nat × List Nat
  have hpop : Primrec (fun input : Input ↦
      popTagged formulaValueTag input.2) :=
    popTagged_primrec.comp (Primrec.const formulaValueTag) Primrec.snd
  have hbody : Primrec₂ (fun (_ : Input) (popped : Popped) ↦
      popped.1) :=
    (Primrec.fst.comp Primrec.snd).to₂
  have htail : Primrec₂ (fun (_ : Input) (popped : Popped) ↦
      popped.2) :=
    (Primrec.snd.comp Primrec.snd).to₂
  have hraw : Primrec₂ (fun (_ : Input) (popped : Popped) ↦
      Nat.pair rawTag popped.1 + 1) :=
    Primrec.succ.comp₂
      (Primrec₂.natPair.comp₂ (Primrec₂.const rawTag) hbody)
  have hresult : Primrec₂ (fun (_ : Input) (popped : Popped) ↦
      pushFormula (Nat.pair rawTag popped.1 + 1) popped.2) :=
    pushFormula_primrec.comp₂ hraw htail
  exact
    (Primrec.option_map hpop hresult).of_eq fun input ↦ by
      cases hpopValue : popTagged formulaValueTag input.2 <;>
        simp [postfixUnaryFormulaBranch, hpopValue]

theorem postfixBranch9_primrec : Primrec₂ postfixBranch9 := by
  exact postfixUnaryFormulaBranch_primrec 6

theorem postfixBranch10_primrec : Primrec₂ postfixBranch10 := by
  exact postfixUnaryFormulaBranch_primrec 7

theorem postfixBinaryFormulaBranch_primrec (rawTag : Nat) :
    Primrec₂ (postfixBinaryFormulaBranch rawTag) := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  let Popped := Nat × List Nat
  have hpopRight : Primrec (fun input : Input ↦
      popTagged formulaValueTag input.2) :=
    popTagged_primrec.comp (Primrec.const formulaValueTag) Primrec.snd
  have hcontinue : Primrec₂ (fun (input : Input) (right : Popped) ↦ do
      let (left, stack) ← popTagged formulaValueTag right.2
      pure
        (pushFormula
          (Nat.pair rawTag (Nat.pair left right.1) + 1) stack)) := by
    apply Primrec₂.mk
    let ContinueInput := Input × Popped
    have hpopLeft : Primrec (fun q : ContinueInput ↦
        popTagged formulaValueTag q.2.2) :=
      popTagged_primrec.comp (Primrec.const formulaValueTag)
        (Primrec.snd.comp Primrec.snd)
    have hleft : Primrec₂ (fun (_ : ContinueInput) (left : Popped) ↦
        left.1) :=
      (Primrec.fst.comp Primrec.snd).to₂
    have hright : Primrec₂ (fun (q : ContinueInput) (_ : Popped) ↦
        q.2.1) :=
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).to₂
    have htail : Primrec₂ (fun (_ : ContinueInput) (left : Popped) ↦
        left.2) :=
      (Primrec.snd.comp Primrec.snd).to₂
    have hpairs : Primrec₂ (fun (q : ContinueInput) (left : Popped) ↦
        Nat.pair left.1 q.2.1) :=
      Primrec₂.natPair.comp₂ hleft hright
    have hraw : Primrec₂ (fun (q : ContinueInput) (left : Popped) ↦
        Nat.pair rawTag (Nat.pair left.1 q.2.1) + 1) :=
      Primrec.succ.comp₂
        (Primrec₂.natPair.comp₂ (Primrec₂.const rawTag) hpairs)
    have hresult : Primrec₂ (fun (q : ContinueInput) (left : Popped) ↦
        pushFormula
          (Nat.pair rawTag (Nat.pair left.1 q.2.1) + 1) left.2) :=
      pushFormula_primrec.comp₂ hraw htail
    exact
      (Primrec.option_map hpopLeft hresult).of_eq fun q ↦ by
        cases hpopValue : popTagged formulaValueTag q.2.2 <;>
          simp [hpopValue]
  exact
    (Primrec.option_bind hpopRight hcontinue).of_eq fun input ↦ by
      cases hpopValue : popTagged formulaValueTag input.2 <;>
        simp [postfixBinaryFormulaBranch, hpopValue]

theorem postfixBranch7_primrec : Primrec₂ postfixBranch7 := by
  exact postfixBinaryFormulaBranch_primrec 4

theorem postfixBranch8_primrec : Primrec₂ postfixBranch8 := by
  exact postfixBinaryFormulaBranch_primrec 5

theorem postfixBranch11_primrec : Primrec₂ postfixBranch11 := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  let Popped := List Nat × List Nat
  have hpopInput : Primrec (fun input : Input ↦
      (formulaValueTag, input.1)) :=
    Primrec.pair (Primrec.const formulaValueTag) Primrec.fst
  have hpop : Primrec (fun input : Input ↦
      popManyTagged formulaValueTag input.1 input.2) :=
    popManyTagged_primrec.comp hpopInput Primrec.snd
  have hraw : Primrec₂ (fun (_ : Input) (popped : Popped) ↦
      rawSequentCode popped.1.reverse) :=
    (rawSequentCode_primrec.comp
      (Primrec.list_reverse.comp
        (Primrec.fst.comp Primrec.snd))).to₂
  have htail : Primrec₂ (fun (_ : Input) (popped : Popped) ↦
      popped.2) :=
    (Primrec.snd.comp Primrec.snd).to₂
  have hresult : Primrec₂ (fun (_ : Input) (popped : Popped) ↦
      pushSequent (rawSequentCode popped.1.reverse) popped.2) :=
    pushSequent_primrec.comp₂ hraw htail
  exact
    (Primrec.option_map hpop hresult).of_eq fun input ↦ by
      cases hpopValue :
          popManyTagged formulaValueTag input.1 input.2 <;>
        simp [postfixBranch11, hpopValue]

theorem postfixFormulaSequentProofBranch_primrec (ruleTag : Nat) :
    Primrec₂ (postfixFormulaSequentProofBranch ruleTag) := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  let Popped := Nat × List Nat
  have hpopFormula : Primrec (fun input : Input ↦
      popTagged formulaValueTag input.2) :=
    popTagged_primrec.comp (Primrec.const formulaValueTag) Primrec.snd
  have hcontinue : Primrec₂ (fun (input : Input) (formula : Popped) ↦ do
      let (sequent, stack) ← popTagged sequentValueTag formula.2
      let raw :=
        Nat.pair sequent (Nat.pair ruleTag formula.1) + 1
      pure (pushProof raw sequent stack)) := by
    apply Primrec₂.mk
    let ContinueInput := Input × Popped
    have hpopSequent : Primrec (fun q : ContinueInput ↦
        popTagged sequentValueTag q.2.2) :=
      popTagged_primrec.comp (Primrec.const sequentValueTag)
        (Primrec.snd.comp Primrec.snd)
    have hformula : Primrec₂ (fun (q : ContinueInput) (_ : Popped) ↦
        q.2.1) :=
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).to₂
    have hsequent : Primrec₂ (fun (_ : ContinueInput) (seq : Popped) ↦
        seq.1) :=
      (Primrec.fst.comp Primrec.snd).to₂
    have htail : Primrec₂ (fun (_ : ContinueInput) (seq : Popped) ↦
        seq.2) :=
      (Primrec.snd.comp Primrec.snd).to₂
    have hruleFormula : Primrec₂
        (fun (q : ContinueInput) (seq : Popped) ↦
          Nat.pair ruleTag q.2.1) :=
      Primrec₂.natPair.comp₂ (Primrec₂.const ruleTag) hformula
    have hraw : Primrec₂ (fun (q : ContinueInput) (seq : Popped) ↦
        Nat.pair seq.1 (Nat.pair ruleTag q.2.1) + 1) :=
      Primrec.succ.comp₂
        (Primrec₂.natPair.comp₂ hsequent hruleFormula)
    have hrawSequent : Primrec₂
        (fun (q : ContinueInput) (seq : Popped) ↦
          (Nat.pair seq.1 (Nat.pair ruleTag q.2.1) + 1,
            seq.1)) :=
      Primrec₂.pair.comp₂ hraw hsequent
    have hresult : Primrec₂ (fun (q : ContinueInput) (seq : Popped) ↦
        pushProof
          (Nat.pair seq.1 (Nat.pair ruleTag q.2.1) + 1)
          seq.1 seq.2) :=
      pushProof_primrec.comp₂ hrawSequent htail
    exact
      (Primrec.option_map hpopSequent hresult).of_eq fun q ↦ by
        cases hpopValue : popTagged sequentValueTag q.2.2 <;>
          simp [hpopValue]
  exact
    (Primrec.option_bind hpopFormula hcontinue).of_eq fun input ↦ by
      cases hpopValue : popTagged formulaValueTag input.2 <;>
        simp [postfixFormulaSequentProofBranch, hpopValue]

theorem postfixBranch12_primrec : Primrec₂ postfixBranch12 := by
  exact postfixFormulaSequentProofBranch_primrec 0

theorem postfixBranch13_primrec : Primrec₂ postfixBranch13 := by
  exact postfixFormulaSequentProofBranch_primrec 9

theorem postfixBranch14_primrec : Primrec₂ postfixBranch14 := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  let Popped := Nat × List Nat
  have hpop : Primrec (fun input : Input ↦
      popTagged sequentValueTag input.2) :=
    popTagged_primrec.comp (Primrec.const sequentValueTag) Primrec.snd
  have hsequent : Primrec₂ (fun (_ : Input) (seq : Popped) ↦
      seq.1) :=
    (Primrec.fst.comp Primrec.snd).to₂
  have htail : Primrec₂ (fun (_ : Input) (seq : Popped) ↦
      seq.2) :=
    (Primrec.snd.comp Primrec.snd).to₂
  have hrawRest : Primrec₂ (fun (_ : Input) (_ : Popped) ↦
      Nat.pair 1 0) :=
    Primrec₂.const (Nat.pair 1 0)
  have hraw : Primrec₂ (fun (_ : Input) (seq : Popped) ↦
      Nat.pair seq.1 (Nat.pair 1 0) + 1) :=
    Primrec.succ.comp₂
      (Primrec₂.natPair.comp₂ hsequent hrawRest)
  have hrawSequent : Primrec₂ (fun (_ : Input) (seq : Popped) ↦
      (Nat.pair seq.1 (Nat.pair 1 0) + 1, seq.1)) :=
    Primrec₂.pair.comp₂ hraw hsequent
  have hresult : Primrec₂ (fun (_ : Input) (seq : Popped) ↦
      pushProof
        (Nat.pair seq.1 (Nat.pair 1 0) + 1) seq.1 seq.2) :=
    pushProof_primrec.comp₂ hrawSequent htail
  exact
    (Primrec.option_map hpop hresult).of_eq fun input ↦ by
      cases hpopValue : popTagged sequentValueTag input.2 <;>
        simp [postfixBranch14, hpopValue]

theorem postfixUnaryProofBranch_primrec (ruleTag : Nat) :
    Primrec₂ (postfixUnaryProofBranch ruleTag) := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  let Popped := Nat × List Nat
  have hpopPremise : Primrec (fun input : Input ↦
      popTagged proofValueTag input.2) :=
    popTagged_primrec.comp (Primrec.const proofValueTag) Primrec.snd
  have hcontinue : Primrec₂ (fun (input : Input) (premise : Popped) ↦ do
      let (sequent, stack) ← popTagged sequentValueTag premise.2
      let raw :=
        Nat.pair sequent (Nat.pair ruleTag premise.1.unpair.1) + 1
      pure (pushProof raw sequent stack)) := by
    apply Primrec₂.mk
    let ContinueInput := Input × Popped
    have hpopSequent : Primrec (fun q : ContinueInput ↦
        popTagged sequentValueTag q.2.2) :=
      popTagged_primrec.comp (Primrec.const sequentValueTag)
        (Primrec.snd.comp Primrec.snd)
    have hpremiseRaw : Primrec₂
        (fun (q : ContinueInput) (_ : Popped) ↦ q.2.1.unpair.1) :=
      (Primrec.fst.comp
        (Primrec.unpair.comp
          (Primrec.fst.comp
            (Primrec.snd.comp Primrec.fst)))).to₂
    have hsequent : Primrec₂ (fun (_ : ContinueInput) (seq : Popped) ↦
        seq.1) :=
      (Primrec.fst.comp Primrec.snd).to₂
    have htail : Primrec₂ (fun (_ : ContinueInput) (seq : Popped) ↦
        seq.2) :=
      (Primrec.snd.comp Primrec.snd).to₂
    have hrulePremise : Primrec₂
        (fun (q : ContinueInput) (seq : Popped) ↦
          Nat.pair ruleTag q.2.1.unpair.1) :=
      Primrec₂.natPair.comp₂ (Primrec₂.const ruleTag) hpremiseRaw
    have hraw : Primrec₂ (fun (q : ContinueInput) (seq : Popped) ↦
        Nat.pair seq.1 (Nat.pair ruleTag q.2.1.unpair.1) + 1) :=
      Primrec.succ.comp₂
        (Primrec₂.natPair.comp₂ hsequent hrulePremise)
    have hrawSequent : Primrec₂
        (fun (q : ContinueInput) (seq : Popped) ↦
          (Nat.pair seq.1 (Nat.pair ruleTag q.2.1.unpair.1) + 1,
            seq.1)) :=
      Primrec₂.pair.comp₂ hraw hsequent
    have hresult : Primrec₂ (fun (q : ContinueInput) (seq : Popped) ↦
        pushProof
          (Nat.pair seq.1 (Nat.pair ruleTag q.2.1.unpair.1) + 1)
          seq.1 seq.2) :=
      pushProof_primrec.comp₂ hrawSequent htail
    exact
      (Primrec.option_map hpopSequent hresult).of_eq fun q ↦ by
        cases hpopValue : popTagged sequentValueTag q.2.2 <;>
          simp [hpopValue]
  exact
    (Primrec.option_bind hpopPremise hcontinue).of_eq fun input ↦ by
      cases hpopValue : popTagged proofValueTag input.2 <;>
        simp [postfixUnaryProofBranch, hpopValue]

theorem postfixBranch19_primrec : Primrec₂ postfixBranch19 := by
  exact postfixUnaryProofBranch_primrec 6

theorem postfixBranch20_primrec : Primrec₂ postfixBranch20 := by
  exact postfixUnaryProofBranch_primrec 7

theorem postfixBranch17_primrec : Primrec₂ postfixBranch17 := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  let Popped := Nat × List Nat
  have hpopPremise : Primrec (fun input : Input ↦
      popTagged proofValueTag input.2) :=
    popTagged_primrec.comp (Primrec.const proofValueTag) Primrec.snd
  have hcontinueFormula :
      Primrec₂ (fun (input : Input) (premise : Popped) ↦ do
        let (formula, stack) ← popTagged formulaValueTag premise.2
        let (sequent, stack) ← popTagged sequentValueTag stack
        pure
          (pushProof
            (rawProofAll sequent formula premise.1.unpair.1)
            sequent stack)) := by
    apply Primrec₂.mk
    let PremiseInput := Input × Popped
    have hpopFormula : Primrec (fun q : PremiseInput ↦
        popTagged formulaValueTag q.2.2) :=
      popTagged_primrec.comp (Primrec.const formulaValueTag)
        (Primrec.snd.comp Primrec.snd)
    have hcontinueSequent :
        Primrec₂ (fun (q : PremiseInput) (formula : Popped) ↦ do
          let (sequent, stack) ← popTagged sequentValueTag formula.2
          pure
            (pushProof
              (rawProofAll sequent formula.1 q.2.1.unpair.1)
              sequent stack)) := by
      apply Primrec₂.mk
      let FormulaInput := PremiseInput × Popped
      have hpopSequent : Primrec (fun r : FormulaInput ↦
          popTagged sequentValueTag r.2.2) :=
        popTagged_primrec.comp (Primrec.const sequentValueTag)
          (Primrec.snd.comp Primrec.snd)
      have hpremiseRaw : Primrec₂
          (fun (r : FormulaInput) (_ : Popped) ↦
            r.1.2.1.unpair.1) :=
        (Primrec.fst.comp
          (Primrec.unpair.comp
            (Primrec.fst.comp
              (Primrec.snd.comp
                (Primrec.fst.comp Primrec.fst))))).to₂
      have hformula : Primrec₂
          (fun (r : FormulaInput) (_ : Popped) ↦ r.2.1) :=
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).to₂
      have hsequent : Primrec₂
          (fun (_ : FormulaInput) (seq : Popped) ↦ seq.1) :=
        (Primrec.fst.comp Primrec.snd).to₂
      have htail : Primrec₂
          (fun (_ : FormulaInput) (seq : Popped) ↦ seq.2) :=
        (Primrec.snd.comp Primrec.snd).to₂
      have hformulaPremise : Primrec₂
          (fun (r : FormulaInput) (seq : Popped) ↦
            Nat.pair r.2.1 r.1.2.1.unpair.1) :=
        Primrec₂.natPair.comp₂ hformula hpremiseRaw
      have hruleRest : Primrec₂
          (fun (r : FormulaInput) (seq : Popped) ↦
            Nat.pair 4 (Nat.pair r.2.1 r.1.2.1.unpair.1)) :=
        Primrec₂.natPair.comp₂ (Primrec₂.const 4) hformulaPremise
      have hraw : Primrec₂
          (fun (r : FormulaInput) (seq : Popped) ↦
            Nat.pair seq.1
              (Nat.pair 4
                (Nat.pair r.2.1 r.1.2.1.unpair.1)) + 1) :=
        Primrec.succ.comp₂
          (Primrec₂.natPair.comp₂ hsequent hruleRest)
      have hrawSequent : Primrec₂
          (fun (r : FormulaInput) (seq : Popped) ↦
            (Nat.pair seq.1
                (Nat.pair 4
                  (Nat.pair r.2.1 r.1.2.1.unpair.1)) + 1,
              seq.1)) :=
        Primrec₂.pair.comp₂ hraw hsequent
      have hresult : Primrec₂
          (fun (r : FormulaInput) (seq : Popped) ↦
            pushProof
              (rawProofAll seq.1 r.2.1 r.1.2.1.unpair.1)
              seq.1 seq.2) := by
        exact
          (pushProof_primrec.comp₂ hrawSequent htail).of_eq
            fun _ _ ↦ rfl
      exact
        (Primrec.option_map hpopSequent hresult).of_eq fun r ↦ by
          cases hpopValue : popTagged sequentValueTag r.2.2 <;>
            simp [hpopValue]
    exact
      (Primrec.option_bind hpopFormula hcontinueSequent).of_eq
        fun q ↦ by
          cases hpopValue : popTagged formulaValueTag q.2.2 <;>
            simp [hpopValue]
  exact
    (Primrec.option_bind hpopPremise hcontinueFormula).of_eq
      fun input ↦ by
        cases hpopValue : popTagged proofValueTag input.2 <;>
          simp [postfixBranch17, hpopValue]

theorem popTaggedPatternStep_primrec :
    Primrec₂ popTaggedPatternStep := by
  apply Primrec₂.mk
  let State := List Nat × List Nat
  let Input := Option State × Nat
  have hcontinueState : Primrec₂
      (fun (input : Input) (state : State) ↦ do
        let (payload, stack) ← popTagged input.2 state.2
        pure (payload :: state.1, stack)) := by
    apply Primrec₂.mk
    let StateInput := Input × State
    let Popped := Nat × List Nat
    have hpop : Primrec (fun q : StateInput ↦
        popTagged q.1.2 q.2.2) :=
      popTagged_primrec.comp
        (Primrec.snd.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd)
    have hpayloads : Primrec₂
        (fun (q : StateInput) (_ : Popped) ↦ q.2.1) :=
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).to₂
    have hpayload : Primrec₂
        (fun (_ : StateInput) (popped : Popped) ↦ popped.1) :=
      (Primrec.fst.comp Primrec.snd).to₂
    have htail : Primrec₂
        (fun (_ : StateInput) (popped : Popped) ↦ popped.2) :=
      (Primrec.snd.comp Primrec.snd).to₂
    have hcons : Primrec₂
        (fun (q : StateInput) (popped : Popped) ↦
          popped.1 :: q.2.1) :=
      Primrec.list_cons.comp₂ hpayload hpayloads
    have hresult : Primrec₂
        (fun (q : StateInput) (popped : Popped) ↦
          (popped.1 :: q.2.1, popped.2)) :=
      Primrec₂.pair.comp₂ hcons htail
    exact
      (Primrec.option_map hpop hresult).of_eq fun q ↦ by
        cases hpopValue : popTagged q.1.2 q.2.2 <;>
          simp [hpopValue]
  exact
    (Primrec.option_bind Primrec.fst hcontinueState).of_eq
      fun input ↦ by
        cases hstate : input.1 <;>
          simp [popTaggedPatternStep, hstate]

theorem popTaggedPattern_primrec : Primrec₂ popTaggedPattern := by
  apply Primrec₂.mk
  let State := List Nat × List Nat
  let Input := List Nat × List Nat
  have hinitial : Primrec (fun input : Input ↦
      some (([], input.2) : State)) :=
    Primrec.option_some.comp
      (Primrec.pair (Primrec.const []) Primrec.snd)
  have hstep : Primrec₂
      (fun (_ : Input) (stateTag : Option State × Nat) ↦
        popTaggedPatternStep stateTag.1 stateTag.2) :=
    (popTaggedPatternStep_primrec.comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂
  have hfold : Primrec (fun input : Input ↦
      input.1.foldl popTaggedPatternStep
        (some ([], input.2))) :=
    Primrec.list_foldl Primrec.fst hinitial hstep
  have hresult : Primrec₂
      (fun (_ : Input) (state : State) ↦
        (state.1.reverse, state.2)) :=
    Primrec₂.pair.comp₂
      ((Primrec.list_reverse.comp
        (Primrec.fst.comp Primrec.snd)).to₂)
      ((Primrec.snd.comp Primrec.snd).to₂)
  exact
    (Primrec.option_map hfold hresult).of_eq fun input ↦ by
      rfl

theorem postfixOneProofTwoSyntaxBranch_primrec
    (ruleTag firstTag secondTag : Nat) :
    Primrec₂
      (postfixOneProofTwoSyntaxBranch ruleTag firstTag secondTag) := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  let Popped := List Nat × List Nat
  have hpop : Primrec (fun input : Input ↦
      popTaggedPattern
        [proofValueTag, firstTag, secondTag, sequentValueTag]
        input.2) :=
    popTaggedPattern_primrec.comp
      (Primrec.const
        [proofValueTag, firstTag, secondTag, sequentValueTag])
      Primrec.snd
  have hvalues : Primrec₂
      (fun (_ : Input) (popped : Popped) ↦ popped.1) :=
    (Primrec.fst.comp Primrec.snd).to₂
  have hvalue (index : Nat) : Primrec₂
      (fun (_ : Input) (popped : Popped) ↦
        popped.1.getD index 0) :=
    (Primrec.list_getD 0).comp₂ hvalues (Primrec₂.const index)
  have hpremiseRaw : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        (popped.1.getD 0 0).unpair.1) :=
    Primrec.fst.comp₂ (Primrec.unpair.comp₂ (hvalue 0))
  have hfirstPremise : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        Nat.pair (popped.1.getD 1 0)
          (popped.1.getD 0 0).unpair.1) :=
    Primrec₂.natPair.comp₂ (hvalue 1) hpremiseRaw
  have hsecondRest : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        Nat.pair (popped.1.getD 2 0)
          (Nat.pair (popped.1.getD 1 0)
            (popped.1.getD 0 0).unpair.1)) :=
    Primrec₂.natPair.comp₂ (hvalue 2) hfirstPremise
  have hruleRest : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        Nat.pair ruleTag
          (Nat.pair (popped.1.getD 2 0)
            (Nat.pair (popped.1.getD 1 0)
              (popped.1.getD 0 0).unpair.1))) :=
    Primrec₂.natPair.comp₂ (Primrec₂.const ruleTag) hsecondRest
  have hraw : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        Nat.pair (popped.1.getD 3 0)
          (Nat.pair ruleTag
            (Nat.pair (popped.1.getD 2 0)
              (Nat.pair (popped.1.getD 1 0)
                (popped.1.getD 0 0).unpair.1))) + 1) :=
    Primrec.succ.comp₂
      (Primrec₂.natPair.comp₂ (hvalue 3) hruleRest)
  have hrawSequent : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        (Nat.pair (popped.1.getD 3 0)
            (Nat.pair ruleTag
              (Nat.pair (popped.1.getD 2 0)
                (Nat.pair (popped.1.getD 1 0)
                  (popped.1.getD 0 0).unpair.1))) + 1,
          popped.1.getD 3 0)) :=
    Primrec₂.pair.comp₂ hraw (hvalue 3)
  have htail : Primrec₂
      (fun (_ : Input) (popped : Popped) ↦ popped.2) :=
    (Primrec.snd.comp Primrec.snd).to₂
  have hresult : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        pushProof
          (Nat.pair (popped.1.getD 3 0)
            (Nat.pair ruleTag
              (Nat.pair (popped.1.getD 2 0)
                (Nat.pair (popped.1.getD 1 0)
                  (popped.1.getD 0 0).unpair.1))) + 1)
          (popped.1.getD 3 0) popped.2) :=
    pushProof_primrec.comp₂ hrawSequent htail
  exact
    (Primrec.option_map hpop hresult).of_eq fun input ↦ by
      cases hpopValue :
          popTaggedPattern
            [proofValueTag, firstTag, secondTag, sequentValueTag]
            input.2 <;>
        simp [postfixOneProofTwoSyntaxBranch, hpopValue]

theorem postfixBranch16_primrec : Primrec₂ postfixBranch16 := by
  exact
    postfixOneProofTwoSyntaxBranch_primrec
      3 formulaValueTag formulaValueTag

theorem postfixBranch18_primrec : Primrec₂ postfixBranch18 := by
  exact
    postfixOneProofTwoSyntaxBranch_primrec
      5 termValueTag formulaValueTag

end FoundationEfficientPAProofPredicateRepresentation
