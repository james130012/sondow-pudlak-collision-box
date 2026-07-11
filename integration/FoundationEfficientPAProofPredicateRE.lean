import integration.FoundationEfficientPAProofPredicateRepresentation

/-!
# Recursive-enumerability of the efficient PA proof predicate

This layer closes the two remaining multi-premise postfix instructions, proves
the full verifier primitive recursive, and arithmetizes its proof predicate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

namespace FoundationEfficientPAProofPredicateRE

open FoundationSuccinctFiniteConsistencyTarget
open FoundationEfficientPAProofPredicateArithmetic
open FoundationEfficientPAProofPredicateRepresentation
open Primrec

def postfixBranch21 (_payload : Nat) (stack : List Nat) :
    Option (List Nat) := do
  let (values, stack) ←
    popTaggedPattern
      [proofValueTag, proofValueTag, formulaValueTag, sequentValueTag]
      stack
  let right := values.getD 0 0
  let left := values.getD 1 0
  let formula := values.getD 2 0
  let sequent := values.getD 3 0
  pure
    (pushProof
      (rawProofCut sequent formula left.unpair.1 right.unpair.1)
      sequent stack)

def postfixBranch15 (_payload : Nat) (stack : List Nat) :
    Option (List Nat) := do
  let (values, stack) ←
    popTaggedPattern
      [proofValueTag, proofValueTag, formulaValueTag,
        formulaValueTag, sequentValueTag]
      stack
  let rightProof := values.getD 0 0
  let leftProof := values.getD 1 0
  let rightFormula := values.getD 2 0
  let leftFormula := values.getD 3 0
  let sequent := values.getD 4 0
  pure
    (pushProof
      (rawProofAnd sequent leftFormula rightFormula
        leftProof.unpair.1 rightProof.unpair.1)
      sequent stack)

theorem postfixBranch21_primrec : Primrec₂ postfixBranch21 := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  let Popped := List Nat × List Nat
  have hpop : Primrec (fun input : Input ↦
      popTaggedPattern
        [proofValueTag, proofValueTag, formulaValueTag, sequentValueTag]
        input.2) :=
    popTaggedPattern_primrec.comp
      (Primrec.const
        [proofValueTag, proofValueTag, formulaValueTag, sequentValueTag])
      Primrec.snd
  have hvalues : Primrec₂
      (fun (_ : Input) (popped : Popped) ↦ popped.1) :=
    (Primrec.fst.comp Primrec.snd).to₂
  have hvalue (index : Nat) : Primrec₂
      (fun (_ : Input) (popped : Popped) ↦
        popped.1.getD index 0) :=
    (Primrec.list_getD 0).comp₂ hvalues (Primrec₂.const index)
  have hproofRaw (index : Nat) : Primrec₂
      (fun (_ : Input) (popped : Popped) ↦
        (popped.1.getD index 0).unpair.1) :=
    Primrec.fst.comp₂ (Primrec.unpair.comp₂ (hvalue index))
  have hproofs : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        Nat.pair (popped.1.getD 1 0).unpair.1
          (popped.1.getD 0 0).unpair.1) :=
    Primrec₂.natPair.comp₂ (hproofRaw 1) (hproofRaw 0)
  have hformulaProofs : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        Nat.pair (popped.1.getD 2 0)
          (Nat.pair (popped.1.getD 1 0).unpair.1
            (popped.1.getD 0 0).unpair.1)) :=
    Primrec₂.natPair.comp₂ (hvalue 2) hproofs
  have hruleRest : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        Nat.pair 8
          (Nat.pair (popped.1.getD 2 0)
            (Nat.pair (popped.1.getD 1 0).unpair.1
              (popped.1.getD 0 0).unpair.1))) :=
    Primrec₂.natPair.comp₂ (Primrec₂.const 8) hformulaProofs
  have hraw : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        Nat.pair (popped.1.getD 3 0)
          (Nat.pair 8
            (Nat.pair (popped.1.getD 2 0)
              (Nat.pair (popped.1.getD 1 0).unpair.1
                (popped.1.getD 0 0).unpair.1))) + 1) :=
    Primrec.succ.comp₂
      (Primrec₂.natPair.comp₂ (hvalue 3) hruleRest)
  have hrawSequent : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        (Nat.pair (popped.1.getD 3 0)
            (Nat.pair 8
              (Nat.pair (popped.1.getD 2 0)
                (Nat.pair (popped.1.getD 1 0).unpair.1
                  (popped.1.getD 0 0).unpair.1))) + 1,
          popped.1.getD 3 0)) :=
    Primrec₂.pair.comp₂ hraw (hvalue 3)
  have htail : Primrec₂
      (fun (_ : Input) (popped : Popped) ↦ popped.2) :=
    (Primrec.snd.comp Primrec.snd).to₂
  have hresult : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        pushProof
          (rawProofCut (popped.1.getD 3 0)
            (popped.1.getD 2 0)
            (popped.1.getD 1 0).unpair.1
            (popped.1.getD 0 0).unpair.1)
          (popped.1.getD 3 0) popped.2) :=
    (pushProof_primrec.comp₂ hrawSequent htail).of_eq fun _ _ ↦ rfl
  exact
    (Primrec.option_map hpop hresult).of_eq fun input ↦ by
      cases hpopValue :
          popTaggedPattern
            [proofValueTag, proofValueTag, formulaValueTag,
              sequentValueTag]
            input.2 <;>
        simp [postfixBranch21, hpopValue]

theorem postfixBranch15_primrec : Primrec₂ postfixBranch15 := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  let Popped := List Nat × List Nat
  have hpop : Primrec (fun input : Input ↦
      popTaggedPattern
        [proofValueTag, proofValueTag, formulaValueTag,
          formulaValueTag, sequentValueTag]
        input.2) :=
    popTaggedPattern_primrec.comp
      (Primrec.const
        [proofValueTag, proofValueTag, formulaValueTag,
          formulaValueTag, sequentValueTag])
      Primrec.snd
  have hvalues : Primrec₂
      (fun (_ : Input) (popped : Popped) ↦ popped.1) :=
    (Primrec.fst.comp Primrec.snd).to₂
  have hvalue (index : Nat) : Primrec₂
      (fun (_ : Input) (popped : Popped) ↦
        popped.1.getD index 0) :=
    (Primrec.list_getD 0).comp₂ hvalues (Primrec₂.const index)
  have hproofRaw (index : Nat) : Primrec₂
      (fun (_ : Input) (popped : Popped) ↦
        (popped.1.getD index 0).unpair.1) :=
    Primrec.fst.comp₂ (Primrec.unpair.comp₂ (hvalue index))
  have hproofs : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        Nat.pair (popped.1.getD 1 0).unpair.1
          (popped.1.getD 0 0).unpair.1) :=
    Primrec₂.natPair.comp₂ (hproofRaw 1) (hproofRaw 0)
  have hrightProofs : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        Nat.pair (popped.1.getD 2 0)
          (Nat.pair (popped.1.getD 1 0).unpair.1
            (popped.1.getD 0 0).unpair.1)) :=
    Primrec₂.natPair.comp₂ (hvalue 2) hproofs
  have hleftRest : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        Nat.pair (popped.1.getD 3 0)
          (Nat.pair (popped.1.getD 2 0)
            (Nat.pair (popped.1.getD 1 0).unpair.1
              (popped.1.getD 0 0).unpair.1))) :=
    Primrec₂.natPair.comp₂ (hvalue 3) hrightProofs
  have hruleRest : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        Nat.pair 2
          (Nat.pair (popped.1.getD 3 0)
            (Nat.pair (popped.1.getD 2 0)
              (Nat.pair (popped.1.getD 1 0).unpair.1
                (popped.1.getD 0 0).unpair.1)))) :=
    Primrec₂.natPair.comp₂ (Primrec₂.const 2) hleftRest
  have hraw : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        Nat.pair (popped.1.getD 4 0)
          (Nat.pair 2
            (Nat.pair (popped.1.getD 3 0)
              (Nat.pair (popped.1.getD 2 0)
                (Nat.pair (popped.1.getD 1 0).unpair.1
                  (popped.1.getD 0 0).unpair.1)))) + 1) :=
    Primrec.succ.comp₂
      (Primrec₂.natPair.comp₂ (hvalue 4) hruleRest)
  have hrawSequent : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        (Nat.pair (popped.1.getD 4 0)
            (Nat.pair 2
              (Nat.pair (popped.1.getD 3 0)
                (Nat.pair (popped.1.getD 2 0)
                  (Nat.pair (popped.1.getD 1 0).unpair.1
                    (popped.1.getD 0 0).unpair.1)))) + 1,
          popped.1.getD 4 0)) :=
    Primrec₂.pair.comp₂ hraw (hvalue 4)
  have htail : Primrec₂
      (fun (_ : Input) (popped : Popped) ↦ popped.2) :=
    (Primrec.snd.comp Primrec.snd).to₂
  have hresult : Primrec₂
      (fun (input : Input) (popped : Popped) ↦
        pushProof
          (rawProofAnd (popped.1.getD 4 0)
            (popped.1.getD 3 0) (popped.1.getD 2 0)
            (popped.1.getD 1 0).unpair.1
            (popped.1.getD 0 0).unpair.1)
          (popped.1.getD 4 0) popped.2) :=
    (pushProof_primrec.comp₂ hrawSequent htail).of_eq fun _ _ ↦ rfl
  exact
    (Primrec.option_map hpop hresult).of_eq fun input ↦ by
      cases hpopValue :
          popTaggedPattern
            [proofValueTag, proofValueTag, formulaValueTag,
              formulaValueTag, sequentValueTag]
            input.2 <;>
        simp [postfixBranch15, hpopValue]

def postfixHandlerTable (payload : Nat) (stack : List Nat) :
    List (Option (List Nat)) :=
  [ postfixBranch0 payload stack,
    postfixBranch1 payload stack,
    postfixBranch2 payload stack,
    postfixBranch3 payload stack,
    postfixBranch4 payload stack,
    postfixBranch5 payload stack,
    postfixBranch6 payload stack,
    postfixBranch7 payload stack,
    postfixBranch8 payload stack,
    postfixBranch9 payload stack,
    postfixBranch10 payload stack,
    postfixBranch11 payload stack,
    postfixBranch12 payload stack,
    postfixBranch13 payload stack,
    postfixBranch14 payload stack,
    postfixBranch15 payload stack,
    postfixBranch16 payload stack,
    postfixBranch17 payload stack,
    postfixBranch18 payload stack,
    postfixBranch19 payload stack,
    postfixBranch20 payload stack,
    postfixBranch21 payload stack ]

theorem postfixHandlerTable_primrec : Primrec₂ postfixHandlerTable := by
  exact
    (Primrec.list_cons.comp₂ postfixBranch0_primrec
      (Primrec.list_cons.comp₂ postfixBranch1_primrec
      (Primrec.list_cons.comp₂ postfixBranch2_primrec
      (Primrec.list_cons.comp₂ postfixBranch3_primrec
      (Primrec.list_cons.comp₂ postfixBranch4_primrec
      (Primrec.list_cons.comp₂ postfixBranch5_primrec
      (Primrec.list_cons.comp₂ postfixBranch6_primrec
      (Primrec.list_cons.comp₂ postfixBranch7_primrec
      (Primrec.list_cons.comp₂ postfixBranch8_primrec
      (Primrec.list_cons.comp₂ postfixBranch9_primrec
      (Primrec.list_cons.comp₂ postfixBranch10_primrec
      (Primrec.list_cons.comp₂ postfixBranch11_primrec
      (Primrec.list_cons.comp₂ postfixBranch12_primrec
      (Primrec.list_cons.comp₂ postfixBranch13_primrec
      (Primrec.list_cons.comp₂ postfixBranch14_primrec
      (Primrec.list_cons.comp₂ postfixBranch15_primrec
      (Primrec.list_cons.comp₂ postfixBranch16_primrec
      (Primrec.list_cons.comp₂ postfixBranch17_primrec
      (Primrec.list_cons.comp₂ postfixBranch18_primrec
      (Primrec.list_cons.comp₂ postfixBranch19_primrec
      (Primrec.list_cons.comp₂ postfixBranch20_primrec
      (Primrec.list_cons.comp₂ postfixBranch21_primrec
        (Primrec₂.const []))))))))))))))))))))))).of_eq
      fun _ _ ↦ rfl

def optionListGet
    (values : List (Option (List Nat))) (index : Nat) :
    Option (Option (List Nat)) :=
  values[index]?

theorem optionListGet_primrec : Primrec₂ optionListGet := by
  exact Primrec.list_getElem?

def postfixTableStep (tok : Nat) (stack : List Nat) :
    Option (List Nat) :=
  (optionListGet (postfixHandlerTable tok.unpair.2 stack)
    tok.unpair.1).join

theorem optionJoin_primrec :
    Primrec (@Option.join (List Nat)) := by
  exact
    (Primrec.option_casesOn Primrec.id
      (Primrec.const none) Primrec₂.right).of_eq fun value ↦ by
        cases value <;> rfl

theorem postfixTableStep_primrec : Primrec₂ postfixTableStep := by
  have htag : Primrec₂
      (fun (tok : Nat) (_ : List Nat) ↦ tok.unpair.1) :=
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)).to₂
  have hpayload : Primrec₂
      (fun (tok : Nat) (_ : List Nat) ↦ tok.unpair.2) :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)).to₂
  have htable : Primrec₂ (fun (tok : Nat) (stack : List Nat) ↦
      postfixHandlerTable tok.unpair.2 stack) :=
    postfixHandlerTable_primrec.comp₂ hpayload Primrec₂.right
  have hlookup : Primrec₂ (fun (tok : Nat) (stack : List Nat) ↦
      optionListGet (postfixHandlerTable tok.unpair.2 stack)
        tok.unpair.1) :=
    optionListGet_primrec.comp₂ htable htag
  exact
    (optionJoin_primrec.comp₂ hlookup).of_eq fun _ _ ↦ rfl

def postfixBranch16Direct (_payload : Nat) (stack : List Nat) :
    Option (List Nat) := do
  let (premise, stack) ← popTagged proofValueTag stack
  let (rightFormula, stack) ← popTagged formulaValueTag stack
  let (leftFormula, stack) ← popTagged formulaValueTag stack
  let (sequent, stack) ← popTagged sequentValueTag stack
  pure
    (pushProof
      (rawProofOr sequent leftFormula rightFormula premise.unpair.1)
      sequent stack)

theorem postfixBranch16_eq_direct (payload : Nat) (stack : List Nat) :
    postfixBranch16 payload stack = postfixBranch16Direct payload stack := by
  cases h0 : popTagged proofValueTag stack with
  | none =>
      simp [postfixBranch16, postfixOneProofTwoSyntaxBranch,
        postfixBranch16Direct, popTaggedPattern,
        popTaggedPatternStep, h0]
  | some premise =>
      rcases premise with ⟨premise, stack⟩
      cases h1 : popTagged formulaValueTag stack with
      | none =>
          simp [postfixBranch16, postfixOneProofTwoSyntaxBranch,
            postfixBranch16Direct, popTaggedPattern,
            popTaggedPatternStep, h0, h1]
      | some right =>
          rcases right with ⟨right, stack⟩
          cases h2 : popTagged formulaValueTag stack with
          | none =>
              simp [postfixBranch16, postfixOneProofTwoSyntaxBranch,
                postfixBranch16Direct, popTaggedPattern,
                popTaggedPatternStep, h0, h1, h2]
          | some left =>
              rcases left with ⟨left, stack⟩
              cases h3 : popTagged sequentValueTag stack with
              | none =>
                  simp [postfixBranch16,
                    postfixOneProofTwoSyntaxBranch,
                    postfixBranch16Direct, popTaggedPattern,
                    popTaggedPatternStep, h0, h1, h2, h3]
              | some sequent =>
                  rcases sequent with ⟨sequent, stack⟩
                  simp [postfixBranch16,
                    postfixOneProofTwoSyntaxBranch,
                    postfixBranch16Direct, popTaggedPattern,
                    popTaggedPatternStep, h0, h1, h2, h3]
                  change
                    pushProof
                        (rawProofOr sequent left right premise.unpair.1)
                        sequent stack = _
                  simp

def postfixOneProofTwoSyntaxDirect
    (ruleTag firstTag secondTag _payload : Nat)
    (stack : List Nat) : Option (List Nat) := do
  let (premise, stack) ← popTagged proofValueTag stack
  let (first, stack) ← popTagged firstTag stack
  let (second, stack) ← popTagged secondTag stack
  let (sequent, stack) ← popTagged sequentValueTag stack
  pure
    (pushProof
      (Nat.pair sequent
        (Nat.pair ruleTag
          (Nat.pair second
            (Nat.pair first premise.unpair.1))) + 1)
      sequent stack)

theorem postfixOneProofTwoSyntax_eq_direct
    (ruleTag firstTag secondTag payload : Nat) (stack : List Nat) :
    postfixOneProofTwoSyntaxBranch
        ruleTag firstTag secondTag payload stack =
      postfixOneProofTwoSyntaxDirect
        ruleTag firstTag secondTag payload stack := by
  cases h0 : popTagged proofValueTag stack with
  | none =>
      simp [postfixOneProofTwoSyntaxBranch,
        postfixOneProofTwoSyntaxDirect, popTaggedPattern,
        popTaggedPatternStep, h0]
  | some premise =>
      rcases premise with ⟨premise, stack⟩
      cases h1 : popTagged firstTag stack with
      | none =>
          simp [postfixOneProofTwoSyntaxBranch,
            postfixOneProofTwoSyntaxDirect, popTaggedPattern,
            popTaggedPatternStep, h0, h1]
      | some first =>
          rcases first with ⟨first, stack⟩
          cases h2 : popTagged secondTag stack with
          | none =>
              simp [postfixOneProofTwoSyntaxBranch,
                postfixOneProofTwoSyntaxDirect, popTaggedPattern,
                popTaggedPatternStep, h0, h1, h2]
          | some second =>
              rcases second with ⟨second, stack⟩
              cases h3 : popTagged sequentValueTag stack with
              | none =>
                  simp [postfixOneProofTwoSyntaxBranch,
                    postfixOneProofTwoSyntaxDirect, popTaggedPattern,
                    popTaggedPatternStep, h0, h1, h2, h3]
              | some sequent =>
                  rcases sequent with ⟨sequent, stack⟩
                  simp [postfixOneProofTwoSyntaxBranch,
                    postfixOneProofTwoSyntaxDirect, popTaggedPattern,
                    popTaggedPatternStep, h0, h1, h2, h3]

theorem popTaggedPattern_four
    (tag0 tag1 tag2 tag3 : Nat) (stack : List Nat) :
    popTaggedPattern [tag0, tag1, tag2, tag3] stack = (do
      let (value0, stack) ← popTagged tag0 stack
      let (value1, stack) ← popTagged tag1 stack
      let (value2, stack) ← popTagged tag2 stack
      let (value3, stack) ← popTagged tag3 stack
      pure ([value0, value1, value2, value3], stack)) := by
  cases h0 : popTagged tag0 stack with
  | none =>
      simp [popTaggedPattern, popTaggedPatternStep, h0]
  | some value0 =>
      rcases value0 with ⟨value0, stack⟩
      cases h1 : popTagged tag1 stack with
      | none =>
          simp [popTaggedPattern, popTaggedPatternStep, h0, h1]
      | some value1 =>
          rcases value1 with ⟨value1, stack⟩
          cases h2 : popTagged tag2 stack with
          | none =>
              simp [popTaggedPattern, popTaggedPatternStep,
                h0, h1, h2]
          | some value2 =>
              rcases value2 with ⟨value2, stack⟩
              cases h3 : popTagged tag3 stack with
              | none =>
                  simp [popTaggedPattern, popTaggedPatternStep,
                    h0, h1, h2, h3]
              | some value3 =>
                  rcases value3 with ⟨value3, stack⟩
                  simp [popTaggedPattern, popTaggedPatternStep,
                    h0, h1, h2, h3]

theorem popTaggedPattern_five
    (tag0 tag1 tag2 tag3 tag4 : Nat) (stack : List Nat) :
    popTaggedPattern [tag0, tag1, tag2, tag3, tag4] stack = (do
      let (value0, stack) ← popTagged tag0 stack
      let (value1, stack) ← popTagged tag1 stack
      let (value2, stack) ← popTagged tag2 stack
      let (value3, stack) ← popTagged tag3 stack
      let (value4, stack) ← popTagged tag4 stack
      pure ([value0, value1, value2, value3, value4], stack)) := by
  cases h0 : popTagged tag0 stack with
  | none =>
      simp [popTaggedPattern, popTaggedPatternStep, h0]
  | some value0 =>
      rcases value0 with ⟨value0, stack⟩
      cases h1 : popTagged tag1 stack with
      | none =>
          simp [popTaggedPattern, popTaggedPatternStep, h0, h1]
      | some value1 =>
          rcases value1 with ⟨value1, stack⟩
          cases h2 : popTagged tag2 stack with
          | none =>
              simp [popTaggedPattern, popTaggedPatternStep,
                h0, h1, h2]
          | some value2 =>
              rcases value2 with ⟨value2, stack⟩
              cases h3 : popTagged tag3 stack with
              | none =>
                  simp [popTaggedPattern, popTaggedPatternStep,
                    h0, h1, h2, h3]
              | some value3 =>
                  rcases value3 with ⟨value3, stack⟩
                  cases h4 : popTagged tag4 stack with
                  | none =>
                      simp [popTaggedPattern, popTaggedPatternStep,
                        h0, h1, h2, h3, h4]
                  | some value4 =>
                      rcases value4 with ⟨value4, stack⟩
                      simp [popTaggedPattern, popTaggedPatternStep,
                        h0, h1, h2, h3, h4]

def postfixBranch21Direct (_payload : Nat) (stack : List Nat) :
    Option (List Nat) := do
  let (right, stack) ← popTagged proofValueTag stack
  let (left, stack) ← popTagged proofValueTag stack
  let (formula, stack) ← popTagged formulaValueTag stack
  let (sequent, stack) ← popTagged sequentValueTag stack
  pure
    (pushProof
      (rawProofCut sequent formula left.unpair.1 right.unpair.1)
      sequent stack)

theorem postfixBranch21_eq_direct (payload : Nat) (stack : List Nat) :
    postfixBranch21 payload stack = postfixBranch21Direct payload stack := by
  cases h0 : popTagged proofValueTag stack with
  | none =>
      simp [postfixBranch21, postfixBranch21Direct,
        popTaggedPattern_four, h0]
  | some right =>
      rcases right with ⟨right, stack⟩
      cases h1 : popTagged proofValueTag stack with
      | none =>
          simp [postfixBranch21, postfixBranch21Direct,
            popTaggedPattern_four, h0, h1]
      | some left =>
          rcases left with ⟨left, stack⟩
          cases h2 : popTagged formulaValueTag stack with
          | none =>
              simp [postfixBranch21, postfixBranch21Direct,
                popTaggedPattern_four, h0, h1, h2]
          | some formula =>
              rcases formula with ⟨formula, stack⟩
              cases h3 : popTagged sequentValueTag stack with
              | none =>
                  simp [postfixBranch21, postfixBranch21Direct,
                    popTaggedPattern_four, h0, h1, h2, h3]
              | some sequent =>
                  rcases sequent with ⟨sequent, stack⟩
                  simp [postfixBranch21, postfixBranch21Direct,
                    popTaggedPattern_four, h0, h1, h2, h3]

def postfixBranch15Direct (_payload : Nat) (stack : List Nat) :
    Option (List Nat) := do
  let (rightProof, stack) ← popTagged proofValueTag stack
  let (leftProof, stack) ← popTagged proofValueTag stack
  let (rightFormula, stack) ← popTagged formulaValueTag stack
  let (leftFormula, stack) ← popTagged formulaValueTag stack
  let (sequent, stack) ← popTagged sequentValueTag stack
  pure
    (pushProof
      (rawProofAnd sequent leftFormula rightFormula
        leftProof.unpair.1 rightProof.unpair.1)
      sequent stack)

theorem postfixBranch15_eq_direct (payload : Nat) (stack : List Nat) :
    postfixBranch15 payload stack = postfixBranch15Direct payload stack := by
  cases h0 : popTagged proofValueTag stack with
  | none =>
      simp [postfixBranch15, postfixBranch15Direct,
        popTaggedPattern_five, h0]
  | some rightProof =>
      rcases rightProof with ⟨rightProof, stack⟩
      cases h1 : popTagged proofValueTag stack with
      | none =>
          simp [postfixBranch15, postfixBranch15Direct,
            popTaggedPattern_five, h0, h1]
      | some leftProof =>
          rcases leftProof with ⟨leftProof, stack⟩
          cases h2 : popTagged formulaValueTag stack with
          | none =>
              simp [postfixBranch15, postfixBranch15Direct,
                popTaggedPattern_five, h0, h1, h2]
          | some rightFormula =>
              rcases rightFormula with ⟨rightFormula, stack⟩
              cases h3 : popTagged formulaValueTag stack with
              | none =>
                  simp [postfixBranch15, postfixBranch15Direct,
                    popTaggedPattern_five, h0, h1, h2, h3]
              | some leftFormula =>
                  rcases leftFormula with ⟨leftFormula, stack⟩
                  cases h4 : popTagged sequentValueTag stack with
                  | none =>
                      simp [postfixBranch15, postfixBranch15Direct,
                        popTaggedPattern_five, h0, h1, h2, h3, h4]
                  | some sequent =>
                      rcases sequent with ⟨sequent, stack⟩
                      simp [postfixBranch15, postfixBranch15Direct,
                        popTaggedPattern_five, h0, h1, h2, h3, h4]

@[simp] theorem inline_rawProofAxL (sequent formula : Nat) :
    Nat.pair sequent (Nat.pair 0 formula) + 1 =
      rawProofAxL sequent formula := by
  rfl

@[simp] theorem inline_rawProofAxm (sequent formula : Nat) :
    Nat.pair sequent (Nat.pair 9 formula) + 1 =
      rawProofAxm sequent formula := by
  rfl

@[simp] theorem inline_rawProofVerum (sequent : Nat) :
    Nat.pair sequent (Nat.pair 1 0) + 1 =
      rawProofVerum sequent := by
  rfl

@[simp] theorem inline_rawProofExs
    (sequent formula witness premise : Nat) :
    Nat.pair sequent
        (Nat.pair 5 (Nat.pair formula (Nat.pair witness premise))) + 1 =
      rawProofExs sequent formula witness premise := by
  rfl

@[simp] theorem inline_rawProofWk (sequent premise : Nat) :
    Nat.pair sequent (Nat.pair 6 premise) + 1 =
      rawProofWk sequent premise := by
  rfl

@[simp] theorem inline_rawProofShift (sequent premise : Nat) :
    Nat.pair sequent (Nat.pair 7 premise) + 1 =
      rawProofShift sequent premise := by
  rfl

theorem postfixTableStep_pair_eq_postfixStep
    (tag payload : Nat) (stack : List Nat) :
    postfixTableStep (Nat.pair tag payload) stack =
      postfixStep (Nat.pair tag payload) stack := by
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch0, pushTerm, taggedValue]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch1, pushTerm, taggedValue]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch2, postfixVectorBranch,
      pushTerm, taggedValue]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch3, postfixVectorBranch,
      pushFormula, taggedValue]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch4, postfixVectorBranch,
      pushFormula, taggedValue]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch5]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch6]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch7, postfixBinaryFormulaBranch]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch8, postfixBinaryFormulaBranch]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch9, postfixUnaryFormulaBranch]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch10, postfixUnaryFormulaBranch]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch11]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch12, postfixFormulaSequentProofBranch]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch13, postfixFormulaSequentProofBranch]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch14]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch15_eq_direct, postfixBranch15Direct]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch16_eq_direct, postfixBranch16Direct]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch17]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch18,
      postfixOneProofTwoSyntax_eq_direct,
      postfixOneProofTwoSyntaxDirect]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch19, postfixUnaryProofBranch]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch20, postfixUnaryProofBranch]
  rcases tag with (_ | tag)
  · simp [postfixTableStep, postfixHandlerTable, optionListGet,
      postfixStep, postfixBranch21_eq_direct, postfixBranch21Direct]
  simp [postfixTableStep, postfixHandlerTable, optionListGet,
    postfixStep]

theorem postfixTableStep_eq_postfixStep
    (tok : Nat) (stack : List Nat) :
    postfixTableStep tok stack = postfixStep tok stack := by
  rw [← Nat.pair_unpair tok]
  exact
    postfixTableStep_pair_eq_postfixStep
      tok.unpair.1 tok.unpair.2 stack

theorem postfixStep_primrec : Primrec₂ postfixStep :=
  postfixTableStep_primrec.of_eq postfixTableStep_eq_postfixStep

def postfixFoldStep
    (stateToken : Option (List Nat) × Nat) : Option (List Nat) :=
  stateToken.1.bind (postfixStep stateToken.2)

theorem postfixFoldStep_primrec : Primrec postfixFoldStep := by
  have hcontinue : Primrec₂
      (fun (stateToken : Option (List Nat) × Nat) (stack : List Nat) ↦
        postfixStep stateToken.2 stack) :=
    postfixStep_primrec.comp₂
      ((Primrec.snd.comp Primrec.fst).to₂) Primrec₂.right
  exact
    (Primrec.option_bind Primrec.fst hcontinue).of_eq
      fun stateToken ↦ rfl

theorem runPostfixFrom_primrec : Primrec₂ runPostfixFrom := by
  apply Primrec₂.mk
  let Input := List Nat × List Nat
  have hinitial : Primrec (fun input : Input ↦ some input.1) :=
    Primrec.option_some.comp Primrec.fst
  have hstep : Primrec₂
      (fun (_ : Input) (stateToken : Option (List Nat) × Nat) ↦
        postfixFoldStep stateToken) :=
    postfixFoldStep_primrec.comp₂ Primrec₂.right
  exact
    (Primrec.list_foldl Primrec.snd hinitial hstep).of_eq
      fun input ↦ rfl

theorem runPostfix_primrec : Primrec runPostfix := by
  exact
    (runPostfixFrom_primrec.comp (Primrec.const []) Primrec.id).of_eq
      fun _ ↦ rfl

def postfixStackResult (stack : List Nat) : Option (Nat × Nat) :=
  match stack with
  | [value] => do
      let payload ← decodeTaggedValue proofValueTag value
      pure payload.unpair
  | _ => none

theorem postfixStackResult_primrec : Primrec postfixStackResult := by
  have hsingleton : PrimrecPred (fun stack : List Nat ↦
      stack.length = 1) :=
    Primrec.eq.comp Primrec.list_length (Primrec.const 1)
  have hhead : Primrec (@List.head? Nat) := Primrec.list_head?
  have hdecode : Primrec (fun stack : List Nat ↦
      stack.head?.bind (decodeTaggedValue proofValueTag)) :=
    Primrec.option_bind hhead
      (decodeTaggedValue_primrec.comp₂
        (Primrec₂.const proofValueTag) Primrec₂.right)
  have hunpair : Primrec₂
      (fun (_ : List Nat) (payload : Nat) ↦ payload.unpair) :=
    Primrec.unpair.comp₂ Primrec₂.right
  have hresult : Primrec (fun stack : List Nat ↦
      (stack.head?.bind (decodeTaggedValue proofValueTag)).map
        Nat.unpair) :=
    Primrec.option_map hdecode hunpair
  exact
    (Primrec.ite hsingleton hresult (Primrec.const none)).of_eq
      fun stack ↦ by
        cases stack with
        | nil => simp [postfixStackResult]
        | cons value tail =>
            cases tail with
            | nil =>
                cases hdecodeValue :
                    decodeTaggedValue proofValueTag value <;>
                  simp [postfixStackResult, hdecodeValue]
            | cons next rest => simp [postfixStackResult]

theorem postfixResult_primrec : Primrec postfixResult := by
  have hcontinue : Primrec₂
      (fun (_ : List Nat) (stack : List Nat) ↦
        postfixStackResult stack) :=
    postfixStackResult_primrec.comp₂ Primrec₂.right
  exact
    (Primrec.option_bind runPostfix_primrec hcontinue).of_eq
      fun tokens ↦ by
        cases hrun : runPostfix tokens with
        | none => simp [postfixResult, hrun]
        | some stack =>
            cases stack with
            | nil => simp [postfixResult, postfixStackResult, hrun]
            | cons value tail =>
                cases tail with
                | nil =>
                    simp [postfixResult, postfixStackResult, hrun]
                | cons next rest =>
                    simp [postfixResult, postfixStackResult, hrun]

theorem natSize_succ (n : Nat) :
    Nat.size (n + 1) =
      if n + 1 = 2 ^ Nat.size n then Nat.size n + 1
      else Nat.size n := by
  by_cases hboundary : n + 1 = 2 ^ Nat.size n
  · simp [hboundary, Nat.size_pow]
  · simp only [hboundary, if_false]
    apply Nat.le_antisymm
    · rw [Nat.size_le]
      exact Nat.lt_of_le_of_ne
        (Nat.succ_le_iff.mpr (Nat.lt_size_self n)) hboundary
    · exact Nat.size_le_size (Nat.le_succ n)

theorem natSize_primrec : Primrec Nat.size := by
  have hstep : Primrec₂ (fun n size ↦
      if n + 1 = 2 ^ size then size + 1 else size) := by
    have hsuccessor : Primrec (fun input : Nat × Nat ↦
        input.1 + 1) :=
      Primrec.succ.comp Primrec.fst
    have hpower : Primrec (fun input : Nat × Nat ↦
        2 ^ input.2) :=
      natPow_primrec.comp (Primrec.const 2) Primrec.snd
    have hboundary : PrimrecPred (fun input : Nat × Nat ↦
        input.1 + 1 = 2 ^ input.2) :=
      Primrec.eq.comp hsuccessor hpower
    exact
      (Primrec.ite hboundary
        (Primrec.succ.comp Primrec.snd) Primrec.snd).to₂
  have hrec : Primrec (Nat.rec 0 fun n size ↦
      if n + 1 = 2 ^ size then size + 1 else size) :=
    Primrec.nat_rec₁ 0 hstep
  exact hrec.of_eq fun n ↦ by
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only []
        rw [ih]
        simpa [Nat.succ_eq_add_one] using (natSize_succ n).symm

theorem binaryNatCode_length (n : Nat) :
    (binaryNatCode n).length = 2 * Nat.size n + 2 := by
  simp [binaryNatCode, ← Nat.size_eq_bits_len, Nat.mul_comm]

theorem postfixTokenBitLength_primrec :
    Primrec postfixTokenBitLength := by
  have htokenCost : Primrec (fun token : Nat ↦
      2 * Nat.size token + 2) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) natSize_primrec)
      (Primrec.const 2)
  have hstep : Primrec₂
      (fun (_ : List Nat) (tokenLength : Nat × Nat) ↦
        2 * Nat.size tokenLength.1 + 2 + tokenLength.2) :=
    Primrec.nat_add.comp₂
      ((htokenCost.comp (Primrec.fst.comp Primrec.snd)).to₂)
      ((Primrec.snd.comp Primrec.snd).to₂)
  refine
    (Primrec.list_foldr
      (f := fun tokens : List Nat ↦ tokens)
      (g := fun _ : List Nat ↦ 0)
      (h := fun (_ : List Nat) (tokenLength : Nat × Nat) ↦
        2 * Nat.size tokenLength.1 + 2 + tokenLength.2)
      Primrec.id (Primrec.const 0) hstep).of_eq ?_
  intro tokens
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
      simp only [List.foldr_cons]
      simp [postfixTokenBitLength, binaryNatCode_length, ih]

theorem primrecPred_re
    {alpha : Type*} [Primcodable alpha]
    {predicate : alpha → Prop}
    (hpredicate : PrimrecPred predicate) :
    REPred predicate := by
  rcases hpredicate with ⟨decision, hdecide⟩
  letI : DecidablePred predicate := decision
  refine ComputablePred.to_re <|
    ComputablePred.computable_iff.mpr ?_
  exact
    ⟨fun input ↦ decide (predicate input),
      Primrec.to_comp hdecide, by funext input; simp⟩

def proofInputVector (input : Nat × Nat) : List.Vector Nat 2 :=
  input.1 ::ᵥ input.2 ::ᵥ List.Vector.nil

theorem proofInputVector_primrec : Primrec proofInputVector := by
  exact
    (Primrec.vector_cons.comp Primrec.fst
      (Primrec.vector_cons.comp Primrec.snd
        (Primrec.const (List.Vector.nil : List.Vector Nat 0)))).of_eq
      fun input ↦ by simp [proofInputVector]

theorem foundationPAProof_re :
    REPred (fun input : Nat × Nat ↦
      LO.FirstOrder.Arithmetic.Bootstrapping.Proof
        F.PA input.1 input.2) := by
  have heval : REPred (fun values : List.Vector Nat 2 ↦
      (LO.FirstOrder.Arithmetic.Bootstrapping.proof F.PA).sigma.val.Eval
        values.get Empty.elim) :=
    sigma1_re Empty.elim
      (by simp)
  exact
    (heval.comp proofInputVector_primrec.to_comp).of_eq
      fun input ↦ by simp [proofInputVector, List.Vector.cons_get]

theorem postfixResultEquation_primrec :
    PrimrecPred (fun input : (List Nat × Nat) × Nat ↦
      postfixResult input.1.1 =
        some (input.2, 2 ^ input.1.2)) := by
  have hactual : Primrec (fun input : (List Nat × Nat) × Nat ↦
      postfixResult input.1.1) :=
    postfixResult_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hpower : Primrec (fun input : (List Nat × Nat) × Nat ↦
      2 ^ input.1.2) :=
    natPow_primrec.comp (Primrec.const 2)
      (Primrec.snd.comp Primrec.fst)
  have hexpected : Primrec (fun input : (List Nat × Nat) × Nat ↦
      some (input.2, 2 ^ input.1.2)) :=
    Primrec.option_some.comp (Primrec.pair Primrec.snd hpower)
  exact Primrec.eq.comp hactual hexpected

theorem postfixPAProofChecks_re :
    REPred (fun input : List Nat × Nat ↦
      PostfixPAProofChecks input.1 input.2) := by
  have hresult : REPred (fun input : (List Nat × Nat) × Nat ↦
      postfixResult input.1.1 =
        some (input.2, 2 ^ input.1.2)) :=
    primrecPred_re postfixResultEquation_primrec
  have hproofInput : Primrec (fun input : (List Nat × Nat) × Nat ↦
      (input.2, input.1.2)) :=
    Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)
  have hproof : REPred (fun input : (List Nat × Nat) × Nat ↦
      LO.FirstOrder.Arithmetic.Bootstrapping.Proof
        F.PA input.2 input.1.2) :=
    foundationPAProof_re.comp hproofInput.to_comp
  exact
    (REPred.projection (hresult.and hproof)).of_eq
      fun input ↦ by
        simp only [PostfixPAProofChecks]

theorem postfixLengthBound_primrec :
    PrimrecPred (fun input : (Nat × Nat) × List Nat ↦
      postfixTokenBitLength input.2 ≤ input.1.1) := by
  exact
    Primrec.nat_le.comp
      (postfixTokenBitLength_primrec.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)

theorem efficientPostfixPAProofPredicate_re :
    REPred (fun input : Nat × Nat ↦
      EfficientPostfixPAProofPredicate input.1 input.2) := by
  have hlength : REPred (fun input : (Nat × Nat) × List Nat ↦
      postfixTokenBitLength input.2 ≤ input.1.1) :=
    primrecPred_re postfixLengthBound_primrec
  have hcheckInput : Primrec
      (fun input : (Nat × Nat) × List Nat ↦
        (input.2, input.1.2)) :=
    Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)
  have hcheck : REPred (fun input : (Nat × Nat) × List Nat ↦
      PostfixPAProofChecks input.2 input.1.2) :=
    postfixPAProofChecks_re.comp hcheckInput.to_comp
  exact
    (REPred.projection (hlength.and hcheck)).of_eq
      fun input ↦ by
        simp only [EfficientPostfixPAProofPredicate]

def pairedEfficientPostfixPAProofPredicate (code : Nat) : Prop :=
  EfficientPostfixPAProofPredicate code.unpair.1 code.unpair.2

theorem pairedEfficientPostfixPAProofPredicate_re :
    REPred pairedEfficientPostfixPAProofPredicate := by
  exact
    (efficientPostfixPAProofPredicate_re.comp
      Primrec.unpair.to_comp).of_eq
      fun code ↦ by rfl

noncomputable def pairedEfficientPostfixPAProofFormula :
    𝚺₁.Semisentence 1 :=
  .mkSigma
    (codeOfREPred pairedEfficientPostfixPAProofPredicate)
    (by simp [codeOfREPred, codeOfPartrec'])

@[simp] theorem pairedEfficientPostfixPAProofFormula_spec
    (code : Nat) :
    pairedEfficientPostfixPAProofFormula.val.Evalb ![code] ↔
      pairedEfficientPostfixPAProofPredicate code := by
  simpa [pairedEfficientPostfixPAProofFormula] using
    (codeOfREPred_spec
      pairedEfficientPostfixPAProofPredicate_re (x := code))

/-- A genuine two-variable Sigma-one formula.  Its first variable is the
binary proof-length bound and its second variable is the formula code. -/
noncomputable def efficientPostfixPAProofFormula :
    𝚺₁.Semisentence 2 :=
  .mkSigma
    “x y. ∃ z, !pairDef z x y ∧
      !(pairedEfficientPostfixPAProofFormula) z”

@[simp] theorem efficientPostfixPAProofFormula_spec
    (bound formulaCode : Nat) :
    efficientPostfixPAProofFormula.val.Evalb
        ![bound, formulaCode] ↔
      EfficientPostfixPAProofPredicate bound formulaCode := by
  simp [efficientPostfixPAProofFormula,
    pairedEfficientPostfixPAProofPredicate, nat_pair_eq,
    Nat.unpair_pair]

#print axioms postfixStep_primrec
#print axioms efficientPostfixPAProofPredicate_re
#print axioms efficientPostfixPAProofFormula_spec

end FoundationEfficientPAProofPredicateRE
