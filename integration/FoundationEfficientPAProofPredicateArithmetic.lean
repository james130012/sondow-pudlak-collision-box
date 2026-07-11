import integration.FoundationSuccinctFiniteConsistencyTarget
import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# Arithmetic target for the efficient PA proof predicate

This file gives the checked proof object a postfix token presentation.  The
verifier is a deterministic fold over a stack of tagged natural numbers.  It
reconstructs exactly the Foundation raw proof code, while proof length counts
the binary token stream rather than that raw code.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationEfficientPAProofPredicateArithmetic

open FoundationSuccinctFiniteConsistencyTarget

namespace F

open FoundationSuccinctFiniteConsistencyTarget

abbrev PA := FoundationSuccinctFiniteConsistencyTarget.PA

end F

/-! ## Tagged stack values -/

def termValueTag : Nat := 0
def formulaValueTag : Nat := 1
def sequentValueTag : Nat := 2
def proofValueTag : Nat := 3

def taggedValue (tag payload : Nat) : Nat := Nat.pair tag payload

def decodeTaggedValue (tag value : Nat) : Option Nat :=
  if value.unpair.1 = tag then some value.unpair.2 else none

def decodeTaggedList (tag : Nat) (values : List Nat) :
    Option (List Nat) :=
  if values.all (fun value ↦ decide (value.unpair.1 = tag)) then
    some (values.map fun value ↦ value.unpair.2)
  else
    none

def popTagged (tag : Nat) : List Nat → Option (Nat × List Nat)
  | [] => none
  | value :: stack => do
      let payload ← decodeTaggedValue tag value
      pure (payload, stack)

def popManyTagged
    (tag count : Nat) (stack : List Nat) :
    Option (List Nat × List Nat) := do
  let front := stack.take count
  guard (front.length = count)
  let payloads ← decodeTaggedList tag front
  pure (payloads, stack.drop count)

def pushTerm (raw : Nat) (stack : List Nat) : List Nat :=
  taggedValue termValueTag raw :: stack

def pushFormula (raw : Nat) (stack : List Nat) : List Nat :=
  taggedValue formulaValueTag raw :: stack

def pushSequent (raw : Nat) (stack : List Nat) : List Nat :=
  taggedValue sequentValueTag raw :: stack

def pushProof (raw sequent : Nat) (stack : List Nat) : List Nat :=
  taggedValue proofValueTag (Nat.pair raw sequent) :: stack

/-! ## Postfix tokens -/

def token (tag payload : Nat) : Nat := Nat.pair tag payload

def termBvarToken (index : Nat) : Nat := token 0 index
def termFvarToken (index : Nat) : Nat := token 1 index
def termFuncToken (arity functionCode : Nat) : Nat :=
  token 2 (Nat.pair arity functionCode)

def formulaRelToken (arity relationCode : Nat) : Nat :=
  token 3 (Nat.pair arity relationCode)

def formulaNrelToken (arity relationCode : Nat) : Nat :=
  token 4 (Nat.pair arity relationCode)

def formulaVerumToken : Nat := token 5 0
def formulaFalsumToken : Nat := token 6 0
def formulaAndToken : Nat := token 7 0
def formulaOrToken : Nat := token 8 0
def formulaAllToken : Nat := token 9 0
def formulaExsToken : Nat := token 10 0
def sequentToken (cardinality : Nat) : Nat := token 11 cardinality

def proofClosedToken : Nat := token 12 0
def proofAxiomToken : Nat := token 13 0
def proofVerumToken : Nat := token 14 0
def proofAndToken : Nat := token 15 0
def proofOrToken : Nat := token 16 0
def proofAllToken : Nat := token 17 0
def proofExsToken : Nat := token 18 0
def proofWkToken : Nat := token 19 0
def proofShiftToken : Nat := token 20 0
def proofCutToken : Nat := token 21 0

/-! ## One-step verifier -/

def postfixStep (tok : Nat) (stack : List Nat) : Option (List Nat) := do
  let tag := tok.unpair.1
  let payload := tok.unpair.2
  match tag with
  | 0 =>
      pure (pushTerm (Nat.pair 0 payload + 1) stack)
  | 1 =>
      pure (pushTerm (Nat.pair 1 payload + 1) stack)
  | 2 => do
      let arity := payload.unpair.1
      let functionCode := payload.unpair.2
      let (arguments, stack) ← popManyTagged termValueTag arity stack
      let raw :=
        Nat.pair 2
          (Nat.pair arity
            (Nat.pair functionCode
              (rawVectorCode arguments.reverse))) + 1
      pure (pushTerm raw stack)
  | 3 => do
      let arity := payload.unpair.1
      let relationCode := payload.unpair.2
      let (arguments, stack) ← popManyTagged termValueTag arity stack
      let raw :=
        Nat.pair 0
          (Nat.pair arity
            (Nat.pair relationCode
              (rawVectorCode arguments.reverse))) + 1
      pure (pushFormula raw stack)
  | 4 => do
      let arity := payload.unpair.1
      let relationCode := payload.unpair.2
      let (arguments, stack) ← popManyTagged termValueTag arity stack
      let raw :=
        Nat.pair 1
          (Nat.pair arity
            (Nat.pair relationCode
              (rawVectorCode arguments.reverse))) + 1
      pure (pushFormula raw stack)
  | 5 =>
      pure (pushFormula (Nat.pair 2 0 + 1) stack)
  | 6 =>
      pure (pushFormula (Nat.pair 3 0 + 1) stack)
  | 7 => do
      let (right, stack) ← popTagged formulaValueTag stack
      let (left, stack) ← popTagged formulaValueTag stack
      pure (pushFormula (Nat.pair 4 (Nat.pair left right) + 1) stack)
  | 8 => do
      let (right, stack) ← popTagged formulaValueTag stack
      let (left, stack) ← popTagged formulaValueTag stack
      pure (pushFormula (Nat.pair 5 (Nat.pair left right) + 1) stack)
  | 9 => do
      let (body, stack) ← popTagged formulaValueTag stack
      pure (pushFormula (Nat.pair 6 body + 1) stack)
  | 10 => do
      let (body, stack) ← popTagged formulaValueTag stack
      pure (pushFormula (Nat.pair 7 body + 1) stack)
  | 11 => do
      let (formulas, stack) ←
        popManyTagged formulaValueTag payload stack
      pure (pushSequent (rawSequentCode formulas.reverse) stack)
  | 12 => do
      let (formula, stack) ← popTagged formulaValueTag stack
      let (sequent, stack) ← popTagged sequentValueTag stack
      pure (pushProof (rawProofAxL sequent formula) sequent stack)
  | 13 => do
      let (formula, stack) ← popTagged formulaValueTag stack
      let (sequent, stack) ← popTagged sequentValueTag stack
      pure (pushProof (rawProofAxm sequent formula) sequent stack)
  | 14 => do
      let (sequent, stack) ← popTagged sequentValueTag stack
      pure (pushProof (rawProofVerum sequent) sequent stack)
  | 15 => do
      let (rightProof, stack) ← popTagged proofValueTag stack
      let (leftProof, stack) ← popTagged proofValueTag stack
      let (rightFormula, stack) ← popTagged formulaValueTag stack
      let (leftFormula, stack) ← popTagged formulaValueTag stack
      let (sequent, stack) ← popTagged sequentValueTag stack
      pure (pushProof
        (rawProofAnd sequent leftFormula rightFormula
          leftProof.unpair.1 rightProof.unpair.1)
        sequent stack)
  | 16 => do
      let (premise, stack) ← popTagged proofValueTag stack
      let (rightFormula, stack) ← popTagged formulaValueTag stack
      let (leftFormula, stack) ← popTagged formulaValueTag stack
      let (sequent, stack) ← popTagged sequentValueTag stack
      pure (pushProof
        (rawProofOr sequent leftFormula rightFormula premise.unpair.1)
        sequent stack)
  | 17 => do
      let (premise, stack) ← popTagged proofValueTag stack
      let (formula, stack) ← popTagged formulaValueTag stack
      let (sequent, stack) ← popTagged sequentValueTag stack
      pure (pushProof
        (rawProofAll sequent formula premise.unpair.1)
        sequent stack)
  | 18 => do
      let (premise, stack) ← popTagged proofValueTag stack
      let (witness, stack) ← popTagged termValueTag stack
      let (formula, stack) ← popTagged formulaValueTag stack
      let (sequent, stack) ← popTagged sequentValueTag stack
      pure (pushProof
        (rawProofExs sequent formula witness premise.unpair.1)
        sequent stack)
  | 19 => do
      let (premise, stack) ← popTagged proofValueTag stack
      let (sequent, stack) ← popTagged sequentValueTag stack
      pure (pushProof (rawProofWk sequent premise.unpair.1)
        sequent stack)
  | 20 => do
      let (premise, stack) ← popTagged proofValueTag stack
      let (sequent, stack) ← popTagged sequentValueTag stack
      pure (pushProof (rawProofShift sequent premise.unpair.1)
        sequent stack)
  | 21 => do
      let (rightProof, stack) ← popTagged proofValueTag stack
      let (leftProof, stack) ← popTagged proofValueTag stack
      let (formula, stack) ← popTagged formulaValueTag stack
      let (sequent, stack) ← popTagged sequentValueTag stack
      pure (pushProof
        (rawProofCut sequent formula
          leftProof.unpair.1 rightProof.unpair.1)
        sequent stack)
  | _ => none

def runPostfixFrom (initial : List Nat) (tokens : List Nat) :
    Option (List Nat) :=
  tokens.foldl
    (fun state tok => state.bind (postfixStep tok))
    (some initial)

def runPostfix (tokens : List Nat) : Option (List Nat) :=
  runPostfixFrom [] tokens

def postfixResult (tokens : List Nat) : Option (Nat × Nat) := do
  let stack ← runPostfix tokens
  match stack with
  | [value] => do
      let payload ← decodeTaggedValue proofValueTag value
      pure payload.unpair
  | _ => none

@[simp] theorem decodeTaggedValue_taggedValue
    (tag payload : Nat) :
    decodeTaggedValue tag (taggedValue tag payload) = some payload := by
  simp [decodeTaggedValue, taggedValue]

@[simp] theorem decodeTaggedList_map_taggedValue
    (tag : Nat) (payloads : List Nat) :
    decodeTaggedList tag (payloads.map (taggedValue tag)) =
      some payloads := by
  simp [decodeTaggedList, taggedValue, Function.comp_def]

@[simp] theorem popTagged_taggedValue_cons
    (tag payload : Nat) (stack : List Nat) :
    popTagged tag (taggedValue tag payload :: stack) =
      some (payload, stack) := by
  simp [popTagged]

@[simp] theorem popManyTagged_map_append
    (tag : Nat) (payloads stack : List Nat) :
    popManyTagged tag payloads.length
        (payloads.map (taggedValue tag) ++ stack) =
      some (payloads, stack) := by
  simp [popManyTagged]

theorem runPostfixFrom_append_of_eq
    {initial middle : List Nat} {left : List Nat}
    (right : List Nat)
    (hleft : runPostfixFrom initial left = some middle) :
    runPostfixFrom initial (left ++ right) =
      runPostfixFrom middle right := by
  simp only [runPostfixFrom] at hleft ⊢
  rw [List.foldl_append, hleft]

theorem runPostfixFrom_flatMap_push
    {alpha : Type*}
    (items : List alpha) (encode : alpha → List Nat)
    (value : alpha → Nat) (initial : List Nat)
    (hitem : ∀ item ∈ items, ∀ stack,
      runPostfixFrom stack (encode item) =
        some (value item :: stack)) :
    runPostfixFrom initial (items.flatMap encode) =
      some ((items.map value).reverse ++ initial) := by
  induction items generalizing initial with
  | nil => simp [runPostfixFrom]
  | cons head tail ih =>
      rw [List.flatMap_cons]
      rw [runPostfixFrom_append_of_eq
        (tail.flatMap encode) (hitem head (by simp) initial)]
      rw [ih (value head :: initial) (by
        intro item hmem stack
        exact hitem item (by simp [hmem]) stack)]
      simp

/-! ## Token generation from the checked certificate tree -/

def termPostfixTokens {arity : Nat} :
    LO.FirstOrder.ArithmeticSemiterm Nat arity → List Nat
  | #index => [termBvarToken index.val]
  | &freeIndex => [termFvarToken freeIndex]
  | Semiterm.func (arity := functionArity) functionSymbol arguments =>
      (List.ofFn fun i => termPostfixTokens (arguments i)).flatten ++
        [termFuncToken functionArity (Encodable.encode functionSymbol)]

theorem runPostfixFrom_termPostfixTokens
    {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (initial : List Nat) :
    runPostfixFrom initial (termPostfixTokens term) =
      some (pushTerm (Encodable.encode term) initial) := by
  induction term generalizing initial with
  | bvar index =>
      simp [termPostfixTokens, runPostfixFrom, postfixStep,
        termBvarToken, token, pushTerm, taggedValue,
        LO.FirstOrder.Semiterm.encode_eq_toNat,
        LO.FirstOrder.Semiterm.toNat]
  | fvar freeIndex =>
      simp [termPostfixTokens, runPostfixFrom, postfixStep,
        termFvarToken, token, pushTerm, taggedValue,
        LO.FirstOrder.Semiterm.encode_eq_toNat,
        LO.FirstOrder.Semiterm.toNat]
  | func functionSymbol arguments ih =>
      have hchildren :=
        runPostfixFrom_flatMap_push
          (List.ofFn arguments) termPostfixTokens
          (fun term ↦ taggedValue termValueTag (Encodable.encode term))
          initial
          (by
            intro child hmem stack
            rcases (List.mem_ofFn' arguments child).mp hmem with
              ⟨i, rfl⟩
            simpa [pushTerm] using ih i stack)
      have hchildren' :
          runPostfixFrom initial
              (List.ofFn fun i ↦
                termPostfixTokens (arguments i)).flatten =
            some
              ((List.ofFn fun i ↦
                taggedValue termValueTag
                  (Encodable.encode (arguments i))).reverse ++ initial) := by
        simpa [List.flatMap, List.map_ofFn,
          Function.comp_def] using hchildren
      have hpop :
          popManyTagged termValueTag (List.ofFn arguments).length
              ((List.ofFn fun i ↦
                taggedValue termValueTag
                  (Encodable.encode (arguments i))).reverse ++ initial) =
            some
              ((List.ofFn fun i ↦
                Encodable.encode (arguments i)).reverse, initial) := by
        simpa [List.map_reverse, List.map_ofFn,
          Function.comp_def] using
            popManyTagged_map_append termValueTag
              (List.ofFn fun i ↦
                Encodable.encode (arguments i)).reverse initial
      simp only [List.length_ofFn] at hpop
      rw [termPostfixTokens,
        runPostfixFrom_append_of_eq _ hchildren']
      simp only [runPostfixFrom, List.foldl_cons, List.foldl_nil]
      simp only [postfixStep, termFuncToken, token,
        Nat.unpair_pair]
      dsimp
      rw [hpop]
      simp [pushTerm, taggedValue,
        LO.FirstOrder.Semiterm.encode_eq_toNat,
        LO.FirstOrder.Semiterm.toNat,
        rawVectorCode_ofFn]

def formulaPostfixTokens :
    {arity : Nat} →
      LO.FirstOrder.ArithmeticSemiformula Nat arity → List Nat
  | _, Semiformula.rel (arity := relationArity) relationSymbol arguments =>
      (List.ofFn fun i => termPostfixTokens (arguments i)).flatten ++
        [formulaRelToken relationArity (Encodable.encode relationSymbol)]
  | _, Semiformula.nrel (arity := relationArity) relationSymbol arguments =>
      (List.ofFn fun i => termPostfixTokens (arguments i)).flatten ++
        [formulaNrelToken relationArity (Encodable.encode relationSymbol)]
  | _, ⊤ => [formulaVerumToken]
  | _, ⊥ => [formulaFalsumToken]
  | _, left ⋏ right =>
      formulaPostfixTokens left ++ formulaPostfixTokens right ++
        [formulaAndToken]
  | _, left ⋎ right =>
      formulaPostfixTokens left ++ formulaPostfixTokens right ++
        [formulaOrToken]
  | _, ∀⁰ body => formulaPostfixTokens body ++ [formulaAllToken]
  | _, ∃⁰ body => formulaPostfixTokens body ++ [formulaExsToken]

theorem runPostfixFrom_formulaPostfixTokens
    {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity)
    (initial : List Nat) :
    runPostfixFrom initial (formulaPostfixTokens formula) =
      some (pushFormula (Encodable.encode formula) initial) := by
  induction formula generalizing initial with
  | rel relationSymbol arguments =>
      have hchildren :=
        runPostfixFrom_flatMap_push
          (List.ofFn arguments) termPostfixTokens
          (fun term ↦ taggedValue termValueTag (Encodable.encode term))
          initial
          (by
            intro child hmem stack
            rcases (List.mem_ofFn' arguments child).mp hmem with
              ⟨i, rfl⟩
            simpa [pushTerm] using
              runPostfixFrom_termPostfixTokens (arguments i) stack)
      have hchildren' :
          runPostfixFrom initial
              (List.ofFn fun i ↦
                termPostfixTokens (arguments i)).flatten =
            some
              ((List.ofFn fun i ↦
                taggedValue termValueTag
                  (Encodable.encode (arguments i))).reverse ++ initial) := by
        simpa [List.flatMap, List.map_ofFn,
          Function.comp_def] using hchildren
      have hpop :
          popManyTagged termValueTag (List.ofFn arguments).length
              ((List.ofFn fun i ↦
                taggedValue termValueTag
                  (Encodable.encode (arguments i))).reverse ++ initial) =
            some
              ((List.ofFn fun i ↦
                Encodable.encode (arguments i)).reverse, initial) := by
        simpa [List.map_reverse, List.map_ofFn,
          Function.comp_def] using
            popManyTagged_map_append termValueTag
              (List.ofFn fun i ↦
                Encodable.encode (arguments i)).reverse initial
      simp only [List.length_ofFn] at hpop
      rw [formulaPostfixTokens,
        runPostfixFrom_append_of_eq _ hchildren']
      simp only [runPostfixFrom, List.foldl_cons, List.foldl_nil]
      simp only [postfixStep, formulaRelToken, token,
        Nat.unpair_pair]
      dsimp
      rw [hpop]
      simp [pushFormula, taggedValue,
        LO.FirstOrder.Semiformula.encode_eq_toNat,
        LO.FirstOrder.Semiformula.toNat,
        LO.FirstOrder.Semiterm.encode_eq_toNat,
        rawVectorCode_ofFn]
  | nrel relationSymbol arguments =>
      have hchildren :=
        runPostfixFrom_flatMap_push
          (List.ofFn arguments) termPostfixTokens
          (fun term ↦ taggedValue termValueTag (Encodable.encode term))
          initial
          (by
            intro child hmem stack
            rcases (List.mem_ofFn' arguments child).mp hmem with
              ⟨i, rfl⟩
            simpa [pushTerm] using
              runPostfixFrom_termPostfixTokens (arguments i) stack)
      have hchildren' :
          runPostfixFrom initial
              (List.ofFn fun i ↦
                termPostfixTokens (arguments i)).flatten =
            some
              ((List.ofFn fun i ↦
                taggedValue termValueTag
                  (Encodable.encode (arguments i))).reverse ++ initial) := by
        simpa [List.flatMap, List.map_ofFn,
          Function.comp_def] using hchildren
      have hpop :
          popManyTagged termValueTag (List.ofFn arguments).length
              ((List.ofFn fun i ↦
                taggedValue termValueTag
                  (Encodable.encode (arguments i))).reverse ++ initial) =
            some
              ((List.ofFn fun i ↦
                Encodable.encode (arguments i)).reverse, initial) := by
        simpa [List.map_reverse, List.map_ofFn,
          Function.comp_def] using
            popManyTagged_map_append termValueTag
              (List.ofFn fun i ↦
                Encodable.encode (arguments i)).reverse initial
      simp only [List.length_ofFn] at hpop
      rw [formulaPostfixTokens,
        runPostfixFrom_append_of_eq _ hchildren']
      simp only [runPostfixFrom, List.foldl_cons, List.foldl_nil]
      simp only [postfixStep, formulaNrelToken, token,
        Nat.unpair_pair]
      dsimp
      rw [hpop]
      simp [pushFormula, taggedValue,
        LO.FirstOrder.Semiformula.encode_eq_toNat,
        LO.FirstOrder.Semiformula.toNat,
        LO.FirstOrder.Semiterm.encode_eq_toNat,
        rawVectorCode_ofFn]
  | verum =>
      simp [formulaPostfixTokens, runPostfixFrom, postfixStep,
        formulaVerumToken, token, pushFormula, taggedValue,
        LO.FirstOrder.Semiformula.encode_eq_toNat,
        LO.FirstOrder.Semiformula.toNat]
  | falsum =>
      simp [formulaPostfixTokens, runPostfixFrom, postfixStep,
        formulaFalsumToken, token, pushFormula, taggedValue,
        LO.FirstOrder.Semiformula.encode_eq_toNat,
        LO.FirstOrder.Semiformula.toNat]
  | and left right ihLeft ihRight =>
      rw [formulaPostfixTokens]
      rw [List.append_assoc]
      rw [runPostfixFrom_append_of_eq _ (ihLeft initial)]
      rw [runPostfixFrom_append_of_eq _
        (ihRight (pushFormula (Encodable.encode left) initial))]
      simp [runPostfixFrom, postfixStep, formulaAndToken, token,
        popTagged, decodeTaggedValue, formulaValueTag,
        pushFormula, taggedValue,
        LO.FirstOrder.Semiformula.encode_eq_toNat,
        LO.FirstOrder.Semiformula.toNat]
  | or left right ihLeft ihRight =>
      rw [formulaPostfixTokens]
      rw [List.append_assoc]
      rw [runPostfixFrom_append_of_eq _ (ihLeft initial)]
      rw [runPostfixFrom_append_of_eq _
        (ihRight (pushFormula (Encodable.encode left) initial))]
      simp [runPostfixFrom, postfixStep, formulaOrToken, token,
        popTagged, decodeTaggedValue, formulaValueTag,
        pushFormula, taggedValue,
        LO.FirstOrder.Semiformula.encode_eq_toNat,
        LO.FirstOrder.Semiformula.toNat]
  | all body ih =>
      rw [formulaPostfixTokens,
        runPostfixFrom_append_of_eq _ (ih initial)]
      simp [runPostfixFrom, postfixStep, formulaAllToken, token,
        popTagged, decodeTaggedValue, formulaValueTag,
        pushFormula, taggedValue,
        LO.FirstOrder.Semiformula.encode_eq_toNat,
        LO.FirstOrder.Semiformula.toNat]
  | exs body ih =>
      rw [formulaPostfixTokens,
        runPostfixFrom_append_of_eq _ (ih initial)]
      simp [runPostfixFrom, postfixStep, formulaExsToken, token,
        popTagged, decodeTaggedValue, formulaValueTag,
        pushFormula, taggedValue,
        LO.FirstOrder.Semiformula.encode_eq_toNat,
        LO.FirstOrder.Semiformula.toNat]

def sequentPostfixTokens
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition) : List Nat :=
  Gamma.toList.flatMap formulaPostfixTokens ++ [sequentToken Gamma.card]

theorem runPostfixFrom_sequentPostfixTokens
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (initial : List Nat) :
    runPostfixFrom initial (sequentPostfixTokens Gamma) =
      some (pushSequent (⌜Gamma⌝ : Nat) initial) := by
  have hchildren :=
    runPostfixFrom_flatMap_push
      Gamma.toList formulaPostfixTokens
      (fun formula ↦
        taggedValue formulaValueTag (Encodable.encode formula))
      initial
      (by
        intro formula _ stack
        simpa [pushFormula] using
          runPostfixFrom_formulaPostfixTokens formula stack)
  have hchildren' :
      runPostfixFrom initial
          (Gamma.toList.flatMap formulaPostfixTokens) =
        some
          ((Gamma.toList.map fun formula ↦
            taggedValue formulaValueTag
              (Encodable.encode formula)).reverse ++ initial) := by
    simpa using hchildren
  have hpop :
      popManyTagged formulaValueTag Gamma.card
          ((Gamma.toList.map fun formula ↦
            taggedValue formulaValueTag
              (Encodable.encode formula)).reverse ++ initial) =
        some
          ((Gamma.toList.map Encodable.encode).reverse, initial) := by
    simpa [List.map_reverse, Function.comp_def] using
      popManyTagged_map_append formulaValueTag
        (Gamma.toList.map Encodable.encode).reverse initial
  rw [sequentPostfixTokens,
    runPostfixFrom_append_of_eq _ hchildren']
  simp only [runPostfixFrom, List.foldl_cons, List.foldl_nil]
  simp only [postfixStep, sequentToken, token, Nat.unpair_pair]
  dsimp
  rw [hpop]
  simp [pushSequent, rawSequentCode_encode_toList]

def proofPostfixTokens : CheckedPAProofTree → List Nat
  | .closed Gamma formula =>
      sequentPostfixTokens Gamma ++ formulaPostfixTokens formula ++
        [proofClosedToken]
  | .axm Gamma sigma =>
      sequentPostfixTokens Gamma ++
        formulaPostfixTokens
          (Rewriting.emb sigma : LO.FirstOrder.ArithmeticProposition) ++
        [proofAxiomToken]
  | .verum Gamma => sequentPostfixTokens Gamma ++ [proofVerumToken]
  | .and Gamma leftFormula rightFormula left right =>
      sequentPostfixTokens Gamma ++ formulaPostfixTokens leftFormula ++
        formulaPostfixTokens rightFormula ++ proofPostfixTokens left ++
        proofPostfixTokens right ++ [proofAndToken]
  | .or Gamma leftFormula rightFormula premise =>
      sequentPostfixTokens Gamma ++ formulaPostfixTokens leftFormula ++
        formulaPostfixTokens rightFormula ++ proofPostfixTokens premise ++
        [proofOrToken]
  | .all Gamma formula premise =>
      sequentPostfixTokens Gamma ++ formulaPostfixTokens formula ++
        proofPostfixTokens premise ++ [proofAllToken]
  | .exs Gamma formula witness premise =>
      sequentPostfixTokens Gamma ++ formulaPostfixTokens formula ++
        termPostfixTokens witness ++ proofPostfixTokens premise ++
        [proofExsToken]
  | .wk Gamma premise =>
      sequentPostfixTokens Gamma ++ proofPostfixTokens premise ++
        [proofWkToken]
  | .shift Gamma premise =>
      sequentPostfixTokens Gamma ++ proofPostfixTokens premise ++
        [proofShiftToken]
  | .cut Gamma formula left right =>
      sequentPostfixTokens Gamma ++ formulaPostfixTokens formula ++
        proofPostfixTokens left ++ proofPostfixTokens right ++
        [proofCutToken]

@[simp] theorem runPostfixFrom_singleton
    (stack : List Nat) (tok : Nat) :
    runPostfixFrom stack [tok] = postfixStep tok stack := by
  rfl

@[simp] theorem postfixStep_proofClosedToken
    (sequent formula : Nat) (stack : List Nat) :
    postfixStep proofClosedToken
        (pushFormula formula (pushSequent sequent stack)) =
      some (pushProof (rawProofAxL sequent formula) sequent stack) := by
  simp [postfixStep, proofClosedToken, token,
    popTagged, decodeTaggedValue, formulaValueTag,
    sequentValueTag, proofValueTag,
    pushFormula, pushSequent, pushProof, taggedValue]

@[simp] theorem postfixStep_proofAxiomToken
    (sequent formula : Nat) (stack : List Nat) :
    postfixStep proofAxiomToken
        (pushFormula formula (pushSequent sequent stack)) =
      some (pushProof (rawProofAxm sequent formula) sequent stack) := by
  simp [postfixStep, proofAxiomToken, token,
    popTagged, decodeTaggedValue, formulaValueTag,
    sequentValueTag, proofValueTag,
    pushFormula, pushSequent, pushProof, taggedValue]

@[simp] theorem postfixStep_proofVerumToken
    (sequent : Nat) (stack : List Nat) :
    postfixStep proofVerumToken (pushSequent sequent stack) =
      some (pushProof (rawProofVerum sequent) sequent stack) := by
  simp [postfixStep, proofVerumToken, token,
    popTagged, decodeTaggedValue, sequentValueTag, proofValueTag,
    pushSequent, pushProof, taggedValue]

@[simp] theorem postfixStep_proofAndToken
    (sequent leftFormula rightFormula leftCode leftSequent
      rightCode rightSequent : Nat)
    (stack : List Nat) :
    postfixStep proofAndToken
        (pushProof rightCode rightSequent
          (pushProof leftCode leftSequent
            (pushFormula rightFormula
              (pushFormula leftFormula
                (pushSequent sequent stack))))) =
      some
        (pushProof
          (rawProofAnd sequent leftFormula rightFormula
            leftCode rightCode)
          sequent stack) := by
  simp [postfixStep, proofAndToken, token,
    popTagged, decodeTaggedValue, formulaValueTag,
    sequentValueTag, proofValueTag,
    pushFormula, pushSequent, pushProof, taggedValue]

@[simp] theorem postfixStep_proofOrToken
    (sequent leftFormula rightFormula premise premiseSequent : Nat)
    (stack : List Nat) :
    postfixStep proofOrToken
        (pushProof premise premiseSequent
          (pushFormula rightFormula
            (pushFormula leftFormula
              (pushSequent sequent stack)))) =
      some
        (pushProof
          (rawProofOr sequent leftFormula rightFormula premise)
          sequent stack) := by
  simp [postfixStep, proofOrToken, token,
    popTagged, decodeTaggedValue, formulaValueTag,
    sequentValueTag, proofValueTag,
    pushFormula, pushSequent, pushProof, taggedValue]

@[simp] theorem postfixStep_proofAllToken
    (sequent formula premise premiseSequent : Nat)
    (stack : List Nat) :
    postfixStep proofAllToken
        (pushProof premise premiseSequent
          (pushFormula formula (pushSequent sequent stack))) =
      some
        (pushProof (rawProofAll sequent formula premise)
          sequent stack) := by
  simp [postfixStep, proofAllToken, token,
    popTagged, decodeTaggedValue, formulaValueTag,
    sequentValueTag, proofValueTag,
    pushFormula, pushSequent, pushProof, taggedValue]

@[simp] theorem postfixStep_proofExsToken
    (sequent formula witness premise premiseSequent : Nat)
    (stack : List Nat) :
    postfixStep proofExsToken
        (pushProof premise premiseSequent
          (pushTerm witness
            (pushFormula formula (pushSequent sequent stack)))) =
      some
        (pushProof (rawProofExs sequent formula witness premise)
          sequent stack) := by
  simp [postfixStep, proofExsToken, token,
    popTagged, decodeTaggedValue, termValueTag, formulaValueTag,
    sequentValueTag, proofValueTag,
    pushTerm, pushFormula, pushSequent, pushProof, taggedValue]

@[simp] theorem postfixStep_proofWkToken
    (sequent premise premiseSequent : Nat) (stack : List Nat) :
    postfixStep proofWkToken
        (pushProof premise premiseSequent
          (pushSequent sequent stack)) =
      some (pushProof (rawProofWk sequent premise) sequent stack) := by
  simp [postfixStep, proofWkToken, token,
    popTagged, decodeTaggedValue, sequentValueTag, proofValueTag,
    pushSequent, pushProof, taggedValue]

@[simp] theorem postfixStep_proofShiftToken
    (sequent premise premiseSequent : Nat) (stack : List Nat) :
    postfixStep proofShiftToken
        (pushProof premise premiseSequent
          (pushSequent sequent stack)) =
      some
        (pushProof (rawProofShift sequent premise) sequent stack) := by
  simp [postfixStep, proofShiftToken, token,
    popTagged, decodeTaggedValue, sequentValueTag, proofValueTag,
    pushSequent, pushProof, taggedValue]

@[simp] theorem postfixStep_proofCutToken
    (sequent formula leftCode leftSequent rightCode rightSequent : Nat)
    (stack : List Nat) :
    postfixStep proofCutToken
        (pushProof rightCode rightSequent
          (pushProof leftCode leftSequent
            (pushFormula formula (pushSequent sequent stack)))) =
      some
        (pushProof (rawProofCut sequent formula leftCode rightCode)
          sequent stack) := by
  simp [postfixStep, proofCutToken, token,
    popTagged, decodeTaggedValue, formulaValueTag,
    sequentValueTag, proofValueTag,
    pushFormula, pushSequent, pushProof, taggedValue]

theorem runPostfixFrom_proofPostfixTokens
    (b : CheckedPAProofTree) (initial : List Nat) :
    runPostfixFrom initial (proofPostfixTokens b) =
      some
        (pushProof b.rawCode (⌜b.conclusion⌝ : Nat) initial) := by
  induction b generalizing initial with
  | closed Gamma formula =>
      simp only [proofPostfixTokens, List.append_assoc]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_sequentPostfixTokens Gamma initial)]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_formulaPostfixTokens formula
          (pushSequent (⌜Gamma⌝ : Nat) initial))]
      rw [runPostfixFrom_singleton, postfixStep_proofClosedToken]
      simp [
        CheckedPAProofTree.rawCode, CheckedPAProofTree.conclusion,
        LO.FirstOrder.Semiformula.quote_eq_encode]
  | axm Gamma sigma =>
      simp only [proofPostfixTokens, List.append_assoc]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_sequentPostfixTokens Gamma initial)]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_formulaPostfixTokens
          (Rewriting.emb sigma : LO.FirstOrder.ArithmeticProposition)
          (pushSequent (⌜Gamma⌝ : Nat) initial))]
      rw [runPostfixFrom_singleton, postfixStep_proofAxiomToken]
      simp [
        CheckedPAProofTree.rawCode, CheckedPAProofTree.conclusion,
        LO.FirstOrder.Sentence.quote_def,
        LO.FirstOrder.Semiformula.quote_eq_encode]
  | verum Gamma =>
      simp only [proofPostfixTokens]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_sequentPostfixTokens Gamma initial)]
      rw [runPostfixFrom_singleton, postfixStep_proofVerumToken]
      simp [
        CheckedPAProofTree.rawCode, CheckedPAProofTree.conclusion]
  | and Gamma leftFormula rightFormula left right ihLeft ihRight =>
      simp only [proofPostfixTokens, List.append_assoc]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_sequentPostfixTokens Gamma initial)]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_formulaPostfixTokens leftFormula
          (pushSequent (⌜Gamma⌝ : Nat) initial))]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_formulaPostfixTokens rightFormula
          (pushFormula (Encodable.encode leftFormula)
            (pushSequent (⌜Gamma⌝ : Nat) initial)))]
      rw [runPostfixFrom_append_of_eq _
        (ihLeft
          (pushFormula (Encodable.encode rightFormula)
            (pushFormula (Encodable.encode leftFormula)
              (pushSequent (⌜Gamma⌝ : Nat) initial))))]
      rw [runPostfixFrom_append_of_eq _
        (ihRight
          (pushProof left.rawCode (⌜left.conclusion⌝ : Nat)
            (pushFormula (Encodable.encode rightFormula)
              (pushFormula (Encodable.encode leftFormula)
                (pushSequent (⌜Gamma⌝ : Nat) initial)))))]
      rw [runPostfixFrom_singleton, postfixStep_proofAndToken]
      simp [
        CheckedPAProofTree.rawCode, CheckedPAProofTree.conclusion,
        LO.FirstOrder.Semiformula.quote_eq_encode]
  | or Gamma leftFormula rightFormula premise ih =>
      simp only [proofPostfixTokens, List.append_assoc]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_sequentPostfixTokens Gamma initial)]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_formulaPostfixTokens leftFormula
          (pushSequent (⌜Gamma⌝ : Nat) initial))]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_formulaPostfixTokens rightFormula
          (pushFormula (Encodable.encode leftFormula)
            (pushSequent (⌜Gamma⌝ : Nat) initial)))]
      rw [runPostfixFrom_append_of_eq _
        (ih
          (pushFormula (Encodable.encode rightFormula)
            (pushFormula (Encodable.encode leftFormula)
              (pushSequent (⌜Gamma⌝ : Nat) initial))))]
      rw [runPostfixFrom_singleton, postfixStep_proofOrToken]
      simp [
        CheckedPAProofTree.rawCode, CheckedPAProofTree.conclusion,
        LO.FirstOrder.Semiformula.quote_eq_encode]
  | all Gamma formula premise ih =>
      simp only [proofPostfixTokens, List.append_assoc]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_sequentPostfixTokens Gamma initial)]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_formulaPostfixTokens formula
          (pushSequent (⌜Gamma⌝ : Nat) initial))]
      rw [runPostfixFrom_append_of_eq _
        (ih
          (pushFormula (Encodable.encode formula)
            (pushSequent (⌜Gamma⌝ : Nat) initial)))]
      rw [runPostfixFrom_singleton, postfixStep_proofAllToken]
      simp [
        CheckedPAProofTree.rawCode, CheckedPAProofTree.conclusion,
        LO.FirstOrder.Semiformula.quote_eq_encode]
  | exs Gamma formula witness premise ih =>
      simp only [proofPostfixTokens, List.append_assoc]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_sequentPostfixTokens Gamma initial)]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_formulaPostfixTokens formula
          (pushSequent (⌜Gamma⌝ : Nat) initial))]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_termPostfixTokens witness
          (pushFormula (Encodable.encode formula)
            (pushSequent (⌜Gamma⌝ : Nat) initial)))]
      rw [runPostfixFrom_append_of_eq _
        (ih
          (pushTerm (Encodable.encode witness)
            (pushFormula (Encodable.encode formula)
              (pushSequent (⌜Gamma⌝ : Nat) initial))))]
      rw [runPostfixFrom_singleton, postfixStep_proofExsToken]
      simp [
        CheckedPAProofTree.rawCode, CheckedPAProofTree.conclusion,
        LO.FirstOrder.Semiterm.quote_eq_encode,
        LO.FirstOrder.Semiformula.quote_eq_encode]
  | wk Gamma premise ih =>
      simp only [proofPostfixTokens, List.append_assoc]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_sequentPostfixTokens Gamma initial)]
      rw [runPostfixFrom_append_of_eq _
        (ih (pushSequent (⌜Gamma⌝ : Nat) initial))]
      rw [runPostfixFrom_singleton, postfixStep_proofWkToken]
      simp [
        CheckedPAProofTree.rawCode, CheckedPAProofTree.conclusion]
  | shift Gamma premise ih =>
      simp only [proofPostfixTokens, List.append_assoc]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_sequentPostfixTokens Gamma initial)]
      rw [runPostfixFrom_append_of_eq _
        (ih (pushSequent (⌜Gamma⌝ : Nat) initial))]
      rw [runPostfixFrom_singleton, postfixStep_proofShiftToken]
      simp [
        CheckedPAProofTree.rawCode, CheckedPAProofTree.conclusion]
  | cut Gamma formula left right ihLeft ihRight =>
      simp only [proofPostfixTokens, List.append_assoc]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_sequentPostfixTokens Gamma initial)]
      rw [runPostfixFrom_append_of_eq _
        (runPostfixFrom_formulaPostfixTokens formula
          (pushSequent (⌜Gamma⌝ : Nat) initial))]
      rw [runPostfixFrom_append_of_eq _
        (ihLeft
          (pushFormula (Encodable.encode formula)
            (pushSequent (⌜Gamma⌝ : Nat) initial)))]
      rw [runPostfixFrom_append_of_eq _
        (ihRight
          (pushProof left.rawCode (⌜left.conclusion⌝ : Nat)
            (pushFormula (Encodable.encode formula)
              (pushSequent (⌜Gamma⌝ : Nat) initial))))]
      rw [runPostfixFrom_singleton, postfixStep_proofCutToken]
      simp [
        CheckedPAProofTree.rawCode, CheckedPAProofTree.conclusion,
        LO.FirstOrder.Semiformula.quote_eq_encode]

@[simp] theorem postfixResult_proofPostfixTokens
    (b : CheckedPAProofTree) :
    postfixResult (proofPostfixTokens b) =
      some (b.rawCode, (⌜b.conclusion⌝ : Nat)) := by
  simp [postfixResult, runPostfix,
    runPostfixFrom_proofPostfixTokens,
    decodeTaggedValue, proofValueTag,
    pushProof, taggedValue]

def postfixTokenBitLength (tokens : List Nat) : Nat :=
  (tokens.flatMap binaryNatCode).length

def PostfixPAProofChecks
    (tokens : List Nat) (formulaCode : Nat) : Prop :=
  ∃ rawCode : Nat,
    postfixResult tokens = some (rawCode, 2 ^ formulaCode) ∧
      LO.FirstOrder.Arithmetic.Bootstrapping.Proof
        F.PA rawCode formulaCode

def EfficientPostfixPAProofPredicate
    (bound formulaCode : Nat) : Prop :=
  ∃ tokens : List Nat,
    postfixTokenBitLength tokens ≤ bound ∧
      PostfixPAProofChecks tokens formulaCode

def checkedPAProofTreePostfixLength (b : CheckedPAProofTree) : Nat :=
  postfixTokenBitLength (proofPostfixTokens b)

theorem proves_postfixChecks
    {b : CheckedPAProofTree}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (h : b.Proves formula) :
    PostfixPAProofChecks (proofPostfixTokens b)
      (Encodable.encode formula) := by
  refine ⟨b.rawCode, ?_, h.rawProof⟩
  rw [postfixResult_proofPostfixTokens, h.2]
  simp [LO.FirstOrder.Derivation2.Sequent.quote_def,
    LO.FirstOrder.Semiformula.quote_eq_encode]

theorem proves_efficientPostfixPredicate
    {b : CheckedPAProofTree}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (h : b.Proves formula) :
    EfficientPostfixPAProofPredicate
      (checkedPAProofTreePostfixLength b)
      (Encodable.encode formula) := by
  exact ⟨proofPostfixTokens b, le_rfl, proves_postfixChecks h⟩

theorem derivation_to_efficientPostfixPredicate
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (b : LO.FirstOrder.Derivation2 F.PA Gamma)
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hGamma : Gamma = {formula}) :
    EfficientPostfixPAProofPredicate
      (checkedPAProofTreePostfixLength
        (CheckedPAProofTree.ofDerivation b))
      (Encodable.encode formula) := by
  let tree := CheckedPAProofTree.ofDerivation b
  have hproves : tree.Proves formula := by
    constructor
    · exact CheckedPAProofTree.valid_ofDerivation b
    · simpa [tree] using hGamma
  simpa [tree] using proves_efficientPostfixPredicate hproves

theorem postfixPAProofChecks_sound
    {tokens : List Nat}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hcheck :
      PostfixPAProofChecks tokens (Encodable.encode formula)) :
    Nonempty (LO.FirstOrder.Derivation2 F.PA {formula}) := by
  rcases hcheck with ⟨rawCode, _, hraw⟩
  exact ⟨
    LO.FirstOrder.Arithmetic.Bootstrapping.Provable.sound2
      (T := F.PA) (by
        refine ⟨rawCode, ?_⟩
        simpa [LO.FirstOrder.Semiformula.quote_eq_encode] using hraw)⟩

end FoundationEfficientPAProofPredicateArithmetic
