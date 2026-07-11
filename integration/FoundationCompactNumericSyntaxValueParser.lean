import integration.FoundationCompactListedPackedBitTokenSynchronization
import integration.FoundationCompactSyntaxTokenMachineInversion

/-!
# Numeric syntax value parsers for the compact verifier

The structural token machines used so far return only the unconsumed suffix.
Local proof checking also needs the consumed term and formula values.  This
file records each value by its exact canonical natural-token slice while
retaining a wholly numeric, primitive-recursive implementation.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericSyntaxValueParser

open FoundationCompactSyntaxTokenMachine
open FoundationCompactSyntaxTokenMachineInversion
open FoundationCompactProofTokenMachine

def consumedTokenPrefix
    (tokens suffix : List Nat) : List Nat :=
  tokens.take (tokens.length - suffix.length)

@[simp] theorem consumedTokenPrefix_append
    (front suffix : List Nat) :
    consumedTokenPrefix (front ++ suffix) suffix = front := by
  simp [consumedTokenPrefix]

theorem consumedTokenPrefix_primrec :
    Primrec₂ consumedTokenPrefix := by
  apply Primrec₂.mk
  let Input := List Nat × List Nat
  have htokens : Primrec (fun input : Input => input.1) :=
    Primrec.fst
  have hsuffix : Primrec (fun input : Input => input.2) :=
    Primrec.snd
  have htokenLength : Primrec (fun input : Input => input.1.length) :=
    Primrec.list_length.comp htokens
  have hsuffixLength : Primrec (fun input : Input => input.2.length) :=
    Primrec.list_length.comp hsuffix
  have hconsumed : Primrec (fun input : Input =>
      input.1.length - input.2.length) :=
    Primrec.nat_sub.comp htokenLength hsuffixLength
  exact
    (Primrec.list_take.comp hconsumed htokens).of_eq
      fun input => by rfl

def compactTermTokenValueParser
    (binderArity : Nat) (tokens : List Nat) :
    Option (List Nat × List Nat) :=
  (compactTermTokenParser binderArity tokens).map fun suffix =>
    (consumedTokenPrefix tokens suffix, suffix)

def compactFormulaTokenValueParser
    (binderArity : Nat) (tokens : List Nat) :
    Option (List Nat × List Nat) :=
  (compactFormulaTokenParser binderArity tokens).map fun suffix =>
    (consumedTokenPrefix tokens suffix, suffix)

theorem compactTermTokenValueParser_primrec :
    Primrec₂ compactTermTokenValueParser := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  have hbinder : Primrec (fun input : Input => input.1) :=
    Primrec.fst
  have htokens : Primrec (fun input : Input => input.2) :=
    Primrec.snd
  have hparser : Primrec (fun input : Input =>
      compactTermTokenParser input.1 input.2) :=
    compactTermTokenParser_primrec.comp hbinder htokens
  have hprefix : Primrec₂ (fun (input : Input) (suffix : List Nat) =>
      consumedTokenPrefix input.2 suffix) :=
    consumedTokenPrefix_primrec.comp₂
      ((Primrec.snd.comp Primrec.fst).to₂) Primrec₂.right
  have hresult : Primrec₂ (fun (input : Input) (suffix : List Nat) =>
      (consumedTokenPrefix input.2 suffix, suffix)) :=
    Primrec₂.pair.comp₂ hprefix Primrec₂.right
  exact
    (Primrec.option_map hparser hresult).of_eq fun input => by
      simp [compactTermTokenValueParser]

theorem compactFormulaTokenValueParser_primrec :
    Primrec₂ compactFormulaTokenValueParser := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  have hbinder : Primrec (fun input : Input => input.1) :=
    Primrec.fst
  have htokens : Primrec (fun input : Input => input.2) :=
    Primrec.snd
  have hparser : Primrec (fun input : Input =>
      compactFormulaTokenParser input.1 input.2) :=
    compactFormulaTokenParser_primrec.comp hbinder htokens
  have hprefix : Primrec₂ (fun (input : Input) (suffix : List Nat) =>
      consumedTokenPrefix input.2 suffix) :=
    consumedTokenPrefix_primrec.comp₂
      ((Primrec.snd.comp Primrec.fst).to₂) Primrec₂.right
  have hresult : Primrec₂ (fun (input : Input) (suffix : List Nat) =>
      (consumedTokenPrefix input.2 suffix, suffix)) :=
    Primrec₂.pair.comp₂ hprefix Primrec₂.right
  exact
    (Primrec.option_map hparser hresult).of_eq fun input => by
      simp [compactFormulaTokenValueParser]

@[simp] theorem compactTermTokenValueParser_canonical_append
    {binderArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix : List Nat) :
    compactTermTokenValueParser binderArity
        (compactArithmeticTermTokens term ++ suffix) =
      some (compactArithmeticTermTokens term, suffix) := by
  simp [compactTermTokenValueParser,
    compactTermTokenParser_canonical_append]

@[simp] theorem compactFormulaTokenValueParser_canonical_append
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix : List Nat) :
    compactFormulaTokenValueParser binderArity
        (compactArithmeticFormulaTokens formula ++ suffix) =
      some (compactArithmeticFormulaTokens formula, suffix) := by
  simp [compactFormulaTokenValueParser,
    compactFormulaTokenParser_canonical_append]

theorem compactTermTokenValueParser_sound
    {binderArity : Nat} {tokens value suffix : List Nat}
    (hparser : compactTermTokenValueParser binderArity tokens =
      some (value, suffix)) :
    exists term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity,
      tokens = compactArithmeticTermTokens term ++ suffix /\
        value = compactArithmeticTermTokens term := by
  cases hraw : compactTermTokenParser binderArity tokens with
  | none =>
      simp [compactTermTokenValueParser, hraw] at hparser
  | some rawSuffix =>
      simp [compactTermTokenValueParser, hraw] at hparser
      rcases hparser with ⟨rfl, rfl⟩
      obtain ⟨term, htokens⟩ :=
        (compactTermTokenParser_success_iff
          binderArity tokens rawSuffix).mp hraw
      subst tokens
      exact ⟨term, rfl, consumedTokenPrefix_append _ _⟩

theorem compactFormulaTokenValueParser_sound
    {binderArity : Nat} {tokens value suffix : List Nat}
    (hparser : compactFormulaTokenValueParser binderArity tokens =
      some (value, suffix)) :
    exists formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity,
      tokens = compactArithmeticFormulaTokens formula ++ suffix /\
        value = compactArithmeticFormulaTokens formula := by
  cases hraw : compactFormulaTokenParser binderArity tokens with
  | none =>
      simp [compactFormulaTokenValueParser, hraw] at hparser
  | some rawSuffix =>
      simp [compactFormulaTokenValueParser, hraw] at hparser
      rcases hparser with ⟨rfl, rfl⟩
      obtain ⟨formula, htokens⟩ :=
        (compactFormulaTokenParser_success_iff
          binderArity tokens rawSuffix).mp hraw
      subst tokens
      exact ⟨formula, rfl, consumedTokenPrefix_append _ _⟩

/-! ## Sequent values -/

abbrev CompactFormulaTokenValuesResult :=
  Option (List (List Nat) × List Nat)

def compactFormulaTokenValuesStep
    (state : CompactFormulaTokenValuesResult) :
    CompactFormulaTokenValuesResult :=
  state.bind fun parsed =>
    (compactFormulaTokenValueParser 0 parsed.2).map fun formulaResult =>
      (parsed.1 ++ [formulaResult.1], formulaResult.2)

@[simp] theorem compactFormulaTokenValuesStep_iterate_none
    (count : Nat) :
    (compactFormulaTokenValuesStep^[count]) none = none := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply]
      change (compactFormulaTokenValuesStep^[count]) none = none
      exact ih

theorem compactFormulaTokenValuesStep_primrec :
    Primrec compactFormulaTokenValuesStep := by
  have hcontinue : Primrec
      (fun parsed : List (List Nat) × List Nat =>
        (compactFormulaTokenValueParser 0 parsed.2).map
          fun formulaResult =>
            (parsed.1 ++ [formulaResult.1], formulaResult.2)) := by
    have hparser : Primrec
        (fun parsed : List (List Nat) × List Nat =>
          compactFormulaTokenValueParser 0 parsed.2) :=
      compactFormulaTokenValueParser_primrec.comp
        (Primrec.const 0) Primrec.snd
    have happend : Primrec₂
        (fun (parsed : List (List Nat) × List Nat)
            (formulaResult : List Nat × List Nat) =>
          parsed.1 ++ [formulaResult.1]) :=
      Primrec.list_concat.comp₂
        (Primrec.fst.comp₂ Primrec₂.left)
        (Primrec.fst.comp₂ Primrec₂.right)
    have hresult : Primrec₂
        (fun (parsed : List (List Nat) × List Nat)
            (formulaResult : List Nat × List Nat) =>
          (parsed.1 ++ [formulaResult.1], formulaResult.2)) :=
      Primrec₂.pair.comp₂ happend
        (Primrec.snd.comp₂ Primrec₂.right)
    exact Primrec.option_map hparser hresult
  exact
    (Primrec.option_bind Primrec.id
      ((hcontinue.comp Primrec.snd).to₂)).of_eq fun state => by
        cases state <;> rfl

def compactFormulaTokenValuesInitial
    (tokens : List Nat) : CompactFormulaTokenValuesResult :=
  some ([], tokens)

theorem compactFormulaTokenValuesInitial_primrec :
    Primrec compactFormulaTokenValuesInitial := by
  exact Primrec.option_some.comp
    (Primrec.pair (Primrec.const []) Primrec.id)

def compactFormulaTokenValuesRepeat
    (count : Nat) (tokens : List Nat) :
    CompactFormulaTokenValuesResult :=
  (compactFormulaTokenValuesStep^[count])
    (compactFormulaTokenValuesInitial tokens)

theorem compactFormulaTokenValuesRepeat_primrec :
    Primrec₂ compactFormulaTokenValuesRepeat := by
  apply Primrec₂.mk
  have hfuel : Primrec
      (fun input : Nat × List Nat => input.1) :=
    Primrec.fst
  have hinitial : Primrec
      (fun input : Nat × List Nat =>
        compactFormulaTokenValuesInitial input.2) :=
    compactFormulaTokenValuesInitial_primrec.comp Primrec.snd
  have hstep : Primrec₂
      (fun (_input : Nat × List Nat)
          (state : CompactFormulaTokenValuesResult) =>
        compactFormulaTokenValuesStep state) :=
    (compactFormulaTokenValuesStep_primrec.comp Primrec.snd).to₂
  exact
    (Primrec.nat_iterate hfuel hinitial hstep).of_eq
      fun input => by rfl

theorem compactFormulaTokenValues_iterate_canonical
    (initialValues : List (List Nat))
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (suffix : List Nat) :
    (compactFormulaTokenValuesStep^[Gamma.length])
        (some (initialValues,
          Gamma.flatMap compactArithmeticFormulaTokens ++ suffix)) =
      some (initialValues ++
        Gamma.map compactArithmeticFormulaTokens, suffix) := by
  induction Gamma generalizing initialValues with
  | nil => simp
  | cons formula Gamma ih =>
      simp [Function.iterate_succ_apply,
        compactFormulaTokenValuesStep, ih, List.append_assoc]

@[simp] theorem compactFormulaTokenValuesRepeat_canonical
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (suffix : List Nat) :
    compactFormulaTokenValuesRepeat Gamma.length
        (Gamma.flatMap compactArithmeticFormulaTokens ++ suffix) =
      some (Gamma.map compactArithmeticFormulaTokens, suffix) := by
  simpa [compactFormulaTokenValuesRepeat,
    compactFormulaTokenValuesInitial] using
      compactFormulaTokenValues_iterate_canonical [] Gamma suffix

theorem compactFormulaTokenValues_iterate_sound
    {count : Nat} {initialValues outputValues : List (List Nat)}
    {tokens suffix : List Nat}
    (hrun : (compactFormulaTokenValuesStep^[count])
        (some (initialValues, tokens)) =
      some (outputValues, suffix)) :
    exists Gamma : List LO.FirstOrder.ArithmeticProposition,
      Gamma.length = count /\
        tokens = Gamma.flatMap compactArithmeticFormulaTokens ++ suffix /\
        outputValues = initialValues ++
          Gamma.map compactArithmeticFormulaTokens := by
  induction count generalizing initialValues tokens with
  | zero =>
      simp at hrun
      rcases hrun with ⟨rfl, rfl⟩
      exact ⟨[], rfl, by simp, by simp⟩
  | succ count ih =>
      rw [Function.iterate_succ_apply] at hrun
      cases hformula : compactFormulaTokenValueParser 0 tokens with
      | none =>
          simp [compactFormulaTokenValuesStep, hformula] at hrun
      | some formulaResult =>
          rcases formulaResult with ⟨formulaValue, afterFormula⟩
          have hstep :
              compactFormulaTokenValuesStep
                  (some (initialValues, tokens)) =
                some (initialValues ++ [formulaValue], afterFormula) := by
            simp [compactFormulaTokenValuesStep, hformula]
          rw [hstep] at hrun
          obtain ⟨Gamma, hlength, hafter, houtput⟩ := ih hrun
          obtain ⟨formula, htokens, hvalue⟩ :=
            compactFormulaTokenValueParser_sound hformula
          refine ⟨formula :: Gamma, by simp [hlength], ?_, ?_⟩
          · rw [htokens, hafter]
            simp [List.append_assoc]
          · rw [houtput, hvalue]
            simp [List.append_assoc]

theorem compactFormulaTokenValuesRepeat_sound
    {count : Nat} {tokens suffix : List Nat}
    {values : List (List Nat)}
    (hrun : compactFormulaTokenValuesRepeat count tokens =
      some (values, suffix)) :
    exists Gamma : List LO.FirstOrder.ArithmeticProposition,
      Gamma.length = count /\
        tokens = Gamma.flatMap compactArithmeticFormulaTokens ++ suffix /\
        values = Gamma.map compactArithmeticFormulaTokens := by
  have hresult := compactFormulaTokenValues_iterate_sound
    (initialValues := [])
    (by simpa [compactFormulaTokenValuesRepeat,
      compactFormulaTokenValuesInitial] using hrun)
  simpa using hresult

def compactSequentTokenValueParser
    (tokens : List Nat) : Option (List (List Nat) × List Nat) :=
  tokens.head?.bind fun count =>
    compactFormulaTokenValuesRepeat count tokens.tail

theorem compactSequentTokenValueParser_primrec :
    Primrec compactSequentTokenValueParser := by
  have hcontinue : Primrec₂
      (fun (tokens : List Nat) (count : Nat) =>
        compactFormulaTokenValuesRepeat count tokens.tail) :=
    compactFormulaTokenValuesRepeat_primrec.comp₂
      Primrec₂.right
      (Primrec.list_tail.comp₂ Primrec₂.left)
  exact
    (Primrec.option_bind Primrec.list_head? hcontinue).of_eq
      fun tokens => by rfl

@[simp] theorem compactSequentTokenValueParser_canonical_append
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (suffix : List Nat) :
    compactSequentTokenValueParser
        (compactSequentListTokens Gamma ++ suffix) =
      some (Gamma.map compactArithmeticFormulaTokens, suffix) := by
  simp [compactSequentTokenValueParser, compactSequentListTokens]

theorem compactSequentTokenValueParser_sound
    {tokens suffix : List Nat} {values : List (List Nat)}
    (hparser : compactSequentTokenValueParser tokens =
      some (values, suffix)) :
    exists Gamma : List LO.FirstOrder.ArithmeticProposition,
      tokens = compactSequentListTokens Gamma ++ suffix /\
        values = Gamma.map compactArithmeticFormulaTokens := by
  cases tokens with
  | nil =>
      simp [compactSequentTokenValueParser] at hparser
  | cons count tail =>
      simp only [compactSequentTokenValueParser, List.head?_cons,
        List.tail_cons, Option.bind_some] at hparser
      obtain ⟨Gamma, hlength, htail, hvalues⟩ :=
        compactFormulaTokenValuesRepeat_sound hparser
      refine ⟨Gamma, ?_, hvalues⟩
      simp [compactSequentListTokens, hlength, htail]

#print axioms consumedTokenPrefix_primrec
#print axioms compactTermTokenValueParser_primrec
#print axioms compactFormulaTokenValueParser_primrec
#print axioms compactTermTokenValueParser_sound
#print axioms compactFormulaTokenValueParser_sound
#print axioms compactFormulaTokenValuesRepeat_primrec
#print axioms compactFormulaTokenValuesRepeat_sound
#print axioms compactSequentTokenValueParser_primrec
#print axioms compactSequentTokenValueParser_sound

end FoundationCompactNumericSyntaxValueParser
