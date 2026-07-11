import integration.FoundationCompactNumericListedRuleChecks

/-!
# Pure numeric immediate-field parsers for listed proof nodes

Each parser consumes only the fields stored at one proof node.  Recursive child
proof tokens are returned untouched as the suffix.  A later task machine uses
that suffix to traverse children in the public serialization order.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedNodeFields

open FoundationCompactSyntaxTokenMachine
open FoundationCompactClosedFormulaTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactListedProofDecoder
open FoundationCompactNumericFormulaListChecks
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertificateTokenMachine

abbrev CompactNumericNodeFields :=
  List (List Nat) ×
    (List Nat × (List Nat × (List Nat × List Nat)))

def compactNumericNodeFieldsSuffix
    (fields : CompactNumericNodeFields) : List Nat :=
  fields.2.2.2.2

def compactNodeSequentOnlyFields
  (tokens : List Nat) : Option CompactNumericNodeFields :=
  (compactSequentTokenValueParser tokens).map fun parsed =>
    (parsed.1, (([] : List Nat),
      (([] : List Nat), (([] : List Nat), parsed.2))))

theorem compactNodeSequentOnlyFields_primrec :
    Primrec compactNodeSequentOnlyFields := by
  have hresult : Primrec₂
      (fun (_tokens : List Nat)
          (parsed : List (List Nat) × List Nat) =>
        (parsed.1, (([] : List Nat),
          (([] : List Nat), (([] : List Nat), parsed.2))))) :=
    Primrec₂.pair.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec₂.pair.comp₂ (Primrec₂.const ([] : List Nat))
        (Primrec₂.pair.comp₂ (Primrec₂.const ([] : List Nat))
          (Primrec₂.pair.comp₂ (Primrec₂.const ([] : List Nat))
            (Primrec.snd.comp₂ Primrec₂.right))))
  exact
    (Primrec.option_map compactSequentTokenValueParser_primrec hresult).of_eq
      fun tokens => by
        simp [compactNodeSequentOnlyFields]

@[simp] theorem compactNodeSequentOnlyFields_canonical_append
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (suffix : List Nat) :
    compactNodeSequentOnlyFields
        (compactSequentListTokens Gamma ++ suffix) =
      some (arithmeticPropositionTokenValues Gamma,
        (([] : List Nat),
          (([] : List Nat), (([] : List Nat), suffix)))) := by
  simp [compactNodeSequentOnlyFields,
    arithmeticPropositionTokenValue,
    arithmeticPropositionTokenValues]

def compactNodeSequentFormulaFields
    (binderArity : Nat) (tokens : List Nat) :
    Option CompactNumericNodeFields := do
  let parsedSequent <- compactSequentTokenValueParser tokens
  (compactFormulaTokenValueParser binderArity parsedSequent.2).map
    fun parsedFormula =>
      (parsedSequent.1,
        (parsedFormula.1, (([] : List Nat),
          (([] : List Nat), parsedFormula.2))))

theorem compactNodeSequentFormulaFields_primrec
    (binderArity : Nat) :
    Primrec (compactNodeSequentFormulaFields binderArity) := by
  have hcontinue : Primrec₂
      (fun (_tokens : List Nat)
          (parsedSequent : List (List Nat) × List Nat) =>
        (compactFormulaTokenValueParser binderArity
          parsedSequent.2).map fun parsedFormula =>
            (parsedSequent.1,
              (parsedFormula.1, (([] : List Nat),
                (([] : List Nat), parsedFormula.2))))) := by
    apply Primrec₂.mk
    let State := List Nat × (List (List Nat) × List Nat)
    have hformula : Primrec (fun state : State =>
        compactFormulaTokenValueParser binderArity state.2.2) :=
      compactFormulaTokenValueParser_primrec.comp
        (Primrec.const binderArity)
        (Primrec.snd.comp Primrec.snd)
    have hresult : Primrec₂
        (fun (state : State) (parsedFormula : List Nat × List Nat) =>
          (state.2.1,
            (parsedFormula.1, (([] : List Nat),
              (([] : List Nat), parsedFormula.2))))) :=
      Primrec₂.pair.comp₂
        ((Primrec.fst.comp
          (Primrec.snd.comp Primrec.fst)).to₂)
        (Primrec₂.pair.comp₂
          (Primrec.fst.comp₂ Primrec₂.right)
          (Primrec₂.pair.comp₂ (Primrec₂.const ([] : List Nat))
            (Primrec₂.pair.comp₂ (Primrec₂.const ([] : List Nat))
              (Primrec.snd.comp₂ Primrec₂.right))))
    exact Primrec.option_map hformula hresult
  exact
    (Primrec.option_bind compactSequentTokenValueParser_primrec
      hcontinue).of_eq fun tokens => by
        simp [compactNodeSequentFormulaFields]

@[simp] theorem compactNodeSequentFormulaFields_canonical_append
    {binderArity : Nat}
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix : List Nat) :
    compactNodeSequentFormulaFields binderArity
        (compactSequentListTokens Gamma ++
          compactArithmeticFormulaTokens formula ++ suffix) =
      some (arithmeticPropositionTokenValues Gamma,
        (compactArithmeticFormulaTokens formula,
          (([] : List Nat), (([] : List Nat), suffix)))) := by
  simp [compactNodeSequentFormulaFields,
    List.append_assoc, arithmeticPropositionTokenValue,
    arithmeticPropositionTokenValues]

def compactNodeSequentTwoFormulaFields
    (binderArity : Nat) (tokens : List Nat) :
    Option CompactNumericNodeFields := do
  let first <- compactNodeSequentFormulaFields binderArity tokens
  (compactFormulaTokenValueParser binderArity
    (compactNumericNodeFieldsSuffix first)).map fun second =>
      (first.1, (first.2.1,
        (second.1, (([] : List Nat), second.2))))

theorem compactNodeSequentTwoFormulaFields_primrec
    (binderArity : Nat) :
    Primrec (compactNodeSequentTwoFormulaFields binderArity) := by
  have hcontinue : Primrec₂
      (fun (_tokens : List Nat) (first : CompactNumericNodeFields) =>
        (compactFormulaTokenValueParser binderArity
          (compactNumericNodeFieldsSuffix first)).map fun second =>
            (first.1, (first.2.1,
              (second.1, (([] : List Nat), second.2))))) := by
    apply Primrec₂.mk
    let State := List Nat × CompactNumericNodeFields
    have hsuffix : Primrec (fun state : State =>
        compactNumericNodeFieldsSuffix state.2) := by
      exact Primrec.snd.comp
        (Primrec.snd.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    have hsecond : Primrec (fun state : State =>
        compactFormulaTokenValueParser binderArity
          (compactNumericNodeFieldsSuffix state.2)) :=
      compactFormulaTokenValueParser_primrec.comp
        (Primrec.const binderArity) hsuffix
    have hresult : Primrec₂
        (fun (state : State) (second : List Nat × List Nat) =>
          (state.2.1, (state.2.2.1,
            (second.1, (([] : List Nat), second.2))))) :=
      Primrec₂.pair.comp₂
        ((Primrec.fst.comp
          (Primrec.snd.comp Primrec.fst)).to₂)
        (Primrec₂.pair.comp₂
          ((Primrec.fst.comp
            (Primrec.snd.comp
              (Primrec.snd.comp Primrec.fst))).to₂)
          (Primrec₂.pair.comp₂
            (Primrec.fst.comp₂ Primrec₂.right)
            (Primrec₂.pair.comp₂ (Primrec₂.const ([] : List Nat))
              (Primrec.snd.comp₂ Primrec₂.right))))
    exact Primrec.option_map hsecond hresult
  exact
    (Primrec.option_bind
      (compactNodeSequentFormulaFields_primrec binderArity)
      hcontinue).of_eq fun tokens => by
        simp [compactNodeSequentTwoFormulaFields]

@[simp] theorem compactNodeSequentTwoFormulaFields_canonical_append
    {binderArity : Nat}
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (first second :
      LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix : List Nat) :
    compactNodeSequentTwoFormulaFields binderArity
        (compactSequentListTokens Gamma ++
          compactArithmeticFormulaTokens first ++
          compactArithmeticFormulaTokens second ++ suffix) =
      some (arithmeticPropositionTokenValues Gamma,
        (compactArithmeticFormulaTokens first,
          (compactArithmeticFormulaTokens second,
            (([] : List Nat), suffix)))) := by
  unfold compactNodeSequentTwoFormulaFields
  rw [show compactNodeSequentFormulaFields binderArity
      (compactSequentListTokens Gamma ++
        compactArithmeticFormulaTokens first ++
        compactArithmeticFormulaTokens second ++ suffix) =
      some (arithmeticPropositionTokenValues Gamma,
        (compactArithmeticFormulaTokens first,
          (([] : List Nat), (([] : List Nat),
            compactArithmeticFormulaTokens second ++ suffix)))) by
    simpa [List.append_assoc] using
      compactNodeSequentFormulaFields_canonical_append
        Gamma first
          (compactArithmeticFormulaTokens second ++ suffix)]
  simp [compactNumericNodeFieldsSuffix]

def compactNodeSequentFormulaTermFields
    (formulaArity termArity : Nat) (tokens : List Nat) :
    Option CompactNumericNodeFields := do
  let first <- compactNodeSequentFormulaFields formulaArity tokens
  (compactTermTokenValueParser termArity
    (compactNumericNodeFieldsSuffix first)).map fun term =>
      (first.1, (first.2.1,
        (([] : List Nat), (term.1, term.2))))

theorem compactNodeSequentFormulaTermFields_primrec
    (formulaArity termArity : Nat) :
    Primrec (compactNodeSequentFormulaTermFields
      formulaArity termArity) := by
  have hcontinue : Primrec₂
      (fun (_tokens : List Nat) (first : CompactNumericNodeFields) =>
        (compactTermTokenValueParser termArity
          (compactNumericNodeFieldsSuffix first)).map fun term =>
            (first.1, (first.2.1,
              (([] : List Nat), (term.1, term.2))))) := by
    apply Primrec₂.mk
    let State := List Nat × CompactNumericNodeFields
    have hsuffix : Primrec (fun state : State =>
        compactNumericNodeFieldsSuffix state.2) := by
      exact Primrec.snd.comp
        (Primrec.snd.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    have hterm : Primrec (fun state : State =>
        compactTermTokenValueParser termArity
          (compactNumericNodeFieldsSuffix state.2)) :=
      compactTermTokenValueParser_primrec.comp
        (Primrec.const termArity) hsuffix
    have hresult : Primrec₂
        (fun (state : State) (term : List Nat × List Nat) =>
          (state.2.1, (state.2.2.1,
            (([] : List Nat), (term.1, term.2))))) :=
      Primrec₂.pair.comp₂
        ((Primrec.fst.comp
          (Primrec.snd.comp Primrec.fst)).to₂)
        (Primrec₂.pair.comp₂
          ((Primrec.fst.comp
            (Primrec.snd.comp
              (Primrec.snd.comp Primrec.fst))).to₂)
          (Primrec₂.pair.comp₂ (Primrec₂.const ([] : List Nat))
            (Primrec₂.pair.comp₂
              (Primrec.fst.comp₂ Primrec₂.right)
              (Primrec.snd.comp₂ Primrec₂.right))))
    exact Primrec.option_map hterm hresult
  exact
    (Primrec.option_bind
      (compactNodeSequentFormulaFields_primrec formulaArity)
      hcontinue).of_eq fun tokens => by
        simp [compactNodeSequentFormulaTermFields]

@[simp] theorem compactNodeSequentFormulaTermFields_canonical_append
    {formulaArity termArity : Nat}
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat formulaArity)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat termArity)
    (suffix : List Nat) :
    compactNodeSequentFormulaTermFields formulaArity termArity
        (compactSequentListTokens Gamma ++
          compactArithmeticFormulaTokens formula ++
          compactArithmeticTermTokens term ++ suffix) =
      some (arithmeticPropositionTokenValues Gamma,
        (compactArithmeticFormulaTokens formula,
          (([] : List Nat),
            (compactArithmeticTermTokens term, suffix)))) := by
  unfold compactNodeSequentFormulaTermFields
  rw [show compactNodeSequentFormulaFields formulaArity
      (compactSequentListTokens Gamma ++
        compactArithmeticFormulaTokens formula ++
        compactArithmeticTermTokens term ++ suffix) =
      some (arithmeticPropositionTokenValues Gamma,
        (compactArithmeticFormulaTokens formula,
          (([] : List Nat), (([] : List Nat),
            compactArithmeticTermTokens term ++ suffix)))) by
    simpa [List.append_assoc] using
      compactNodeSequentFormulaFields_canonical_append
        Gamma formula
          (compactArithmeticTermTokens term ++ suffix)]
  simp [compactNumericNodeFieldsSuffix]

def compactClosedFormulaTokenValueParser
    (tokens : List Nat) : Option (List Nat × List Nat) :=
  (compactClosedFormulaTokenParser 0 tokens).map fun suffix =>
    (consumedTokenPrefix tokens suffix, suffix)

theorem compactClosedFormulaTokenValueParser_primrec :
    Primrec compactClosedFormulaTokenValueParser := by
  have hparser : Primrec (fun tokens : List Nat =>
      compactClosedFormulaTokenParser 0 tokens) :=
    compactClosedFormulaTokenParser_primrec.comp
      (Primrec.const 0) Primrec.id
  have hprefix : Primrec₂
      (fun (tokens : List Nat) (suffix : List Nat) =>
        consumedTokenPrefix tokens suffix) :=
    consumedTokenPrefix_primrec
  have hresult : Primrec₂
      (fun (tokens : List Nat) (suffix : List Nat) =>
        (consumedTokenPrefix tokens suffix, suffix)) :=
    Primrec₂.pair.comp₂ hprefix Primrec₂.right
  exact
    (Primrec.option_map hparser hresult).of_eq fun tokens => by
      simp [compactClosedFormulaTokenValueParser]

@[simp] theorem compactClosedFormulaTokenValueParser_canonical_append
    (sentence : LO.FirstOrder.ArithmeticSentence)
    (suffix : List Nat) :
    compactClosedFormulaTokenValueParser
        (compactArithmeticFormulaTokens
            (Rewriting.emb sentence :
              LO.FirstOrder.ArithmeticProposition) ++ suffix) =
      some (compactArithmeticFormulaTokens
          (Rewriting.emb sentence :
            LO.FirstOrder.ArithmeticProposition), suffix) := by
  simp [compactClosedFormulaTokenValueParser,
    compactClosedFormulaTokenParser_canonical_append]

def compactNodeSequentClosedFormulaFields
    (tokens : List Nat) : Option CompactNumericNodeFields := do
  let parsedSequent <- compactSequentTokenValueParser tokens
  (compactClosedFormulaTokenValueParser parsedSequent.2).map
    fun parsedFormula =>
      (parsedSequent.1,
        (parsedFormula.1, (([] : List Nat),
          (([] : List Nat), parsedFormula.2))))

theorem compactNodeSequentClosedFormulaFields_primrec :
    Primrec compactNodeSequentClosedFormulaFields := by
  have hcontinue : Primrec₂
      (fun (_tokens : List Nat)
          (parsedSequent : List (List Nat) × List Nat) =>
        (compactClosedFormulaTokenValueParser
          parsedSequent.2).map fun parsedFormula =>
            (parsedSequent.1,
              (parsedFormula.1, (([] : List Nat),
                (([] : List Nat), parsedFormula.2))))) := by
    apply Primrec₂.mk
    let State := List Nat × (List (List Nat) × List Nat)
    have hformula : Primrec (fun state : State =>
        compactClosedFormulaTokenValueParser state.2.2) :=
      compactClosedFormulaTokenValueParser_primrec.comp
        (Primrec.snd.comp Primrec.snd)
    have hresult : Primrec₂
        (fun (state : State) (parsedFormula : List Nat × List Nat) =>
          (state.2.1,
            (parsedFormula.1, (([] : List Nat),
              (([] : List Nat), parsedFormula.2))))) :=
      Primrec₂.pair.comp₂
        ((Primrec.fst.comp
          (Primrec.snd.comp Primrec.fst)).to₂)
        (Primrec₂.pair.comp₂
          (Primrec.fst.comp₂ Primrec₂.right)
          (Primrec₂.pair.comp₂ (Primrec₂.const ([] : List Nat))
            (Primrec₂.pair.comp₂ (Primrec₂.const ([] : List Nat))
              (Primrec.snd.comp₂ Primrec₂.right))))
    exact Primrec.option_map hformula hresult
  exact
    (Primrec.option_bind compactSequentTokenValueParser_primrec
      hcontinue).of_eq fun tokens => by
        simp [compactNodeSequentClosedFormulaFields]

@[simp] theorem compactNodeSequentClosedFormulaFields_canonical_append
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (sentence : LO.FirstOrder.ArithmeticSentence)
    (suffix : List Nat) :
    compactNodeSequentClosedFormulaFields
        (compactSequentListTokens Gamma ++
          compactArithmeticFormulaTokens
            (Rewriting.emb sentence :
              LO.FirstOrder.ArithmeticProposition) ++ suffix) =
      some (arithmeticPropositionTokenValues Gamma,
        (compactArithmeticFormulaTokens
            (Rewriting.emb sentence :
              LO.FirstOrder.ArithmeticProposition),
          (([] : List Nat), (([] : List Nat), suffix)))) := by
  simp [compactNodeSequentClosedFormulaFields,
    List.append_assoc, arithmeticPropositionTokenValue,
    arithmeticPropositionTokenValues]

/-! ## Proof-node tag dispatch -/

def compactTagNumericNodeFields
    (tag : Nat) (fields : Option CompactNumericNodeFields) :
    Option (Nat × CompactNumericNodeFields) :=
  fields.map fun value => (tag, value)

theorem compactTagNumericNodeFields_primrec :
    Primrec₂ compactTagNumericNodeFields := by
  apply Primrec₂.mk
  let Input := Nat × Option CompactNumericNodeFields
  have hfields : Primrec (fun input : Input => input.2) :=
    Primrec.snd
  have hresult : Primrec₂
      (fun (input : Input) (fields : CompactNumericNodeFields) =>
        (input.1, fields)) :=
    Primrec₂.pair.comp₂
      ((Primrec.fst.comp Primrec.fst).to₂) Primrec₂.right
  exact
    (Primrec.option_map hfields hresult).of_eq fun input => by
      simp [compactTagNumericNodeFields]

def compactListedProofNodeFieldsParser
    (tokens : List Nat) : Option (Nat × CompactNumericNodeFields) :=
  match tokens with
  | [] => none
  | tag :: suffix =>
      if tag = 0 then
        compactTagNumericNodeFields 0
          (compactNodeSequentFormulaFields 0 suffix)
      else if tag = 1 then
        compactTagNumericNodeFields 1
          (compactNodeSequentClosedFormulaFields suffix)
      else if tag = 2 then
        compactTagNumericNodeFields 2
          (compactNodeSequentOnlyFields suffix)
      else if tag = 3 then
        compactTagNumericNodeFields 3
          (compactNodeSequentTwoFormulaFields 0 suffix)
      else if tag = 4 then
        compactTagNumericNodeFields 4
          (compactNodeSequentTwoFormulaFields 0 suffix)
      else if tag = 5 then
        compactTagNumericNodeFields 5
          (compactNodeSequentFormulaFields 1 suffix)
      else if tag = 6 then
        compactTagNumericNodeFields 6
          (compactNodeSequentFormulaTermFields 1 0 suffix)
      else if tag = 7 then
        compactTagNumericNodeFields 7
          (compactNodeSequentOnlyFields suffix)
      else if tag = 8 then
        compactTagNumericNodeFields 8
          (compactNodeSequentOnlyFields suffix)
      else if tag = 9 then
        compactTagNumericNodeFields 9
          (compactNodeSequentFormulaFields 0 suffix)
      else
        none

theorem compactListedProofNodeFieldsParser_primrec :
    Primrec compactListedProofNodeFieldsParser := by
  have hempty : PrimrecPred (fun tokens : List Nat => tokens = []) :=
    Primrec.eq.comp Primrec.id (Primrec.const [])
  have htail : Primrec (fun tokens : List Nat => tokens.tail) :=
    Primrec.list_tail
  have htag : Primrec (fun tokens : List Nat =>
      tokens.head?.getD 10) :=
    Primrec.option_getD.comp Primrec.list_head? (Primrec.const 10)
  have htagEq (tag : Nat) : PrimrecPred (fun tokens : List Nat =>
      tokens.head?.getD 10 = tag) :=
    Primrec.eq.comp htag (Primrec.const tag)
  have hbranch (tag : Nat)
      (parser : List Nat -> Option CompactNumericNodeFields)
      (hparser : Primrec parser) :
      Primrec (fun tokens : List Nat =>
        compactTagNumericNodeFields tag (parser tokens.tail)) :=
    compactTagNumericNodeFields_primrec.comp
      (Primrec.const tag) (hparser.comp htail)
  have h0 := hbranch 0 (compactNodeSequentFormulaFields 0)
    (compactNodeSequentFormulaFields_primrec 0)
  have h1 := hbranch 1 compactNodeSequentClosedFormulaFields
    compactNodeSequentClosedFormulaFields_primrec
  have h2 := hbranch 2 compactNodeSequentOnlyFields
    compactNodeSequentOnlyFields_primrec
  have h3 := hbranch 3 (compactNodeSequentTwoFormulaFields 0)
    (compactNodeSequentTwoFormulaFields_primrec 0)
  have h4 := hbranch 4 (compactNodeSequentTwoFormulaFields 0)
    (compactNodeSequentTwoFormulaFields_primrec 0)
  have h5 := hbranch 5 (compactNodeSequentFormulaFields 1)
    (compactNodeSequentFormulaFields_primrec 1)
  have h6 := hbranch 6 (compactNodeSequentFormulaTermFields 1 0)
    (compactNodeSequentFormulaTermFields_primrec 1 0)
  have h7 := hbranch 7 compactNodeSequentOnlyFields
    compactNodeSequentOnlyFields_primrec
  have h8 := hbranch 8 compactNodeSequentOnlyFields
    compactNodeSequentOnlyFields_primrec
  have h9 := hbranch 9 (compactNodeSequentFormulaFields 0)
    (compactNodeSequentFormulaFields_primrec 0)
  have hnone : Primrec (fun _tokens : List Nat =>
      (none : Option (Nat × CompactNumericNodeFields))) :=
    Primrec.const none
  have hnonempty : Primrec (fun tokens : List Nat =>
      if tokens.head?.getD 10 = 0 then
        compactTagNumericNodeFields 0
          (compactNodeSequentFormulaFields 0 tokens.tail)
      else if tokens.head?.getD 10 = 1 then
        compactTagNumericNodeFields 1
          (compactNodeSequentClosedFormulaFields tokens.tail)
      else if tokens.head?.getD 10 = 2 then
        compactTagNumericNodeFields 2
          (compactNodeSequentOnlyFields tokens.tail)
      else if tokens.head?.getD 10 = 3 then
        compactTagNumericNodeFields 3
          (compactNodeSequentTwoFormulaFields 0 tokens.tail)
      else if tokens.head?.getD 10 = 4 then
        compactTagNumericNodeFields 4
          (compactNodeSequentTwoFormulaFields 0 tokens.tail)
      else if tokens.head?.getD 10 = 5 then
        compactTagNumericNodeFields 5
          (compactNodeSequentFormulaFields 1 tokens.tail)
      else if tokens.head?.getD 10 = 6 then
        compactTagNumericNodeFields 6
          (compactNodeSequentFormulaTermFields 1 0 tokens.tail)
      else if tokens.head?.getD 10 = 7 then
        compactTagNumericNodeFields 7
          (compactNodeSequentOnlyFields tokens.tail)
      else if tokens.head?.getD 10 = 8 then
        compactTagNumericNodeFields 8
          (compactNodeSequentOnlyFields tokens.tail)
      else if tokens.head?.getD 10 = 9 then
        compactTagNumericNodeFields 9
          (compactNodeSequentFormulaFields 0 tokens.tail)
      else none) :=
    Primrec.ite (htagEq 0) h0
      (Primrec.ite (htagEq 1) h1
        (Primrec.ite (htagEq 2) h2
          (Primrec.ite (htagEq 3) h3
            (Primrec.ite (htagEq 4) h4
              (Primrec.ite (htagEq 5) h5
                (Primrec.ite (htagEq 6) h6
                  (Primrec.ite (htagEq 7) h7
                    (Primrec.ite (htagEq 8) h8
                      (Primrec.ite (htagEq 9) h9 hnone)))))))))
  exact
    (Primrec.ite hempty hnone hnonempty).of_eq fun tokens => by
      cases tokens <;>
        simp [compactListedProofNodeFieldsParser]

def compactListedProofNodeExpectedFields
    (tree : ListedCheckedPAProofTree) (suffix : List Nat) :
    Nat × CompactNumericNodeFields :=
  match tree with
  | .closed Gamma formula =>
      (0, (arithmeticPropositionTokenValues Gamma,
        (arithmeticPropositionTokenValue formula,
          ([], ([], suffix)))))
  | .axm Gamma sentence =>
      (1, (arithmeticPropositionTokenValues Gamma,
        (arithmeticPropositionTokenValue
            (Rewriting.emb sentence :
              LO.FirstOrder.ArithmeticProposition),
          ([], ([], suffix)))))
  | .verum Gamma =>
      (2, (arithmeticPropositionTokenValues Gamma,
        ([], ([], ([], suffix)))))
  | .and Gamma leftFormula rightFormula left right =>
      (3, (arithmeticPropositionTokenValues Gamma,
        (arithmeticPropositionTokenValue leftFormula,
          (arithmeticPropositionTokenValue rightFormula,
            ([], compactListedProofTokens left ++
              compactListedProofTokens right ++ suffix)))))
  | .or Gamma leftFormula rightFormula premise =>
      (4, (arithmeticPropositionTokenValues Gamma,
        (arithmeticPropositionTokenValue leftFormula,
          (arithmeticPropositionTokenValue rightFormula,
            ([], compactListedProofTokens premise ++ suffix)))))
  | .all Gamma formula premise =>
      (5, (arithmeticPropositionTokenValues Gamma,
        (compactArithmeticFormulaTokens formula,
          ([], ([], compactListedProofTokens premise ++ suffix)))))
  | .exs Gamma formula witness premise =>
      (6, (arithmeticPropositionTokenValues Gamma,
        (compactArithmeticFormulaTokens formula,
          ([], (compactArithmeticTermTokens witness,
            compactListedProofTokens premise ++ suffix)))))
  | .wk Gamma premise =>
      (7, (arithmeticPropositionTokenValues Gamma,
        ([], ([], ([], compactListedProofTokens premise ++ suffix)))))
  | .shift Gamma premise =>
      (8, (arithmeticPropositionTokenValues Gamma,
        ([], ([], ([], compactListedProofTokens premise ++ suffix)))))
  | .cut Gamma formula left right =>
      (9, (arithmeticPropositionTokenValues Gamma,
        (arithmeticPropositionTokenValue formula,
          ([], ([], compactListedProofTokens left ++
            compactListedProofTokens right ++ suffix)))))

@[simp] theorem compactListedProofNodeFieldsParser_canonical_append
    (tree : ListedCheckedPAProofTree) (suffix : List Nat) :
    compactListedProofNodeFieldsParser
        (compactListedProofTokens tree ++ suffix) =
      some (compactListedProofNodeExpectedFields tree suffix) := by
  cases tree with
  | closed Gamma formula =>
      simpa [compactListedProofNodeFieldsParser,
        compactListedProofNodeExpectedFields,
        compactListedProofTokens, compactTagNumericNodeFields,
        List.append_assoc, arithmeticPropositionTokenValue] using
          compactNodeSequentFormulaFields_canonical_append
            Gamma formula suffix
  | axm Gamma sentence =>
      simpa [compactListedProofNodeFieldsParser,
        compactListedProofNodeExpectedFields,
        compactListedProofTokens, compactTagNumericNodeFields,
        List.append_assoc, arithmeticPropositionTokenValue] using
          compactNodeSequentClosedFormulaFields_canonical_append
            Gamma sentence suffix
  | verum Gamma =>
      simpa [compactListedProofNodeFieldsParser,
        compactListedProofNodeExpectedFields,
        compactListedProofTokens, compactTagNumericNodeFields] using
          compactNodeSequentOnlyFields_canonical_append Gamma suffix
  | and Gamma leftFormula rightFormula left right =>
      simpa [compactListedProofNodeFieldsParser,
        compactListedProofNodeExpectedFields,
        compactListedProofTokens, compactTagNumericNodeFields,
        List.append_assoc, arithmeticPropositionTokenValue] using
          compactNodeSequentTwoFormulaFields_canonical_append
            Gamma leftFormula rightFormula
              (compactListedProofTokens left ++
                compactListedProofTokens right ++ suffix)
  | or Gamma leftFormula rightFormula premise =>
      simpa [compactListedProofNodeFieldsParser,
        compactListedProofNodeExpectedFields,
        compactListedProofTokens, compactTagNumericNodeFields,
        List.append_assoc, arithmeticPropositionTokenValue] using
          compactNodeSequentTwoFormulaFields_canonical_append
            Gamma leftFormula rightFormula
              (compactListedProofTokens premise ++ suffix)
  | all Gamma formula premise =>
      simpa [compactListedProofNodeFieldsParser,
        compactListedProofNodeExpectedFields,
        compactListedProofTokens, compactTagNumericNodeFields,
        List.append_assoc] using
          compactNodeSequentFormulaFields_canonical_append
            Gamma formula (compactListedProofTokens premise ++ suffix)
  | exs Gamma formula witness premise =>
      simpa [compactListedProofNodeFieldsParser,
        compactListedProofNodeExpectedFields,
        compactListedProofTokens, compactTagNumericNodeFields,
        List.append_assoc] using
          compactNodeSequentFormulaTermFields_canonical_append
            Gamma formula witness
              (compactListedProofTokens premise ++ suffix)
  | wk Gamma premise =>
      simpa [compactListedProofNodeFieldsParser,
        compactListedProofNodeExpectedFields,
        compactListedProofTokens, compactTagNumericNodeFields,
        List.append_assoc] using
          compactNodeSequentOnlyFields_canonical_append Gamma
            (compactListedProofTokens premise ++ suffix)
  | shift Gamma premise =>
      simpa [compactListedProofNodeFieldsParser,
        compactListedProofNodeExpectedFields,
        compactListedProofTokens, compactTagNumericNodeFields,
        List.append_assoc] using
          compactNodeSequentOnlyFields_canonical_append Gamma
            (compactListedProofTokens premise ++ suffix)
  | cut Gamma formula left right =>
      simpa [compactListedProofNodeFieldsParser,
        compactListedProofNodeExpectedFields,
        compactListedProofTokens, compactTagNumericNodeFields,
        List.append_assoc, arithmeticPropositionTokenValue] using
          compactNodeSequentFormulaFields_canonical_append
            Gamma formula
              (compactListedProofTokens left ++
                compactListedProofTokens right ++ suffix)

/-! ## Structural-certificate node dispatch -/

abbrev CompactNumericCertificateNode := Nat × (List Nat × List Nat)

def compactStructuralCertificateNodeParser
    (tokens : List Nat) : Option CompactNumericCertificateNode :=
  match tokens with
  | [] => none
  | tag :: suffix =>
      if tag = 0 then some (0, ([], suffix))
      else if tag = 1 then
        (compactPAAxiomCertificateTokenParser suffix).map fun after =>
          (1, (consumedTokenPrefix suffix after, after))
      else if tag = 2 then some (2, ([], suffix))
      else if tag = 3 then some (3, ([], suffix))
      else none

theorem compactStructuralCertificateNodeParser_primrec :
    Primrec compactStructuralCertificateNodeParser := by
  have hempty : PrimrecPred (fun tokens : List Nat => tokens = []) :=
    Primrec.eq.comp Primrec.id (Primrec.const [])
  have htail : Primrec (fun tokens : List Nat => tokens.tail) :=
    Primrec.list_tail
  have htag : Primrec (fun tokens : List Nat =>
      tokens.head?.getD 4) :=
    Primrec.option_getD.comp Primrec.list_head? (Primrec.const 4)
  have htagEq (tag : Nat) : PrimrecPred (fun tokens : List Nat =>
      tokens.head?.getD 4 = tag) :=
    Primrec.eq.comp htag (Primrec.const tag)
  have hsimple (tag : Nat) : Primrec (fun tokens : List Nat =>
      some (tag, (([] : List Nat), tokens.tail))) :=
    Primrec.option_some.comp
      (Primrec.pair (Primrec.const tag)
        (Primrec.pair (Primrec.const ([] : List Nat)) htail))
  have hparser : Primrec (fun tokens : List Nat =>
      compactPAAxiomCertificateTokenParser tokens.tail) :=
    compactPAAxiomCertificateTokenParser_primrec.comp htail
  have haxiomResult : Primrec₂
      (fun (tokens : List Nat) (after : List Nat) =>
        (1, (consumedTokenPrefix tokens.tail after, after))) :=
    Primrec₂.pair.comp₂ (Primrec₂.const 1)
      (Primrec₂.pair.comp₂
        (consumedTokenPrefix_primrec.comp₂
          (Primrec.list_tail.comp₂ Primrec₂.left) Primrec₂.right)
        Primrec₂.right)
  have haxiom : Primrec (fun tokens : List Nat =>
      (compactPAAxiomCertificateTokenParser tokens.tail).map fun after =>
        (1, (consumedTokenPrefix tokens.tail after, after))) :=
    Primrec.option_map hparser haxiomResult
  have hnone : Primrec (fun _tokens : List Nat =>
      (none : Option CompactNumericCertificateNode)) :=
    Primrec.const none
  have hnonempty : Primrec (fun tokens : List Nat =>
      if tokens.head?.getD 4 = 0 then
        some (0, (([] : List Nat), tokens.tail))
      else if tokens.head?.getD 4 = 1 then
        (compactPAAxiomCertificateTokenParser tokens.tail).map fun after =>
          (1, (consumedTokenPrefix tokens.tail after, after))
      else if tokens.head?.getD 4 = 2 then
        some (2, (([] : List Nat), tokens.tail))
      else if tokens.head?.getD 4 = 3 then
        some (3, (([] : List Nat), tokens.tail))
      else none) :=
    Primrec.ite (htagEq 0) (hsimple 0)
      (Primrec.ite (htagEq 1) haxiom
        (Primrec.ite (htagEq 2) (hsimple 2)
          (Primrec.ite (htagEq 3) (hsimple 3) hnone)))
  exact
    (Primrec.ite hempty hnone hnonempty).of_eq fun tokens => by
      cases tokens <;>
        simp [compactStructuralCertificateNodeParser]

def compactStructuralCertificateNodeExpected
    (certificate : StructuralValidityCertificate) (suffix : List Nat) :
    CompactNumericCertificateNode :=
  match certificate with
  | .leaf => (0, ([], suffix))
  | .axiomCert paCertificate =>
      (1, (compactPAAxiomCertificateTokens paCertificate, suffix))
  | .unary premise =>
      (2, ([], compactStructuralCertificateTokens premise ++ suffix))
  | .binary left right =>
      (3, ([], compactStructuralCertificateTokens left ++
        compactStructuralCertificateTokens right ++ suffix))

@[simp] theorem compactStructuralCertificateNodeParser_canonical_append
    (certificate : StructuralValidityCertificate) (suffix : List Nat) :
    compactStructuralCertificateNodeParser
        (compactStructuralCertificateTokens certificate ++ suffix) =
      some (compactStructuralCertificateNodeExpected certificate suffix) := by
  cases certificate with
  | leaf =>
      simp [compactStructuralCertificateNodeParser,
        compactStructuralCertificateTokens,
        compactStructuralCertificateNodeExpected]
  | axiomCert paCertificate =>
      simp [compactStructuralCertificateNodeParser,
        compactStructuralCertificateTokens,
        compactStructuralCertificateNodeExpected,
        compactPAAxiomCertificateTokenParser_canonical_append]
  | unary premise =>
      simp [compactStructuralCertificateNodeParser,
        compactStructuralCertificateTokens,
        compactStructuralCertificateNodeExpected]
  | binary left right =>
      simp [compactStructuralCertificateNodeParser,
        compactStructuralCertificateTokens,
        compactStructuralCertificateNodeExpected,
        List.append_assoc]

#print axioms compactNodeSequentOnlyFields_primrec
#print axioms compactNodeSequentFormulaFields_primrec
#print axioms compactNodeSequentTwoFormulaFields_primrec
#print axioms compactNodeSequentFormulaTermFields_primrec
#print axioms compactClosedFormulaTokenValueParser_primrec
#print axioms compactNodeSequentClosedFormulaFields_primrec
#print axioms compactListedProofNodeFieldsParser_primrec
#print axioms compactListedProofNodeFieldsParser_canonical_append
#print axioms compactStructuralCertificateNodeParser_primrec
#print axioms compactStructuralCertificateNodeParser_canonical_append

end FoundationCompactNumericListedNodeFields
