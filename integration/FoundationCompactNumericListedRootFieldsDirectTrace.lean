import integration.FoundationCompactNumericListedRootFieldsDecomposition
import integration.FoundationCompactSequentValueDirectTrace
import integration.FoundationCompactParserDirectTrace

/-!
# Direct traces for compact root-node field branches

The ten public proof-node tags select five field-parser shapes.  This module
composes the checked sequent trace with zero, one, or two formula traces, a term
trace, or a closed-formula trace.  The uniform witness requires every unused
component to be empty, preventing irrelevant trace padding.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedRootFieldsDirectTrace

open FoundationCompactSyntaxTokenMachine
open FoundationCompactClosedFormulaTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactSequentValueDirectTrace
open FoundationCompactParserDirectTrace

abbrev CompactNumericRootFieldBranchDirectTrace :=
  (List Nat × CompactSequentTokenValueDirectTrace) ×
    ((List Nat × CompactFormulaTokenParserDirectTrace) ×
      (List Nat ×
        (CompactFormulaTokenParserDirectTrace ×
          (CompactTermTokenParserDirectTrace ×
            CompactClosedFormulaTokenParserDirectTrace))))

@[simp] def compactRootBranchAfterSequent
    (trace : CompactNumericRootFieldBranchDirectTrace) : List Nat :=
  trace.1.1

@[simp] def compactRootBranchSequentTrace
    (trace : CompactNumericRootFieldBranchDirectTrace) :
    CompactSequentTokenValueDirectTrace :=
  trace.1.2

@[simp] def compactRootBranchAfterFirst
    (trace : CompactNumericRootFieldBranchDirectTrace) : List Nat :=
  trace.2.1.1

@[simp] def compactRootBranchFirstFormulaTrace
    (trace : CompactNumericRootFieldBranchDirectTrace) :
    CompactFormulaTokenParserDirectTrace :=
  trace.2.1.2

@[simp] def compactRootBranchSecondFormulaTrace
    (trace : CompactNumericRootFieldBranchDirectTrace) :
    CompactFormulaTokenParserDirectTrace :=
  trace.2.2.2.1

@[simp] def compactRootBranchFinalSuffix
    (trace : CompactNumericRootFieldBranchDirectTrace) : List Nat :=
  trace.2.2.1

@[simp] def compactRootBranchTermTrace
    (trace : CompactNumericRootFieldBranchDirectTrace) :
    CompactTermTokenParserDirectTrace :=
  trace.2.2.2.2.1

@[simp] def compactRootBranchClosedFormulaTrace
    (trace : CompactNumericRootFieldBranchDirectTrace) :
    CompactClosedFormulaTokenParserDirectTrace :=
  trace.2.2.2.2.2

theorem compactRootBranchAfterSequent_primrec :
    Primrec compactRootBranchAfterSequent :=
  Primrec.fst.comp Primrec.fst

theorem compactRootBranchSequentTrace_primrec :
    Primrec compactRootBranchSequentTrace :=
  Primrec.snd.comp Primrec.fst

theorem compactRootBranchAfterFirst_primrec :
    Primrec compactRootBranchAfterFirst :=
  Primrec.fst.comp (Primrec.fst.comp Primrec.snd)

theorem compactRootBranchFirstFormulaTrace_primrec :
    Primrec compactRootBranchFirstFormulaTrace :=
  Primrec.snd.comp (Primrec.fst.comp Primrec.snd)

theorem compactRootBranchFinalSuffix_primrec :
    Primrec compactRootBranchFinalSuffix :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

theorem compactRootBranchSecondFormulaTrace_primrec :
    Primrec compactRootBranchSecondFormulaTrace :=
  Primrec.fst.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

theorem compactRootBranchTermTrace_primrec :
    Primrec compactRootBranchTermTrace :=
  Primrec.fst.comp
    (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

theorem compactRootBranchClosedFormulaTrace_primrec :
    Primrec compactRootBranchClosedFormulaTrace :=
  Primrec.snd.comp
    (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

abbrev CompactRootFieldExpectedInput :=
  (List (List Nat) × List Nat) × (List Nat × List Nat)

def compactNodeSequentOnlyExpectedFields
    (input : CompactRootFieldExpectedInput) : CompactNumericNodeFields :=
  (input.1.1, (([] : List Nat),
    (([] : List Nat), (([] : List Nat), input.2.2))))

def compactNodeSequentFormulaExpectedFields
    (input : CompactRootFieldExpectedInput) : CompactNumericNodeFields :=
  (input.1.1,
    (consumedTokenPrefix input.1.2 input.2.1,
      (([] : List Nat), (([] : List Nat), input.2.2))))

def compactNodeSequentTwoFormulaExpectedFields
    (input : CompactRootFieldExpectedInput) : CompactNumericNodeFields :=
  (input.1.1,
    (consumedTokenPrefix input.1.2 input.2.1,
      (consumedTokenPrefix input.2.1 input.2.2,
        (([] : List Nat), input.2.2))))

def compactNodeSequentFormulaTermExpectedFields
    (input : CompactRootFieldExpectedInput) : CompactNumericNodeFields :=
  (input.1.1,
    (consumedTokenPrefix input.1.2 input.2.1,
      (([] : List Nat),
        (consumedTokenPrefix input.2.1 input.2.2, input.2.2))))

def compactNodeSequentClosedFormulaExpectedFields
    (input : CompactRootFieldExpectedInput) : CompactNumericNodeFields :=
  (input.1.1,
    (consumedTokenPrefix input.1.2 input.2.2,
      (([] : List Nat), (([] : List Nat), input.2.2))))

theorem compactNodeSequentOnlyExpectedFields_primrec :
    Primrec compactNodeSequentOnlyExpectedFields := by
  exact Primrec.pair
    (Primrec.fst.comp Primrec.fst)
    (Primrec.pair (Primrec.const [])
      (Primrec.pair (Primrec.const [])
        (Primrec.pair (Primrec.const [])
          (Primrec.snd.comp Primrec.snd))))

theorem compactNodeSequentFormulaExpectedFields_primrec :
    Primrec compactNodeSequentFormulaExpectedFields := by
  have hconsumed : Primrec (fun input : CompactRootFieldExpectedInput =>
      consumedTokenPrefix input.1.2 input.2.1) :=
    consumedTokenPrefix_primrec.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  exact Primrec.pair
    (Primrec.fst.comp Primrec.fst)
    (Primrec.pair hconsumed
      (Primrec.pair (Primrec.const [])
        (Primrec.pair (Primrec.const [])
          (Primrec.snd.comp Primrec.snd))))

theorem compactNodeSequentTwoFormulaExpectedFields_primrec :
    Primrec compactNodeSequentTwoFormulaExpectedFields := by
  have hfirst : Primrec (fun input : CompactRootFieldExpectedInput =>
      consumedTokenPrefix input.1.2 input.2.1) :=
    consumedTokenPrefix_primrec.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  have hsecond : Primrec (fun input : CompactRootFieldExpectedInput =>
      consumedTokenPrefix input.2.1 input.2.2) :=
    consumedTokenPrefix_primrec.comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.pair
    (Primrec.fst.comp Primrec.fst)
    (Primrec.pair hfirst
      (Primrec.pair hsecond
        (Primrec.pair (Primrec.const [])
          (Primrec.snd.comp Primrec.snd))))

theorem compactNodeSequentFormulaTermExpectedFields_primrec :
    Primrec compactNodeSequentFormulaTermExpectedFields := by
  have hformula : Primrec (fun input : CompactRootFieldExpectedInput =>
      consumedTokenPrefix input.1.2 input.2.1) :=
    consumedTokenPrefix_primrec.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  have hterm : Primrec (fun input : CompactRootFieldExpectedInput =>
      consumedTokenPrefix input.2.1 input.2.2) :=
    consumedTokenPrefix_primrec.comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.pair
    (Primrec.fst.comp Primrec.fst)
    (Primrec.pair hformula
      (Primrec.pair (Primrec.const [])
        (Primrec.pair hterm
          (Primrec.snd.comp Primrec.snd))))

theorem compactNodeSequentClosedFormulaExpectedFields_primrec :
    Primrec compactNodeSequentClosedFormulaExpectedFields := by
  have hformula : Primrec (fun input : CompactRootFieldExpectedInput =>
      consumedTokenPrefix input.1.2 input.2.2) :=
    consumedTokenPrefix_primrec.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.pair
    (Primrec.fst.comp Primrec.fst)
    (Primrec.pair hformula
      (Primrec.pair (Primrec.const [])
        (Primrec.pair (Primrec.const [])
          (Primrec.snd.comp Primrec.snd))))

theorem compactTermTokenValueParser_eq_some_iff
    (binderArity : Nat) (tokens value suffix : List Nat) :
    compactTermTokenValueParser binderArity tokens =
        some (value, suffix) ↔
      compactTermTokenParser binderArity tokens = some suffix ∧
        value = consumedTokenPrefix tokens suffix := by
  cases hparser : compactTermTokenParser binderArity tokens with
  | none =>
      simp [compactTermTokenValueParser, hparser]
  | some parsedSuffix =>
      simp only [compactTermTokenValueParser, hparser, Option.map_some,
        Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨hvalue, rfl⟩
        exact ⟨rfl, hvalue.symm⟩
      · rintro ⟨rfl, hvalue⟩
        exact ⟨hvalue.symm, rfl⟩

theorem compactClosedFormulaTokenValueParser_eq_some_iff
    (tokens value suffix : List Nat) :
    compactClosedFormulaTokenValueParser tokens =
        some (value, suffix) ↔
      compactClosedFormulaTokenParser 0 tokens = some suffix ∧
        value = consumedTokenPrefix tokens suffix := by
  cases hparser : compactClosedFormulaTokenParser 0 tokens with
  | none =>
      simp [compactClosedFormulaTokenValueParser, hparser]
  | some parsedSuffix =>
      simp only [compactClosedFormulaTokenValueParser, hparser,
        Option.map_some, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨hvalue, rfl⟩
        exact ⟨rfl, hvalue.symm⟩
      · rintro ⟨rfl, hvalue⟩
        exact ⟨hvalue.symm, rfl⟩

theorem compactNodeSequentFormulaFields_of_results
    (binderArity : Nat) (tokens : List Nat)
    (values : List (List Nat)) (afterSequent formulaValue afterFirst : List Nat)
    (hsequent : compactSequentTokenValueParser tokens =
      some (values, afterSequent))
    (hformula : compactFormulaTokenValueParser binderArity afterSequent =
      some (formulaValue, afterFirst)) :
    compactNodeSequentFormulaFields binderArity tokens =
      some (values, (formulaValue,
        (([] : List Nat), (([] : List Nat), afterFirst)))) := by
  simp [compactNodeSequentFormulaFields, hsequent, hformula]

theorem compactNodeSequentTwoFormulaFields_of_results
    (binderArity : Nat) (tokens : List Nat)
    (first : CompactNumericNodeFields)
    (secondValue finalSuffix : List Nat)
    (hfirst : compactNodeSequentFormulaFields binderArity tokens = some first)
    (hsecond : compactFormulaTokenValueParser binderArity
      (compactNumericNodeFieldsSuffix first) =
        some (secondValue, finalSuffix)) :
    compactNodeSequentTwoFormulaFields binderArity tokens =
      some (first.1, (first.2.1,
        (secondValue, (([] : List Nat), finalSuffix)))) := by
  simp [compactNodeSequentTwoFormulaFields, hfirst, hsecond]

theorem compactNodeSequentFormulaTermFields_of_results
    (formulaArity termArity : Nat) (tokens : List Nat)
    (first : CompactNumericNodeFields)
    (termValue finalSuffix : List Nat)
    (hfirst : compactNodeSequentFormulaFields formulaArity tokens = some first)
    (hterm : compactTermTokenValueParser termArity
      (compactNumericNodeFieldsSuffix first) =
        some (termValue, finalSuffix)) :
    compactNodeSequentFormulaTermFields formulaArity termArity tokens =
      some (first.1, (first.2.1,
        (([] : List Nat), (termValue, finalSuffix)))) := by
  simp [compactNodeSequentFormulaTermFields, hfirst, hterm]

theorem compactNodeSequentClosedFormulaFields_of_results
    (tokens : List Nat) (values : List (List Nat))
    (afterSequent formulaValue finalSuffix : List Nat)
    (hsequent : compactSequentTokenValueParser tokens =
      some (values, afterSequent))
    (hclosed : compactClosedFormulaTokenValueParser afterSequent =
      some (formulaValue, finalSuffix)) :
    compactNodeSequentClosedFormulaFields tokens =
      some (values, (formulaValue,
        (([] : List Nat), (([] : List Nat), finalSuffix)))) := by
  simp [compactNodeSequentClosedFormulaFields, hsequent, hclosed]

def CompactNodeSequentOnlyDirectTraceValid
    (tokens : List Nat) (fields : CompactNumericNodeFields)
    (trace : CompactNumericRootFieldBranchDirectTrace) : Prop :=
  let afterSequent := compactRootBranchAfterSequent trace
  let finalSuffix := compactRootBranchFinalSuffix trace
  CompactSequentTokenValueDirectTraceValid
      tokens fields.1 afterSequent
      (compactRootBranchSequentTrace trace) ∧
    fields =
      (fields.1, (([] : List Nat),
        (([] : List Nat), (([] : List Nat), finalSuffix)))) ∧
    afterSequent = finalSuffix ∧
    compactRootBranchAfterFirst trace = [] ∧
    compactRootBranchFirstFormulaTrace trace = [] ∧
    compactRootBranchSecondFormulaTrace trace = [] ∧
    compactRootBranchTermTrace trace = [] ∧
    compactRootBranchClosedFormulaTrace trace = []

def CompactNodeSequentFormulaDirectTraceValid
    (binderArity : Nat) (tokens : List Nat)
    (fields : CompactNumericNodeFields)
    (trace : CompactNumericRootFieldBranchDirectTrace) : Prop :=
  let afterSequent := compactRootBranchAfterSequent trace
  let afterFirst := compactRootBranchAfterFirst trace
  let finalSuffix := compactRootBranchFinalSuffix trace
  CompactSequentTokenValueDirectTraceValid
      tokens fields.1 afterSequent
      (compactRootBranchSequentTrace trace) ∧
    CompactFormulaTokenParserDirectTraceValid
      binderArity afterSequent afterFirst
      (compactRootBranchFirstFormulaTrace trace) ∧
    fields =
      (fields.1,
        (consumedTokenPrefix afterSequent afterFirst,
          (([] : List Nat), (([] : List Nat), finalSuffix)))) ∧
    afterFirst = finalSuffix ∧
    compactRootBranchSecondFormulaTrace trace = [] ∧
    compactRootBranchTermTrace trace = [] ∧
    compactRootBranchClosedFormulaTrace trace = []

def CompactNodeSequentTwoFormulaDirectTraceValid
    (binderArity : Nat) (tokens : List Nat)
    (fields : CompactNumericNodeFields)
    (trace : CompactNumericRootFieldBranchDirectTrace) : Prop :=
  let afterSequent := compactRootBranchAfterSequent trace
  let afterFirst := compactRootBranchAfterFirst trace
  let finalSuffix := compactRootBranchFinalSuffix trace
  CompactSequentTokenValueDirectTraceValid
      tokens fields.1 afterSequent
      (compactRootBranchSequentTrace trace) ∧
    CompactFormulaTokenParserDirectTraceValid
      binderArity afterSequent afterFirst
      (compactRootBranchFirstFormulaTrace trace) ∧
    CompactFormulaTokenParserDirectTraceValid
      binderArity afterFirst finalSuffix
      (compactRootBranchSecondFormulaTrace trace) ∧
    fields =
      (fields.1,
        (consumedTokenPrefix afterSequent afterFirst,
          (consumedTokenPrefix afterFirst finalSuffix,
            (([] : List Nat), finalSuffix)))) ∧
    compactRootBranchTermTrace trace = [] ∧
    compactRootBranchClosedFormulaTrace trace = []

def CompactNodeSequentFormulaTermDirectTraceValid
    (formulaArity termArity : Nat) (tokens : List Nat)
    (fields : CompactNumericNodeFields)
    (trace : CompactNumericRootFieldBranchDirectTrace) : Prop :=
  let afterSequent := compactRootBranchAfterSequent trace
  let afterFirst := compactRootBranchAfterFirst trace
  let finalSuffix := compactRootBranchFinalSuffix trace
  CompactSequentTokenValueDirectTraceValid
      tokens fields.1 afterSequent
      (compactRootBranchSequentTrace trace) ∧
    CompactFormulaTokenParserDirectTraceValid
      formulaArity afterSequent afterFirst
      (compactRootBranchFirstFormulaTrace trace) ∧
    CompactTermTokenParserDirectTraceValid
      termArity afterFirst finalSuffix
      (compactRootBranchTermTrace trace) ∧
    fields =
      (fields.1,
        (consumedTokenPrefix afterSequent afterFirst,
          (([] : List Nat),
            (consumedTokenPrefix afterFirst finalSuffix, finalSuffix)))) ∧
    compactRootBranchSecondFormulaTrace trace = [] ∧
    compactRootBranchClosedFormulaTrace trace = []

def CompactNodeSequentClosedFormulaDirectTraceValid
    (tokens : List Nat) (fields : CompactNumericNodeFields)
    (trace : CompactNumericRootFieldBranchDirectTrace) : Prop :=
  let afterSequent := compactRootBranchAfterSequent trace
  let finalSuffix := compactRootBranchFinalSuffix trace
  CompactSequentTokenValueDirectTraceValid
      tokens fields.1 afterSequent
      (compactRootBranchSequentTrace trace) ∧
    CompactClosedFormulaTokenParserDirectTraceValid
      0 afterSequent finalSuffix
      (compactRootBranchClosedFormulaTrace trace) ∧
    fields =
      (fields.1,
        (consumedTokenPrefix afterSequent finalSuffix,
          (([] : List Nat), (([] : List Nat), finalSuffix)))) ∧
    compactRootBranchAfterFirst trace = [] ∧
    compactRootBranchFirstFormulaTrace trace = [] ∧
    compactRootBranchSecondFormulaTrace trace = [] ∧
    compactRootBranchTermTrace trace = []

theorem compactNodeSequentOnlyDirectTraceValid_primrec :
    PrimrecPred (fun input :
        (List Nat × CompactNumericNodeFields) ×
          CompactNumericRootFieldBranchDirectTrace =>
      CompactNodeSequentOnlyDirectTraceValid
        input.1.1 input.1.2 input.2) := by
  let Input :=
    (List Nat × CompactNumericNodeFields) ×
      CompactNumericRootFieldBranchDirectTrace
  have htokens : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hfields : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have htrace : Primrec (fun input : Input => input.2) :=
    Primrec.snd
  have hvalues : Primrec (fun input : Input => input.1.2.1) :=
    Primrec.fst.comp hfields
  have hafterSequent : Primrec (fun input : Input =>
      compactRootBranchAfterSequent input.2) :=
    compactRootBranchAfterSequent_primrec.comp htrace
  have hsequentTrace : Primrec (fun input : Input =>
      compactRootBranchSequentTrace input.2) :=
    compactRootBranchSequentTrace_primrec.comp htrace
  have hafterFirst : Primrec (fun input : Input =>
      compactRootBranchAfterFirst input.2) :=
    compactRootBranchAfterFirst_primrec.comp htrace
  have hfirstTrace : Primrec (fun input : Input =>
      compactRootBranchFirstFormulaTrace input.2) :=
    compactRootBranchFirstFormulaTrace_primrec.comp htrace
  have hfinal : Primrec (fun input : Input =>
      compactRootBranchFinalSuffix input.2) :=
    compactRootBranchFinalSuffix_primrec.comp htrace
  have hsecondTrace : Primrec (fun input : Input =>
      compactRootBranchSecondFormulaTrace input.2) :=
    compactRootBranchSecondFormulaTrace_primrec.comp htrace
  have htermTrace : Primrec (fun input : Input =>
      compactRootBranchTermTrace input.2) :=
    compactRootBranchTermTrace_primrec.comp htrace
  have hclosedTrace : Primrec (fun input : Input =>
      compactRootBranchClosedFormulaTrace input.2) :=
    compactRootBranchClosedFormulaTrace_primrec.comp htrace
  have hsequent : PrimrecPred (fun input : Input =>
      CompactSequentTokenValueDirectTraceValid
        input.1.1 input.1.2.1
        (compactRootBranchAfterSequent input.2)
        (compactRootBranchSequentTrace input.2)) :=
    compactSequentTokenValueDirectTraceValid_primrec.comp <|
      Primrec.pair
        (Primrec.pair htokens (Primrec.pair hvalues hafterSequent))
        hsequentTrace
  have hexpectedInput : Primrec (fun input : Input =>
      ((input.1.2.1, compactRootBranchAfterSequent input.2),
        (compactRootBranchAfterFirst input.2,
          compactRootBranchFinalSuffix input.2))) :=
    Primrec.pair (Primrec.pair hvalues hafterSequent)
      (Primrec.pair hafterFirst hfinal)
  have hfieldEq : PrimrecPred (fun input : Input =>
      input.1.2 = compactNodeSequentOnlyExpectedFields
        ((input.1.2.1, compactRootBranchAfterSequent input.2),
          (compactRootBranchAfterFirst input.2,
            compactRootBranchFinalSuffix input.2))) :=
    Primrec.eq.comp hfields
      (compactNodeSequentOnlyExpectedFields_primrec.comp hexpectedInput)
  have hafterEq : PrimrecPred (fun input : Input =>
      compactRootBranchAfterSequent input.2 =
        compactRootBranchFinalSuffix input.2) :=
    Primrec.eq.comp hafterSequent hfinal
  have hafterFirstEmpty : PrimrecPred (fun input : Input =>
      compactRootBranchAfterFirst input.2 = []) :=
    Primrec.eq.comp hafterFirst (Primrec.const [])
  have hfirstEmpty : PrimrecPred (fun input : Input =>
      compactRootBranchFirstFormulaTrace input.2 = []) :=
    Primrec.eq.comp hfirstTrace (Primrec.const [])
  have hsecondEmpty : PrimrecPred (fun input : Input =>
      compactRootBranchSecondFormulaTrace input.2 = []) :=
    Primrec.eq.comp hsecondTrace (Primrec.const [])
  have htermEmpty : PrimrecPred (fun input : Input =>
      compactRootBranchTermTrace input.2 = []) :=
    Primrec.eq.comp htermTrace (Primrec.const [])
  have hclosedEmpty : PrimrecPred (fun input : Input =>
      compactRootBranchClosedFormulaTrace input.2 = []) :=
    Primrec.eq.comp hclosedTrace (Primrec.const [])
  exact
    (hsequent.and
      (hfieldEq.and
        (hafterEq.and
          (hafterFirstEmpty.and
            (hfirstEmpty.and
              (hsecondEmpty.and
                (htermEmpty.and hclosedEmpty))))))).of_eq fun input => by
                  simp only [CompactNodeSequentOnlyDirectTraceValid,
                    compactNodeSequentOnlyExpectedFields]

theorem compactNodeSequentFormulaDirectTraceValid_primrec :
    PrimrecPred (fun input :
        ((Nat × List Nat) × CompactNumericNodeFields) ×
          CompactNumericRootFieldBranchDirectTrace =>
      CompactNodeSequentFormulaDirectTraceValid
        input.1.1.1 input.1.1.2 input.1.2 input.2) := by
  let Input :=
    ((Nat × List Nat) × CompactNumericNodeFields) ×
      CompactNumericRootFieldBranchDirectTrace
  have hbinder : Primrec (fun input : Input => input.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have htokens : Primrec (fun input : Input => input.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hfields : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have htrace : Primrec (fun input : Input => input.2) := Primrec.snd
  have hvalues := Primrec.fst.comp hfields
  have hafterSequent := compactRootBranchAfterSequent_primrec.comp htrace
  have hsequentTrace := compactRootBranchSequentTrace_primrec.comp htrace
  have hafterFirst := compactRootBranchAfterFirst_primrec.comp htrace
  have hfirstTrace := compactRootBranchFirstFormulaTrace_primrec.comp htrace
  have hfinal := compactRootBranchFinalSuffix_primrec.comp htrace
  have hsecondTrace := compactRootBranchSecondFormulaTrace_primrec.comp htrace
  have htermTrace := compactRootBranchTermTrace_primrec.comp htrace
  have hclosedTrace := compactRootBranchClosedFormulaTrace_primrec.comp htrace
  have hsequent : PrimrecPred (fun input : Input =>
      CompactSequentTokenValueDirectTraceValid input.1.1.2 input.1.2.1
        (compactRootBranchAfterSequent input.2)
        (compactRootBranchSequentTrace input.2)) :=
    compactSequentTokenValueDirectTraceValid_primrec.comp <|
      Primrec.pair
        (Primrec.pair htokens (Primrec.pair hvalues hafterSequent))
        hsequentTrace
  have hformula : PrimrecPred (fun input : Input =>
      CompactFormulaTokenParserDirectTraceValid input.1.1.1
        (compactRootBranchAfterSequent input.2)
        (compactRootBranchAfterFirst input.2)
        (compactRootBranchFirstFormulaTrace input.2)) :=
    compactFormulaTokenParserDirectTraceValid_primrec.comp <|
      Primrec.pair
        (Primrec.pair (Primrec.pair hbinder hafterSequent) hafterFirst)
        hfirstTrace
  have hexpectedInput : Primrec (fun input : Input =>
      ((input.1.2.1, compactRootBranchAfterSequent input.2),
        (compactRootBranchAfterFirst input.2,
          compactRootBranchFinalSuffix input.2))) :=
    Primrec.pair (Primrec.pair hvalues hafterSequent)
      (Primrec.pair hafterFirst hfinal)
  have hfieldEq : PrimrecPred (fun input : Input =>
      input.1.2 = compactNodeSequentFormulaExpectedFields
        ((input.1.2.1, compactRootBranchAfterSequent input.2),
          (compactRootBranchAfterFirst input.2,
            compactRootBranchFinalSuffix input.2))) :=
    Primrec.eq.comp hfields
      (compactNodeSequentFormulaExpectedFields_primrec.comp hexpectedInput)
  have hafterEq : PrimrecPred (fun input : Input =>
      compactRootBranchAfterFirst input.2 =
        compactRootBranchFinalSuffix input.2) :=
    Primrec.eq.comp hafterFirst hfinal
  have hsecondEmpty : PrimrecPred (fun input : Input =>
      compactRootBranchSecondFormulaTrace input.2 = []) :=
    Primrec.eq.comp hsecondTrace (Primrec.const [])
  have htermEmpty : PrimrecPred (fun input : Input =>
      compactRootBranchTermTrace input.2 = []) :=
    Primrec.eq.comp htermTrace (Primrec.const [])
  have hclosedEmpty : PrimrecPred (fun input : Input =>
      compactRootBranchClosedFormulaTrace input.2 = []) :=
    Primrec.eq.comp hclosedTrace (Primrec.const [])
  exact
    (hsequent.and
      (hformula.and
        (hfieldEq.and
          (hafterEq.and
            (hsecondEmpty.and
              (htermEmpty.and hclosedEmpty)))))).of_eq fun input => by
                simp only [CompactNodeSequentFormulaDirectTraceValid,
                  compactNodeSequentFormulaExpectedFields]

theorem compactNodeSequentTwoFormulaDirectTraceValid_primrec :
    PrimrecPred (fun input :
        ((Nat × List Nat) × CompactNumericNodeFields) ×
          CompactNumericRootFieldBranchDirectTrace =>
      CompactNodeSequentTwoFormulaDirectTraceValid
        input.1.1.1 input.1.1.2 input.1.2 input.2) := by
  let Input :=
    ((Nat × List Nat) × CompactNumericNodeFields) ×
      CompactNumericRootFieldBranchDirectTrace
  have hbinder : Primrec (fun input : Input => input.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have htokens : Primrec (fun input : Input => input.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hfields : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have htrace : Primrec (fun input : Input => input.2) := Primrec.snd
  have hvalues := Primrec.fst.comp hfields
  have hafterSequent := compactRootBranchAfterSequent_primrec.comp htrace
  have hsequentTrace := compactRootBranchSequentTrace_primrec.comp htrace
  have hafterFirst := compactRootBranchAfterFirst_primrec.comp htrace
  have hfirstTrace := compactRootBranchFirstFormulaTrace_primrec.comp htrace
  have hfinal := compactRootBranchFinalSuffix_primrec.comp htrace
  have hsecondTrace := compactRootBranchSecondFormulaTrace_primrec.comp htrace
  have htermTrace := compactRootBranchTermTrace_primrec.comp htrace
  have hclosedTrace := compactRootBranchClosedFormulaTrace_primrec.comp htrace
  have hsequent : PrimrecPred (fun input : Input =>
      CompactSequentTokenValueDirectTraceValid input.1.1.2 input.1.2.1
        (compactRootBranchAfterSequent input.2)
        (compactRootBranchSequentTrace input.2)) :=
    compactSequentTokenValueDirectTraceValid_primrec.comp <|
      Primrec.pair
        (Primrec.pair htokens (Primrec.pair hvalues hafterSequent))
        hsequentTrace
  have hfirst : PrimrecPred (fun input : Input =>
      CompactFormulaTokenParserDirectTraceValid input.1.1.1
        (compactRootBranchAfterSequent input.2)
        (compactRootBranchAfterFirst input.2)
        (compactRootBranchFirstFormulaTrace input.2)) :=
    compactFormulaTokenParserDirectTraceValid_primrec.comp <|
      Primrec.pair
        (Primrec.pair (Primrec.pair hbinder hafterSequent) hafterFirst)
        hfirstTrace
  have hsecond : PrimrecPred (fun input : Input =>
      CompactFormulaTokenParserDirectTraceValid input.1.1.1
        (compactRootBranchAfterFirst input.2)
        (compactRootBranchFinalSuffix input.2)
        (compactRootBranchSecondFormulaTrace input.2)) :=
    compactFormulaTokenParserDirectTraceValid_primrec.comp <|
      Primrec.pair
        (Primrec.pair (Primrec.pair hbinder hafterFirst) hfinal)
        hsecondTrace
  have hexpectedInput : Primrec (fun input : Input =>
      ((input.1.2.1, compactRootBranchAfterSequent input.2),
        (compactRootBranchAfterFirst input.2,
          compactRootBranchFinalSuffix input.2))) :=
    Primrec.pair (Primrec.pair hvalues hafterSequent)
      (Primrec.pair hafterFirst hfinal)
  have hfieldEq : PrimrecPred (fun input : Input =>
      input.1.2 = compactNodeSequentTwoFormulaExpectedFields
        ((input.1.2.1, compactRootBranchAfterSequent input.2),
          (compactRootBranchAfterFirst input.2,
            compactRootBranchFinalSuffix input.2))) :=
    Primrec.eq.comp hfields
      (compactNodeSequentTwoFormulaExpectedFields_primrec.comp hexpectedInput)
  have htermEmpty : PrimrecPred (fun input : Input =>
      compactRootBranchTermTrace input.2 = []) :=
    Primrec.eq.comp htermTrace (Primrec.const [])
  have hclosedEmpty : PrimrecPred (fun input : Input =>
      compactRootBranchClosedFormulaTrace input.2 = []) :=
    Primrec.eq.comp hclosedTrace (Primrec.const [])
  exact
    (hsequent.and
      (hfirst.and
        (hsecond.and
          (hfieldEq.and
            (htermEmpty.and hclosedEmpty))))).of_eq fun input => by
              simp only [CompactNodeSequentTwoFormulaDirectTraceValid,
                compactNodeSequentTwoFormulaExpectedFields]

theorem compactNodeSequentFormulaTermDirectTraceValid_primrec :
    PrimrecPred (fun input :
        (((Nat × Nat) × List Nat) × CompactNumericNodeFields) ×
          CompactNumericRootFieldBranchDirectTrace =>
      CompactNodeSequentFormulaTermDirectTraceValid
        input.1.1.1.1 input.1.1.1.2 input.1.1.2
          input.1.2 input.2) := by
  let Input :=
    (((Nat × Nat) × List Nat) × CompactNumericNodeFields) ×
      CompactNumericRootFieldBranchDirectTrace
  have hformulaArity : Primrec (fun input : Input => input.1.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have htermArity : Primrec (fun input : Input => input.1.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have htokens : Primrec (fun input : Input => input.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hfields : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have htrace : Primrec (fun input : Input => input.2) := Primrec.snd
  have hvalues := Primrec.fst.comp hfields
  have hafterSequent := compactRootBranchAfterSequent_primrec.comp htrace
  have hsequentTrace := compactRootBranchSequentTrace_primrec.comp htrace
  have hafterFirst := compactRootBranchAfterFirst_primrec.comp htrace
  have hfirstTrace := compactRootBranchFirstFormulaTrace_primrec.comp htrace
  have hfinal := compactRootBranchFinalSuffix_primrec.comp htrace
  have hsecondTrace := compactRootBranchSecondFormulaTrace_primrec.comp htrace
  have htermTrace := compactRootBranchTermTrace_primrec.comp htrace
  have hclosedTrace := compactRootBranchClosedFormulaTrace_primrec.comp htrace
  have hsequent : PrimrecPred (fun input : Input =>
      CompactSequentTokenValueDirectTraceValid input.1.1.2 input.1.2.1
        (compactRootBranchAfterSequent input.2)
        (compactRootBranchSequentTrace input.2)) :=
    compactSequentTokenValueDirectTraceValid_primrec.comp <|
      Primrec.pair
        (Primrec.pair htokens (Primrec.pair hvalues hafterSequent))
        hsequentTrace
  have hformula : PrimrecPred (fun input : Input =>
      CompactFormulaTokenParserDirectTraceValid input.1.1.1.1
        (compactRootBranchAfterSequent input.2)
        (compactRootBranchAfterFirst input.2)
        (compactRootBranchFirstFormulaTrace input.2)) :=
    compactFormulaTokenParserDirectTraceValid_primrec.comp <|
      Primrec.pair
        (Primrec.pair
          (Primrec.pair hformulaArity hafterSequent) hafterFirst)
        hfirstTrace
  have hterm : PrimrecPred (fun input : Input =>
      CompactTermTokenParserDirectTraceValid input.1.1.1.2
        (compactRootBranchAfterFirst input.2)
        (compactRootBranchFinalSuffix input.2)
        (compactRootBranchTermTrace input.2)) :=
    compactTermTokenParserDirectTraceValid_primrec.comp <|
      Primrec.pair
        (Primrec.pair
          (Primrec.pair htermArity hafterFirst) hfinal)
        htermTrace
  have hexpectedInput : Primrec (fun input : Input =>
      ((input.1.2.1, compactRootBranchAfterSequent input.2),
        (compactRootBranchAfterFirst input.2,
          compactRootBranchFinalSuffix input.2))) :=
    Primrec.pair (Primrec.pair hvalues hafterSequent)
      (Primrec.pair hafterFirst hfinal)
  have hfieldEq : PrimrecPred (fun input : Input =>
      input.1.2 = compactNodeSequentFormulaTermExpectedFields
        ((input.1.2.1, compactRootBranchAfterSequent input.2),
          (compactRootBranchAfterFirst input.2,
            compactRootBranchFinalSuffix input.2))) :=
    Primrec.eq.comp hfields
      (compactNodeSequentFormulaTermExpectedFields_primrec.comp hexpectedInput)
  have hsecondEmpty : PrimrecPred (fun input : Input =>
      compactRootBranchSecondFormulaTrace input.2 = []) :=
    Primrec.eq.comp hsecondTrace (Primrec.const [])
  have hclosedEmpty : PrimrecPred (fun input : Input =>
      compactRootBranchClosedFormulaTrace input.2 = []) :=
    Primrec.eq.comp hclosedTrace (Primrec.const [])
  exact
    (hsequent.and
      (hformula.and
        (hterm.and
          (hfieldEq.and
            (hsecondEmpty.and hclosedEmpty))))).of_eq fun input => by
              simp only [CompactNodeSequentFormulaTermDirectTraceValid,
                compactNodeSequentFormulaTermExpectedFields]

theorem compactNodeSequentClosedFormulaDirectTraceValid_primrec :
    PrimrecPred (fun input :
        (List Nat × CompactNumericNodeFields) ×
          CompactNumericRootFieldBranchDirectTrace =>
      CompactNodeSequentClosedFormulaDirectTraceValid
        input.1.1 input.1.2 input.2) := by
  let Input :=
    (List Nat × CompactNumericNodeFields) ×
      CompactNumericRootFieldBranchDirectTrace
  have htokens : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hfields : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have htrace : Primrec (fun input : Input => input.2) := Primrec.snd
  have hvalues := Primrec.fst.comp hfields
  have hafterSequent := compactRootBranchAfterSequent_primrec.comp htrace
  have hsequentTrace := compactRootBranchSequentTrace_primrec.comp htrace
  have hafterFirst := compactRootBranchAfterFirst_primrec.comp htrace
  have hfirstTrace := compactRootBranchFirstFormulaTrace_primrec.comp htrace
  have hfinal := compactRootBranchFinalSuffix_primrec.comp htrace
  have hsecondTrace := compactRootBranchSecondFormulaTrace_primrec.comp htrace
  have htermTrace := compactRootBranchTermTrace_primrec.comp htrace
  have hclosedTrace := compactRootBranchClosedFormulaTrace_primrec.comp htrace
  have hsequent : PrimrecPred (fun input : Input =>
      CompactSequentTokenValueDirectTraceValid input.1.1 input.1.2.1
        (compactRootBranchAfterSequent input.2)
        (compactRootBranchSequentTrace input.2)) :=
    compactSequentTokenValueDirectTraceValid_primrec.comp <|
      Primrec.pair
        (Primrec.pair htokens (Primrec.pair hvalues hafterSequent))
        hsequentTrace
  have hclosed : PrimrecPred (fun input : Input =>
      CompactClosedFormulaTokenParserDirectTraceValid 0
        (compactRootBranchAfterSequent input.2)
        (compactRootBranchFinalSuffix input.2)
        (compactRootBranchClosedFormulaTrace input.2)) :=
    compactClosedFormulaTokenParserDirectTraceValid_primrec.comp <|
      Primrec.pair
        (Primrec.pair
          (Primrec.pair (Primrec.const 0) hafterSequent) hfinal)
        hclosedTrace
  have hexpectedInput : Primrec (fun input : Input =>
      ((input.1.2.1, compactRootBranchAfterSequent input.2),
        (compactRootBranchAfterFirst input.2,
          compactRootBranchFinalSuffix input.2))) :=
    Primrec.pair (Primrec.pair hvalues hafterSequent)
      (Primrec.pair hafterFirst hfinal)
  have hfieldEq : PrimrecPred (fun input : Input =>
      input.1.2 = compactNodeSequentClosedFormulaExpectedFields
        ((input.1.2.1, compactRootBranchAfterSequent input.2),
          (compactRootBranchAfterFirst input.2,
            compactRootBranchFinalSuffix input.2))) :=
    Primrec.eq.comp hfields
      (compactNodeSequentClosedFormulaExpectedFields_primrec.comp hexpectedInput)
  have hafterFirstEmpty : PrimrecPred (fun input : Input =>
      compactRootBranchAfterFirst input.2 = []) :=
    Primrec.eq.comp hafterFirst (Primrec.const [])
  have hfirstEmpty : PrimrecPred (fun input : Input =>
      compactRootBranchFirstFormulaTrace input.2 = []) :=
    Primrec.eq.comp hfirstTrace (Primrec.const [])
  have hsecondEmpty : PrimrecPred (fun input : Input =>
      compactRootBranchSecondFormulaTrace input.2 = []) :=
    Primrec.eq.comp hsecondTrace (Primrec.const [])
  have htermEmpty : PrimrecPred (fun input : Input =>
      compactRootBranchTermTrace input.2 = []) :=
    Primrec.eq.comp htermTrace (Primrec.const [])
  exact
    (hsequent.and
      (hclosed.and
        (hfieldEq.and
          (hafterFirstEmpty.and
            (hfirstEmpty.and
              (hsecondEmpty.and htermEmpty)))))).of_eq fun input => by
                simp only [CompactNodeSequentClosedFormulaDirectTraceValid,
                  compactNodeSequentClosedFormulaExpectedFields]

theorem compactNodeSequentOnlyFields_eq_some_iff_exists_directTrace
    (tokens : List Nat) (fields : CompactNumericNodeFields) :
    compactNodeSequentOnlyFields tokens = some fields ↔
      ∃ trace : CompactNumericRootFieldBranchDirectTrace,
        CompactNodeSequentOnlyDirectTraceValid tokens fields trace := by
  constructor
  · intro hfields
    cases hsequent : compactSequentTokenValueParser tokens with
    | none =>
        simp [compactNodeSequentOnlyFields, hsequent] at hfields
    | some parsed =>
        rcases parsed with ⟨values, suffix⟩
        have hfieldsEq :
            (values, (([] : List Nat),
              (([] : List Nat), (([] : List Nat), suffix)))) = fields := by
          simpa [compactNodeSequentOnlyFields, hsequent] using hfields
        subst fields
        obtain ⟨sequentTrace, hsequentTrace⟩ :=
          (compactSequentTokenValueParser_eq_some_iff_exists_directTrace
            tokens values suffix).mp hsequent
        refine ⟨((suffix, sequentTrace),
          (([], []), (suffix, ([], ([], []))))), ?_⟩
        simpa [CompactNodeSequentOnlyDirectTraceValid]
          using hsequentTrace
  · rintro ⟨trace, htrace⟩
    unfold CompactNodeSequentOnlyDirectTraceValid at htrace
    dsimp only at htrace
    rcases htrace with ⟨hsequent, hfields, hafterSequentFinal, _⟩
    have hsequentResult :=
      (compactSequentTokenValueParser_eq_some_iff_exists_directTrace
        tokens fields.1 (compactRootBranchAfterSequent trace)).mpr
          ⟨compactRootBranchSequentTrace trace, hsequent⟩
    rw [← hafterSequentFinal] at hfields
    rw [hfields]
    simp [compactNodeSequentOnlyFields, hsequentResult]

theorem compactNodeSequentFormulaFields_eq_some_iff_exists_directTrace
    (binderArity : Nat) (tokens : List Nat)
    (fields : CompactNumericNodeFields) :
    compactNodeSequentFormulaFields binderArity tokens = some fields ↔
      ∃ trace : CompactNumericRootFieldBranchDirectTrace,
        CompactNodeSequentFormulaDirectTraceValid
          binderArity tokens fields trace := by
  constructor
  · intro hfields
    cases hsequent : compactSequentTokenValueParser tokens with
    | none =>
        simp [compactNodeSequentFormulaFields, hsequent] at hfields
    | some parsedSequent =>
        rcases parsedSequent with ⟨values, afterSequent⟩
        cases hformula :
            compactFormulaTokenValueParser binderArity afterSequent with
        | none =>
            simp [compactNodeSequentFormulaFields,
              hsequent, hformula] at hfields
        | some parsedFormula =>
            rcases parsedFormula with ⟨formulaValue, afterFirst⟩
            have hfieldsEq :
                (values, (formulaValue,
                  (([] : List Nat),
                    (([] : List Nat), afterFirst)))) = fields := by
              simpa [compactNodeSequentFormulaFields,
                hsequent, hformula] using hfields
            subst fields
            obtain ⟨sequentTrace, hsequentTrace⟩ :=
              (compactSequentTokenValueParser_eq_some_iff_exists_directTrace
                tokens values afterSequent).mp hsequent
            obtain ⟨hformulaResult, hformulaValue⟩ :=
              (compactFormulaTokenValueParser_eq_some_iff
                binderArity afterSequent formulaValue afterFirst).mp hformula
            obtain ⟨formulaTrace, hformulaTrace⟩ :=
              (compactFormulaTokenParser_eq_some_iff_exists_directTrace
                binderArity afterSequent afterFirst).mp hformulaResult
            refine ⟨((afterSequent, sequentTrace),
              ((afterFirst, formulaTrace),
                (afterFirst, ([], ([], []))))), ?_⟩
            simp [CompactNodeSequentFormulaDirectTraceValid,
              hsequentTrace, hformulaTrace, hformulaValue]
  · rintro ⟨trace, htrace⟩
    unfold CompactNodeSequentFormulaDirectTraceValid at htrace
    dsimp only at htrace
    rcases htrace with
      ⟨hsequent, hformula, hfields, hafterFirstFinal, _⟩
    have hsequentResult :=
      (compactSequentTokenValueParser_eq_some_iff_exists_directTrace
        tokens fields.1 (compactRootBranchAfterSequent trace)).mpr
          ⟨compactRootBranchSequentTrace trace, hsequent⟩
    have hformulaResult :=
      (compactFormulaTokenParser_eq_some_iff_exists_directTrace
        binderArity (compactRootBranchAfterSequent trace)
          (compactRootBranchAfterFirst trace)).mpr
            ⟨compactRootBranchFirstFormulaTrace trace, hformula⟩
    have hformulaValue :=
      (compactFormulaTokenValueParser_eq_some_iff
        binderArity (compactRootBranchAfterSequent trace)
          (consumedTokenPrefix
            (compactRootBranchAfterSequent trace)
            (compactRootBranchAfterFirst trace))
          (compactRootBranchAfterFirst trace)).mpr
            ⟨hformulaResult, rfl⟩
    rw [← hafterFirstFinal] at hfields
    have hresult := compactNodeSequentFormulaFields_of_results
      binderArity tokens fields.1
        (compactRootBranchAfterSequent trace)
        (consumedTokenPrefix
          (compactRootBranchAfterSequent trace)
          (compactRootBranchAfterFirst trace))
        (compactRootBranchAfterFirst trace)
        hsequentResult hformulaValue
    exact hresult.trans (congrArg some hfields.symm)

theorem compactNodeSequentTwoFormulaFields_eq_some_iff_exists_directTrace
    (binderArity : Nat) (tokens : List Nat)
    (fields : CompactNumericNodeFields) :
    compactNodeSequentTwoFormulaFields binderArity tokens = some fields ↔
      ∃ trace : CompactNumericRootFieldBranchDirectTrace,
        CompactNodeSequentTwoFormulaDirectTraceValid
          binderArity tokens fields trace := by
  constructor
  · intro hfields
    unfold compactNodeSequentTwoFormulaFields at hfields
    cases hfirst : compactNodeSequentFormulaFields binderArity tokens with
    | none => simp [hfirst] at hfields
    | some first =>
        cases hsecond : compactFormulaTokenValueParser binderArity
            (compactNumericNodeFieldsSuffix first) with
        | none => simp [hfirst, hsecond] at hfields
        | some second =>
            rcases second with ⟨secondValue, finalSuffix⟩
            have hfieldsEq :
                (first.1, (first.2.1,
                  (secondValue, (([] : List Nat), finalSuffix)))) = fields := by
              simpa [hfirst, hsecond] using hfields
            obtain ⟨firstTrace, hfirstTrace⟩ :=
              (compactNodeSequentFormulaFields_eq_some_iff_exists_directTrace
                binderArity tokens first).mp hfirst
            obtain ⟨hsecondResult, hsecondValue⟩ :=
              (compactFormulaTokenValueParser_eq_some_iff
                binderArity (compactNumericNodeFieldsSuffix first)
                  secondValue finalSuffix).mp hsecond
            obtain ⟨secondTrace, hsecondTrace⟩ :=
              (compactFormulaTokenParser_eq_some_iff_exists_directTrace
                binderArity (compactNumericNodeFieldsSuffix first)
                  finalSuffix).mp hsecondResult
            subst fields
            refine ⟨(firstTrace.1,
              (firstTrace.2.1, (finalSuffix,
                (secondTrace, ([], []))))), ?_⟩
            rcases hfirstTrace with
              ⟨hsequent, hformula, hfirstFields,
                hafterFirstFinal, _hsecondEmpty,
                _htermEmpty, _hclosedEmpty⟩
            have hfirstSuffix :
                compactNumericNodeFieldsSuffix first =
                  compactRootBranchAfterFirst firstTrace := by
              rw [hfirstFields]
              simp only [compactNumericNodeFieldsSuffix]
              exact hafterFirstFinal.symm
            rw [hfirstSuffix] at hsecondValue
            simp only [CompactNodeSequentTwoFormulaDirectTraceValid]
            refine ⟨hsequent, hformula, ?_, ?_, rfl, rfl⟩
            · simpa [hfirstSuffix] using hsecondTrace
            · rw [hfirstFields]
              simp [hsecondValue]
  · rintro ⟨trace, htrace⟩
    unfold CompactNodeSequentTwoFormulaDirectTraceValid at htrace
    rcases htrace with
      ⟨hsequent, hfirst, hsecond, hfields, _, _⟩
    have hsequentResult :=
      (compactSequentTokenValueParser_eq_some_iff_exists_directTrace
        tokens fields.1 (compactRootBranchAfterSequent trace)).mpr
          ⟨compactRootBranchSequentTrace trace, hsequent⟩
    have hfirstResult :=
      (compactFormulaTokenParser_eq_some_iff_exists_directTrace
        binderArity (compactRootBranchAfterSequent trace)
          (compactRootBranchAfterFirst trace)).mpr
            ⟨compactRootBranchFirstFormulaTrace trace, hfirst⟩
    have hfirstValue :=
      (compactFormulaTokenValueParser_eq_some_iff
        binderArity (compactRootBranchAfterSequent trace)
          (consumedTokenPrefix
            (compactRootBranchAfterSequent trace)
            (compactRootBranchAfterFirst trace))
          (compactRootBranchAfterFirst trace)).mpr
            ⟨hfirstResult, rfl⟩
    have hsecondResult :=
      (compactFormulaTokenParser_eq_some_iff_exists_directTrace
        binderArity (compactRootBranchAfterFirst trace)
          (compactRootBranchFinalSuffix trace)).mpr
            ⟨compactRootBranchSecondFormulaTrace trace, hsecond⟩
    have hsecondValue :=
      (compactFormulaTokenValueParser_eq_some_iff
        binderArity (compactRootBranchAfterFirst trace)
          (consumedTokenPrefix
            (compactRootBranchAfterFirst trace)
            (compactRootBranchFinalSuffix trace))
          (compactRootBranchFinalSuffix trace)).mpr
            ⟨hsecondResult, rfl⟩
    have hfirstFields :
        compactNodeSequentFormulaFields binderArity tokens =
          some
            (fields.1,
              (consumedTokenPrefix
                (compactRootBranchAfterSequent trace)
                (compactRootBranchAfterFirst trace),
                (([] : List Nat),
                  (([] : List Nat),
                    compactRootBranchAfterFirst trace)))) := by
      exact compactNodeSequentFormulaFields_of_results
        binderArity tokens fields.1
          (compactRootBranchAfterSequent trace)
          (consumedTokenPrefix
            (compactRootBranchAfterSequent trace)
            (compactRootBranchAfterFirst trace))
          (compactRootBranchAfterFirst trace)
          hsequentResult hfirstValue
    have hresult :
        compactNodeSequentTwoFormulaFields binderArity tokens =
          some
            (fields.1,
              (consumedTokenPrefix
                (compactRootBranchAfterSequent trace)
                (compactRootBranchAfterFirst trace),
                (consumedTokenPrefix
                  (compactRootBranchAfterFirst trace)
                  (compactRootBranchFinalSuffix trace),
                  (([] : List Nat),
                    compactRootBranchFinalSuffix trace)))) := by
      exact compactNodeSequentTwoFormulaFields_of_results
        binderArity tokens
          (fields.1,
            (consumedTokenPrefix
              (compactRootBranchAfterSequent trace)
              (compactRootBranchAfterFirst trace),
              (([] : List Nat),
                (([] : List Nat),
                  compactRootBranchAfterFirst trace))))
          (consumedTokenPrefix
            (compactRootBranchAfterFirst trace)
            (compactRootBranchFinalSuffix trace))
          (compactRootBranchFinalSuffix trace)
          hfirstFields (by simpa [compactNumericNodeFieldsSuffix]
            using hsecondValue)
    exact hresult.trans (congrArg some hfields.symm)

theorem compactNodeSequentFormulaTermFields_eq_some_iff_exists_directTrace
    (formulaArity termArity : Nat) (tokens : List Nat)
    (fields : CompactNumericNodeFields) :
    compactNodeSequentFormulaTermFields
        formulaArity termArity tokens = some fields ↔
      ∃ trace : CompactNumericRootFieldBranchDirectTrace,
        CompactNodeSequentFormulaTermDirectTraceValid
          formulaArity termArity tokens fields trace := by
  constructor
  · intro hfields
    unfold compactNodeSequentFormulaTermFields at hfields
    cases hfirst : compactNodeSequentFormulaFields formulaArity tokens with
    | none => simp [hfirst] at hfields
    | some first =>
        cases hterm : compactTermTokenValueParser termArity
            (compactNumericNodeFieldsSuffix first) with
        | none => simp [hfirst, hterm] at hfields
        | some term =>
            rcases term with ⟨termValue, finalSuffix⟩
            have hfieldsEq :
                (first.1, (first.2.1,
                  (([] : List Nat), (termValue, finalSuffix)))) = fields := by
              simpa [hfirst, hterm] using hfields
            obtain ⟨firstTrace, hfirstTrace⟩ :=
              (compactNodeSequentFormulaFields_eq_some_iff_exists_directTrace
                formulaArity tokens first).mp hfirst
            obtain ⟨htermResult, htermValue⟩ :=
              (compactTermTokenValueParser_eq_some_iff
                termArity (compactNumericNodeFieldsSuffix first)
                  termValue finalSuffix).mp hterm
            obtain ⟨termTrace, htermTrace⟩ :=
              (compactTermTokenParser_eq_some_iff_exists_directTrace
                termArity (compactNumericNodeFieldsSuffix first)
                  finalSuffix).mp htermResult
            subst fields
            refine ⟨(firstTrace.1,
              (firstTrace.2.1, (finalSuffix,
                ([], (termTrace, []))))), ?_⟩
            rcases hfirstTrace with
              ⟨hsequent, hformula, hfirstFields,
                hafterFirstFinal, _hsecondEmpty,
                _htermEmpty, _hclosedEmpty⟩
            have hfirstSuffix :
                compactNumericNodeFieldsSuffix first =
                  compactRootBranchAfterFirst firstTrace := by
              rw [hfirstFields]
              simp only [compactNumericNodeFieldsSuffix]
              exact hafterFirstFinal.symm
            rw [hfirstSuffix] at htermValue
            simp only [CompactNodeSequentFormulaTermDirectTraceValid]
            refine ⟨hsequent, hformula, ?_, ?_, rfl, rfl⟩
            · simpa [hfirstSuffix] using htermTrace
            · rw [hfirstFields]
              simp [htermValue]
  · rintro ⟨trace, htrace⟩
    unfold CompactNodeSequentFormulaTermDirectTraceValid at htrace
    rcases htrace with
      ⟨hsequent, hformula, hterm, hfields, _, _⟩
    have hsequentResult :=
      (compactSequentTokenValueParser_eq_some_iff_exists_directTrace
        tokens fields.1 (compactRootBranchAfterSequent trace)).mpr
          ⟨compactRootBranchSequentTrace trace, hsequent⟩
    have hformulaResult :=
      (compactFormulaTokenParser_eq_some_iff_exists_directTrace
        formulaArity (compactRootBranchAfterSequent trace)
          (compactRootBranchAfterFirst trace)).mpr
            ⟨compactRootBranchFirstFormulaTrace trace, hformula⟩
    have hformulaValue :=
      (compactFormulaTokenValueParser_eq_some_iff
        formulaArity (compactRootBranchAfterSequent trace)
          (consumedTokenPrefix
            (compactRootBranchAfterSequent trace)
            (compactRootBranchAfterFirst trace))
          (compactRootBranchAfterFirst trace)).mpr
            ⟨hformulaResult, rfl⟩
    have htermResult :=
      (compactTermTokenParser_eq_some_iff_exists_directTrace
        termArity (compactRootBranchAfterFirst trace)
          (compactRootBranchFinalSuffix trace)).mpr
            ⟨compactRootBranchTermTrace trace, hterm⟩
    have htermValue :=
      (compactTermTokenValueParser_eq_some_iff
        termArity (compactRootBranchAfterFirst trace)
          (consumedTokenPrefix
            (compactRootBranchAfterFirst trace)
            (compactRootBranchFinalSuffix trace))
          (compactRootBranchFinalSuffix trace)).mpr
            ⟨htermResult, rfl⟩
    have hfirstFields :
        compactNodeSequentFormulaFields formulaArity tokens =
          some
            (fields.1,
              (consumedTokenPrefix
                (compactRootBranchAfterSequent trace)
                (compactRootBranchAfterFirst trace),
                (([] : List Nat),
                  (([] : List Nat),
                    compactRootBranchAfterFirst trace)))) := by
      exact compactNodeSequentFormulaFields_of_results
        formulaArity tokens fields.1
          (compactRootBranchAfterSequent trace)
          (consumedTokenPrefix
            (compactRootBranchAfterSequent trace)
            (compactRootBranchAfterFirst trace))
          (compactRootBranchAfterFirst trace)
          hsequentResult hformulaValue
    have hresult :
        compactNodeSequentFormulaTermFields
            formulaArity termArity tokens =
          some
            (fields.1,
              (consumedTokenPrefix
                (compactRootBranchAfterSequent trace)
                (compactRootBranchAfterFirst trace),
                (([] : List Nat),
                  (consumedTokenPrefix
                    (compactRootBranchAfterFirst trace)
                    (compactRootBranchFinalSuffix trace),
                    compactRootBranchFinalSuffix trace)))) := by
      exact compactNodeSequentFormulaTermFields_of_results
        formulaArity termArity tokens
          (fields.1,
            (consumedTokenPrefix
              (compactRootBranchAfterSequent trace)
              (compactRootBranchAfterFirst trace),
              (([] : List Nat),
                (([] : List Nat),
                  compactRootBranchAfterFirst trace))))
          (consumedTokenPrefix
            (compactRootBranchAfterFirst trace)
            (compactRootBranchFinalSuffix trace))
          (compactRootBranchFinalSuffix trace)
          hfirstFields (by simpa [compactNumericNodeFieldsSuffix]
            using htermValue)
    exact hresult.trans (congrArg some hfields.symm)

theorem compactNodeSequentClosedFormulaFields_eq_some_iff_exists_directTrace
    (tokens : List Nat) (fields : CompactNumericNodeFields) :
    compactNodeSequentClosedFormulaFields tokens = some fields ↔
      ∃ trace : CompactNumericRootFieldBranchDirectTrace,
        CompactNodeSequentClosedFormulaDirectTraceValid
          tokens fields trace := by
  constructor
  · intro hfields
    cases hsequent : compactSequentTokenValueParser tokens with
    | none =>
        simp [compactNodeSequentClosedFormulaFields,
          hsequent] at hfields
    | some parsedSequent =>
        rcases parsedSequent with ⟨values, afterSequent⟩
        cases hclosed : compactClosedFormulaTokenValueParser afterSequent with
        | none =>
            simp [compactNodeSequentClosedFormulaFields,
              hsequent, hclosed] at hfields
        | some parsedFormula =>
            rcases parsedFormula with ⟨formulaValue, finalSuffix⟩
            have hfieldsEq :
                (values, (formulaValue,
                  (([] : List Nat),
                    (([] : List Nat), finalSuffix)))) = fields := by
              simpa [compactNodeSequentClosedFormulaFields,
                hsequent, hclosed] using hfields
            subst fields
            obtain ⟨sequentTrace, hsequentTrace⟩ :=
              (compactSequentTokenValueParser_eq_some_iff_exists_directTrace
                tokens values afterSequent).mp hsequent
            obtain ⟨hclosedResult, hformulaValue⟩ :=
              (compactClosedFormulaTokenValueParser_eq_some_iff
                afterSequent formulaValue finalSuffix).mp hclosed
            obtain ⟨closedTrace, hclosedTrace⟩ :=
              (compactClosedFormulaTokenParser_eq_some_iff_exists_directTrace
                0 afterSequent finalSuffix).mp hclosedResult
            refine ⟨((afterSequent, sequentTrace),
              (([], []),
                (finalSuffix, ([], ([], closedTrace))))), ?_⟩
            simp [CompactNodeSequentClosedFormulaDirectTraceValid,
              hsequentTrace, hclosedTrace, hformulaValue]
  · rintro ⟨trace, htrace⟩
    unfold CompactNodeSequentClosedFormulaDirectTraceValid at htrace
    dsimp only at htrace
    rcases htrace with
      ⟨hsequent, hclosed, hfields, _⟩
    have hsequentResult :=
      (compactSequentTokenValueParser_eq_some_iff_exists_directTrace
        tokens fields.1 (compactRootBranchAfterSequent trace)).mpr
          ⟨compactRootBranchSequentTrace trace, hsequent⟩
    have hclosedResult :=
      (compactClosedFormulaTokenParser_eq_some_iff_exists_directTrace
        0 (compactRootBranchAfterSequent trace)
          (compactRootBranchFinalSuffix trace)).mpr
            ⟨compactRootBranchClosedFormulaTrace trace, hclosed⟩
    have hclosedValue :=
      (compactClosedFormulaTokenValueParser_eq_some_iff
        (compactRootBranchAfterSequent trace)
          (consumedTokenPrefix
            (compactRootBranchAfterSequent trace)
            (compactRootBranchFinalSuffix trace))
          (compactRootBranchFinalSuffix trace)).mpr
            ⟨hclosedResult, rfl⟩
    have hresult := compactNodeSequentClosedFormulaFields_of_results
      tokens fields.1 (compactRootBranchAfterSequent trace)
        (consumedTokenPrefix
          (compactRootBranchAfterSequent trace)
          (compactRootBranchFinalSuffix trace))
        (compactRootBranchFinalSuffix trace)
        hsequentResult hclosedValue
    exact hresult.trans (congrArg some hfields.symm)

/-- Direct local semantics of the public ten-tag root-field dispatcher. -/
def CompactNumericProofRootDirectTraceValid
    (tokens : List Nat) (root : CompactNumericProofRoot)
    (trace : CompactNumericRootFieldBranchDirectTrace) : Prop :=
  (tokens.head?.getD 10 = 0 ∧ root.1 = 0 ∧
      CompactNodeSequentFormulaDirectTraceValid
        0 tokens.tail root.2 trace) ∨
    (tokens.head?.getD 10 = 1 ∧ root.1 = 1 ∧
      CompactNodeSequentClosedFormulaDirectTraceValid
        tokens.tail root.2 trace) ∨
    (tokens.head?.getD 10 = 2 ∧ root.1 = 2 ∧
      CompactNodeSequentOnlyDirectTraceValid
        tokens.tail root.2 trace) ∨
    (tokens.head?.getD 10 = 3 ∧ root.1 = 3 ∧
      CompactNodeSequentTwoFormulaDirectTraceValid
        0 tokens.tail root.2 trace) ∨
    (tokens.head?.getD 10 = 4 ∧ root.1 = 4 ∧
      CompactNodeSequentTwoFormulaDirectTraceValid
        0 tokens.tail root.2 trace) ∨
    (tokens.head?.getD 10 = 5 ∧ root.1 = 5 ∧
      CompactNodeSequentFormulaDirectTraceValid
        1 tokens.tail root.2 trace) ∨
    (tokens.head?.getD 10 = 6 ∧ root.1 = 6 ∧
      CompactNodeSequentFormulaTermDirectTraceValid
        1 0 tokens.tail root.2 trace) ∨
    (tokens.head?.getD 10 = 7 ∧ root.1 = 7 ∧
      CompactNodeSequentOnlyDirectTraceValid
        tokens.tail root.2 trace) ∨
    (tokens.head?.getD 10 = 8 ∧ root.1 = 8 ∧
      CompactNodeSequentOnlyDirectTraceValid
        tokens.tail root.2 trace) ∨
    (tokens.head?.getD 10 = 9 ∧ root.1 = 9 ∧
      CompactNodeSequentFormulaDirectTraceValid
        0 tokens.tail root.2 trace)

theorem compactListedProofNodeFieldsParser_eq_some_iff_exists_directTrace
    (tokens : List Nat) (root : CompactNumericProofRoot) :
    compactListedProofNodeFieldsParser tokens = some root ↔
      ∃ trace : CompactNumericRootFieldBranchDirectTrace,
        CompactNumericProofRootDirectTraceValid tokens root trace := by
  rw [compactListedProofNodeFieldsParser_eq_some_iff_branchValid]
  cases tokens with
  | nil =>
      simp [CompactNumericProofRootBranchValid,
        CompactNumericProofRootDirectTraceValid]
  | cons tag suffix =>
      by_cases h0 : tag = 0
      · simp_all [CompactNumericProofRootBranchValid,
          CompactNumericProofRootDirectTraceValid,
          compactNodeSequentFormulaFields_eq_some_iff_exists_directTrace]
      by_cases h1 : tag = 1
      · simp_all [CompactNumericProofRootBranchValid,
          CompactNumericProofRootDirectTraceValid,
          compactNodeSequentClosedFormulaFields_eq_some_iff_exists_directTrace]
      by_cases h2 : tag = 2
      · simp_all [CompactNumericProofRootBranchValid,
          CompactNumericProofRootDirectTraceValid,
          compactNodeSequentOnlyFields_eq_some_iff_exists_directTrace]
      by_cases h3 : tag = 3
      · simp_all [CompactNumericProofRootBranchValid,
          CompactNumericProofRootDirectTraceValid,
          compactNodeSequentTwoFormulaFields_eq_some_iff_exists_directTrace]
      by_cases h4 : tag = 4
      · simp_all [CompactNumericProofRootBranchValid,
          CompactNumericProofRootDirectTraceValid,
          compactNodeSequentTwoFormulaFields_eq_some_iff_exists_directTrace]
      by_cases h5 : tag = 5
      · simp_all [CompactNumericProofRootBranchValid,
          CompactNumericProofRootDirectTraceValid,
          compactNodeSequentFormulaFields_eq_some_iff_exists_directTrace]
      by_cases h6 : tag = 6
      · simp_all [CompactNumericProofRootBranchValid,
          CompactNumericProofRootDirectTraceValid,
          compactNodeSequentFormulaTermFields_eq_some_iff_exists_directTrace]
      by_cases h7 : tag = 7
      · simp_all [CompactNumericProofRootBranchValid,
          CompactNumericProofRootDirectTraceValid,
          compactNodeSequentOnlyFields_eq_some_iff_exists_directTrace]
      by_cases h8 : tag = 8
      · simp_all [CompactNumericProofRootBranchValid,
          CompactNumericProofRootDirectTraceValid,
          compactNodeSequentOnlyFields_eq_some_iff_exists_directTrace]
      by_cases h9 : tag = 9
      · simp_all [CompactNumericProofRootBranchValid,
          CompactNumericProofRootDirectTraceValid,
          compactNodeSequentFormulaFields_eq_some_iff_exists_directTrace]
      simp_all [CompactNumericProofRootBranchValid,
        CompactNumericProofRootDirectTraceValid]

theorem compactNumericProofRootDirectTraceValid_primrec :
    PrimrecPred (fun input :
        (List Nat × CompactNumericProofRoot) ×
          CompactNumericRootFieldBranchDirectTrace =>
      CompactNumericProofRootDirectTraceValid
        input.1.1 input.1.2 input.2) := by
  let Input :=
    (List Nat × CompactNumericProofRoot) ×
      CompactNumericRootFieldBranchDirectTrace
  have htokens : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hroot : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have htrace : Primrec (fun input : Input => input.2) := Primrec.snd
  have htag : Primrec (fun input : Input =>
      input.1.1.head?.getD 10) :=
    Primrec.option_getD.comp
      (Primrec.list_head?.comp htokens) (Primrec.const 10)
  have hsuffix : Primrec (fun input : Input => input.1.1.tail) :=
    Primrec.list_tail.comp htokens
  have hrootTag : Primrec (fun input : Input => input.1.2.1) :=
    Primrec.fst.comp hroot
  have hfields : Primrec (fun input : Input => input.1.2.2) :=
    Primrec.snd.comp hroot
  have htagEq (tag : Nat) : PrimrecPred (fun input : Input =>
      input.1.1.head?.getD 10 = tag) :=
    Primrec.eq.comp htag (Primrec.const tag)
  have hrootEq (tag : Nat) : PrimrecPred (fun input : Input =>
      input.1.2.1 = tag) :=
    Primrec.eq.comp hrootTag (Primrec.const tag)
  have hformula (binderArity : Nat) : PrimrecPred (fun input : Input =>
      CompactNodeSequentFormulaDirectTraceValid binderArity
        input.1.1.tail input.1.2.2 input.2) :=
    compactNodeSequentFormulaDirectTraceValid_primrec.comp <|
      Primrec.pair
        (Primrec.pair
          (Primrec.pair (Primrec.const binderArity) hsuffix) hfields)
        htrace
  have hclosed : PrimrecPred (fun input : Input =>
      CompactNodeSequentClosedFormulaDirectTraceValid
        input.1.1.tail input.1.2.2 input.2) :=
    compactNodeSequentClosedFormulaDirectTraceValid_primrec.comp <|
      Primrec.pair (Primrec.pair hsuffix hfields) htrace
  have honly : PrimrecPred (fun input : Input =>
      CompactNodeSequentOnlyDirectTraceValid
        input.1.1.tail input.1.2.2 input.2) :=
    compactNodeSequentOnlyDirectTraceValid_primrec.comp <|
      Primrec.pair (Primrec.pair hsuffix hfields) htrace
  have htwo (binderArity : Nat) : PrimrecPred (fun input : Input =>
      CompactNodeSequentTwoFormulaDirectTraceValid binderArity
        input.1.1.tail input.1.2.2 input.2) :=
    compactNodeSequentTwoFormulaDirectTraceValid_primrec.comp <|
      Primrec.pair
        (Primrec.pair
          (Primrec.pair (Primrec.const binderArity) hsuffix) hfields)
        htrace
  have hformulaTerm (formulaArity termArity : Nat) :
      PrimrecPred (fun input : Input =>
        CompactNodeSequentFormulaTermDirectTraceValid
          formulaArity termArity input.1.1.tail
            input.1.2.2 input.2) :=
    compactNodeSequentFormulaTermDirectTraceValid_primrec.comp <|
      Primrec.pair
        (Primrec.pair
          (Primrec.pair
            (Primrec.pair
              (Primrec.const formulaArity) (Primrec.const termArity))
            hsuffix)
          hfields)
        htrace
  have h0 := (htagEq 0).and ((hrootEq 0).and (hformula 0))
  have h1 := (htagEq 1).and ((hrootEq 1).and hclosed)
  have h2 := (htagEq 2).and ((hrootEq 2).and honly)
  have h3 := (htagEq 3).and ((hrootEq 3).and (htwo 0))
  have h4 := (htagEq 4).and ((hrootEq 4).and (htwo 0))
  have h5 := (htagEq 5).and ((hrootEq 5).and (hformula 1))
  have h6 := (htagEq 6).and ((hrootEq 6).and (hformulaTerm 1 0))
  have h7 := (htagEq 7).and ((hrootEq 7).and honly)
  have h8 := (htagEq 8).and ((hrootEq 8).and honly)
  have h9 := (htagEq 9).and ((hrootEq 9).and (hformula 0))
  exact
    (h0.or (h1.or (h2.or (h3.or (h4.or
      (h5.or (h6.or (h7.or (h8.or h9))))))))).of_eq fun input => by
        rfl

#print axioms compactNodeSequentOnlyFields_eq_some_iff_exists_directTrace
#print axioms compactNodeSequentFormulaFields_eq_some_iff_exists_directTrace
#print axioms compactNodeSequentTwoFormulaFields_eq_some_iff_exists_directTrace
#print axioms compactNodeSequentFormulaTermFields_eq_some_iff_exists_directTrace
#print axioms compactNodeSequentClosedFormulaFields_eq_some_iff_exists_directTrace
#print axioms compactListedProofNodeFieldsParser_eq_some_iff_exists_directTrace
#print axioms compactNumericProofRootDirectTraceValid_primrec

end FoundationCompactNumericListedRootFieldsDirectTrace
