import integration.FoundationCompactProofTokenMachine
import integration.FoundationCompactPAAxiomCertificate

/-!
# Numeric token machines for compact PA certificates

The PA-axiom parser handles all 23 tags directly on natural-number tokens.
The recursive structural-certificate parser is added on top of this finite
base parser.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

namespace FoundationCompactCertificateTokenMachine

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactArithmeticSymbolCode
open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactPAAxiomCertificate

def compactPAAxiomCertificateTokens : PAAxiomCertificate -> List Nat
  | .eqRefl => [0]
  | .eqSymm => [1]
  | .eqTrans => [2]
  | .eqFuncExt (arity := arity) functionSymbol =>
      [3, arity, Encodable.encode functionSymbol]
  | .eqRelExt (arity := arity) relationSymbol =>
      [4, arity, Encodable.encode relationSymbol]
  | .addZero => [5]
  | .addAssoc => [6]
  | .addComm => [7]
  | .addEqOfLt => [8]
  | .zeroLe => [9]
  | .zeroLtOne => [10]
  | .oneLeOfZeroLt => [11]
  | .addLtAdd => [12]
  | .mulZero => [13]
  | .mulOne => [14]
  | .mulAssoc => [15]
  | .mulComm => [16]
  | .mulLtMul => [17]
  | .distr => [18]
  | .ltIrrefl => [19]
  | .ltTrans => [20]
  | .ltTri => [21]
  | .induction body => 22 :: compactArithmeticFormulaTokens body

def compactPAAxiomCertificateTokenParser
    (tokens : List Nat) : Option (List Nat) :=
  match tokens with
  | [] => none
  | tag :: suffix =>
      if tag = 3 then
        if 2 <= suffix.length then
          let arity := compactTokenAt 0 suffix
          let functionCode := compactTokenAt 1 suffix
          if ArithmeticFuncCodeValid arity functionCode then
            some (suffix.drop 2)
          else none
        else none
      else if tag = 4 then
        if 2 <= suffix.length then
          let arity := compactTokenAt 0 suffix
          let relationCode := compactTokenAt 1 suffix
          if ArithmeticRelCodeValid arity relationCode then
            some (suffix.drop 2)
          else none
        else none
      else if tag = 22 then
        compactFormulaTokenParser 1 suffix
      else if tag < 22 then some suffix
      else none

theorem binaryPAAxiomCertificateCode_eq_tokenStream
    (certificate : PAAxiomCertificate) :
    binaryPAAxiomCertificateCode certificate =
      (compactPAAxiomCertificateTokens certificate).flatMap binaryNatCode := by
  cases certificate <;>
    simp [binaryPAAxiomCertificateCode,
      compactPAAxiomCertificateTokens,
      binaryFormulaCode_eq_tokenStream]

theorem compactPAAxiomCertificateTokens_length_pos
    (certificate : PAAxiomCertificate) :
    0 < (compactPAAxiomCertificateTokens certificate).length := by
  cases certificate <;>
    simp [compactPAAxiomCertificateTokens]

theorem compactPAAxiomCertificateTokenParser_canonical_append
    (certificate : PAAxiomCertificate) (suffix : List Nat) :
    compactPAAxiomCertificateTokenParser
        (compactPAAxiomCertificateTokens certificate ++ suffix) =
      some suffix := by
  cases certificate with
  | eqFuncExt functionSymbol =>
      have hvalid := arithmeticFuncCodeValid_encode functionSymbol
      simp [compactPAAxiomCertificateTokens,
        compactPAAxiomCertificateTokenParser, compactTokenAt, hvalid]
  | eqRelExt relationSymbol =>
      have hvalid := arithmeticRelCodeValid_encode relationSymbol
      simp [compactPAAxiomCertificateTokens,
        compactPAAxiomCertificateTokenParser, compactTokenAt, hvalid]
  | induction body =>
      simp [compactPAAxiomCertificateTokens,
        compactPAAxiomCertificateTokenParser,
        compactFormulaTokenParser_canonical_append]
  | eqRefl => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]
  | eqSymm => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]
  | eqTrans => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]
  | addZero => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]
  | addAssoc => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]
  | addComm => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]
  | addEqOfLt => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]
  | zeroLe => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]
  | zeroLtOne => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]
  | oneLeOfZeroLt => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]
  | addLtAdd => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]
  | mulZero => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]
  | mulOne => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]
  | mulAssoc => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]
  | mulComm => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]
  | mulLtMul => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]
  | distr => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]
  | ltIrrefl => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]
  | ltTrans => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]
  | ltTri => simp [compactPAAxiomCertificateTokens,
      compactPAAxiomCertificateTokenParser]

theorem compactPAAxiomCertificateTokenParser_primrec :
    Primrec compactPAAxiomCertificateTokenParser := by
  have hempty : PrimrecPred (fun tokens : List Nat => tokens = []) :=
    Primrec.eq.comp Primrec.id (Primrec.const [])
  have htail : Primrec (fun tokens : List Nat => tokens.tail) :=
    Primrec.list_tail
  have hheadOption : Primrec (fun tokens : List Nat => tokens.head?) :=
    Primrec.list_head?
  have htag : Primrec
      (fun tokens : List Nat => tokens.head?.getD 0) :=
    Primrec.option_getD.comp hheadOption (Primrec.const 0)
  have hsuffixLength : Primrec
      (fun tokens : List Nat => tokens.tail.length) :=
    Primrec.list_length.comp htail
  have hhasTwo : PrimrecPred
      (fun tokens : List Nat => 2 <= tokens.tail.length) :=
    Primrec.nat_le.comp (Primrec.const 2) hsuffixLength
  have harity : Primrec
      (fun tokens : List Nat => compactTokenAt 0 tokens.tail) :=
    compactTokenAt_primrec.comp (Primrec.const 0) htail
  have hsymbolCode : Primrec
      (fun tokens : List Nat => compactTokenAt 1 tokens.tail) :=
    compactTokenAt_primrec.comp (Primrec.const 1) htail
  have hfuncValid : PrimrecPred
      (fun tokens : List Nat =>
        ArithmeticFuncCodeValid
          (compactTokenAt 0 tokens.tail)
          (compactTokenAt 1 tokens.tail)) :=
    arithmeticFuncCodeValid_primrec.comp harity hsymbolCode
  have hrelValid : PrimrecPred
      (fun tokens : List Nat =>
        ArithmeticRelCodeValid
          (compactTokenAt 0 tokens.tail)
          (compactTokenAt 1 tokens.tail)) :=
    arithmeticRelCodeValid_primrec.comp harity hsymbolCode
  have hdropTwo : Primrec (fun tokens : List Nat => tokens.tail.drop 2) :=
    Primrec.list_drop.comp (Primrec.const 2) htail
  have hsuccessTwo : Primrec
      (fun tokens : List Nat => some (tokens.tail.drop 2)) :=
    Primrec.option_some.comp hdropTwo
  have hnone : Primrec
      (fun _tokens : List Nat => (none : Option (List Nat))) :=
    Primrec.const none
  have hfuncBranch : Primrec
      (fun tokens : List Nat =>
        if 2 <= tokens.tail.length then
          if ArithmeticFuncCodeValid
              (compactTokenAt 0 tokens.tail)
              (compactTokenAt 1 tokens.tail) then
            some (tokens.tail.drop 2)
          else none
        else none) :=
    Primrec.ite hhasTwo (Primrec.ite hfuncValid hsuccessTwo hnone) hnone
  have hrelBranch : Primrec
      (fun tokens : List Nat =>
        if 2 <= tokens.tail.length then
          if ArithmeticRelCodeValid
              (compactTokenAt 0 tokens.tail)
              (compactTokenAt 1 tokens.tail) then
            some (tokens.tail.drop 2)
          else none
        else none) :=
    Primrec.ite hhasTwo (Primrec.ite hrelValid hsuccessTwo hnone) hnone
  have hformula : Primrec
      (fun tokens : List Nat => compactFormulaTokenParser 1 tokens.tail) :=
    compactFormulaTokenParser_primrec.comp
      (Primrec.const 1) htail
  have hfixed : Primrec
      (fun tokens : List Nat => some tokens.tail) :=
    Primrec.option_some.comp htail
  have htagEq (tag : Nat) : PrimrecPred
      (fun tokens : List Nat => tokens.head?.getD 0 = tag) :=
    Primrec.eq.comp htag (Primrec.const tag)
  have htagLt22 : PrimrecPred
      (fun tokens : List Nat => tokens.head?.getD 0 < 22) :=
    Primrec.nat_lt.comp htag (Primrec.const 22)
  have hnonempty : Primrec
      (fun tokens : List Nat =>
        if tokens.head?.getD 0 = 3 then
          if 2 <= tokens.tail.length then
            if ArithmeticFuncCodeValid
                (compactTokenAt 0 tokens.tail)
                (compactTokenAt 1 tokens.tail) then
              some (tokens.tail.drop 2)
            else none
          else none
        else if tokens.head?.getD 0 = 4 then
          if 2 <= tokens.tail.length then
            if ArithmeticRelCodeValid
                (compactTokenAt 0 tokens.tail)
                (compactTokenAt 1 tokens.tail) then
              some (tokens.tail.drop 2)
            else none
          else none
        else if tokens.head?.getD 0 = 22 then
          compactFormulaTokenParser 1 tokens.tail
        else if tokens.head?.getD 0 < 22 then some tokens.tail
        else none) :=
    Primrec.ite (htagEq 3) hfuncBranch
      (Primrec.ite (htagEq 4) hrelBranch
        (Primrec.ite (htagEq 22) hformula
          (Primrec.ite htagLt22 hfixed hnone)))
  exact
    (Primrec.ite hempty hnone hnonempty).of_eq fun tokens => by
      cases tokens <;>
        simp [compactPAAxiomCertificateTokenParser]

def compactStructuralCertificateTokens :
    StructuralValidityCertificate -> List Nat
  | .leaf => [0]
  | .axiomCert certificate =>
      1 :: compactPAAxiomCertificateTokens certificate
  | .unary premise =>
      2 :: compactStructuralCertificateTokens premise
  | .binary left right =>
      3 :: compactStructuralCertificateTokens left ++
        compactStructuralCertificateTokens right

theorem binaryStructuralValidityCertificateCode_eq_tokenStream
    (certificate : StructuralValidityCertificate) :
    binaryStructuralValidityCertificateCode certificate =
      (compactStructuralCertificateTokens certificate).flatMap
        binaryNatCode := by
  induction certificate with
  | leaf =>
      simp [binaryStructuralValidityCertificateCode,
        compactStructuralCertificateTokens]
  | axiomCert certificate =>
      simp [binaryStructuralValidityCertificateCode,
        compactStructuralCertificateTokens,
        binaryPAAxiomCertificateCode_eq_tokenStream]
  | unary premise ih =>
      simp [binaryStructuralValidityCertificateCode,
        compactStructuralCertificateTokens, ih]
  | binary left right ihLeft ihRight =>
      simp [binaryStructuralValidityCertificateCode,
        compactStructuralCertificateTokens, ihLeft, ihRight,
        List.flatMap_append, List.append_assoc]

abbrev CompactCertificateTask := Nat × Nat × Nat

abbrev CompactCertificateParserState :=
  List Nat × List CompactCertificateTask ×
    Option (Option (List Nat))

def compactStructuralCertificateTask : CompactCertificateTask :=
  (8, 0, 0)

def compactPAAxiomCertificateTask : CompactCertificateTask :=
  (9, 0, 0)

def compactStructuralCertificateTaskSteps :
    StructuralValidityCertificate -> Nat
  | .leaf => 1
  | .axiomCert _ => 2
  | .unary premise =>
      1 + compactStructuralCertificateTaskSteps premise
  | .binary left right =>
      1 + compactStructuralCertificateTaskSteps left +
        compactStructuralCertificateTaskSteps right

def compactCertificateAxiomTokenStep
    (tokens : List Nat) (tasks : List CompactCertificateTask) :
    CompactCertificateParserState :=
  match compactPAAxiomCertificateTokenParser tokens with
  | none => compactSyntaxFailure tokens tasks
  | some suffix => compactSyntaxContinue suffix tasks

def compactStructuralCertificateNodeTokenStep
    (tokens : List Nat) (tasks : List CompactCertificateTask) :
    CompactCertificateParserState :=
  match tokens with
  | [] => compactSyntaxFailure tokens tasks
  | tag :: suffix =>
      if tag = 0 then compactSyntaxContinue suffix tasks
      else if tag = 1 then
        compactSyntaxContinue suffix
          (compactPAAxiomCertificateTask :: tasks)
      else if tag = 2 then
        compactSyntaxContinue suffix
          (compactStructuralCertificateTask :: tasks)
      else if tag = 3 then
        compactSyntaxContinue suffix
          (compactStructuralCertificateTask ::
            compactStructuralCertificateTask :: tasks)
      else compactSyntaxFailure tokens tasks

def compactCertificateTaskTokenStep
    (input : CompactCertificateTask × List Nat ×
      List CompactCertificateTask) : CompactCertificateParserState :=
  let kind := input.1.1
  let tokens := input.2.1
  let tasks := input.2.2
  if kind = 8 then
    compactStructuralCertificateNodeTokenStep tokens tasks
  else if kind = 9 then
    compactCertificateAxiomTokenStep tokens tasks
  else compactSyntaxFailure tokens tasks

def compactCertificateParserRunningStep
    (state : CompactCertificateParserState) :
    CompactCertificateParserState :=
  match state.2.1 with
  | [] => (state.1, [], some (some state.1))
  | task :: tasks =>
      compactCertificateTaskTokenStep (task, state.1, tasks)

def compactCertificateParserStep
    (state : CompactCertificateParserState) :
    CompactCertificateParserState :=
  if state.2.2.isSome then state else compactCertificateParserRunningStep state

def compactCertificateParserFuelBound (tokens : List Nat) : Nat :=
  16 * (tokens.length + 1) * (tokens.length + 1) + 8

def compactCertificateParserInitialState
    (tokens : List Nat) : CompactCertificateParserState :=
  (tokens, [compactStructuralCertificateTask], none)

def compactStructuralCertificateTokenParserRun
    (tokens : List Nat) : CompactCertificateParserState :=
  (compactCertificateParserStep^[compactCertificateParserFuelBound tokens])
    (compactCertificateParserInitialState tokens)

def compactStructuralCertificateTokenParser
    (tokens : List Nat) : Option (List Nat) :=
  compactSyntaxParserStateOutput
    (compactStructuralCertificateTokenParserRun tokens)

@[simp] theorem compactCertificateParserStep_structural
    (tokens : List Nat) (tasks : List CompactCertificateTask) :
    compactCertificateParserStep
        (tokens, compactStructuralCertificateTask :: tasks, none) =
      compactStructuralCertificateNodeTokenStep tokens tasks := by
  simp [compactCertificateParserStep,
    compactCertificateParserRunningStep,
    compactCertificateTaskTokenStep, compactStructuralCertificateTask]

@[simp] theorem compactCertificateParserStep_axiom
    (tokens : List Nat) (tasks : List CompactCertificateTask) :
    compactCertificateParserStep
        (tokens, compactPAAxiomCertificateTask :: tasks, none) =
      compactCertificateAxiomTokenStep tokens tasks := by
  simp [compactCertificateParserStep,
    compactCertificateParserRunningStep,
    compactCertificateTaskTokenStep, compactPAAxiomCertificateTask]

theorem compactCertificateParser_iterate_trans
    {start middle finish : CompactCertificateParserState}
    {firstSteps secondSteps : Nat}
    (hfirst : (compactCertificateParserStep^[firstSteps]) start = middle)
    (hsecond : (compactCertificateParserStep^[secondSteps]) middle = finish) :
    (compactCertificateParserStep^[firstSteps + secondSteps]) start = finish := by
  rw [Nat.add_comm, Function.iterate_add_apply, hfirst, hsecond]

theorem compactCertificateParser_iterate_one_axiom_canonical
    (certificate : PAAxiomCertificate) (suffix : List Nat)
    (tasks : List CompactCertificateTask) :
    (compactCertificateParserStep^[1])
        (compactPAAxiomCertificateTokens certificate ++ suffix,
          compactPAAxiomCertificateTask :: tasks, none) =
      (suffix, tasks, none) := by
  simp [Function.iterate_one, compactCertificateAxiomTokenStep,
    compactPAAxiomCertificateTokenParser_canonical_append,
    compactSyntaxContinue]

theorem compactStructuralCertificateTask_execute
    (certificate : StructuralValidityCertificate)
    (suffix : List Nat) (tasks : List CompactCertificateTask) :
    (compactCertificateParserStep^[
        compactStructuralCertificateTaskSteps certificate])
        (compactStructuralCertificateTokens certificate ++ suffix,
          compactStructuralCertificateTask :: tasks, none) =
      (suffix, tasks, none) := by
  induction certificate generalizing suffix tasks with
  | leaf =>
      simp [compactStructuralCertificateTaskSteps,
        compactStructuralCertificateTokens, Function.iterate_one,
        compactStructuralCertificateNodeTokenStep, compactSyntaxContinue]
  | axiomCert certificate =>
      have hnode :
          (compactCertificateParserStep^[1])
              (compactStructuralCertificateTokens
                    (.axiomCert certificate) ++ suffix,
                compactStructuralCertificateTask :: tasks, none) =
            (compactPAAxiomCertificateTokens certificate ++ suffix,
              compactPAAxiomCertificateTask :: tasks, none) := by
        simp [compactStructuralCertificateTokens, Function.iterate_one,
          compactStructuralCertificateNodeTokenStep, compactSyntaxContinue]
      have haxiom :=
        compactCertificateParser_iterate_one_axiom_canonical
          certificate suffix tasks
      have hrun := compactCertificateParser_iterate_trans hnode haxiom
      simpa [compactStructuralCertificateTaskSteps] using hrun
  | unary premise ih =>
      have hnode :
          (compactCertificateParserStep^[1])
              (compactStructuralCertificateTokens (.unary premise) ++ suffix,
                compactStructuralCertificateTask :: tasks, none) =
            (compactStructuralCertificateTokens premise ++ suffix,
              compactStructuralCertificateTask :: tasks, none) := by
        simp [compactStructuralCertificateTokens, Function.iterate_one,
          compactStructuralCertificateNodeTokenStep, compactSyntaxContinue]
      have hpremise := ih suffix tasks
      have hrun := compactCertificateParser_iterate_trans hnode hpremise
      simpa [compactStructuralCertificateTaskSteps] using hrun
  | binary left right ihLeft ihRight =>
      have hnode :
          (compactCertificateParserStep^[1])
              (compactStructuralCertificateTokens (.binary left right) ++
                  suffix,
                compactStructuralCertificateTask :: tasks, none) =
            (compactStructuralCertificateTokens left ++
                (compactStructuralCertificateTokens right ++ suffix),
              compactStructuralCertificateTask ::
                compactStructuralCertificateTask :: tasks,
              none) := by
        simp [compactStructuralCertificateTokens, Function.iterate_one,
          compactStructuralCertificateNodeTokenStep, compactSyntaxContinue,
          List.append_assoc]
      have hleft := ihLeft
        (compactStructuralCertificateTokens right ++ suffix)
        (compactStructuralCertificateTask :: tasks)
      have hright := ihRight suffix tasks
      have hfirst := compactCertificateParser_iterate_trans hnode hleft
      have hrun := compactCertificateParser_iterate_trans hfirst hright
      simpa [compactStructuralCertificateTaskSteps, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, List.append_assoc] using hrun

theorem compactStructuralCertificateTokens_length_pos
    (certificate : StructuralValidityCertificate) :
    0 < (compactStructuralCertificateTokens certificate).length := by
  cases certificate <;>
    simp [compactStructuralCertificateTokens]

theorem compactStructuralCertificateTaskSteps_le_tokenLength
    (certificate : StructuralValidityCertificate) :
    compactStructuralCertificateTaskSteps certificate <=
      (compactStructuralCertificateTokens certificate).length := by
  induction certificate with
  | leaf =>
      simp [compactStructuralCertificateTaskSteps,
        compactStructuralCertificateTokens]
  | axiomCert certificate =>
      have haxiom := compactPAAxiomCertificateTokens_length_pos certificate
      simp [compactStructuralCertificateTaskSteps,
        compactStructuralCertificateTokens]
      omega
  | unary premise ih =>
      simp [compactStructuralCertificateTaskSteps,
        compactStructuralCertificateTokens]
      omega
  | binary left right ihLeft ihRight =>
      simp [compactStructuralCertificateTaskSteps,
        compactStructuralCertificateTokens]
      omega

theorem compactCertificateParserFuelBound_length_add_one
    (tokens : List Nat) :
    tokens.length + 1 <= compactCertificateParserFuelBound tokens := by
  simp only [compactCertificateParserFuelBound]
  nlinarith

@[simp] theorem compactCertificateParserStep_empty
    (tokens : List Nat) :
    compactCertificateParserStep (tokens, [], none) =
      (tokens, [], some (some tokens)) := by
  simp [compactCertificateParserStep,
    compactCertificateParserRunningStep]

theorem compactCertificateParserStep_done
    (tokens : List Nat) (tasks : List CompactCertificateTask)
    (result : Option (List Nat)) :
    compactCertificateParserStep (tokens, tasks, some result) =
      (tokens, tasks, some result) := by
  simp [compactCertificateParserStep]

theorem compactCertificateParserStep_iterate_done
    (fuel : Nat) (tokens : List Nat)
    (tasks : List CompactCertificateTask)
    (result : Option (List Nat)) :
    (compactCertificateParserStep^[fuel])
        (tokens, tasks, some result) =
      (tokens, tasks, some result) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply,
        compactCertificateParserStep_done, ih]

theorem compactStructuralCertificateTokenParser_canonical_append
    (certificate : StructuralValidityCertificate) (suffix : List Nat) :
    compactStructuralCertificateTokenParser
        (compactStructuralCertificateTokens certificate ++ suffix) =
      some suffix := by
  let tokens := compactStructuralCertificateTokens certificate ++ suffix
  let used := compactStructuralCertificateTaskSteps certificate + 1
  have htask := compactStructuralCertificateTask_execute certificate suffix []
  have hfinish :
      (compactCertificateParserStep^[used])
          (tokens, [compactStructuralCertificateTask], none) =
        (suffix, [], some (some suffix)) := by
    apply compactCertificateParser_iterate_trans htask
    simp [Function.iterate_one]
  have hsteps :=
    compactStructuralCertificateTaskSteps_le_tokenLength certificate
  have hprefixLength :
      (compactStructuralCertificateTokens certificate).length <=
        tokens.length := by
    simp [tokens]
  have hfuel := compactCertificateParserFuelBound_length_add_one tokens
  have hused : used <= compactCertificateParserFuelBound tokens := by
    omega
  obtain ⟨extra, hfuelEq⟩ := exists_add_of_le hused
  have hrun :
      (compactCertificateParserStep^[compactCertificateParserFuelBound tokens])
          (tokens, [compactStructuralCertificateTask], none) =
        (suffix, [], some (some suffix)) := by
    rw [hfuelEq]
    exact compactCertificateParser_iterate_trans hfinish
      (compactCertificateParserStep_iterate_done
        extra suffix [] (some suffix))
  simp [compactStructuralCertificateTokenParser,
    compactStructuralCertificateTokenParserRun,
    compactCertificateParserInitialState,
    compactSyntaxParserStateOutput, tokens, hrun]

theorem compactCertificateAxiomTokenStep_primrec :
    Primrec₂ compactCertificateAxiomTokenStep := by
  apply Primrec₂.mk
  have htokens : Primrec
      (fun input : List Nat × List CompactCertificateTask => input.1) :=
    Primrec.fst
  have htasks : Primrec
      (fun input : List Nat × List CompactCertificateTask => input.2) :=
    Primrec.snd
  have hparse : Primrec
      (fun input : List Nat × List CompactCertificateTask =>
        compactPAAxiomCertificateTokenParser input.1) :=
    compactPAAxiomCertificateTokenParser_primrec.comp htokens
  have hfailure : Primrec
      (fun input : List Nat × List CompactCertificateTask =>
        compactSyntaxFailure input.1 input.2) :=
    compactSyntaxFailure_primrec.comp htokens htasks
  have hsuccess : Primrec₂
      (fun (input : List Nat × List CompactCertificateTask)
          (suffix : List Nat) =>
        compactSyntaxContinue suffix input.2) :=
    compactSyntaxContinue_primrec.comp₂ Primrec₂.right
      ((htasks.comp Primrec.fst).to₂)
  exact
    (Primrec.option_casesOn hparse hfailure hsuccess).of_eq
      fun input => by
        cases hresult : compactPAAxiomCertificateTokenParser input.1 <;>
          simp [compactCertificateAxiomTokenStep, hresult]

theorem compactStructuralCertificateNodeTokenStep_primrec :
    Primrec₂ compactStructuralCertificateNodeTokenStep := by
  apply Primrec₂.mk
  have htokens : Primrec
      (fun input : List Nat × List CompactCertificateTask => input.1) :=
    Primrec.fst
  have htasks : Primrec
      (fun input : List Nat × List CompactCertificateTask => input.2) :=
    Primrec.snd
  have hempty : PrimrecPred
      (fun input : List Nat × List CompactCertificateTask =>
        input.1 = []) :=
    Primrec.eq.comp htokens (Primrec.const [])
  have hheadOption : Primrec
      (fun input : List Nat × List CompactCertificateTask =>
        input.1.head?) :=
    Primrec.list_head?.comp htokens
  have htag : Primrec
      (fun input : List Nat × List CompactCertificateTask =>
        input.1.head?.getD 0) :=
    Primrec.option_getD.comp hheadOption (Primrec.const 0)
  have htail : Primrec
      (fun input : List Nat × List CompactCertificateTask =>
        input.1.tail) :=
    Primrec.list_tail.comp htokens
  have hfailure : Primrec
      (fun input : List Nat × List CompactCertificateTask =>
        compactSyntaxFailure input.1 input.2) :=
    compactSyntaxFailure_primrec.comp htokens htasks
  have hprepend (taskPrefix : List CompactCertificateTask) : Primrec
      (fun input : List Nat × List CompactCertificateTask =>
        taskPrefix ++ input.2) := by
    induction taskPrefix with
    | nil => simpa using htasks
    | cons head tail ih =>
        exact Primrec.list_cons.comp (Primrec.const head) ih
  have hcontinue (taskPrefix : List CompactCertificateTask) : Primrec
      (fun input : List Nat × List CompactCertificateTask =>
        compactSyntaxContinue input.1.tail (taskPrefix ++ input.2)) :=
    compactSyntaxContinue_primrec.comp htail (hprepend taskPrefix)
  have htagEq (tag : Nat) : PrimrecPred
      (fun input : List Nat × List CompactCertificateTask =>
        input.1.head?.getD 0 = tag) :=
    Primrec.eq.comp htag (Primrec.const tag)
  have h0 := hcontinue []
  have h1 := hcontinue [compactPAAxiomCertificateTask]
  have h2 := hcontinue [compactStructuralCertificateTask]
  have h3 := hcontinue
    [compactStructuralCertificateTask, compactStructuralCertificateTask]
  have hnonempty : Primrec
      (fun input : List Nat × List CompactCertificateTask =>
        if input.1.head?.getD 0 = 0 then
          compactSyntaxContinue input.1.tail input.2
        else if input.1.head?.getD 0 = 1 then
          compactSyntaxContinue input.1.tail
            (compactPAAxiomCertificateTask :: input.2)
        else if input.1.head?.getD 0 = 2 then
          compactSyntaxContinue input.1.tail
            (compactStructuralCertificateTask :: input.2)
        else if input.1.head?.getD 0 = 3 then
          compactSyntaxContinue input.1.tail
            (compactStructuralCertificateTask ::
              compactStructuralCertificateTask :: input.2)
        else compactSyntaxFailure input.1 input.2) :=
    Primrec.ite (htagEq 0) h0
      (Primrec.ite (htagEq 1) h1
        (Primrec.ite (htagEq 2) h2
          (Primrec.ite (htagEq 3) h3 hfailure)))
  exact
    (Primrec.ite hempty hfailure hnonempty).of_eq fun input => by
      cases input.1 <;>
        simp [compactStructuralCertificateNodeTokenStep]

theorem compactCertificateTaskTokenStep_primrec :
    Primrec compactCertificateTaskTokenStep := by
  have htask : Primrec
      (fun input : CompactCertificateTask × List Nat ×
          List CompactCertificateTask => input.1) :=
    Primrec.fst
  have hkind : Primrec
      (fun input : CompactCertificateTask × List Nat ×
          List CompactCertificateTask => input.1.1) :=
    Primrec.fst.comp htask
  have htokens : Primrec
      (fun input : CompactCertificateTask × List Nat ×
          List CompactCertificateTask => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have htasks : Primrec
      (fun input : CompactCertificateTask × List Nat ×
          List CompactCertificateTask => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hkindEq (kind : Nat) : PrimrecPred
      (fun input : CompactCertificateTask × List Nat ×
          List CompactCertificateTask => input.1.1 = kind) :=
    Primrec.eq.comp hkind (Primrec.const kind)
  have hstructural : Primrec
      (fun input : CompactCertificateTask × List Nat ×
          List CompactCertificateTask =>
        compactStructuralCertificateNodeTokenStep input.2.1 input.2.2) :=
    compactStructuralCertificateNodeTokenStep_primrec.comp htokens htasks
  have haxiom : Primrec
      (fun input : CompactCertificateTask × List Nat ×
          List CompactCertificateTask =>
        compactCertificateAxiomTokenStep input.2.1 input.2.2) :=
    compactCertificateAxiomTokenStep_primrec.comp htokens htasks
  have hfailure : Primrec
      (fun input : CompactCertificateTask × List Nat ×
          List CompactCertificateTask =>
        compactSyntaxFailure input.2.1 input.2.2) :=
    compactSyntaxFailure_primrec.comp htokens htasks
  exact
    (Primrec.ite (hkindEq 8) hstructural
      (Primrec.ite (hkindEq 9) haxiom hfailure)).of_eq
      fun input => by
        simp only [compactCertificateTaskTokenStep]

theorem compactCertificateParserRunningStep_primrec :
    Primrec compactCertificateParserRunningStep := by
  have htokens : Primrec
      (fun state : CompactCertificateParserState => state.1) :=
    Primrec.fst
  have htasks : Primrec
      (fun state : CompactCertificateParserState => state.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hempty : PrimrecPred
      (fun state : CompactCertificateParserState => state.2.1 = []) :=
    Primrec.eq.comp htasks (Primrec.const [])
  have hsuccessStatus : Primrec
      (fun state : CompactCertificateParserState => some (some state.1)) :=
    Primrec.option_some.comp (Primrec.option_some.comp htokens)
  have hsuccess : Primrec
      (fun state : CompactCertificateParserState =>
        (state.1, [], some (some state.1))) :=
    Primrec.pair htokens
      (Primrec.pair (Primrec.const ([] : List CompactCertificateTask))
        hsuccessStatus)
  have hheadOption : Primrec
      (fun state : CompactCertificateParserState => state.2.1.head?) :=
    Primrec.list_head?.comp htasks
  have hhead : Primrec
      (fun state : CompactCertificateParserState =>
        state.2.1.head?.getD compactStructuralCertificateTask) :=
    Primrec.option_getD.comp hheadOption
      (Primrec.const compactStructuralCertificateTask)
  have htail : Primrec
      (fun state : CompactCertificateParserState => state.2.1.tail) :=
    Primrec.list_tail.comp htasks
  have hinput : Primrec
      (fun state : CompactCertificateParserState =>
        (state.2.1.head?.getD compactStructuralCertificateTask,
          state.1, state.2.1.tail)) :=
    Primrec.pair hhead (Primrec.pair htokens htail)
  have hbranch : Primrec
      (fun state : CompactCertificateParserState =>
        compactCertificateTaskTokenStep
          (state.2.1.head?.getD compactStructuralCertificateTask,
            state.1, state.2.1.tail)) :=
    compactCertificateTaskTokenStep_primrec.comp hinput
  exact
    (Primrec.ite hempty hsuccess hbranch).of_eq fun state => by
      cases htasksValue : state.2.1 <;>
        simp [compactCertificateParserRunningStep, htasksValue]

theorem compactCertificateParserStep_primrec :
    Primrec compactCertificateParserStep := by
  have hstatus : Primrec
      (fun state : CompactCertificateParserState => state.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hdone : Primrec
      (fun state : CompactCertificateParserState => state.2.2.isSome) :=
    Primrec.option_isSome.comp hstatus
  exact
    (Primrec.cond hdone Primrec.id
      compactCertificateParserRunningStep_primrec).of_eq fun state => by
        cases hstatusValue : state.2.2 <;>
          simp [compactCertificateParserStep, hstatusValue]

theorem compactCertificateParserFuelBound_primrec :
    Primrec compactCertificateParserFuelBound := by
  have hsize : Primrec (fun tokens : List Nat => tokens.length + 1) :=
    Primrec.succ.comp Primrec.list_length
  have hsquare : Primrec
      (fun tokens : List Nat =>
        (tokens.length + 1) * (tokens.length + 1)) :=
    Primrec.nat_mul.comp hsize hsize
  have hscaled : Primrec
      (fun tokens : List Nat =>
        16 * ((tokens.length + 1) * (tokens.length + 1))) :=
    Primrec.nat_mul.comp (Primrec.const 16) hsquare
  exact
    (Primrec.nat_add.comp hscaled (Primrec.const 8)).of_eq
      fun tokens => by
        simp [compactCertificateParserFuelBound, Nat.mul_assoc]

theorem compactCertificateParserInitialState_primrec :
    Primrec compactCertificateParserInitialState := by
  exact
    (Primrec.pair Primrec.id
      (Primrec.pair
        (Primrec.const
          ([compactStructuralCertificateTask] : List CompactCertificateTask))
        (Primrec.const (none : Option (Option (List Nat)))))).of_eq
      fun tokens => by rfl

theorem compactStructuralCertificateTokenParserRun_primrec :
    Primrec compactStructuralCertificateTokenParserRun := by
  have hstep : Primrec₂
      (fun (_tokens : List Nat) (state : CompactCertificateParserState) =>
        compactCertificateParserStep state) :=
    (compactCertificateParserStep_primrec.comp Primrec.snd).to₂
  exact
    (Primrec.nat_iterate compactCertificateParserFuelBound_primrec
      compactCertificateParserInitialState_primrec hstep).of_eq
      fun tokens => by rfl

theorem compactStructuralCertificateTokenParser_primrec :
    Primrec compactStructuralCertificateTokenParser := by
  exact
    (compactSyntaxParserStateOutput_primrec.comp
      compactStructuralCertificateTokenParserRun_primrec).of_eq
      fun tokens => by rfl

#print axioms compactPAAxiomCertificateTokenParser_primrec
#print axioms compactPAAxiomCertificateTokenParser_canonical_append
#print axioms compactStructuralCertificateNodeTokenStep_primrec
#print axioms compactCertificateParserStep_primrec
#print axioms compactStructuralCertificateTokenParser_primrec
#print axioms compactStructuralCertificateTask_execute
#print axioms compactStructuralCertificateTokenParser_canonical_append

end FoundationCompactCertificateTokenMachine
