import integration.FoundationCompactNumericListedNodeFields

/-!
# Pure numeric synchronized task machine for listed proofs

The machine consumes proof and structural-certificate token streams together.
Node parsers expose immediate fields; a finite task stack schedules children;
the local rule functions combine child conclusions and Boolean results.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedTaskMachine

open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedNodeFields
open FoundationCompactListedProofDecoder
open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericFixedPAAxiomSentence

abbrev CompactNumericVerifierTask := Nat × CompactNumericNodeFields

abbrev CompactNumericRunningPayload :=
  (List Nat × List Nat) ×
    (List CompactNumericVerifierTask × List CompactNumericChildResult)

abbrev CompactNumericVerifierState :=
  CompactNumericRunningPayload × Option Bool

def compactNumericEmptyNodeFields : CompactNumericNodeFields :=
  ([], ([], ([], ([], []))))

def compactNumericParseTask : CompactNumericVerifierTask :=
  (10, compactNumericEmptyNodeFields)

def compactNumericCombineTask
    (tag : Nat) (fields : CompactNumericNodeFields) :
    CompactNumericVerifierTask :=
  (tag, fields)

def compactNumericNodeTransition
    (proofNode : Nat × CompactNumericNodeFields)
    (certificateNode : CompactNumericCertificateNode)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    Option CompactNumericRunningPayload :=
  let proofTag := proofNode.1
  let fields := proofNode.2
  let certificateTag := certificateNode.1
  let axiomTokens := certificateNode.2.1
  let proofSuffix := compactNumericNodeFieldsSuffix fields
  let certificateSuffix := certificateNode.2.2
  let Gamma := fields.1
  let firstFormula := fields.2.1
  let secondFormula := fields.2.2.1
  let witness := fields.2.2.2.1
  if proofTag = 0 then
    if certificateTag = 0 then
      some ((proofSuffix, certificateSuffix),
        (restTasks,
          (Gamma, compactClosedRuleCheck (Gamma, firstFormula)) :: values))
    else none
  else if proofTag = 1 then
    if certificateTag = 1 then
      some ((proofSuffix, certificateSuffix),
        (restTasks,
          (Gamma, compactAxmRuleCheck
            (Gamma, (firstFormula, axiomTokens))) :: values))
    else none
  else if proofTag = 2 then
    if certificateTag = 0 then
      some ((proofSuffix, certificateSuffix),
        (restTasks,
          (Gamma, compactVerumRuleCheck Gamma) :: values))
    else none
  else if proofTag = 3 then
    if certificateTag = 3 then
      some ((proofSuffix, certificateSuffix),
        (compactNumericParseTask :: compactNumericParseTask ::
          compactNumericCombineTask 3 fields :: restTasks, values))
    else none
  else if proofTag = 4 then
    if certificateTag = 2 then
      some ((proofSuffix, certificateSuffix),
        (compactNumericParseTask ::
          compactNumericCombineTask 4 fields :: restTasks, values))
    else none
  else if proofTag = 5 then
    if certificateTag = 2 then
      some ((proofSuffix, certificateSuffix),
        (compactNumericParseTask ::
          compactNumericCombineTask 5 fields :: restTasks, values))
    else none
  else if proofTag = 6 then
    if certificateTag = 2 then
      some ((proofSuffix, certificateSuffix),
        (compactNumericParseTask ::
          compactNumericCombineTask 6 fields :: restTasks, values))
    else none
  else if proofTag = 7 then
    if certificateTag = 2 then
      some ((proofSuffix, certificateSuffix),
        (compactNumericParseTask ::
          compactNumericCombineTask 7 fields :: restTasks, values))
    else none
  else if proofTag = 8 then
    if certificateTag = 2 then
      some ((proofSuffix, certificateSuffix),
        (compactNumericParseTask ::
          compactNumericCombineTask 8 fields :: restTasks, values))
    else none
  else if proofTag = 9 then
    if certificateTag = 3 then
      some ((proofSuffix, certificateSuffix),
        (compactNumericParseTask :: compactNumericParseTask ::
          compactNumericCombineTask 9 fields :: restTasks, values))
    else none
  else
    none

theorem compactNumericNodeTransition_primrec :
    Primrec
      (fun input :
          (Nat × CompactNumericNodeFields) ×
            (CompactNumericCertificateNode ×
              (List CompactNumericVerifierTask ×
                List CompactNumericChildResult)) =>
        compactNumericNodeTransition input.1 input.2.1
          input.2.2.1 input.2.2.2) := by
  let Input :=
    (Nat × CompactNumericNodeFields) ×
      (CompactNumericCertificateNode ×
        (List CompactNumericVerifierTask ×
          List CompactNumericChildResult))
  have hproofNode : Primrec (fun input : Input => input.1) :=
    Primrec.fst
  have hfields : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hproofTag : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hcertificateNode : Primrec (fun input : Input => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hcertificateTag : Primrec (fun input : Input => input.2.1.1) :=
    Primrec.fst.comp hcertificateNode
  have haxiomTokens : Primrec (fun input : Input => input.2.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp hcertificateNode)
  have hcertificateSuffix : Primrec
      (fun input : Input => input.2.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp hcertificateNode)
  have hrestTasks : Primrec (fun input : Input => input.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hvalues : Primrec (fun input : Input => input.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hproofSuffix : Primrec (fun input : Input =>
      compactNumericNodeFieldsSuffix input.1.2) :=
    Primrec.snd.comp
      (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp hfields)))
  have hGamma : Primrec (fun input : Input => input.1.2.1) :=
    Primrec.fst.comp hfields
  have hfirstFormula : Primrec (fun input : Input => input.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp hfields)
  have hstreamPair : Primrec (fun input : Input =>
      (compactNumericNodeFieldsSuffix input.1.2,
        input.2.1.2.2)) :=
    Primrec.pair hproofSuffix hcertificateSuffix
  have hproofTagEq (tag : Nat) : PrimrecPred (fun input : Input =>
      input.1.1 = tag) :=
    Primrec.eq.comp hproofTag (Primrec.const tag)
  have hcertificateTagEq (tag : Nat) :
      PrimrecPred (fun input : Input => input.2.1.1 = tag) :=
    Primrec.eq.comp hcertificateTag (Primrec.const tag)
  have hclosedCheck : Primrec (fun input : Input =>
      compactClosedRuleCheck (input.1.2.1, input.1.2.2.1)) :=
    compactClosedRuleCheck_primrec.comp
      (Primrec.pair hGamma hfirstFormula)
  have haxmInput : Primrec (fun input : Input =>
      (input.1.2.1, (input.1.2.2.1, input.2.1.2.1))) :=
    Primrec.pair hGamma (Primrec.pair hfirstFormula haxiomTokens)
  have haxmCheck : Primrec (fun input : Input =>
      compactAxmRuleCheck
        (input.1.2.1, (input.1.2.2.1, input.2.1.2.1))) :=
    compactAxmRuleCheck_primrec.comp haxmInput
  have hverumCheck : Primrec (fun input : Input =>
      compactVerumRuleCheck input.1.2.1) :=
    compactVerumRuleCheck_primrec.comp hGamma
  have hleafPayload (check : Input -> Bool)
      (hcheck : Primrec check) : Primrec (fun input : Input =>
      some ((compactNumericNodeFieldsSuffix input.1.2,
          input.2.1.2.2),
        (input.2.2.1,
          (input.1.2.1, check input) :: input.2.2.2))) := by
    have hchild : Primrec (fun input : Input =>
        (input.1.2.1, check input)) :=
      Primrec.pair hGamma hcheck
    have hnewValues : Primrec (fun input : Input =>
        (input.1.2.1, check input) :: input.2.2.2) :=
      Primrec.list_cons.comp hchild hvalues
    exact Primrec.option_some.comp
      (Primrec.pair hstreamPair
        (Primrec.pair hrestTasks hnewValues))
  have hclosedPayload : Primrec (fun input : Input =>
      some ((compactNumericNodeFieldsSuffix input.1.2,
          input.2.1.2.2),
        (input.2.2.1,
          (input.1.2.1, compactClosedRuleCheck
            (input.1.2.1, input.1.2.2.1)) :: input.2.2.2))) :=
    hleafPayload _ hclosedCheck
  have haxmPayload : Primrec (fun input : Input =>
      some ((compactNumericNodeFieldsSuffix input.1.2,
          input.2.1.2.2),
        (input.2.2.1,
          (input.1.2.1, compactAxmRuleCheck
            (input.1.2.1,
              (input.1.2.2.1, input.2.1.2.1))) :: input.2.2.2))) :=
    hleafPayload _ haxmCheck
  have hverumPayload : Primrec (fun input : Input =>
      some ((compactNumericNodeFieldsSuffix input.1.2,
          input.2.1.2.2),
        (input.2.2.1,
          (input.1.2.1, compactVerumRuleCheck
            input.1.2.1) :: input.2.2.2))) :=
    hleafPayload _ hverumCheck
  have hcombineTask (tag : Nat) : Primrec (fun input : Input =>
      compactNumericCombineTask tag input.1.2) :=
    Primrec.pair (Primrec.const tag) hfields
  have hunaryTasks (tag : Nat) : Primrec (fun input : Input =>
      compactNumericParseTask :: compactNumericCombineTask tag input.1.2 ::
        input.2.2.1) :=
    Primrec.list_cons.comp (Primrec.const compactNumericParseTask)
      (Primrec.list_cons.comp (hcombineTask tag) hrestTasks)
  have hbinaryTasks (tag : Nat) : Primrec (fun input : Input =>
      compactNumericParseTask :: compactNumericParseTask ::
        compactNumericCombineTask tag input.1.2 :: input.2.2.1) :=
    Primrec.list_cons.comp (Primrec.const compactNumericParseTask)
      (Primrec.list_cons.comp (Primrec.const compactNumericParseTask)
        (Primrec.list_cons.comp (hcombineTask tag) hrestTasks))
  have hschedule (tasks : Input -> List CompactNumericVerifierTask)
      (htasks : Primrec tasks) : Primrec (fun input : Input =>
      some ((compactNumericNodeFieldsSuffix input.1.2,
          input.2.1.2.2),
        (tasks input, input.2.2.2))) :=
    Primrec.option_some.comp
      (Primrec.pair hstreamPair (Primrec.pair htasks hvalues))
  have hunaryPayload (tag : Nat) : Primrec (fun input : Input =>
      some ((compactNumericNodeFieldsSuffix input.1.2,
          input.2.1.2.2),
        (compactNumericParseTask :: compactNumericCombineTask tag
            input.1.2 :: input.2.2.1,
          input.2.2.2))) :=
    hschedule _ (hunaryTasks tag)
  have hbinaryPayload (tag : Nat) : Primrec (fun input : Input =>
      some ((compactNumericNodeFieldsSuffix input.1.2,
          input.2.1.2.2),
        (compactNumericParseTask :: compactNumericParseTask ::
            compactNumericCombineTask tag input.1.2 :: input.2.2.1,
          input.2.2.2))) :=
    hschedule _ (hbinaryTasks tag)
  have hnone : Primrec (fun _input : Input =>
      (none : Option CompactNumericRunningPayload)) :=
    Primrec.const none
  exact
    (Primrec.ite (hproofTagEq 0)
      (Primrec.ite (hcertificateTagEq 0) hclosedPayload hnone)
      (Primrec.ite (hproofTagEq 1)
        (Primrec.ite (hcertificateTagEq 1) haxmPayload hnone)
        (Primrec.ite (hproofTagEq 2)
          (Primrec.ite (hcertificateTagEq 0) hverumPayload hnone)
          (Primrec.ite (hproofTagEq 3)
            (Primrec.ite (hcertificateTagEq 3)
              (hbinaryPayload 3) hnone)
            (Primrec.ite (hproofTagEq 4)
              (Primrec.ite (hcertificateTagEq 2)
                (hunaryPayload 4) hnone)
              (Primrec.ite (hproofTagEq 5)
                (Primrec.ite (hcertificateTagEq 2)
                  (hunaryPayload 5) hnone)
                (Primrec.ite (hproofTagEq 6)
                  (Primrec.ite (hcertificateTagEq 2)
                    (hunaryPayload 6) hnone)
                  (Primrec.ite (hproofTagEq 7)
                    (Primrec.ite (hcertificateTagEq 2)
                      (hunaryPayload 7) hnone)
                    (Primrec.ite (hproofTagEq 8)
                      (Primrec.ite (hcertificateTagEq 2)
                        (hunaryPayload 8) hnone)
                      (Primrec.ite (hproofTagEq 9)
                        (Primrec.ite (hcertificateTagEq 3)
                          (hbinaryPayload 9) hnone)
                        hnone)))))))))).of_eq fun input => by
      simp [compactNumericNodeTransition]

def compactNumericDefaultChildResult : CompactNumericChildResult :=
  ([], false)

def compactNumericCombineTransition
    (task : CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    Option (CompactNumericChildResult × List CompactNumericChildResult) :=
  let tag := task.1
  let fields := task.2
  let Gamma := fields.1
  let firstFormula := fields.2.1
  let secondFormula := fields.2.2.1
  let witness := fields.2.2.2.1
  if tag = 3 then
    if 2 <= values.length then
      let right := values.head?.getD compactNumericDefaultChildResult
      let left := values.tail.head?.getD compactNumericDefaultChildResult
      some ((Gamma, compactAndRuleCheck
        (Gamma, (firstFormula, (secondFormula, (left, right))))),
        values.drop 2)
    else none
  else if tag = 4 then
    if 1 <= values.length then
      let premise := values.head?.getD compactNumericDefaultChildResult
      some ((Gamma, compactOrRuleCheck
        (Gamma, (firstFormula, (secondFormula, premise)))), values.tail)
    else none
  else if tag = 5 then
    if 1 <= values.length then
      let premise := values.head?.getD compactNumericDefaultChildResult
      some ((Gamma, compactAllRuleCheck
        (Gamma, (firstFormula, premise))), values.tail)
    else none
  else if tag = 6 then
    if 1 <= values.length then
      let premise := values.head?.getD compactNumericDefaultChildResult
      some ((Gamma, compactExsRuleCheck
        (Gamma, (firstFormula, (witness, premise)))), values.tail)
    else none
  else if tag = 7 then
    if 1 <= values.length then
      let premise := values.head?.getD compactNumericDefaultChildResult
      some ((Gamma, compactWkRuleCheck (Gamma, premise)), values.tail)
    else none
  else if tag = 8 then
    if 1 <= values.length then
      let premise := values.head?.getD compactNumericDefaultChildResult
      some ((Gamma, compactShiftRuleCheck (Gamma, premise)), values.tail)
    else none
  else if tag = 9 then
    if 2 <= values.length then
      let right := values.head?.getD compactNumericDefaultChildResult
      let left := values.tail.head?.getD compactNumericDefaultChildResult
      some ((Gamma, compactCutRuleCheck
        (Gamma, (firstFormula, (left, right)))), values.drop 2)
    else none
  else none

theorem compactNumericCombineTransition_primrec :
    Primrec₂ compactNumericCombineTransition := by
  apply Primrec₂.mk
  let Input := CompactNumericVerifierTask ×
    List CompactNumericChildResult
  have htask : Primrec (fun input : Input => input.1) :=
    Primrec.fst
  have htag : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hfields : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hGamma : Primrec (fun input : Input => input.1.2.1) :=
    Primrec.fst.comp hfields
  have hfirstFormula : Primrec (fun input : Input => input.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp hfields)
  have hsecondFormula : Primrec (fun input : Input => input.1.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hfields))
  have hwitness : Primrec (fun input : Input => input.1.2.2.2.2.1) :=
    Primrec.fst.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hfields)))
  have hvalues : Primrec (fun input : Input => input.2) :=
    Primrec.snd
  have hvalueLength : Primrec (fun input : Input => input.2.length) :=
    Primrec.list_length.comp hvalues
  have hhasOne : PrimrecPred (fun input : Input => 1 <= input.2.length) :=
    Primrec.nat_le.comp (Primrec.const 1) hvalueLength
  have hhasTwo : PrimrecPred (fun input : Input => 2 <= input.2.length) :=
    Primrec.nat_le.comp (Primrec.const 2) hvalueLength
  have hrightOption : Primrec (fun input : Input => input.2.head?) :=
    Primrec.list_head?.comp hvalues
  have hright : Primrec (fun input : Input =>
      input.2.head?.getD compactNumericDefaultChildResult) :=
    Primrec.option_getD.comp hrightOption
      (Primrec.const compactNumericDefaultChildResult)
  have hvalueTail : Primrec (fun input : Input => input.2.tail) :=
    Primrec.list_tail.comp hvalues
  have hleftOption : Primrec (fun input : Input => input.2.tail.head?) :=
    Primrec.list_head?.comp hvalueTail
  have hleft : Primrec (fun input : Input =>
      input.2.tail.head?.getD compactNumericDefaultChildResult) :=
    Primrec.option_getD.comp hleftOption
      (Primrec.const compactNumericDefaultChildResult)
  have hdropTwo : Primrec (fun input : Input => input.2.drop 2) :=
    Primrec.list_drop.comp (Primrec.const 2) hvalues
  have htagEq (tag : Nat) : PrimrecPred (fun input : Input =>
      input.1.1 = tag) :=
    Primrec.eq.comp htag (Primrec.const tag)
  have hnone : Primrec (fun _input : Input =>
      (none : Option
        (CompactNumericChildResult × List CompactNumericChildResult))) :=
    Primrec.const none
  have hbinaryResult
      (check : Input -> Bool) (hcheck : Primrec check) :
      Primrec (fun input : Input =>
        some ((input.1.2.1, check input), input.2.drop 2)) := by
    have hchild : Primrec (fun input : Input =>
        (input.1.2.1, check input)) :=
      Primrec.pair hGamma hcheck
    exact Primrec.option_some.comp
      (Primrec.pair hchild hdropTwo)
  have hunaryResult
      (check : Input -> Bool) (hcheck : Primrec check) :
      Primrec (fun input : Input =>
        some ((input.1.2.1, check input), input.2.tail)) := by
    have hchild : Primrec (fun input : Input =>
        (input.1.2.1, check input)) :=
      Primrec.pair hGamma hcheck
    exact Primrec.option_some.comp
      (Primrec.pair hchild hvalueTail)
  have handInput : Primrec (fun input : Input =>
      (input.1.2.1,
        (input.1.2.2.1, (input.1.2.2.2.1,
          (input.2.tail.head?.getD compactNumericDefaultChildResult,
            input.2.head?.getD compactNumericDefaultChildResult))))) :=
    Primrec.pair hGamma
      (Primrec.pair hfirstFormula
        (Primrec.pair hsecondFormula (Primrec.pair hleft hright)))
  have handCheck : Primrec (fun input : Input =>
      compactAndRuleCheck
        (input.1.2.1,
          (input.1.2.2.1, (input.1.2.2.2.1,
            (input.2.tail.head?.getD compactNumericDefaultChildResult,
              input.2.head?.getD compactNumericDefaultChildResult))))) :=
    compactAndRuleCheck_primrec.comp handInput
  have horInput : Primrec (fun input : Input =>
      (input.1.2.1,
        (input.1.2.2.1, (input.1.2.2.2.1,
          input.2.head?.getD compactNumericDefaultChildResult)))) :=
    Primrec.pair hGamma
      (Primrec.pair hfirstFormula (Primrec.pair hsecondFormula hright))
  have horCheck : Primrec (fun input : Input =>
      compactOrRuleCheck
        (input.1.2.1,
          (input.1.2.2.1, (input.1.2.2.2.1,
            input.2.head?.getD compactNumericDefaultChildResult)))) :=
    compactOrRuleCheck_primrec.comp horInput
  have hallInput : Primrec (fun input : Input =>
      (input.1.2.1,
        (input.1.2.2.1,
          input.2.head?.getD compactNumericDefaultChildResult))) :=
    Primrec.pair hGamma (Primrec.pair hfirstFormula hright)
  have hallCheck : Primrec (fun input : Input =>
      compactAllRuleCheck
        (input.1.2.1,
          (input.1.2.2.1,
            input.2.head?.getD compactNumericDefaultChildResult))) :=
    compactAllRuleCheck_primrec.comp hallInput
  have hexsInput : Primrec (fun input : Input =>
      (input.1.2.1,
        (input.1.2.2.1, (input.1.2.2.2.2.1,
          input.2.head?.getD compactNumericDefaultChildResult)))) :=
    Primrec.pair hGamma
      (Primrec.pair hfirstFormula (Primrec.pair hwitness hright))
  have hexsCheck : Primrec (fun input : Input =>
      compactExsRuleCheck
        (input.1.2.1,
          (input.1.2.2.1, (input.1.2.2.2.2.1,
            input.2.head?.getD compactNumericDefaultChildResult)))) :=
    compactExsRuleCheck_primrec.comp hexsInput
  have hwkInput : Primrec (fun input : Input =>
      (input.1.2.1,
        input.2.head?.getD compactNumericDefaultChildResult)) :=
    Primrec.pair hGamma hright
  have hwkCheck : Primrec (fun input : Input =>
      compactWkRuleCheck
        (input.1.2.1,
          input.2.head?.getD compactNumericDefaultChildResult)) :=
    compactWkRuleCheck_primrec.comp hwkInput
  have hshiftCheck : Primrec (fun input : Input =>
      compactShiftRuleCheck
        (input.1.2.1,
          input.2.head?.getD compactNumericDefaultChildResult)) :=
    compactShiftRuleCheck_primrec.comp hwkInput
  have hcutInput : Primrec (fun input : Input =>
      (input.1.2.1, (input.1.2.2.1,
        (input.2.tail.head?.getD compactNumericDefaultChildResult,
          input.2.head?.getD compactNumericDefaultChildResult)))) :=
    Primrec.pair hGamma
      (Primrec.pair hfirstFormula (Primrec.pair hleft hright))
  have hcutCheck : Primrec (fun input : Input =>
      compactCutRuleCheck
        (input.1.2.1, (input.1.2.2.1,
          (input.2.tail.head?.getD compactNumericDefaultChildResult,
            input.2.head?.getD compactNumericDefaultChildResult)))) :=
    compactCutRuleCheck_primrec.comp hcutInput
  have handResult := hbinaryResult _ handCheck
  have horResult := hunaryResult _ horCheck
  have hallResult := hunaryResult _ hallCheck
  have hexsResult := hunaryResult _ hexsCheck
  have hwkResult := hunaryResult _ hwkCheck
  have hshiftResult := hunaryResult _ hshiftCheck
  have hcutResult := hbinaryResult _ hcutCheck
  exact
    (Primrec.ite (htagEq 3)
      (Primrec.ite hhasTwo handResult hnone)
      (Primrec.ite (htagEq 4)
        (Primrec.ite hhasOne horResult hnone)
        (Primrec.ite (htagEq 5)
          (Primrec.ite hhasOne hallResult hnone)
          (Primrec.ite (htagEq 6)
            (Primrec.ite hhasOne hexsResult hnone)
            (Primrec.ite (htagEq 7)
              (Primrec.ite hhasOne hwkResult hnone)
              (Primrec.ite (htagEq 8)
                (Primrec.ite hhasOne hshiftResult hnone)
                (Primrec.ite (htagEq 9)
                  (Primrec.ite hhasTwo hcutResult hnone)
                  hnone))))))).of_eq fun input => by
      simp [compactNumericCombineTransition]

def compactNumericParsePayload
    (payload : CompactNumericRunningPayload) :
    Option CompactNumericRunningPayload := do
  let proofNode <- compactListedProofNodeFieldsParser payload.1.1
  let certificateNode <-
    compactStructuralCertificateNodeParser payload.1.2
  compactNumericNodeTransition proofNode certificateNode
    payload.2.1 payload.2.2

theorem compactNumericParsePayload_primrec :
    Primrec compactNumericParsePayload := by
  have hproofParser : Primrec
      (fun payload : CompactNumericRunningPayload =>
        compactListedProofNodeFieldsParser payload.1.1) :=
    compactListedProofNodeFieldsParser_primrec.comp
      (Primrec.fst.comp Primrec.fst)
  have hcertificateThenTransition : Primrec₂
      (fun (payload : CompactNumericRunningPayload)
          (proofNode : Nat × CompactNumericNodeFields) =>
        (compactStructuralCertificateNodeParser payload.1.2).bind
          fun certificateNode =>
            compactNumericNodeTransition proofNode certificateNode
              payload.2.1 payload.2.2) := by
    apply Primrec₂.mk
    let State := CompactNumericRunningPayload ×
      (Nat × CompactNumericNodeFields)
    have hcertificateParser : Primrec (fun state : State =>
        compactStructuralCertificateNodeParser state.1.1.2) :=
      compactStructuralCertificateNodeParser_primrec.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have htransitionInput : Primrec₂
        (fun (state : State)
            (certificateNode : CompactNumericCertificateNode) =>
          (state.2,
            (certificateNode, (state.1.2.1, state.1.2.2)))) :=
      Primrec₂.pair.comp₂
        ((Primrec.snd.comp Primrec.fst).to₂)
        (Primrec₂.pair.comp₂ Primrec₂.right
          (Primrec₂.pair.comp₂
            ((Primrec.fst.comp
              (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).to₂)
            ((Primrec.snd.comp
              (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).to₂)))
    have htransition : Primrec₂
        (fun (state : State)
            (certificateNode : CompactNumericCertificateNode) =>
          compactNumericNodeTransition state.2 certificateNode
            state.1.2.1 state.1.2.2) :=
      compactNumericNodeTransition_primrec.comp₂ htransitionInput
    exact Primrec.option_bind hcertificateParser htransition
  exact
    (Primrec.option_bind hproofParser
      hcertificateThenTransition).of_eq fun payload => by
        simp [compactNumericParsePayload]

def compactNumericParseState
    (payload : CompactNumericRunningPayload) :
    CompactNumericVerifierState :=
  match compactNumericParsePayload payload with
  | none => (payload, some false)
  | some next => (next, none)

theorem compactNumericParseState_primrec :
    Primrec compactNumericParseState := by
  have hfailure : Primrec (fun payload : CompactNumericRunningPayload =>
      (payload, some false)) :=
    Primrec.pair Primrec.id (Primrec.const (some false))
  have hsuccess : Primrec₂
      (fun (_payload : CompactNumericRunningPayload)
          (next : CompactNumericRunningPayload) =>
        (next, (none : Option Bool))) :=
    Primrec₂.pair.comp₂ Primrec₂.right
      (Primrec₂.const (none : Option Bool))
  exact
    (Primrec.option_casesOn compactNumericParsePayload_primrec
      hfailure hsuccess).of_eq fun payload => by
        cases hresult : compactNumericParsePayload payload <;>
          simp [compactNumericParseState, hresult]

def compactNumericCombineState
    (task : CompactNumericVerifierTask)
    (payload : CompactNumericRunningPayload) :
    CompactNumericVerifierState :=
  match compactNumericCombineTransition task payload.2.2 with
  | none => (payload, some false)
  | some combined =>
      ((payload.1, (payload.2.1, combined.1 :: combined.2)), none)

theorem compactNumericCombineState_primrec :
    Primrec₂ compactNumericCombineState := by
  apply Primrec₂.mk
  let Input := CompactNumericVerifierTask × CompactNumericRunningPayload
  have htransition : Primrec (fun input : Input =>
      compactNumericCombineTransition input.1 input.2.2.2) :=
    compactNumericCombineTransition_primrec.comp
      Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hfailure : Primrec (fun input : Input =>
      (input.2, some false)) :=
    Primrec.pair Primrec.snd (Primrec.const (some false))
  have hsuccess : Primrec₂
      (fun (input : Input)
          (combined : CompactNumericChildResult ×
            List CompactNumericChildResult) =>
        ((input.2.1,
          (input.2.2.1, combined.1 :: combined.2)),
          (none : Option Bool))) := by
    let Combined := CompactNumericChildResult ×
      List CompactNumericChildResult
    let PairInput := Input × Combined
    have hstreams : Primrec (fun pair : PairInput => pair.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have htasks : Primrec (fun pair : PairInput => pair.1.2.2.1) :=
      Primrec.fst.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    have hvalues : Primrec (fun pair : PairInput =>
        pair.2.1 :: pair.2.2) :=
      Primrec.list_cons.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)
    have hpayload : Primrec (fun pair : PairInput =>
        (pair.1.2.1, (pair.1.2.2.1, pair.2.1 :: pair.2.2))) :=
      Primrec.pair hstreams (Primrec.pair htasks hvalues)
    exact Primrec₂.mk <|
      Primrec.pair hpayload (Primrec.const (none : Option Bool))
  exact
    (Primrec.option_casesOn htransition hfailure hsuccess).of_eq
      fun input => by
        cases hresult : compactNumericCombineTransition
            input.1 input.2.2.2 <;>
          simp [compactNumericCombineState, hresult]

def compactNumericFinishState
    (payload : CompactNumericRunningPayload) :
    CompactNumericVerifierState :=
  if payload.1.1 = [] ∧ payload.1.2 = [] ∧
      payload.2.1 = [] ∧ payload.2.2.length = 1 then
    (payload, some
      (payload.2.2.head?.getD compactNumericDefaultChildResult).2)
  else
    (payload, some false)

theorem compactNumericFinishState_primrec :
    Primrec compactNumericFinishState := by
  let Input := CompactNumericRunningPayload
  have hproofEmpty : PrimrecPred (fun input : Input => input.1.1 = []) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.const [])
  have hcertificateEmpty : PrimrecPred
      (fun input : Input => input.1.2 = []) :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.const [])
  have htasksEmpty : PrimrecPred (fun input : Input => input.2.1 = []) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.const [])
  have hvalueLength : Primrec (fun input : Input => input.2.2.length) :=
    Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)
  have honeValue : PrimrecPred
      (fun input : Input => input.2.2.length = 1) :=
    Primrec.eq.comp hvalueLength (Primrec.const 1)
  have hguard : PrimrecPred (fun input : Input =>
      input.1.1 = [] ∧ input.1.2 = [] ∧
        input.2.1 = [] ∧ input.2.2.length = 1) :=
    hproofEmpty.and
      (hcertificateEmpty.and (htasksEmpty.and honeValue))
  have hheadOption : Primrec (fun input : Input => input.2.2.head?) :=
    Primrec.list_head?.comp (Primrec.snd.comp Primrec.snd)
  have hhead : Primrec (fun input : Input =>
      input.2.2.head?.getD compactNumericDefaultChildResult) :=
    Primrec.option_getD.comp hheadOption
      (Primrec.const compactNumericDefaultChildResult)
  have hresult : Primrec (fun input : Input =>
      (input.2.2.head?.getD compactNumericDefaultChildResult).2) :=
    Primrec.snd.comp hhead
  have hsuccess : Primrec (fun input : Input =>
      (input, some
        (input.2.2.head?.getD compactNumericDefaultChildResult).2)) :=
    Primrec.pair Primrec.id (Primrec.option_some.comp hresult)
  have hfailure : Primrec (fun input : Input =>
      (input, some false)) :=
    Primrec.pair Primrec.id (Primrec.const (some false))
  exact
    (Primrec.ite hguard hsuccess hfailure).of_eq fun input => by
      simp [compactNumericFinishState]

def compactNumericRunningStep
    (payload : CompactNumericRunningPayload) :
    CompactNumericVerifierState :=
  match payload.2.1 with
  | [] => compactNumericFinishState payload
  | task :: restTasks =>
      let restPayload := (payload.1, (restTasks, payload.2.2))
      if task.1 = 10 then
        compactNumericParseState restPayload
      else
        compactNumericCombineState task restPayload

theorem compactNumericRunningStep_primrec :
    Primrec compactNumericRunningStep := by
  let Input := CompactNumericRunningPayload
  have htasks : Primrec (fun input : Input => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have htaskOption : Primrec (fun input : Input => input.2.1.head?) :=
    Primrec.list_head?.comp htasks
  have htask : Primrec (fun input : Input =>
      input.2.1.head?.getD compactNumericParseTask) :=
    Primrec.option_getD.comp htaskOption
      (Primrec.const compactNumericParseTask)
  have hrestTasks : Primrec (fun input : Input => input.2.1.tail) :=
    Primrec.list_tail.comp htasks
  have hrestPayload : Primrec (fun input : Input =>
      (input.1, (input.2.1.tail, input.2.2))) :=
    Primrec.pair Primrec.fst
      (Primrec.pair hrestTasks (Primrec.snd.comp Primrec.snd))
  have hparseTag : PrimrecPred (fun input : Input =>
      (input.2.1.head?.getD compactNumericParseTask).1 = 10) :=
    Primrec.eq.comp (Primrec.fst.comp htask) (Primrec.const 10)
  have hparse : Primrec (fun input : Input =>
      compactNumericParseState
        (input.1, (input.2.1.tail, input.2.2))) :=
    compactNumericParseState_primrec.comp hrestPayload
  have hcombine : Primrec (fun input : Input =>
      compactNumericCombineState
        (input.2.1.head?.getD compactNumericParseTask)
        (input.1, (input.2.1.tail, input.2.2))) :=
    compactNumericCombineState_primrec.comp htask hrestPayload
  have hnonempty : Primrec (fun input : Input =>
      if (input.2.1.head?.getD compactNumericParseTask).1 = 10 then
        compactNumericParseState
          (input.1, (input.2.1.tail, input.2.2))
      else
        compactNumericCombineState
          (input.2.1.head?.getD compactNumericParseTask)
          (input.1, (input.2.1.tail, input.2.2))) :=
    Primrec.ite hparseTag hparse hcombine
  have hempty : PrimrecPred (fun input : Input => input.2.1 = []) :=
    Primrec.eq.comp htasks (Primrec.const [])
  exact
    (Primrec.ite hempty compactNumericFinishState_primrec hnonempty).of_eq
      fun input => by
        cases htasksValue : input.2.1 <;>
          simp [compactNumericRunningStep, htasksValue]

def compactNumericVerifierStep
    (state : CompactNumericVerifierState) :
    CompactNumericVerifierState :=
  if state.2.isSome then state
  else compactNumericRunningStep state.1

theorem compactNumericVerifierStep_primrec :
    Primrec compactNumericVerifierStep := by
  have hhalted : Primrec (fun state : CompactNumericVerifierState =>
      state.2.isSome) :=
    Primrec.option_isSome.comp Primrec.snd
  have hrunning : Primrec (fun state : CompactNumericVerifierState =>
      compactNumericRunningStep state.1) :=
    compactNumericRunningStep_primrec.comp Primrec.fst
  exact
    (Primrec.cond hhalted Primrec.id hrunning).of_eq fun state => by
      cases hstatusValue : state.2 <;>
        simp [compactNumericVerifierStep, hstatusValue]

def compactNumericVerifierFuelBound
    (proofTokens certificateTokens : List Nat) : Nat :=
  4 * (proofTokens.length + certificateTokens.length + 1) + 8

def compactNumericVerifierInitialState
    (proofTokens certificateTokens : List Nat) :
    CompactNumericVerifierState :=
  (((proofTokens, certificateTokens),
      ([compactNumericParseTask], [])), none)

def compactNumericVerifierRun
    (proofTokens certificateTokens : List Nat) :
    CompactNumericVerifierState :=
  (compactNumericVerifierStep^[
      compactNumericVerifierFuelBound proofTokens certificateTokens])
    (compactNumericVerifierInitialState proofTokens certificateTokens)

def compactNumericVerifierResult
    (proofTokens certificateTokens : List Nat) : Bool :=
  (compactNumericVerifierRun proofTokens certificateTokens).2.getD false

theorem compactNumericVerifierFuelBound_primrec :
    Primrec₂ compactNumericVerifierFuelBound := by
  apply Primrec₂.mk
  let Input := List Nat × List Nat
  have hproofLength : Primrec (fun input : Input => input.1.length) :=
    Primrec.list_length.comp Primrec.fst
  have hcertificateLength : Primrec
      (fun input : Input => input.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have htotal : Primrec (fun input : Input =>
      input.1.length + input.2.length) :=
    Primrec.nat_add.comp hproofLength hcertificateLength
  have hsize : Primrec (fun input : Input =>
      input.1.length + input.2.length + 1) :=
    Primrec.succ.comp htotal
  have hscaled : Primrec (fun input : Input =>
      4 * (input.1.length + input.2.length + 1)) :=
    Primrec.nat_mul.comp (Primrec.const 4) hsize
  exact
    (Primrec.nat_add.comp hscaled (Primrec.const 8)).of_eq
      fun input => by simp [compactNumericVerifierFuelBound]

theorem compactNumericVerifierInitialState_primrec :
    Primrec₂ compactNumericVerifierInitialState := by
  apply Primrec₂.mk
  let Input := List Nat × List Nat
  have hstreams : Primrec (fun input : Input => (input.1, input.2)) :=
    Primrec.pair Primrec.fst Primrec.snd
  have hwork : Primrec (fun _input : Input =>
      ([compactNumericParseTask],
        ([] : List CompactNumericChildResult))) :=
    Primrec.const ([compactNumericParseTask],
      ([] : List CompactNumericChildResult))
  exact
    (Primrec.pair (Primrec.pair hstreams hwork)
      (Primrec.const (none : Option Bool))).of_eq fun input => by
        rfl

theorem compactNumericVerifierRun_primrec :
    Primrec₂ compactNumericVerifierRun := by
  apply Primrec₂.mk
  let Input := List Nat × List Nat
  have hstep : Primrec₂
      (fun (_input : Input) (state : CompactNumericVerifierState) =>
        compactNumericVerifierStep state) :=
    (compactNumericVerifierStep_primrec.comp Primrec.snd).to₂
  exact
    (Primrec.nat_iterate compactNumericVerifierFuelBound_primrec
      compactNumericVerifierInitialState_primrec hstep).of_eq
      fun input => by rfl

theorem compactNumericVerifierResult_primrec :
    Primrec₂ compactNumericVerifierResult := by
  have hstatus : Primrec₂
      (fun proofTokens certificateTokens =>
        (compactNumericVerifierRun proofTokens certificateTokens).2) :=
    Primrec.snd.comp₂ compactNumericVerifierRun_primrec
  exact
    (Primrec.option_getD.comp₂ hstatus (Primrec₂.const false)).of_eq
      fun _proofTokens _certificateTokens => by rfl

theorem compactNumericVerifierStep_halted
    (payload : CompactNumericRunningPayload) (result : Bool) :
    compactNumericVerifierStep (payload, some result) =
      (payload, some result) := by
  simp [compactNumericVerifierStep]

theorem compactNumericVerifierStep_iterate_halted
    (fuel : Nat) (payload : CompactNumericRunningPayload) (result : Bool) :
    (compactNumericVerifierStep^[fuel]) (payload, some result) =
      (payload, some result) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply,
        compactNumericVerifierStep_halted, ih]

theorem compactNumericVerifier_iterate_trans
    {start middle finish : CompactNumericVerifierState}
    {firstSteps secondSteps : Nat}
    (hfirst : (compactNumericVerifierStep^[firstSteps]) start = middle)
    (hsecond : (compactNumericVerifierStep^[secondSteps]) middle = finish) :
    (compactNumericVerifierStep^[firstSteps + secondSteps]) start = finish := by
  rw [Nat.add_comm, Function.iterate_add_apply, hfirst, hsecond]

theorem compactNumericVerifier_iterate_unary
    {start afterNode afterChild finish : CompactNumericVerifierState}
    {childSteps : Nat}
    (hnode : (compactNumericVerifierStep^[1]) start = afterNode)
    (hchild : (compactNumericVerifierStep^[childSteps])
      afterNode = afterChild)
    (hcombine : (compactNumericVerifierStep^[1]) afterChild = finish) :
    (compactNumericVerifierStep^[1 + childSteps + 1]) start = finish := by
  have hfirst := compactNumericVerifier_iterate_trans hnode hchild
  exact compactNumericVerifier_iterate_trans hfirst hcombine

theorem compactNumericVerifier_iterate_binary
    {start afterNode afterLeft afterRight finish :
      CompactNumericVerifierState}
    {leftSteps rightSteps : Nat}
    (hnode : (compactNumericVerifierStep^[1]) start = afterNode)
    (hleft : (compactNumericVerifierStep^[leftSteps])
      afterNode = afterLeft)
    (hright : (compactNumericVerifierStep^[rightSteps])
      afterLeft = afterRight)
    (hcombine : (compactNumericVerifierStep^[1]) afterRight = finish) :
    (compactNumericVerifierStep^[1 + leftSteps + rightSteps + 1])
      start = finish := by
  have hfirst := compactNumericVerifier_iterate_trans hnode hleft
  have hsecond := compactNumericVerifier_iterate_trans hfirst hright
  exact compactNumericVerifier_iterate_trans hsecond hcombine

theorem compactNumericVerifier_iterate_unary_failure
    {start afterNode : CompactNumericVerifierState}
    {childSteps : Nat}
    (hnode : (compactNumericVerifierStep^[1]) start = afterNode)
    (hchild : ∃ payload,
      (compactNumericVerifierStep^[childSteps]) afterNode =
        (payload, some false)) :
    ∃ payload,
      (compactNumericVerifierStep^[1 + childSteps + 1]) start =
        (payload, some false) := by
  rcases hchild with ⟨payload, hchild⟩
  refine ⟨payload, ?_⟩
  have hhalted :
      (compactNumericVerifierStep^[1]) (payload, some false) =
        (payload, some false) := by
    simpa only [Function.iterate_one] using
      compactNumericVerifierStep_halted payload false
  exact compactNumericVerifier_iterate_unary hnode hchild hhalted

theorem compactNumericVerifier_iterate_binary_left_failure
    {start afterNode : CompactNumericVerifierState}
    {leftSteps rightSteps : Nat}
    (hnode : (compactNumericVerifierStep^[1]) start = afterNode)
    (hleft : ∃ payload,
      (compactNumericVerifierStep^[leftSteps]) afterNode =
        (payload, some false)) :
    ∃ payload,
      (compactNumericVerifierStep^[1 + leftSteps + rightSteps + 1])
        start = (payload, some false) := by
  rcases hleft with ⟨payload, hleft⟩
  refine ⟨payload, ?_⟩
  have hfirst := compactNumericVerifier_iterate_trans hnode hleft
  have hhalted := compactNumericVerifierStep_iterate_halted
    (rightSteps + 1) payload false
  have hall := compactNumericVerifier_iterate_trans hfirst hhalted
  simpa [Nat.add_assoc] using hall

theorem compactNumericVerifier_iterate_binary_right_failure
    {start afterNode afterLeft : CompactNumericVerifierState}
    {leftSteps rightSteps : Nat}
    (hnode : (compactNumericVerifierStep^[1]) start = afterNode)
    (hleft : (compactNumericVerifierStep^[leftSteps])
      afterNode = afterLeft)
    (hright : ∃ payload,
      (compactNumericVerifierStep^[rightSteps]) afterLeft =
        (payload, some false)) :
    ∃ payload,
      (compactNumericVerifierStep^[1 + leftSteps + rightSteps + 1])
        start = (payload, some false) := by
  rcases hright with ⟨payload, hright⟩
  refine ⟨payload, ?_⟩
  have hhalted :
      (compactNumericVerifierStep^[1]) (payload, some false) =
        (payload, some false) := by
    simpa only [Function.iterate_one] using
      compactNumericVerifierStep_halted payload false
  exact compactNumericVerifier_iterate_binary
    hnode hleft hright hhalted

@[simp] theorem compactNumericVerifierStep_parse_canonical
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    compactNumericVerifierStep
        ((((compactListedProofTokens tree ++ proofSuffix,
              compactStructuralCertificateTokens certificate ++
                certificateSuffix),
            (compactNumericParseTask :: restTasks, values)), none)) =
      match compactNumericNodeTransition
          (compactListedProofNodeExpectedFields tree proofSuffix)
          (compactStructuralCertificateNodeExpected certificate
            certificateSuffix)
          restTasks values with
      | none =>
          (((compactListedProofTokens tree ++ proofSuffix,
              compactStructuralCertificateTokens certificate ++
                certificateSuffix),
            (restTasks, values)), some false)
      | some next => (next, none) := by
  simp [compactNumericVerifierStep, compactNumericRunningStep,
    compactNumericParseTask, compactNumericParseState,
    compactNumericParsePayload]

def compactNumericTreeCertificateShapeMatches :
    ListedCheckedPAProofTree -> StructuralValidityCertificate -> Bool
  | .closed _ _, .leaf => true
  | .axm _ _, .axiomCert _ => true
  | .verum _, .leaf => true
  | .and _ _ _ left right, .binary leftCertificate rightCertificate =>
      compactNumericTreeCertificateShapeMatches left leftCertificate &&
        compactNumericTreeCertificateShapeMatches right rightCertificate
  | .or _ _ _ premise, .unary premiseCertificate =>
      compactNumericTreeCertificateShapeMatches premise premiseCertificate
  | .all _ _ premise, .unary premiseCertificate =>
      compactNumericTreeCertificateShapeMatches premise premiseCertificate
  | .exs _ _ _ premise, .unary premiseCertificate =>
      compactNumericTreeCertificateShapeMatches premise premiseCertificate
  | .wk _ premise, .unary premiseCertificate =>
      compactNumericTreeCertificateShapeMatches premise premiseCertificate
  | .shift _ premise, .unary premiseCertificate =>
      compactNumericTreeCertificateShapeMatches premise premiseCertificate
  | .cut _ _ left right, .binary leftCertificate rightCertificate =>
      compactNumericTreeCertificateShapeMatches left leftCertificate &&
        compactNumericTreeCertificateShapeMatches right rightCertificate
  | _, _ => false

def compactNumericTreeCertificateRootMatches :
    ListedCheckedPAProofTree -> StructuralValidityCertificate -> Bool
  | .closed _ _, .leaf => true
  | .axm _ _, .axiomCert _ => true
  | .verum _, .leaf => true
  | .and _ _ _ _ _, .binary _ _ => true
  | .or _ _ _ _, .unary _ => true
  | .all _ _ _, .unary _ => true
  | .exs _ _ _ _, .unary _ => true
  | .wk _ _, .unary _ => true
  | .shift _ _, .unary _ => true
  | .cut _ _ _ _, .binary _ _ => true
  | _, _ => false

theorem compactNumericTreeTask_root_mismatch
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hroot :
      compactNumericTreeCertificateRootMatches tree certificate = false) :
    (compactNumericVerifierStep^[1])
        ((((compactListedProofTokens tree ++ proofSuffix,
              compactStructuralCertificateTokens certificate ++
                certificateSuffix),
            (compactNumericParseTask :: restTasks, values)), none)) =
      (((compactListedProofTokens tree ++ proofSuffix,
          compactStructuralCertificateTokens certificate ++
            certificateSuffix),
        (restTasks, values)), some false) := by
  rw [Function.iterate_one,
    compactNumericVerifierStep_parse_canonical]
  cases tree <;> cases certificate <;>
    simp_all [compactNumericTreeCertificateRootMatches,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix,
      compactNumericNodeTransition]

def compactNumericTreeTaskSteps :
    ListedCheckedPAProofTree -> StructuralValidityCertificate -> Nat
  | .and _ _ _ left right, .binary leftCertificate rightCertificate =>
      1 + compactNumericTreeTaskSteps left leftCertificate +
        compactNumericTreeTaskSteps right rightCertificate + 1
  | .or _ _ _ premise, .unary premiseCertificate =>
      1 + compactNumericTreeTaskSteps premise premiseCertificate + 1
  | .all _ _ premise, .unary premiseCertificate =>
      1 + compactNumericTreeTaskSteps premise premiseCertificate + 1
  | .exs _ _ _ premise, .unary premiseCertificate =>
      1 + compactNumericTreeTaskSteps premise premiseCertificate + 1
  | .wk _ premise, .unary premiseCertificate =>
      1 + compactNumericTreeTaskSteps premise premiseCertificate + 1
  | .shift _ premise, .unary premiseCertificate =>
      1 + compactNumericTreeTaskSteps premise premiseCertificate + 1
  | .cut _ _ left right, .binary leftCertificate rightCertificate =>
      1 + compactNumericTreeTaskSteps left leftCertificate +
        compactNumericTreeTaskSteps right rightCertificate + 1
  | _, _ => 1

theorem compactNumericTreeTask_root_mismatch_failure
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hroot :
      compactNumericTreeCertificateRootMatches tree certificate = false) :
    ∃ payload,
      (compactNumericVerifierStep^[
          compactNumericTreeTaskSteps tree certificate])
          ((((compactListedProofTokens tree ++ proofSuffix,
                compactStructuralCertificateTokens certificate ++
                  certificateSuffix),
              (compactNumericParseTask :: restTasks, values)), none)) =
        (payload, some false) := by
  let payload : CompactNumericRunningPayload :=
    ((compactListedProofTokens tree ++ proofSuffix,
        compactStructuralCertificateTokens certificate ++
          certificateSuffix),
      (restTasks, values))
  refine ⟨payload, ?_⟩
  have hone := compactNumericTreeTask_root_mismatch tree certificate
    proofSuffix certificateSuffix restTasks values hroot
  have hsteps : compactNumericTreeTaskSteps tree certificate = 1 := by
    cases tree <;> cases certificate <;>
      simp_all [compactNumericTreeCertificateRootMatches,
        compactNumericTreeTaskSteps]
  simpa [payload, hsteps] using hone

def compactNumericTreeTaskSuccessState
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    CompactNumericVerifierState :=
  (((proofSuffix, certificateSuffix),
      (restTasks,
        (arithmeticPropositionTokenValues tree.conclusionList,
          (listedCertificateValidTrace tree certificate).1) :: values)),
    none)

theorem compactNumericClosedLeafTask_execute
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    (compactNumericVerifierStep^[
        compactNumericTreeTaskSteps (.closed Gamma formula) .leaf])
        ((((compactListedProofTokens (.closed Gamma formula) ++ proofSuffix,
              compactStructuralCertificateTokens .leaf ++
                certificateSuffix),
            (compactNumericParseTask :: restTasks, values)), none)) =
      compactNumericTreeTaskSuccessState (.closed Gamma formula) .leaf
        proofSuffix certificateSuffix restTasks values := by
  simp [compactNumericTreeTaskSteps,
    compactNumericTreeTaskSuccessState,
    compactListedProofNodeExpectedFields,
    compactStructuralCertificateNodeExpected,
    compactNumericNodeFieldsSuffix,
    compactNumericNodeTransition,
    compactClosedRuleCheck_canonical,
    ListedCheckedPAProofTree.conclusionList]

theorem compactNumericAxmLeafTask_execute
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (sentence : LO.FirstOrder.ArithmeticSentence)
    (paCertificate : PAAxiomCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    (compactNumericVerifierStep^[
        compactNumericTreeTaskSteps (.axm Gamma sentence)
          (.axiomCert paCertificate)])
        ((((compactListedProofTokens (.axm Gamma sentence) ++ proofSuffix,
              compactStructuralCertificateTokens
                  (.axiomCert paCertificate) ++ certificateSuffix),
            (compactNumericParseTask :: restTasks, values)), none)) =
      compactNumericTreeTaskSuccessState (.axm Gamma sentence)
        (.axiomCert paCertificate) proofSuffix certificateSuffix
        restTasks values := by
  simp [compactNumericTreeTaskSteps,
    compactNumericTreeTaskSuccessState,
    compactListedProofNodeExpectedFields,
    compactStructuralCertificateNodeExpected,
    compactNumericNodeFieldsSuffix,
    compactNumericNodeTransition,
    arithmeticPropositionTokenValue,
    ListedCheckedPAProofTree.conclusionList]
  simpa [compactSentenceTokens] using
    compactAxmRuleCheck_canonical Gamma sentence paCertificate

theorem compactNumericVerumLeafTask_execute
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult) :
    (compactNumericVerifierStep^[
        compactNumericTreeTaskSteps (.verum Gamma) .leaf])
        ((((compactListedProofTokens (.verum Gamma) ++ proofSuffix,
              compactStructuralCertificateTokens .leaf ++
                certificateSuffix),
            (compactNumericParseTask :: restTasks, values)), none)) =
      compactNumericTreeTaskSuccessState (.verum Gamma) .leaf
        proofSuffix certificateSuffix restTasks values := by
  simp [compactNumericTreeTaskSteps,
    compactNumericTreeTaskSuccessState,
    compactListedProofNodeExpectedFields,
    compactStructuralCertificateNodeExpected,
    compactNumericNodeFieldsSuffix,
    compactNumericNodeTransition,
    compactVerumRuleCheck_canonical,
    ListedCheckedPAProofTree.conclusionList]

theorem compactNumericOrTask_execute
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hpremise :
      let fields := (compactListedProofNodeExpectedFields
        (.or Gamma leftFormula rightFormula premise) proofSuffix).2
      (compactNumericVerifierStep^[
          compactNumericTreeTaskSteps premise premiseCertificate])
          ((((compactListedProofTokens premise ++ proofSuffix,
                compactStructuralCertificateTokens premiseCertificate ++
                  certificateSuffix),
              (compactNumericParseTask ::
                compactNumericCombineTask 4 fields :: restTasks,
                values)), none)) =
        compactNumericTreeTaskSuccessState premise premiseCertificate
          proofSuffix certificateSuffix
          (compactNumericCombineTask 4 fields :: restTasks) values) :
    (compactNumericVerifierStep^[
        compactNumericTreeTaskSteps
          (.or Gamma leftFormula rightFormula premise)
          (.unary premiseCertificate)])
        ((((compactListedProofTokens
                (.or Gamma leftFormula rightFormula premise) ++ proofSuffix,
              compactStructuralCertificateTokens
                  (.unary premiseCertificate) ++ certificateSuffix),
            (compactNumericParseTask :: restTasks, values)), none)) =
      compactNumericTreeTaskSuccessState
        (.or Gamma leftFormula rightFormula premise)
        (.unary premiseCertificate) proofSuffix certificateSuffix
        restTasks values := by
  let fields := (compactListedProofNodeExpectedFields
    (.or Gamma leftFormula rightFormula premise) proofSuffix).2
  have hnode :
      (compactNumericVerifierStep^[1])
          ((((compactListedProofTokens
                  (.or Gamma leftFormula rightFormula premise) ++ proofSuffix,
                compactStructuralCertificateTokens
                    (.unary premiseCertificate) ++ certificateSuffix),
              (compactNumericParseTask :: restTasks, values)), none)) =
        (((compactListedProofTokens premise ++ proofSuffix,
            compactStructuralCertificateTokens premiseCertificate ++
              certificateSuffix),
          (compactNumericParseTask ::
            compactNumericCombineTask 4 fields :: restTasks, values)),
          none) := by
    simp [Function.iterate_one, fields,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix,
      compactNumericNodeTransition]
  have hcombine :
      (compactNumericVerifierStep^[1])
          (compactNumericTreeTaskSuccessState premise premiseCertificate
            proofSuffix certificateSuffix
            (compactNumericCombineTask 4 fields :: restTasks) values) =
        compactNumericTreeTaskSuccessState
          (.or Gamma leftFormula rightFormula premise)
          (.unary premiseCertificate) proofSuffix certificateSuffix
          restTasks values := by
    simp [Function.iterate_one, fields,
      compactNumericTreeTaskSuccessState,
      compactNumericVerifierStep, compactNumericRunningStep,
      compactNumericCombineTask, compactNumericCombineState,
      compactNumericCombineTransition,
      compactListedProofNodeExpectedFields]
    constructor
    · rfl
    · exact compactOrRuleCheck_canonical Gamma leftFormula rightFormula
        premise premiseCertificate
  have hfirst := compactNumericVerifier_iterate_trans hnode hpremise
  have hall := compactNumericVerifier_iterate_trans hfirst hcombine
  simpa [compactNumericTreeTaskSteps, Nat.add_assoc] using hall

theorem compactNumericAllTask_execute
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hpremise :
      let fields := (compactListedProofNodeExpectedFields
        (.all Gamma formula premise) proofSuffix).2
      (compactNumericVerifierStep^[
          compactNumericTreeTaskSteps premise premiseCertificate])
          ((((compactListedProofTokens premise ++ proofSuffix,
                compactStructuralCertificateTokens premiseCertificate ++
                  certificateSuffix),
              (compactNumericParseTask ::
                compactNumericCombineTask 5 fields :: restTasks,
                values)), none)) =
        compactNumericTreeTaskSuccessState premise premiseCertificate
          proofSuffix certificateSuffix
          (compactNumericCombineTask 5 fields :: restTasks) values) :
    (compactNumericVerifierStep^[
        compactNumericTreeTaskSteps (.all Gamma formula premise)
          (.unary premiseCertificate)])
        ((((compactListedProofTokens (.all Gamma formula premise) ++
                proofSuffix,
              compactStructuralCertificateTokens
                  (.unary premiseCertificate) ++ certificateSuffix),
            (compactNumericParseTask :: restTasks, values)), none)) =
      compactNumericTreeTaskSuccessState (.all Gamma formula premise)
        (.unary premiseCertificate) proofSuffix certificateSuffix
        restTasks values := by
  let fields := (compactListedProofNodeExpectedFields
    (.all Gamma formula premise) proofSuffix).2
  have hnode :
      (compactNumericVerifierStep^[1])
          ((((compactListedProofTokens (.all Gamma formula premise) ++
                  proofSuffix,
                compactStructuralCertificateTokens
                    (.unary premiseCertificate) ++ certificateSuffix),
              (compactNumericParseTask :: restTasks, values)), none)) =
        (((compactListedProofTokens premise ++ proofSuffix,
            compactStructuralCertificateTokens premiseCertificate ++
              certificateSuffix),
          (compactNumericParseTask ::
            compactNumericCombineTask 5 fields :: restTasks, values)),
          none) := by
    simp [fields, compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix,
      compactNumericNodeTransition]
  have hcombine :
      (compactNumericVerifierStep^[1])
          (compactNumericTreeTaskSuccessState premise premiseCertificate
            proofSuffix certificateSuffix
            (compactNumericCombineTask 5 fields :: restTasks) values) =
        compactNumericTreeTaskSuccessState (.all Gamma formula premise)
          (.unary premiseCertificate) proofSuffix certificateSuffix
          restTasks values := by
    simp [fields, compactNumericTreeTaskSuccessState,
      compactNumericVerifierStep, compactNumericRunningStep,
      compactNumericCombineTask, compactNumericCombineState,
      compactNumericCombineTransition,
      compactListedProofNodeExpectedFields]
    constructor
    · rfl
    · exact compactAllRuleCheck_canonical Gamma formula premise
        premiseCertificate
  have hall := compactNumericVerifier_iterate_unary
    hnode hpremise hcombine
  simpa [compactNumericTreeTaskSteps] using hall

theorem compactNumericExsTask_execute
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hpremise :
      let fields := (compactListedProofNodeExpectedFields
        (.exs Gamma formula witness premise) proofSuffix).2
      (compactNumericVerifierStep^[
          compactNumericTreeTaskSteps premise premiseCertificate])
          ((((compactListedProofTokens premise ++ proofSuffix,
                compactStructuralCertificateTokens premiseCertificate ++
                  certificateSuffix),
              (compactNumericParseTask ::
                compactNumericCombineTask 6 fields :: restTasks,
                values)), none)) =
        compactNumericTreeTaskSuccessState premise premiseCertificate
          proofSuffix certificateSuffix
          (compactNumericCombineTask 6 fields :: restTasks) values) :
    (compactNumericVerifierStep^[
        compactNumericTreeTaskSteps (.exs Gamma formula witness premise)
          (.unary premiseCertificate)])
        ((((compactListedProofTokens
                (.exs Gamma formula witness premise) ++ proofSuffix,
              compactStructuralCertificateTokens
                  (.unary premiseCertificate) ++ certificateSuffix),
            (compactNumericParseTask :: restTasks, values)), none)) =
      compactNumericTreeTaskSuccessState
        (.exs Gamma formula witness premise) (.unary premiseCertificate)
        proofSuffix certificateSuffix restTasks values := by
  let fields := (compactListedProofNodeExpectedFields
    (.exs Gamma formula witness premise) proofSuffix).2
  have hnode :
      (compactNumericVerifierStep^[1])
          ((((compactListedProofTokens
                  (.exs Gamma formula witness premise) ++ proofSuffix,
                compactStructuralCertificateTokens
                    (.unary premiseCertificate) ++ certificateSuffix),
              (compactNumericParseTask :: restTasks, values)), none)) =
        (((compactListedProofTokens premise ++ proofSuffix,
            compactStructuralCertificateTokens premiseCertificate ++
              certificateSuffix),
          (compactNumericParseTask ::
            compactNumericCombineTask 6 fields :: restTasks, values)),
          none) := by
    simp [fields, compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix,
      compactNumericNodeTransition]
  have hcombine :
      (compactNumericVerifierStep^[1])
          (compactNumericTreeTaskSuccessState premise premiseCertificate
            proofSuffix certificateSuffix
            (compactNumericCombineTask 6 fields :: restTasks) values) =
        compactNumericTreeTaskSuccessState
          (.exs Gamma formula witness premise) (.unary premiseCertificate)
          proofSuffix certificateSuffix restTasks values := by
    simp [fields, compactNumericTreeTaskSuccessState,
      compactNumericVerifierStep, compactNumericRunningStep,
      compactNumericCombineTask, compactNumericCombineState,
      compactNumericCombineTransition,
      compactListedProofNodeExpectedFields]
    constructor
    · rfl
    · exact compactExsRuleCheck_canonical Gamma formula witness premise
        premiseCertificate
  have hall := compactNumericVerifier_iterate_unary
    hnode hpremise hcombine
  simpa [compactNumericTreeTaskSteps] using hall

theorem compactNumericWkTask_execute
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hpremise :
      let fields := (compactListedProofNodeExpectedFields
        (.wk Gamma premise) proofSuffix).2
      (compactNumericVerifierStep^[
          compactNumericTreeTaskSteps premise premiseCertificate])
          ((((compactListedProofTokens premise ++ proofSuffix,
                compactStructuralCertificateTokens premiseCertificate ++
                  certificateSuffix),
              (compactNumericParseTask ::
                compactNumericCombineTask 7 fields :: restTasks,
                values)), none)) =
        compactNumericTreeTaskSuccessState premise premiseCertificate
          proofSuffix certificateSuffix
          (compactNumericCombineTask 7 fields :: restTasks) values) :
    (compactNumericVerifierStep^[
        compactNumericTreeTaskSteps (.wk Gamma premise)
          (.unary premiseCertificate)])
        ((((compactListedProofTokens (.wk Gamma premise) ++ proofSuffix,
              compactStructuralCertificateTokens
                  (.unary premiseCertificate) ++ certificateSuffix),
            (compactNumericParseTask :: restTasks, values)), none)) =
      compactNumericTreeTaskSuccessState (.wk Gamma premise)
        (.unary premiseCertificate) proofSuffix certificateSuffix
        restTasks values := by
  let fields := (compactListedProofNodeExpectedFields
    (.wk Gamma premise) proofSuffix).2
  have hnode :
      (compactNumericVerifierStep^[1])
          ((((compactListedProofTokens (.wk Gamma premise) ++ proofSuffix,
                compactStructuralCertificateTokens
                    (.unary premiseCertificate) ++ certificateSuffix),
              (compactNumericParseTask :: restTasks, values)), none)) =
        (((compactListedProofTokens premise ++ proofSuffix,
            compactStructuralCertificateTokens premiseCertificate ++
              certificateSuffix),
          (compactNumericParseTask ::
            compactNumericCombineTask 7 fields :: restTasks, values)),
          none) := by
    simp [fields, compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix,
      compactNumericNodeTransition]
  have hcombine :
      (compactNumericVerifierStep^[1])
          (compactNumericTreeTaskSuccessState premise premiseCertificate
            proofSuffix certificateSuffix
            (compactNumericCombineTask 7 fields :: restTasks) values) =
        compactNumericTreeTaskSuccessState (.wk Gamma premise)
          (.unary premiseCertificate) proofSuffix certificateSuffix
          restTasks values := by
    simp [fields, compactNumericTreeTaskSuccessState,
      compactNumericVerifierStep, compactNumericRunningStep,
      compactNumericCombineTask, compactNumericCombineState,
      compactNumericCombineTransition,
      compactListedProofNodeExpectedFields]
    constructor
    · rfl
    · exact compactWkRuleCheck_canonical Gamma premise premiseCertificate
  have hall := compactNumericVerifier_iterate_unary
    hnode hpremise hcombine
  simpa [compactNumericTreeTaskSteps] using hall

theorem compactNumericShiftTask_execute
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hpremise :
      let fields := (compactListedProofNodeExpectedFields
        (.shift Gamma premise) proofSuffix).2
      (compactNumericVerifierStep^[
          compactNumericTreeTaskSteps premise premiseCertificate])
          ((((compactListedProofTokens premise ++ proofSuffix,
                compactStructuralCertificateTokens premiseCertificate ++
                  certificateSuffix),
              (compactNumericParseTask ::
                compactNumericCombineTask 8 fields :: restTasks,
                values)), none)) =
        compactNumericTreeTaskSuccessState premise premiseCertificate
          proofSuffix certificateSuffix
          (compactNumericCombineTask 8 fields :: restTasks) values) :
    (compactNumericVerifierStep^[
        compactNumericTreeTaskSteps (.shift Gamma premise)
          (.unary premiseCertificate)])
        ((((compactListedProofTokens (.shift Gamma premise) ++ proofSuffix,
              compactStructuralCertificateTokens
                  (.unary premiseCertificate) ++ certificateSuffix),
            (compactNumericParseTask :: restTasks, values)), none)) =
      compactNumericTreeTaskSuccessState (.shift Gamma premise)
        (.unary premiseCertificate) proofSuffix certificateSuffix
        restTasks values := by
  let fields := (compactListedProofNodeExpectedFields
    (.shift Gamma premise) proofSuffix).2
  have hnode :
      (compactNumericVerifierStep^[1])
          ((((compactListedProofTokens (.shift Gamma premise) ++ proofSuffix,
                compactStructuralCertificateTokens
                    (.unary premiseCertificate) ++ certificateSuffix),
              (compactNumericParseTask :: restTasks, values)), none)) =
        (((compactListedProofTokens premise ++ proofSuffix,
            compactStructuralCertificateTokens premiseCertificate ++
              certificateSuffix),
          (compactNumericParseTask ::
            compactNumericCombineTask 8 fields :: restTasks, values)),
          none) := by
    simp [fields, compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix,
      compactNumericNodeTransition]
  have hcombine :
      (compactNumericVerifierStep^[1])
          (compactNumericTreeTaskSuccessState premise premiseCertificate
            proofSuffix certificateSuffix
            (compactNumericCombineTask 8 fields :: restTasks) values) =
        compactNumericTreeTaskSuccessState (.shift Gamma premise)
          (.unary premiseCertificate) proofSuffix certificateSuffix
          restTasks values := by
    simp [fields, compactNumericTreeTaskSuccessState,
      compactNumericVerifierStep, compactNumericRunningStep,
      compactNumericCombineTask, compactNumericCombineState,
      compactNumericCombineTransition,
      compactListedProofNodeExpectedFields]
    constructor
    · rfl
    · exact compactShiftRuleCheck_canonical Gamma premise
        premiseCertificate
  have hall := compactNumericVerifier_iterate_unary
    hnode hpremise hcombine
  simpa [compactNumericTreeTaskSteps] using hall

theorem compactNumericAndTask_execute
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
    (left right : ListedCheckedPAProofTree)
    (leftCertificate rightCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hleft :
      let fields := (compactListedProofNodeExpectedFields
        (.and Gamma leftFormula rightFormula left right) proofSuffix).2
      (compactNumericVerifierStep^[
          compactNumericTreeTaskSteps left leftCertificate])
          ((((compactListedProofTokens left ++
                  compactListedProofTokens right ++ proofSuffix,
                compactStructuralCertificateTokens leftCertificate ++
                  compactStructuralCertificateTokens rightCertificate ++
                  certificateSuffix),
              (compactNumericParseTask :: compactNumericParseTask ::
                compactNumericCombineTask 3 fields :: restTasks,
                values)), none)) =
        compactNumericTreeTaskSuccessState left leftCertificate
          (compactListedProofTokens right ++ proofSuffix)
          (compactStructuralCertificateTokens rightCertificate ++
            certificateSuffix)
          (compactNumericParseTask ::
            compactNumericCombineTask 3 fields :: restTasks) values)
    (hright :
      let fields := (compactListedProofNodeExpectedFields
        (.and Gamma leftFormula rightFormula left right) proofSuffix).2
      let leftResult : CompactNumericChildResult :=
        (arithmeticPropositionTokenValues left.conclusionList,
          (listedCertificateValidTrace left leftCertificate).1)
      (compactNumericVerifierStep^[
          compactNumericTreeTaskSteps right rightCertificate])
          ((((compactListedProofTokens right ++ proofSuffix,
                compactStructuralCertificateTokens rightCertificate ++
                  certificateSuffix),
              (compactNumericParseTask ::
                compactNumericCombineTask 3 fields :: restTasks,
                leftResult :: values)), none)) =
        compactNumericTreeTaskSuccessState right rightCertificate
          proofSuffix certificateSuffix
          (compactNumericCombineTask 3 fields :: restTasks)
          (leftResult :: values)) :
    (compactNumericVerifierStep^[
        compactNumericTreeTaskSteps
          (.and Gamma leftFormula rightFormula left right)
          (.binary leftCertificate rightCertificate)])
        ((((compactListedProofTokens
                (.and Gamma leftFormula rightFormula left right) ++
                proofSuffix,
              compactStructuralCertificateTokens
                  (.binary leftCertificate rightCertificate) ++
                certificateSuffix),
            (compactNumericParseTask :: restTasks, values)), none)) =
      compactNumericTreeTaskSuccessState
        (.and Gamma leftFormula rightFormula left right)
        (.binary leftCertificate rightCertificate)
        proofSuffix certificateSuffix restTasks values := by
  let fields := (compactListedProofNodeExpectedFields
    (.and Gamma leftFormula rightFormula left right) proofSuffix).2
  let leftResult : CompactNumericChildResult :=
    (arithmeticPropositionTokenValues left.conclusionList,
      (listedCertificateValidTrace left leftCertificate).1)
  have hnode :
      (compactNumericVerifierStep^[1])
          ((((compactListedProofTokens
                  (.and Gamma leftFormula rightFormula left right) ++
                  proofSuffix,
                compactStructuralCertificateTokens
                    (.binary leftCertificate rightCertificate) ++
                  certificateSuffix),
              (compactNumericParseTask :: restTasks, values)), none)) =
        (((compactListedProofTokens left ++
              compactListedProofTokens right ++ proofSuffix,
            compactStructuralCertificateTokens leftCertificate ++
              compactStructuralCertificateTokens rightCertificate ++
              certificateSuffix),
          (compactNumericParseTask :: compactNumericParseTask ::
            compactNumericCombineTask 3 fields :: restTasks, values)),
          none) := by
    simp [fields, compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix,
      compactNumericNodeTransition, List.append_assoc]
  have hcombine :
      (compactNumericVerifierStep^[1])
          (compactNumericTreeTaskSuccessState right rightCertificate
            proofSuffix certificateSuffix
            (compactNumericCombineTask 3 fields :: restTasks)
            (leftResult :: values)) =
        compactNumericTreeTaskSuccessState
          (.and Gamma leftFormula rightFormula left right)
          (.binary leftCertificate rightCertificate)
          proofSuffix certificateSuffix restTasks values := by
    simp [fields, leftResult, compactNumericTreeTaskSuccessState,
      compactNumericVerifierStep, compactNumericRunningStep,
      compactNumericCombineTask, compactNumericCombineState,
      compactNumericCombineTransition,
      compactListedProofNodeExpectedFields]
    constructor
    · rfl
    · exact compactAndRuleCheck_canonical Gamma leftFormula rightFormula
        left right leftCertificate rightCertificate
  have hall := compactNumericVerifier_iterate_binary
    hnode hleft hright hcombine
  simpa [compactNumericTreeTaskSteps] using hall

theorem compactNumericCutTask_execute
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (left right : ListedCheckedPAProofTree)
    (leftCertificate rightCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hleft :
      let fields := (compactListedProofNodeExpectedFields
        (.cut Gamma formula left right) proofSuffix).2
      (compactNumericVerifierStep^[
          compactNumericTreeTaskSteps left leftCertificate])
          ((((compactListedProofTokens left ++
                  compactListedProofTokens right ++ proofSuffix,
                compactStructuralCertificateTokens leftCertificate ++
                  compactStructuralCertificateTokens rightCertificate ++
                  certificateSuffix),
              (compactNumericParseTask :: compactNumericParseTask ::
                compactNumericCombineTask 9 fields :: restTasks,
                values)), none)) =
        compactNumericTreeTaskSuccessState left leftCertificate
          (compactListedProofTokens right ++ proofSuffix)
          (compactStructuralCertificateTokens rightCertificate ++
            certificateSuffix)
          (compactNumericParseTask ::
            compactNumericCombineTask 9 fields :: restTasks) values)
    (hright :
      let fields := (compactListedProofNodeExpectedFields
        (.cut Gamma formula left right) proofSuffix).2
      let leftResult : CompactNumericChildResult :=
        (arithmeticPropositionTokenValues left.conclusionList,
          (listedCertificateValidTrace left leftCertificate).1)
      (compactNumericVerifierStep^[
          compactNumericTreeTaskSteps right rightCertificate])
          ((((compactListedProofTokens right ++ proofSuffix,
                compactStructuralCertificateTokens rightCertificate ++
                  certificateSuffix),
              (compactNumericParseTask ::
                compactNumericCombineTask 9 fields :: restTasks,
                leftResult :: values)), none)) =
        compactNumericTreeTaskSuccessState right rightCertificate
          proofSuffix certificateSuffix
          (compactNumericCombineTask 9 fields :: restTasks)
          (leftResult :: values)) :
    (compactNumericVerifierStep^[
        compactNumericTreeTaskSteps (.cut Gamma formula left right)
          (.binary leftCertificate rightCertificate)])
        ((((compactListedProofTokens (.cut Gamma formula left right) ++
                proofSuffix,
              compactStructuralCertificateTokens
                  (.binary leftCertificate rightCertificate) ++
                certificateSuffix),
            (compactNumericParseTask :: restTasks, values)), none)) =
      compactNumericTreeTaskSuccessState (.cut Gamma formula left right)
        (.binary leftCertificate rightCertificate)
        proofSuffix certificateSuffix restTasks values := by
  let fields := (compactListedProofNodeExpectedFields
    (.cut Gamma formula left right) proofSuffix).2
  let leftResult : CompactNumericChildResult :=
    (arithmeticPropositionTokenValues left.conclusionList,
      (listedCertificateValidTrace left leftCertificate).1)
  have hnode :
      (compactNumericVerifierStep^[1])
          ((((compactListedProofTokens (.cut Gamma formula left right) ++
                  proofSuffix,
                compactStructuralCertificateTokens
                    (.binary leftCertificate rightCertificate) ++
                  certificateSuffix),
              (compactNumericParseTask :: restTasks, values)), none)) =
        (((compactListedProofTokens left ++
              compactListedProofTokens right ++ proofSuffix,
            compactStructuralCertificateTokens leftCertificate ++
              compactStructuralCertificateTokens rightCertificate ++
              certificateSuffix),
          (compactNumericParseTask :: compactNumericParseTask ::
            compactNumericCombineTask 9 fields :: restTasks, values)),
          none) := by
    simp [fields, compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix,
      compactNumericNodeTransition, List.append_assoc]
  have hcombine :
      (compactNumericVerifierStep^[1])
          (compactNumericTreeTaskSuccessState right rightCertificate
            proofSuffix certificateSuffix
            (compactNumericCombineTask 9 fields :: restTasks)
            (leftResult :: values)) =
        compactNumericTreeTaskSuccessState (.cut Gamma formula left right)
          (.binary leftCertificate rightCertificate)
          proofSuffix certificateSuffix restTasks values := by
    simp [fields, leftResult, compactNumericTreeTaskSuccessState,
      compactNumericVerifierStep, compactNumericRunningStep,
      compactNumericCombineTask, compactNumericCombineState,
      compactNumericCombineTransition,
      compactListedProofNodeExpectedFields]
    constructor
    · rfl
    · exact compactCutRuleCheck_canonical Gamma formula left right
        leftCertificate rightCertificate
  have hall := compactNumericVerifier_iterate_binary
    hnode hleft hright hcombine
  simpa [compactNumericTreeTaskSteps] using hall

theorem compactNumericTreeTask_execute_of_shape
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hshape :
      compactNumericTreeCertificateShapeMatches tree certificate = true) :
    (compactNumericVerifierStep^[
        compactNumericTreeTaskSteps tree certificate])
        ((((compactListedProofTokens tree ++ proofSuffix,
              compactStructuralCertificateTokens certificate ++
                certificateSuffix),
            (compactNumericParseTask :: restTasks, values)), none)) =
      compactNumericTreeTaskSuccessState tree certificate
        proofSuffix certificateSuffix restTasks values := by
  induction tree generalizing certificate proofSuffix certificateSuffix
      restTasks values with
  | closed Gamma formula =>
      cases certificate with
      | leaf =>
          exact compactNumericClosedLeafTask_execute Gamma formula
            proofSuffix certificateSuffix restTasks values
      | axiomCert paCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | unary premiseCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | binary leftCertificate rightCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
  | axm Gamma sentence =>
      cases certificate with
      | leaf =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | axiomCert paCertificate =>
          exact compactNumericAxmLeafTask_execute Gamma sentence paCertificate
            proofSuffix certificateSuffix restTasks values
      | unary premiseCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | binary leftCertificate rightCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
  | verum Gamma =>
      cases certificate with
      | leaf =>
          exact compactNumericVerumLeafTask_execute Gamma proofSuffix
            certificateSuffix restTasks values
      | axiomCert paCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | unary premiseCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | binary leftCertificate rightCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
  | and Gamma leftFormula rightFormula left right ihLeft ihRight =>
      cases certificate with
      | leaf =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | axiomCert paCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | unary premiseCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | binary leftCertificate rightCertificate =>
          simp only [compactNumericTreeCertificateShapeMatches,
            Bool.and_eq_true] at hshape
          rcases hshape with ⟨hleftShape, hrightShape⟩
          let fields := (compactListedProofNodeExpectedFields
            (.and Gamma leftFormula rightFormula left right) proofSuffix).2
          let leftResult : CompactNumericChildResult :=
            (arithmeticPropositionTokenValues left.conclusionList,
              (listedCertificateValidTrace left leftCertificate).1)
          have hleft := ihLeft leftCertificate
            (compactListedProofTokens right ++ proofSuffix)
            (compactStructuralCertificateTokens rightCertificate ++
              certificateSuffix)
            (compactNumericParseTask ::
              compactNumericCombineTask 3 fields :: restTasks)
            values hleftShape
          have hright := ihRight rightCertificate proofSuffix
            certificateSuffix
            (compactNumericCombineTask 3 fields :: restTasks)
            (leftResult :: values) hrightShape
          apply compactNumericAndTask_execute Gamma leftFormula rightFormula
            left right leftCertificate rightCertificate proofSuffix
            certificateSuffix restTasks values
          · simpa [List.append_assoc] using hleft
          · exact hright
  | or Gamma leftFormula rightFormula premise ih =>
      cases certificate with
      | leaf =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | axiomCert paCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | unary premiseCertificate =>
          have hpremise := ih premiseCertificate proofSuffix
            certificateSuffix
            (compactNumericCombineTask 4
                (compactListedProofNodeExpectedFields
                  (.or Gamma leftFormula rightFormula premise)
                  proofSuffix).2 :: restTasks)
            values hshape
          exact compactNumericOrTask_execute Gamma leftFormula rightFormula
            premise premiseCertificate proofSuffix certificateSuffix
            restTasks values hpremise
      | binary leftCertificate rightCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
  | all Gamma formula premise ih =>
      cases certificate with
      | leaf =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | axiomCert paCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | unary premiseCertificate =>
          have hpremise := ih premiseCertificate proofSuffix
            certificateSuffix
            (compactNumericCombineTask 5
                (compactListedProofNodeExpectedFields
                  (.all Gamma formula premise) proofSuffix).2 :: restTasks)
            values hshape
          exact compactNumericAllTask_execute Gamma formula premise
            premiseCertificate proofSuffix certificateSuffix restTasks values
            hpremise
      | binary leftCertificate rightCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
  | exs Gamma formula witness premise ih =>
      cases certificate with
      | leaf =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | axiomCert paCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | unary premiseCertificate =>
          have hpremise := ih premiseCertificate proofSuffix
            certificateSuffix
            (compactNumericCombineTask 6
                (compactListedProofNodeExpectedFields
                  (.exs Gamma formula witness premise) proofSuffix).2 ::
              restTasks)
            values hshape
          exact compactNumericExsTask_execute Gamma formula witness premise
            premiseCertificate proofSuffix certificateSuffix restTasks values
            hpremise
      | binary leftCertificate rightCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
  | wk Gamma premise ih =>
      cases certificate with
      | leaf =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | axiomCert paCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | unary premiseCertificate =>
          have hpremise := ih premiseCertificate proofSuffix
            certificateSuffix
            (compactNumericCombineTask 7
                (compactListedProofNodeExpectedFields
                  (.wk Gamma premise) proofSuffix).2 :: restTasks)
            values hshape
          exact compactNumericWkTask_execute Gamma premise premiseCertificate
            proofSuffix certificateSuffix restTasks values hpremise
      | binary leftCertificate rightCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
  | shift Gamma premise ih =>
      cases certificate with
      | leaf =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | axiomCert paCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | unary premiseCertificate =>
          have hpremise := ih premiseCertificate proofSuffix
            certificateSuffix
            (compactNumericCombineTask 8
                (compactListedProofNodeExpectedFields
                  (.shift Gamma premise) proofSuffix).2 :: restTasks)
            values hshape
          exact compactNumericShiftTask_execute Gamma premise
            premiseCertificate proofSuffix certificateSuffix restTasks values
            hpremise
      | binary leftCertificate rightCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
  | cut Gamma formula left right ihLeft ihRight =>
      cases certificate with
      | leaf =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | axiomCert paCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | unary premiseCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | binary leftCertificate rightCertificate =>
          simp only [compactNumericTreeCertificateShapeMatches,
            Bool.and_eq_true] at hshape
          rcases hshape with ⟨hleftShape, hrightShape⟩
          let fields := (compactListedProofNodeExpectedFields
            (.cut Gamma formula left right) proofSuffix).2
          let leftResult : CompactNumericChildResult :=
            (arithmeticPropositionTokenValues left.conclusionList,
              (listedCertificateValidTrace left leftCertificate).1)
          have hleft := ihLeft leftCertificate
            (compactListedProofTokens right ++ proofSuffix)
            (compactStructuralCertificateTokens rightCertificate ++
              certificateSuffix)
            (compactNumericParseTask ::
              compactNumericCombineTask 9 fields :: restTasks)
            values hleftShape
          have hright := ihRight rightCertificate proofSuffix
            certificateSuffix
            (compactNumericCombineTask 9 fields :: restTasks)
            (leftResult :: values) hrightShape
          apply compactNumericCutTask_execute Gamma formula left right
            leftCertificate rightCertificate proofSuffix certificateSuffix
            restTasks values
          · simpa [List.append_assoc] using hleft
          · exact hright

theorem compactNumericTreeTask_failure_of_shape
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hshape :
      compactNumericTreeCertificateShapeMatches tree certificate = false) :
    ∃ payload,
      (compactNumericVerifierStep^[
          compactNumericTreeTaskSteps tree certificate])
          ((((compactListedProofTokens tree ++ proofSuffix,
                compactStructuralCertificateTokens certificate ++
                  certificateSuffix),
              (compactNumericParseTask :: restTasks, values)), none)) =
        (payload, some false) := by
  induction tree generalizing certificate proofSuffix certificateSuffix
      restTasks values with
  | closed Gamma formula =>
      cases certificate with
      | leaf =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | axiomCert paCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.closed Gamma formula) (.axiomCert paCertificate)
            proofSuffix certificateSuffix restTasks values (by rfl)
      | unary premiseCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.closed Gamma formula) (.unary premiseCertificate)
            proofSuffix certificateSuffix restTasks values (by rfl)
      | binary leftCertificate rightCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.closed Gamma formula)
            (.binary leftCertificate rightCertificate)
            proofSuffix certificateSuffix restTasks values (by rfl)
  | axm Gamma sentence =>
      cases certificate with
      | leaf =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.axm Gamma sentence) .leaf proofSuffix certificateSuffix
            restTasks values (by rfl)
      | axiomCert paCertificate =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | unary premiseCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.axm Gamma sentence) (.unary premiseCertificate)
            proofSuffix certificateSuffix restTasks values (by rfl)
      | binary leftCertificate rightCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.axm Gamma sentence) (.binary leftCertificate rightCertificate)
            proofSuffix certificateSuffix restTasks values (by rfl)
  | verum Gamma =>
      cases certificate with
      | leaf =>
          simp [compactNumericTreeCertificateShapeMatches] at hshape
      | axiomCert paCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.verum Gamma) (.axiomCert paCertificate)
            proofSuffix certificateSuffix restTasks values (by rfl)
      | unary premiseCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.verum Gamma) (.unary premiseCertificate)
            proofSuffix certificateSuffix restTasks values (by rfl)
      | binary leftCertificate rightCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.verum Gamma) (.binary leftCertificate rightCertificate)
            proofSuffix certificateSuffix restTasks values (by rfl)
  | and Gamma leftFormula rightFormula left right ihLeft ihRight =>
      cases certificate with
      | leaf =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.and Gamma leftFormula rightFormula left right) .leaf
            proofSuffix certificateSuffix restTasks values (by rfl)
      | axiomCert paCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.and Gamma leftFormula rightFormula left right)
            (.axiomCert paCertificate) proofSuffix certificateSuffix
            restTasks values (by rfl)
      | unary premiseCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.and Gamma leftFormula rightFormula left right)
            (.unary premiseCertificate) proofSuffix certificateSuffix
            restTasks values (by rfl)
      | binary leftCertificate rightCertificate =>
          let fields := (compactListedProofNodeExpectedFields
            (.and Gamma leftFormula rightFormula left right) proofSuffix).2
          let leftResult : CompactNumericChildResult :=
            (arithmeticPropositionTokenValues left.conclusionList,
              (listedCertificateValidTrace left leftCertificate).1)
          have hnode :
              (compactNumericVerifierStep^[1])
                  ((((compactListedProofTokens
                          (.and Gamma leftFormula rightFormula left right) ++
                          proofSuffix,
                        compactStructuralCertificateTokens
                            (.binary leftCertificate rightCertificate) ++
                          certificateSuffix),
                      (compactNumericParseTask :: restTasks, values)),
                    none)) =
                (((compactListedProofTokens left ++
                      compactListedProofTokens right ++ proofSuffix,
                    compactStructuralCertificateTokens leftCertificate ++
                      compactStructuralCertificateTokens rightCertificate ++
                      certificateSuffix),
                  (compactNumericParseTask :: compactNumericParseTask ::
                    compactNumericCombineTask 3 fields :: restTasks,
                    values)), none) := by
            simp [fields, compactListedProofNodeExpectedFields,
              compactStructuralCertificateNodeExpected,
              compactNumericNodeFieldsSuffix,
              compactNumericNodeTransition, List.append_assoc]
          cases hleftShape :
              compactNumericTreeCertificateShapeMatches
                left leftCertificate with
          | false =>
              have hleftFailure := ihLeft leftCertificate
                (compactListedProofTokens right ++ proofSuffix)
                (compactStructuralCertificateTokens rightCertificate ++
                  certificateSuffix)
                (compactNumericParseTask ::
                  compactNumericCombineTask 3 fields :: restTasks)
                values hleftShape
              have hall :=
                compactNumericVerifier_iterate_binary_left_failure
                  (rightSteps := compactNumericTreeTaskSteps
                    right rightCertificate) hnode
                  (by simpa [List.append_assoc] using hleftFailure)
              simpa [compactNumericTreeTaskSteps] using hall
          | true =>
              have hrightShape :
                  compactNumericTreeCertificateShapeMatches
                    right rightCertificate = false := by
                simpa [compactNumericTreeCertificateShapeMatches,
                  hleftShape] using hshape
              have hleftSuccess :=
                compactNumericTreeTask_execute_of_shape left leftCertificate
                  (compactListedProofTokens right ++ proofSuffix)
                  (compactStructuralCertificateTokens rightCertificate ++
                    certificateSuffix)
                  (compactNumericParseTask ::
                    compactNumericCombineTask 3 fields :: restTasks)
                  values hleftShape
              have hrightFailure := ihRight rightCertificate proofSuffix
                certificateSuffix
                (compactNumericCombineTask 3 fields :: restTasks)
                (leftResult :: values) hrightShape
              have hall :=
                compactNumericVerifier_iterate_binary_right_failure hnode
                  (by
                    simpa [List.append_assoc,
                      compactNumericTreeTaskSuccessState, leftResult] using
                      hleftSuccess)
                  hrightFailure
              simpa [compactNumericTreeTaskSteps] using hall
  | or Gamma leftFormula rightFormula premise ih =>
      cases certificate with
      | leaf =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.or Gamma leftFormula rightFormula premise) .leaf
            proofSuffix certificateSuffix restTasks values (by rfl)
      | axiomCert paCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.or Gamma leftFormula rightFormula premise)
            (.axiomCert paCertificate) proofSuffix certificateSuffix
            restTasks values (by rfl)
      | unary premiseCertificate =>
          let fields := (compactListedProofNodeExpectedFields
            (.or Gamma leftFormula rightFormula premise) proofSuffix).2
          have hnode :
              (compactNumericVerifierStep^[1])
                  ((((compactListedProofTokens
                          (.or Gamma leftFormula rightFormula premise) ++
                          proofSuffix,
                        compactStructuralCertificateTokens
                            (.unary premiseCertificate) ++
                          certificateSuffix),
                      (compactNumericParseTask :: restTasks, values)),
                    none)) =
                (((compactListedProofTokens premise ++ proofSuffix,
                    compactStructuralCertificateTokens premiseCertificate ++
                      certificateSuffix),
                  (compactNumericParseTask ::
                    compactNumericCombineTask 4 fields :: restTasks,
                    values)), none) := by
            simp [fields, compactListedProofNodeExpectedFields,
              compactStructuralCertificateNodeExpected,
              compactNumericNodeFieldsSuffix,
              compactNumericNodeTransition]
          have hpremise := ih premiseCertificate proofSuffix
            certificateSuffix
            (compactNumericCombineTask 4 fields :: restTasks)
            values hshape
          have hall := compactNumericVerifier_iterate_unary_failure
            hnode hpremise
          simpa [compactNumericTreeTaskSteps] using hall
      | binary leftCertificate rightCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.or Gamma leftFormula rightFormula premise)
            (.binary leftCertificate rightCertificate)
            proofSuffix certificateSuffix restTasks values (by rfl)
  | all Gamma formula premise ih =>
      cases certificate with
      | leaf =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.all Gamma formula premise) .leaf proofSuffix
            certificateSuffix restTasks values (by rfl)
      | axiomCert paCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.all Gamma formula premise) (.axiomCert paCertificate)
            proofSuffix certificateSuffix restTasks values (by rfl)
      | unary premiseCertificate =>
          let fields := (compactListedProofNodeExpectedFields
            (.all Gamma formula premise) proofSuffix).2
          have hnode :
              (compactNumericVerifierStep^[1])
                  ((((compactListedProofTokens (.all Gamma formula premise) ++
                          proofSuffix,
                        compactStructuralCertificateTokens
                            (.unary premiseCertificate) ++
                          certificateSuffix),
                      (compactNumericParseTask :: restTasks, values)),
                    none)) =
                (((compactListedProofTokens premise ++ proofSuffix,
                    compactStructuralCertificateTokens premiseCertificate ++
                      certificateSuffix),
                  (compactNumericParseTask ::
                    compactNumericCombineTask 5 fields :: restTasks,
                    values)), none) := by
            simp [fields, compactListedProofNodeExpectedFields,
              compactStructuralCertificateNodeExpected,
              compactNumericNodeFieldsSuffix,
              compactNumericNodeTransition]
          have hpremise := ih premiseCertificate proofSuffix
            certificateSuffix
            (compactNumericCombineTask 5 fields :: restTasks)
            values hshape
          have hall := compactNumericVerifier_iterate_unary_failure
            hnode hpremise
          simpa [compactNumericTreeTaskSteps] using hall
      | binary leftCertificate rightCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.all Gamma formula premise)
            (.binary leftCertificate rightCertificate)
            proofSuffix certificateSuffix restTasks values (by rfl)
  | exs Gamma formula witness premise ih =>
      cases certificate with
      | leaf =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.exs Gamma formula witness premise) .leaf proofSuffix
            certificateSuffix restTasks values (by rfl)
      | axiomCert paCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.exs Gamma formula witness premise)
            (.axiomCert paCertificate) proofSuffix certificateSuffix
            restTasks values (by rfl)
      | unary premiseCertificate =>
          let fields := (compactListedProofNodeExpectedFields
            (.exs Gamma formula witness premise) proofSuffix).2
          have hnode :
              (compactNumericVerifierStep^[1])
                  ((((compactListedProofTokens
                          (.exs Gamma formula witness premise) ++ proofSuffix,
                        compactStructuralCertificateTokens
                            (.unary premiseCertificate) ++
                          certificateSuffix),
                      (compactNumericParseTask :: restTasks, values)),
                    none)) =
                (((compactListedProofTokens premise ++ proofSuffix,
                    compactStructuralCertificateTokens premiseCertificate ++
                      certificateSuffix),
                  (compactNumericParseTask ::
                    compactNumericCombineTask 6 fields :: restTasks,
                    values)), none) := by
            simp [fields, compactListedProofNodeExpectedFields,
              compactStructuralCertificateNodeExpected,
              compactNumericNodeFieldsSuffix,
              compactNumericNodeTransition]
          have hpremise := ih premiseCertificate proofSuffix
            certificateSuffix
            (compactNumericCombineTask 6 fields :: restTasks)
            values hshape
          have hall := compactNumericVerifier_iterate_unary_failure
            hnode hpremise
          simpa [compactNumericTreeTaskSteps] using hall
      | binary leftCertificate rightCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.exs Gamma formula witness premise)
            (.binary leftCertificate rightCertificate)
            proofSuffix certificateSuffix restTasks values (by rfl)
  | wk Gamma premise ih =>
      cases certificate with
      | leaf =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.wk Gamma premise) .leaf proofSuffix certificateSuffix
            restTasks values (by rfl)
      | axiomCert paCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.wk Gamma premise) (.axiomCert paCertificate)
            proofSuffix certificateSuffix restTasks values (by rfl)
      | unary premiseCertificate =>
          let fields := (compactListedProofNodeExpectedFields
            (.wk Gamma premise) proofSuffix).2
          have hnode :
              (compactNumericVerifierStep^[1])
                  ((((compactListedProofTokens (.wk Gamma premise) ++
                          proofSuffix,
                        compactStructuralCertificateTokens
                            (.unary premiseCertificate) ++
                          certificateSuffix),
                      (compactNumericParseTask :: restTasks, values)),
                    none)) =
                (((compactListedProofTokens premise ++ proofSuffix,
                    compactStructuralCertificateTokens premiseCertificate ++
                      certificateSuffix),
                  (compactNumericParseTask ::
                    compactNumericCombineTask 7 fields :: restTasks,
                    values)), none) := by
            simp [fields, compactListedProofNodeExpectedFields,
              compactStructuralCertificateNodeExpected,
              compactNumericNodeFieldsSuffix,
              compactNumericNodeTransition]
          have hpremise := ih premiseCertificate proofSuffix
            certificateSuffix
            (compactNumericCombineTask 7 fields :: restTasks)
            values hshape
          have hall := compactNumericVerifier_iterate_unary_failure
            hnode hpremise
          simpa [compactNumericTreeTaskSteps] using hall
      | binary leftCertificate rightCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.wk Gamma premise) (.binary leftCertificate rightCertificate)
            proofSuffix certificateSuffix restTasks values (by rfl)
  | shift Gamma premise ih =>
      cases certificate with
      | leaf =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.shift Gamma premise) .leaf proofSuffix certificateSuffix
            restTasks values (by rfl)
      | axiomCert paCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.shift Gamma premise) (.axiomCert paCertificate)
            proofSuffix certificateSuffix restTasks values (by rfl)
      | unary premiseCertificate =>
          let fields := (compactListedProofNodeExpectedFields
            (.shift Gamma premise) proofSuffix).2
          have hnode :
              (compactNumericVerifierStep^[1])
                  ((((compactListedProofTokens (.shift Gamma premise) ++
                          proofSuffix,
                        compactStructuralCertificateTokens
                            (.unary premiseCertificate) ++
                          certificateSuffix),
                      (compactNumericParseTask :: restTasks, values)),
                    none)) =
                (((compactListedProofTokens premise ++ proofSuffix,
                    compactStructuralCertificateTokens premiseCertificate ++
                      certificateSuffix),
                  (compactNumericParseTask ::
                    compactNumericCombineTask 8 fields :: restTasks,
                    values)), none) := by
            simp [fields, compactListedProofNodeExpectedFields,
              compactStructuralCertificateNodeExpected,
              compactNumericNodeFieldsSuffix,
              compactNumericNodeTransition]
          have hpremise := ih premiseCertificate proofSuffix
            certificateSuffix
            (compactNumericCombineTask 8 fields :: restTasks)
            values hshape
          have hall := compactNumericVerifier_iterate_unary_failure
            hnode hpremise
          simpa [compactNumericTreeTaskSteps] using hall
      | binary leftCertificate rightCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.shift Gamma premise)
            (.binary leftCertificate rightCertificate)
            proofSuffix certificateSuffix restTasks values (by rfl)
  | cut Gamma formula left right ihLeft ihRight =>
      cases certificate with
      | leaf =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.cut Gamma formula left right) .leaf proofSuffix
            certificateSuffix restTasks values (by rfl)
      | axiomCert paCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.cut Gamma formula left right) (.axiomCert paCertificate)
            proofSuffix certificateSuffix restTasks values (by rfl)
      | unary premiseCertificate =>
          exact compactNumericTreeTask_root_mismatch_failure
            (.cut Gamma formula left right) (.unary premiseCertificate)
            proofSuffix certificateSuffix restTasks values (by rfl)
      | binary leftCertificate rightCertificate =>
          let fields := (compactListedProofNodeExpectedFields
            (.cut Gamma formula left right) proofSuffix).2
          let leftResult : CompactNumericChildResult :=
            (arithmeticPropositionTokenValues left.conclusionList,
              (listedCertificateValidTrace left leftCertificate).1)
          have hnode :
              (compactNumericVerifierStep^[1])
                  ((((compactListedProofTokens
                          (.cut Gamma formula left right) ++ proofSuffix,
                        compactStructuralCertificateTokens
                            (.binary leftCertificate rightCertificate) ++
                          certificateSuffix),
                      (compactNumericParseTask :: restTasks, values)),
                    none)) =
                (((compactListedProofTokens left ++
                      compactListedProofTokens right ++ proofSuffix,
                    compactStructuralCertificateTokens leftCertificate ++
                      compactStructuralCertificateTokens rightCertificate ++
                      certificateSuffix),
                  (compactNumericParseTask :: compactNumericParseTask ::
                    compactNumericCombineTask 9 fields :: restTasks,
                    values)), none) := by
            simp [fields, compactListedProofNodeExpectedFields,
              compactStructuralCertificateNodeExpected,
              compactNumericNodeFieldsSuffix,
              compactNumericNodeTransition, List.append_assoc]
          cases hleftShape :
              compactNumericTreeCertificateShapeMatches
                left leftCertificate with
          | false =>
              have hleftFailure := ihLeft leftCertificate
                (compactListedProofTokens right ++ proofSuffix)
                (compactStructuralCertificateTokens rightCertificate ++
                  certificateSuffix)
                (compactNumericParseTask ::
                  compactNumericCombineTask 9 fields :: restTasks)
                values hleftShape
              have hall :=
                compactNumericVerifier_iterate_binary_left_failure
                  (rightSteps := compactNumericTreeTaskSteps
                    right rightCertificate) hnode
                  (by simpa [List.append_assoc] using hleftFailure)
              simpa [compactNumericTreeTaskSteps] using hall
          | true =>
              have hrightShape :
                  compactNumericTreeCertificateShapeMatches
                    right rightCertificate = false := by
                simpa [compactNumericTreeCertificateShapeMatches,
                  hleftShape] using hshape
              have hleftSuccess :=
                compactNumericTreeTask_execute_of_shape left leftCertificate
                  (compactListedProofTokens right ++ proofSuffix)
                  (compactStructuralCertificateTokens rightCertificate ++
                    certificateSuffix)
                  (compactNumericParseTask ::
                    compactNumericCombineTask 9 fields :: restTasks)
                  values hleftShape
              have hrightFailure := ihRight rightCertificate proofSuffix
                certificateSuffix
                (compactNumericCombineTask 9 fields :: restTasks)
                (leftResult :: values) hrightShape
              have hall :=
                compactNumericVerifier_iterate_binary_right_failure hnode
                  (by
                    simpa [List.append_assoc,
                      compactNumericTreeTaskSuccessState, leftResult] using
                      hleftSuccess)
                  hrightFailure
              simpa [compactNumericTreeTaskSteps] using hall

theorem compactNumericTreeTaskSteps_le_two_mul_proofTokenLength
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    compactNumericTreeTaskSteps tree certificate <=
      2 * (compactListedProofTokens tree).length := by
  induction tree generalizing certificate with
  | closed Gamma formula =>
      cases certificate <;>
        simp [compactNumericTreeTaskSteps, compactListedProofTokens] <;>
        omega
  | axm Gamma sentence =>
      cases certificate <;>
        simp [compactNumericTreeTaskSteps, compactListedProofTokens] <;>
        omega
  | verum Gamma =>
      cases certificate <;>
        simp [compactNumericTreeTaskSteps, compactListedProofTokens] <;>
        omega
  | and Gamma leftFormula rightFormula left right ihLeft ihRight =>
      cases certificate with
      | leaf | axiomCert | unary =>
          simp [compactNumericTreeTaskSteps, compactListedProofTokens] <;>
            omega
      | binary leftCertificate rightCertificate =>
          have hleft := ihLeft leftCertificate
          have hright := ihRight rightCertificate
          simp only [compactNumericTreeTaskSteps, compactListedProofTokens,
            List.length_cons, List.length_append]
          omega
  | or Gamma leftFormula rightFormula premise ih =>
      cases certificate with
      | leaf | axiomCert | binary =>
          simp [compactNumericTreeTaskSteps, compactListedProofTokens] <;>
            omega
      | unary premiseCertificate =>
          have hpremise := ih premiseCertificate
          simp only [compactNumericTreeTaskSteps, compactListedProofTokens,
            List.length_cons, List.length_append]
          omega
  | all Gamma formula premise ih =>
      cases certificate with
      | leaf | axiomCert | binary =>
          simp [compactNumericTreeTaskSteps, compactListedProofTokens] <;>
            omega
      | unary premiseCertificate =>
          have hpremise := ih premiseCertificate
          simp only [compactNumericTreeTaskSteps, compactListedProofTokens,
            List.length_cons, List.length_append]
          omega
  | exs Gamma formula witness premise ih =>
      cases certificate with
      | leaf | axiomCert | binary =>
          simp [compactNumericTreeTaskSteps, compactListedProofTokens] <;>
            omega
      | unary premiseCertificate =>
          have hpremise := ih premiseCertificate
          simp only [compactNumericTreeTaskSteps, compactListedProofTokens,
            List.length_cons, List.length_append]
          omega
  | wk Gamma premise ih =>
      cases certificate with
      | leaf | axiomCert | binary =>
          simp [compactNumericTreeTaskSteps, compactListedProofTokens] <;>
            omega
      | unary premiseCertificate =>
          have hpremise := ih premiseCertificate
          simp only [compactNumericTreeTaskSteps, compactListedProofTokens,
            List.length_cons, List.length_append]
          omega
  | shift Gamma premise ih =>
      cases certificate with
      | leaf | axiomCert | binary =>
          simp [compactNumericTreeTaskSteps, compactListedProofTokens] <;>
            omega
      | unary premiseCertificate =>
          have hpremise := ih premiseCertificate
          simp only [compactNumericTreeTaskSteps, compactListedProofTokens,
            List.length_cons, List.length_append]
          omega
  | cut Gamma formula left right ihLeft ihRight =>
      cases certificate with
      | leaf | axiomCert | unary =>
          simp [compactNumericTreeTaskSteps, compactListedProofTokens] <;>
            omega
      | binary leftCertificate rightCertificate =>
          have hleft := ihLeft leftCertificate
          have hright := ihRight rightCertificate
          simp only [compactNumericTreeTaskSteps, compactListedProofTokens,
            List.length_cons, List.length_append]
          omega

theorem compactNumericTreeTaskSteps_add_one_le_fuel
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    compactNumericTreeTaskSteps tree certificate + 1 <=
      compactNumericVerifierFuelBound
        (compactListedProofTokens tree)
        (compactStructuralCertificateTokens certificate) := by
  have hsteps :=
    compactNumericTreeTaskSteps_le_two_mul_proofTokenLength
      tree certificate
  simp only [compactNumericVerifierFuelBound]
  omega

theorem listedCertificateValidTrace_result_false_of_shape_mismatch
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hshape :
      compactNumericTreeCertificateShapeMatches tree certificate = false) :
    (listedCertificateValidTrace tree certificate).1 = false := by
  induction tree generalizing certificate with
  | closed Gamma formula =>
      cases certificate <;>
        simp_all [compactNumericTreeCertificateShapeMatches,
          listedCertificateValidTrace]
  | axm Gamma sentence =>
      cases certificate <;>
        simp_all [compactNumericTreeCertificateShapeMatches,
          listedCertificateValidTrace]
  | verum Gamma =>
      cases certificate <;>
        simp_all [compactNumericTreeCertificateShapeMatches,
          listedCertificateValidTrace]
  | and Gamma leftFormula rightFormula left right ihLeft ihRight =>
      cases certificate with
      | leaf | axiomCert | unary =>
          simp [listedCertificateValidTrace]
      | binary leftCertificate rightCertificate =>
          cases hleftShape :
              compactNumericTreeCertificateShapeMatches
                left leftCertificate with
          | false =>
              have hleftTrace := ihLeft leftCertificate hleftShape
              simp [listedCertificateValidTrace, traceAnd, hleftTrace]
          | true =>
              have hrightShape :
                  compactNumericTreeCertificateShapeMatches
                    right rightCertificate = false := by
                simpa [compactNumericTreeCertificateShapeMatches,
                  hleftShape] using hshape
              have hrightTrace := ihRight rightCertificate hrightShape
              simp [listedCertificateValidTrace, traceAnd, hrightTrace]
  | or Gamma leftFormula rightFormula premise ih =>
      cases certificate with
      | leaf | axiomCert | binary =>
          simp [listedCertificateValidTrace]
      | unary premiseCertificate =>
          have hpremise := ih premiseCertificate hshape
          simp [listedCertificateValidTrace, traceAnd, hpremise]
  | all Gamma formula premise ih =>
      cases certificate with
      | leaf | axiomCert | binary =>
          simp [listedCertificateValidTrace]
      | unary premiseCertificate =>
          have hpremise := ih premiseCertificate hshape
          simp [listedCertificateValidTrace, traceAnd, hpremise]
  | exs Gamma formula witness premise ih =>
      cases certificate with
      | leaf | axiomCert | binary =>
          simp [listedCertificateValidTrace]
      | unary premiseCertificate =>
          have hpremise := ih premiseCertificate hshape
          simp [listedCertificateValidTrace, traceAnd, hpremise]
  | wk Gamma premise ih =>
      cases certificate with
      | leaf | axiomCert | binary =>
          simp [listedCertificateValidTrace]
      | unary premiseCertificate =>
          have hpremise := ih premiseCertificate hshape
          simp [listedCertificateValidTrace, traceAnd, hpremise]
  | shift Gamma premise ih =>
      cases certificate with
      | leaf | axiomCert | binary =>
          simp [listedCertificateValidTrace]
      | unary premiseCertificate =>
          have hpremise := ih premiseCertificate hshape
          simp [listedCertificateValidTrace, traceAnd, hpremise]
  | cut Gamma formula left right ihLeft ihRight =>
      cases certificate with
      | leaf | axiomCert | unary =>
          simp [listedCertificateValidTrace]
      | binary leftCertificate rightCertificate =>
          cases hleftShape :
              compactNumericTreeCertificateShapeMatches
                left leftCertificate with
          | false =>
              have hleftTrace := ihLeft leftCertificate hleftShape
              simp [listedCertificateValidTrace, traceAnd, hleftTrace]
          | true =>
              have hrightShape :
                  compactNumericTreeCertificateShapeMatches
                    right rightCertificate = false := by
                simpa [compactNumericTreeCertificateShapeMatches,
                  hleftShape] using hshape
              have hrightTrace := ihRight rightCertificate hrightShape
              simp [listedCertificateValidTrace, traceAnd, hrightTrace]

def compactNumericTreeFinalPayload
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    CompactNumericRunningPayload :=
  (([], []),
    ([],
      [(arithmeticPropositionTokenValues tree.conclusionList,
        (listedCertificateValidTrace tree certificate).1)]))

theorem compactNumericVerifierStep_finish_canonical
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    compactNumericVerifierStep
        (compactNumericTreeTaskSuccessState tree certificate
          [] [] [] []) =
      (compactNumericTreeFinalPayload tree certificate,
        some (listedCertificateValidTrace tree certificate).1) := by
  simp [compactNumericTreeTaskSuccessState,
    compactNumericTreeFinalPayload,
    compactNumericVerifierStep, compactNumericRunningStep,
    compactNumericFinishState]

theorem compactNumericVerifierResult_canonical
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    compactNumericVerifierResult
        (compactListedProofTokens tree)
        (compactStructuralCertificateTokens certificate) =
      (listedCertificateValidTrace tree certificate).1 := by
  cases hshape :
      compactNumericTreeCertificateShapeMatches tree certificate with
  | false =>
      rcases compactNumericTreeTask_failure_of_shape tree certificate
          [] [] [] [] hshape with ⟨payload, hfailure⟩
      have hfailure' :
          (compactNumericVerifierStep^[
              compactNumericTreeTaskSteps tree certificate])
              (compactNumericVerifierInitialState
                (compactListedProofTokens tree)
                (compactStructuralCertificateTokens certificate)) =
            (payload, some false) := by
        simpa [compactNumericVerifierInitialState] using hfailure
      have hfuelPlus := compactNumericTreeTaskSteps_add_one_le_fuel
        tree certificate
      have hfuel :
          compactNumericTreeTaskSteps tree certificate <=
            compactNumericVerifierFuelBound
              (compactListedProofTokens tree)
              (compactStructuralCertificateTokens certificate) := by
        omega
      obtain ⟨extra, hfuelEq⟩ := exists_add_of_le hfuel
      have hrun :
          (compactNumericVerifierStep^[
              compactNumericVerifierFuelBound
                (compactListedProofTokens tree)
                (compactStructuralCertificateTokens certificate)])
              (compactNumericVerifierInitialState
                (compactListedProofTokens tree)
                (compactStructuralCertificateTokens certificate)) =
            (payload, some false) := by
        rw [hfuelEq]
        exact compactNumericVerifier_iterate_trans hfailure'
          (compactNumericVerifierStep_iterate_halted extra payload false)
      have htrace :=
        listedCertificateValidTrace_result_false_of_shape_mismatch
          tree certificate hshape
      simp [compactNumericVerifierResult, compactNumericVerifierRun,
        hrun, htrace]
  | true =>
      have htask := compactNumericTreeTask_execute_of_shape tree certificate
        [] [] [] [] hshape
      have htask' :
          (compactNumericVerifierStep^[
              compactNumericTreeTaskSteps tree certificate])
              (compactNumericVerifierInitialState
                (compactListedProofTokens tree)
                (compactStructuralCertificateTokens certificate)) =
            compactNumericTreeTaskSuccessState tree certificate
              [] [] [] [] := by
        simpa [compactNumericVerifierInitialState] using htask
      have hfinish :
          (compactNumericVerifierStep^[1])
              (compactNumericTreeTaskSuccessState tree certificate
                [] [] [] []) =
            (compactNumericTreeFinalPayload tree certificate,
              some (listedCertificateValidTrace tree certificate).1) := by
        simpa only [Function.iterate_one] using
          compactNumericVerifierStep_finish_canonical tree certificate
      have hused := compactNumericVerifier_iterate_trans htask' hfinish
      have hfuel := compactNumericTreeTaskSteps_add_one_le_fuel
        tree certificate
      obtain ⟨extra, hfuelEq⟩ := exists_add_of_le hfuel
      have hrun :
          (compactNumericVerifierStep^[
              compactNumericVerifierFuelBound
                (compactListedProofTokens tree)
                (compactStructuralCertificateTokens certificate)])
              (compactNumericVerifierInitialState
                (compactListedProofTokens tree)
                (compactStructuralCertificateTokens certificate)) =
            (compactNumericTreeFinalPayload tree certificate,
              some (listedCertificateValidTrace tree certificate).1) := by
        rw [hfuelEq]
        exact compactNumericVerifier_iterate_trans hused
          (compactNumericVerifierStep_iterate_halted extra
            (compactNumericTreeFinalPayload tree certificate)
            (listedCertificateValidTrace tree certificate).1)
      simp [compactNumericVerifierResult, compactNumericVerifierRun, hrun]

#print axioms compactNumericNodeTransition_primrec
#print axioms compactNumericCombineTransition_primrec
#print axioms compactNumericParsePayload_primrec
#print axioms compactNumericParseState_primrec
#print axioms compactNumericCombineState_primrec
#print axioms compactNumericFinishState_primrec
#print axioms compactNumericRunningStep_primrec
#print axioms compactNumericVerifierStep_primrec
#print axioms compactNumericVerifierFuelBound_primrec
#print axioms compactNumericVerifierInitialState_primrec
#print axioms compactNumericVerifierRun_primrec
#print axioms compactNumericVerifierResult_primrec
#print axioms compactNumericVerifierResult_canonical

end FoundationCompactNumericListedTaskMachine
