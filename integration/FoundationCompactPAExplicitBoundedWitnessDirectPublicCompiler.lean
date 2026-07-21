import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds

/-!
# Direct bounded-witness compiler with a public scalar resource

The PA proof and its public resource bound are advanced in the same recursion.
The resource contains no concrete witness coordinate and no generated proof
payload.  Each successor step is justified by the audited exact head bound and
the public one-layer scalar theorem.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicScalarBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

noncomputable def compileExplicitBoundedWitnessDirectPublicWithResource :
    {valuation : Nat -> Nat} -> {arity : Nat} ->
    (contextCodeBound bound bodyCodeBound : Nat) ->
    (body : ArithmeticSemiformula Nat arity) ->
    (values : Fin arity -> Nat) ->
    (hvalues : forall index, values index <= bound) ->
    (binaryFormulaCode body).length <= bodyCodeBound ->
    formulaCodeSum (valuationContext body.freeVariables valuation) <=
      contextCodeBound ->
    (terminalResource : Nat) ->
    (terminal : CertifiedPAContextProof
      (valuationContext
        (body ⇜ fun index =>
          shortBinaryNumeralTerm (values index)).freeVariables valuation)
      (body ⇜ fun index => shortBinaryNumeralTerm (values index))) ->
    terminal.payloadLength <= terminalResource ->
    ExplicitBoundedWitnessDirectCompilation valuation
  | valuation, 0, contextCodeBound, bound, bodyCodeBound, body, values,
      hvalues, hbody, hcontext, terminalResource, terminal, hterminal => by
      exact compileExplicitBoundedWitnessDirectWithResource bound body values
        hvalues terminalResource terminal hterminal
  | valuation, arity + 1, contextCodeBound, bound, bodyCodeBound, body,
      values, hvalues, hbody, hcontext, terminalResource, terminal,
      hterminal => by
      let recursiveBody := body.bexsLTSucc
        (closedShift arity (shortBinaryNumeralTerm bound))
      let tailValues : Fin arity -> Nat := fun index => values index.succ
      let recursiveTerminal : CertifiedPAContextProof
          (valuationContext
            (recursiveBody ⇜
              (fun index : Fin arity =>
                shortBinaryNumeralTerm (tailValues index))).freeVariables
            valuation)
          (recursiveBody ⇜
            (fun index : Fin arity =>
              shortBinaryNumeralTerm (tailValues index))) :=
        advanceExplicitBoundedWitnessDirectTerminal
          bound body values (hvalues 0) terminal
      have hexact : recursiveTerminal.payloadLength <=
          terminalResource +
            explicitBoundedWitnessDirectHeadPayloadEnvelope
              valuation bound body values := by
        exact advanceExplicitBoundedWitnessDirectTerminal_payloadLength_le
          (terminalResource := terminalResource)
          bound body values (hvalues 0) terminal hterminal
      have hhead := explicitBoundedWitnessDirectHeadPayloadEnvelope_le_public
        valuation contextCodeBound bound bodyCodeBound body values hvalues
          hbody hcontext
      have hpublic : recursiveTerminal.payloadLength <=
          terminalResource +
            explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
              contextCodeBound bound bodyCodeBound :=
        hexact.trans (Nat.add_le_add_left hhead terminalResource)
      have hrecursiveBody :
          (binaryFormulaCode recursiveBody).length <=
            explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope
              arity bound bodyCodeBound :=
        explicitBoundedWitnessRecursiveBody_code_length_le_public
          bound bodyCodeBound body hbody
      have hrecursiveContext :
          formulaCodeSum
              (valuationContext recursiveBody.freeVariables valuation) <=
            contextCodeBound := by
        exact (formulaCodeSum_mono
          (valuationContext_mono valuation
            (explicitBoundedWitnessRecursiveBody_freeVariables_subset
              bound body))).trans hcontext
      exact compileExplicitBoundedWitnessDirectPublicWithResource
        contextCodeBound bound
        (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope
          arity bound bodyCodeBound)
        recursiveBody tailValues (fun index => hvalues index.succ)
        hrecursiveBody hrecursiveContext
        (terminalResource +
          explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
            contextCodeBound bound bodyCodeBound)
        recursiveTerminal hpublic

#print axioms compileExplicitBoundedWitnessDirectPublicWithResource

end FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
