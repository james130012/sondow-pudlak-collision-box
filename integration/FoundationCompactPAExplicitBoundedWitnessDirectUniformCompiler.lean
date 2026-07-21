import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds

/-!
# Direct bounded-witness compiler with an intrinsic uniform resource

The compiler pays the value-independent public cost at the same recursive step
that constructs each bounded existential witness.  No post-hoc comparison of
two dependent recursive envelopes is required.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPAExplicitBoundedWitnessDirectUniformCompiler

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

noncomputable def compileExplicitBoundedWitnessDirectUniformWithResource :
    {valuation : Nat -> Nat} -> {arity : Nat} ->
    (bound : Nat) ->
    (body : ArithmeticSemiformula Nat arity) ->
    (values : Fin arity -> Nat) ->
    (hvalues : forall index, values index <= bound) ->
    (terminalResource : Nat) ->
    (terminal : CertifiedPAContextProof
      (valuationContext
        (body ⇜ fun index =>
          shortBinaryNumeralTerm (values index)).freeVariables valuation)
      (body ⇜ fun index => shortBinaryNumeralTerm (values index))) ->
    terminal.payloadLength <= terminalResource ->
    ExplicitBoundedWitnessDirectCompilation valuation
  | valuation, 0, bound, body, values, hvalues,
      terminalResource, terminal, hterminal => by
      exact compileExplicitBoundedWitnessDirectWithResource bound body values
        hvalues terminalResource terminal hterminal
  | valuation, arity + 1, bound, body, values, hvalues,
      terminalResource, terminal, hterminal => by
      let tailValues : Fin arity -> Nat := fun index => values index.succ
      let recursiveBody := body.bexsLTSucc
        (closedShift arity (shortBinaryNumeralTerm bound))
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
      have hhead := explicitBoundedWitnessDirectHeadPayloadEnvelope_le_uniform
        valuation bound body values hvalues
      have huniform : recursiveTerminal.payloadLength <=
          terminalResource +
            explicitBoundedWitnessDirectHeadUniformPayloadPolynomial
              valuation bound body :=
        hexact.trans (Nat.add_le_add_left hhead terminalResource)
      exact compileExplicitBoundedWitnessDirectUniformWithResource bound
        recursiveBody tailValues (fun index => hvalues index.succ)
        (terminalResource +
          explicitBoundedWitnessDirectHeadUniformPayloadPolynomial
            valuation bound body)
        recursiveTerminal huniform

#print axioms compileExplicitBoundedWitnessDirectUniformWithResource

end FoundationCompactPAExplicitBoundedWitnessDirectUniformCompiler
