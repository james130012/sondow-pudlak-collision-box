import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
import integration.FoundationCompactPAExplicitBoundedWitnessDirectHeadPayloadMonotonicity
import integration.FoundationCompactPAExplicitBoundedWitnessDirectRecursiveBodyMonotonicity

/-! # Direct bounded-witness compiler with separate formula and resource bounds -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactPAExplicitBoundedWitnessDirectPublicUniformResourceCompiler

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
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectHeadPayloadMonotonicity
open FoundationCompactPAExplicitBoundedWitnessDirectRecursiveBodyMonotonicity
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

noncomputable def
    compileExplicitBoundedWitnessDirectPublicWithUniformResource :
    {valuation : Nat -> Nat} -> {arity : Nat} ->
    (contextCodeBound formulaBound resourceBound bodyCodeBound : Nat) ->
    formulaBound <= resourceBound ->
    (body : ArithmeticSemiformula Nat arity) ->
    (values : Fin arity -> Nat) ->
    (hvalues : forall index, values index <= formulaBound) ->
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
  | valuation, 0, contextCodeBound, formulaBound, _resourceBound, bodyCodeBound,
      _hbound, body, values, hvalues, hbody, hcontext, terminalResource,
      terminal, hterminal => by
      exact compileExplicitBoundedWitnessDirectWithResource formulaBound body
        values hvalues terminalResource terminal hterminal
  | valuation, arity + 1, contextCodeBound, formulaBound, resourceBound,
      bodyCodeBound, hbound, body, values, hvalues, hbody, hcontext,
      terminalResource, terminal, hterminal => by
      let recursiveBody := body.bexsLTSucc
        (closedShift arity (shortBinaryNumeralTerm formulaBound))
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
        advanceExplicitBoundedWitnessDirectTerminal formulaBound body values
          (hvalues 0) terminal
      have hexact : recursiveTerminal.payloadLength <=
          terminalResource +
            explicitBoundedWitnessDirectHeadPayloadEnvelope valuation formulaBound
              body values := by
        exact advanceExplicitBoundedWitnessDirectTerminal_payloadLength_le
          (terminalResource := terminalResource) formulaBound body values
          (hvalues 0) terminal hterminal
      have hheadActual :=
        explicitBoundedWitnessDirectHeadPayloadEnvelope_le_public valuation
          contextCodeBound formulaBound bodyCodeBound body values hvalues hbody
          hcontext
      have hheadUniform :
          explicitBoundedWitnessDirectHeadPublicPayloadPolynomial contextCodeBound
              formulaBound bodyCodeBound <=
            explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
              contextCodeBound resourceBound bodyCodeBound :=
        explicitBoundedWitnessDirectHeadPublicPayloadPolynomial_mono
          contextCodeBound hbound (Nat.le_refl _)
      have hhead :
          explicitBoundedWitnessDirectHeadPayloadEnvelope valuation formulaBound
              body values <=
            explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
              contextCodeBound resourceBound bodyCodeBound :=
        hheadActual.trans hheadUniform
      have hpublic : recursiveTerminal.payloadLength <=
          terminalResource +
            explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
              contextCodeBound resourceBound bodyCodeBound :=
        hexact.trans (Nat.add_le_add_left hhead terminalResource)
      have hrecursiveBodyActual :
          (binaryFormulaCode recursiveBody).length <=
            explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope arity
              formulaBound bodyCodeBound :=
        explicitBoundedWitnessRecursiveBody_code_length_le_public formulaBound
          bodyCodeBound body hbody
      have hrecursiveBodyUniform :
          explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope arity formulaBound
              bodyCodeBound <=
            explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope arity
              resourceBound bodyCodeBound :=
        explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono arity hbound
          (Nat.le_refl _)
      have hrecursiveBody :
          (binaryFormulaCode recursiveBody).length <=
            explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope arity
              resourceBound bodyCodeBound :=
        hrecursiveBodyActual.trans hrecursiveBodyUniform
      have hrecursiveContext :
          formulaCodeSum
              (valuationContext recursiveBody.freeVariables valuation) <=
            contextCodeBound := by
        exact (formulaCodeSum_mono
          (valuationContext_mono valuation
            (explicitBoundedWitnessRecursiveBody_freeVariables_subset formulaBound
              body))).trans hcontext
      exact compileExplicitBoundedWitnessDirectPublicWithUniformResource
        contextCodeBound formulaBound resourceBound
        (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope arity resourceBound
          bodyCodeBound)
        hbound recursiveBody tailValues (fun index => hvalues index.succ)
        hrecursiveBody hrecursiveContext
        (terminalResource +
          explicitBoundedWitnessDirectHeadPublicPayloadPolynomial contextCodeBound
            resourceBound bodyCodeBound)
        recursiveTerminal hpublic

#print axioms compileExplicitBoundedWitnessDirectPublicWithUniformResource

end FoundationCompactPAExplicitBoundedWitnessDirectPublicUniformResourceCompiler
