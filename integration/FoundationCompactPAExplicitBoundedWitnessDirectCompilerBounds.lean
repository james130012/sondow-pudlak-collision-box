import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompiler

/-!
# Structural bound for the direct bounded-witness compiler

The recursive envelope starts with an independently established terminal
resource and adds only the audited one-layer constructor costs.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option Elab.async false

namespace FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler

/-- Recursive structural envelope for a complete bounded witness vector.  The
terminal resource is advanced only by explicit one-layer constructor costs. -/
def explicitBoundedWitnessDirectPayloadEnvelope :
    {k : Nat} ->
    (valuation : Nat -> Nat) ->
    (bound : Nat) ->
    (body : ArithmeticSemiformula Nat k) ->
    (values : Fin k -> Nat) ->
    (terminalResource : Nat) -> Nat
  | 0, _, _, _, _, terminalResource => terminalResource
  | k + 1, valuation, bound, body, values, terminalResource =>
      let tailValues : Fin k -> Nat := fun index => values index.succ
      explicitBoundedWitnessDirectPayloadEnvelope valuation bound
        (body.bexsLTSucc
          (closedShift k (shortBinaryNumeralTerm bound)))
        tailValues
        (terminalResource +
          explicitBoundedWitnessDirectHeadPayloadEnvelope
            valuation bound body values)

/-- A real context proof together with its internally verified structural
payload budget.  The formula and resource are data fields rather than
recursive type indices, which keeps kernel reduction bounded. -/
structure ExplicitBoundedWitnessDirectCompilation
    (valuation : Nat -> Nat) where
  formula : ValuationFormula
  proof : CertifiedPAContextProof
    (valuationContext formula.freeVariables valuation) formula
  payloadResource : Nat
  payloadLength_le : proof.payloadLength ≤ payloadResource

/-- Quantitative compiler.  The bound proof is constructed in the same
recursion as the PA proof, so no generated proof length is accepted as an
input. -/
noncomputable def compileExplicitBoundedWitnessDirectWithResource :
    {valuation : Nat -> Nat} -> {k : Nat} ->
    (bound : Nat) ->
    (body : ArithmeticSemiformula Nat k) ->
    (values : Fin k -> Nat) ->
    (hbounds : ∀ index, values index ≤ bound) ->
    (terminalResource : Nat) ->
    (terminal : CertifiedPAContextProof
      (valuationContext
        (body ⇜ fun index =>
          shortBinaryNumeralTerm (values index)).freeVariables valuation)
      (body ⇜ fun index => shortBinaryNumeralTerm (values index))) ->
    terminal.payloadLength ≤ terminalResource ->
    ExplicitBoundedWitnessDirectCompilation valuation
  | valuation, 0, bound, body, values, hbounds,
      terminalResource, terminal, hterminal => by
      have hformula :
          (body ⇜ fun index => shortBinaryNumeralTerm (values index)) =
            body := by simp
      let atSourceContext : CertifiedPAContextProof
          (valuationContext
            (body ⇜ fun index =>
              shortBinaryNumeralTerm (values index)).freeVariables valuation)
          body :=
        CertifiedPAContextProof.cast hformula terminal
      have hcontext :
          valuationContext
              (body ⇜ fun index =>
                shortBinaryNumeralTerm (values index)).freeVariables valuation =
            valuationContext body.freeVariables valuation :=
        congrArg (fun formula =>
          valuationContext formula.freeVariables valuation) hformula
      let baseProof := CertifiedPAContextProof.castContext hcontext
        atSourceContext
      have hbasePayload : baseProof.payloadLength = terminal.payloadLength := by
        calc
          baseProof.payloadLength = atSourceContext.payloadLength :=
            CertifiedPAContextProof.castContext_payloadLength
              hcontext atSourceContext
          _ = terminal.payloadLength :=
            CertifiedPAContextProof.cast_payloadLength hformula terminal
      exact
        { formula := body
          proof := baseProof
          payloadResource := terminalResource
          payloadLength_le := hbasePayload ▸ hterminal }
  | valuation, k + 1, bound, body, values, hbounds,
      terminalResource, terminal, hterminal => by
      let tailValues : Fin k -> Nat := fun index => values index.succ
      let recursiveBody := body.bexsLTSucc
        (closedShift k (shortBinaryNumeralTerm bound))
      let recursiveTerminal : CertifiedPAContextProof
          (valuationContext
            (recursiveBody ⇜
              (fun index : Fin k =>
                shortBinaryNumeralTerm (tailValues index))).freeVariables
            valuation)
          (recursiveBody ⇜
            (fun index : Fin k =>
              shortBinaryNumeralTerm (tailValues index))) :=
        advanceExplicitBoundedWitnessDirectTerminal
          bound body values (hbounds 0) terminal
      have hrecursive : recursiveTerminal.payloadLength ≤
          terminalResource +
            explicitBoundedWitnessDirectHeadPayloadEnvelope
              valuation bound body values := by
        exact advanceExplicitBoundedWitnessDirectTerminal_payloadLength_le
          (terminalResource := terminalResource)
          bound body values (hbounds 0) terminal hterminal
      exact compileExplicitBoundedWitnessDirectWithResource bound
        recursiveBody tailValues (fun index => hbounds index.succ)
        (terminalResource +
          explicitBoundedWitnessDirectHeadPayloadEnvelope
            valuation bound body values)
        recursiveTerminal hrecursive

#print axioms explicitBoundedWitnessDirectPayloadEnvelope
#print axioms compileExplicitBoundedWitnessDirectWithResource

end FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
