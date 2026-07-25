import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedBounds

/-!
# Fixed public payload bound for two explicit bounded witnesses

This is the exact two-step counterpart of the audited arity-four expansion.
It is used by natural-list row lookup, whose two cursor witnesses are both
bounded by the same public numeric ceiling.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 80000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

private theorem head_le_fixed_of_terminal_arity02
    (valuation : Nat -> Nat) {arity : Nat}
    (contextCodeBound bound numericBound bodyCodeBound : Nat)
    (body : ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat)
    {terminalSmall terminalLarge : Nat}
    (hvalues : forall index, values index <= bound)
    (hbound : bound <= numericBound)
    (hbody : (binaryFormulaCode body).length <= bodyCodeBound)
    (hcontext : formulaCodeSum
      (valuationContext body.freeVariables valuation) <= contextCodeBound)
    (hterminal : terminalSmall <= terminalLarge) :
    explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope valuation bound
        body values terminalSmall <=
      terminalLarge +
        explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial
          contextCodeBound numericBound bodyCodeBound := by
  exact
    (explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope_mono
      valuation bound body values hterminal).trans
      (explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope_le_fullyFixed
        valuation contextCodeBound bound numericBound bodyCodeBound body
        values terminalLarge hvalues hbound hbody hcontext)

private theorem recursive_body_code_le_fixed_arity02
    {arity bound numericBound bodyCodeBound : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1))
    (hbound : bound <= numericBound)
    (hbody : (binaryFormulaCode body).length <= bodyCodeBound) :
    (binaryFormulaCode
      (body.bexsLTSucc
        (closedShift arity (shortBinaryNumeralTerm bound)))).length <=
      explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope arity numericBound
        bodyCodeBound := by
  exact
    (explicitBoundedWitnessRecursiveBody_code_length_le_public
      bound bodyCodeBound body hbody).trans
      (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_hybridFixed
        arity hbound (Nat.le_refl bodyCodeBound))

private theorem recursive_body_context_le_arity02
    (valuation : Nat -> Nat) {arity bound contextCodeBound : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1))
    (hcontext : formulaCodeSum
      (valuationContext body.freeVariables valuation) <= contextCodeBound) :
    formulaCodeSum
        (valuationContext
          (body.bexsLTSucc
            (closedShift arity
              (shortBinaryNumeralTerm bound))).freeVariables valuation) <=
      contextCodeBound := by
  exact
    (formulaCodeSum_mono
      (valuationContext_mono valuation
        (explicitBoundedWitnessRecursiveBody_freeVariables_subset
          bound body))).trans hcontext

def explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02
    (contextCodeBound numericBound bodyCodeBound terminalResource : Nat) : Nat :=
  let bodyCode01 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 numericBound
      bodyCodeBound
  terminalResource +
    explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial
      contextCodeBound numericBound bodyCodeBound +
    explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial
      contextCodeBound numericBound bodyCode01

theorem
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity02
    (valuation : Nat -> Nat)
    (contextCodeBound bound numericBound bodyCodeBound : Nat)
    (body02 : ArithmeticSemiformula Nat 2)
    (values02 : Fin 2 -> Nat)
    {terminalSmall terminalLarge : Nat}
    (hvalues02 : forall index, values02 index <= bound)
    (hbound : bound <= numericBound)
    (hbody02 : (binaryFormulaCode body02).length <= bodyCodeBound)
    (hcontext02 : formulaCodeSum
      (valuationContext body02.freeVariables valuation) <= contextCodeBound)
    (hterminal : terminalSmall <= terminalLarge) :
    explicitBoundedWitnessHybridStructuralPayloadEnvelope valuation bound
        body02 values02 terminalSmall <=
      explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02
        contextCodeBound numericBound bodyCodeBound terminalLarge := by
  let body01 : ArithmeticSemiformula Nat 1 :=
    body02.bexsLTSucc (closedShift 1 (shortBinaryNumeralTerm bound))
  let values01 : Fin 1 -> Nat := fun index => values02 index.succ
  let bodyCode01 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 numericBound
      bodyCodeBound
  let resource01 :=
    terminalLarge +
      explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial
        contextCodeBound numericBound bodyCodeBound
  let resource02 :=
    resource01 +
      explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial
        contextCodeBound numericBound bodyCode01
  have hvalues01 : forall index, values01 index <= bound :=
    fun index => hvalues02 index.succ
  have hbody01 : (binaryFormulaCode body01).length <= bodyCode01 :=
    recursive_body_code_le_fixed_arity02 body02 hbound hbody02
  have hcontext01 :
      formulaCodeSum (valuationContext body01.freeVariables valuation) <=
        contextCodeBound :=
    recursive_body_context_le_arity02 valuation body02 hcontext02
  have hhead02 :
      explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope valuation bound
          body02 values02 terminalSmall <= resource01 :=
    head_le_fixed_of_terminal_arity02 valuation contextCodeBound bound
      numericBound bodyCodeBound body02 values02 hvalues02 hbound hbody02
      hcontext02 hterminal
  have hhead01 :
      explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope valuation bound
          body01 values01
          (explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope valuation
            bound body02 values02 terminalSmall) <= resource02 :=
    head_le_fixed_of_terminal_arity02 valuation contextCodeBound bound
      numericBound bodyCode01 body01 values01 hvalues01 hbound hbody01
      hcontext01 hhead02
  simpa only [explicitBoundedWitnessHybridStructuralPayloadEnvelope, body01,
    values01, explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02,
    bodyCode01, resource01, resource02] using hhead01

#print axioms
  explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity02

end FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds
