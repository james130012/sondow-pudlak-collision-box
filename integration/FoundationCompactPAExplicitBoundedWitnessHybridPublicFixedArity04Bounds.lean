import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedBounds

/-!
# Fixed public payload bound for four explicit bounded witnesses

`NatListSameRows` has exactly four bounded row-entry witnesses.  This file
unrolls those four steps instead of elaborating a dependent recursion over an
arbitrary arity.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity04Bounds

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

private theorem head_le_fixed_of_terminal
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

private theorem recursive_body_code_le_fixed
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

private theorem recursive_body_context_le
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

def explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity04
    (contextCodeBound numericBound bodyCodeBound terminalResource : Nat) :
    Nat :=
  let bodyCode03 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 3 numericBound
      bodyCodeBound
  let bodyCode02 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 2 numericBound
      bodyCode03
  let bodyCode01 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 numericBound
      bodyCode02
  terminalResource +
    explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial
      contextCodeBound numericBound bodyCodeBound +
    explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial
      contextCodeBound numericBound bodyCode03 +
    explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial
      contextCodeBound numericBound bodyCode02 +
    explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial
      contextCodeBound numericBound bodyCode01

theorem
    explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial_mono_context
    {smallContext largeContext numericBound bodyCodeBound : Nat}
    (hcontext : smallContext <= largeContext) :
    explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial smallContext
        numericBound bodyCodeBound <=
      explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial largeContext
        numericBound bodyCodeBound := by
  have hdirect :=
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicScalarBounds.explicitBoundedWitnessDirectHeadPublicPayloadPolynomial_mono_context
      hcontext numericBound bodyCodeBound
  unfold explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial
  omega

theorem
    explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity04_mono_context
    {smallContext largeContext numericBound bodyCodeBound terminalResource :
      Nat}
    (hcontext : smallContext <= largeContext) :
    explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity04 smallContext
        numericBound bodyCodeBound terminalResource <=
      explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity04 largeContext
        numericBound bodyCodeBound terminalResource := by
  let bodyCode03 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 3 numericBound
      bodyCodeBound
  let bodyCode02 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 2 numericBound
      bodyCode03
  let bodyCode01 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 numericBound
      bodyCode02
  have h04 :=
    explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial_mono_context
      (numericBound := numericBound) (bodyCodeBound := bodyCodeBound) hcontext
  have h03 :=
    explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial_mono_context
      (numericBound := numericBound) (bodyCodeBound := bodyCode03) hcontext
  have h02 :=
    explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial_mono_context
      (numericBound := numericBound) (bodyCodeBound := bodyCode02) hcontext
  have h01 :=
    explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial_mono_context
      (numericBound := numericBound) (bodyCodeBound := bodyCode01) hcontext
  simpa only [explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity04,
    bodyCode03, bodyCode02, bodyCode01] using
    Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add_left h04 terminalResource)
          h03)
        h02)
      h01

theorem
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity04
    (valuation : Nat -> Nat)
    (contextCodeBound bound numericBound bodyCodeBound : Nat)
    (body04 : ArithmeticSemiformula Nat 4)
    (values04 : Fin 4 -> Nat)
    {terminalSmall terminalLarge : Nat}
    (hvalues04 : forall index, values04 index <= bound)
    (hbound : bound <= numericBound)
    (hbody04 : (binaryFormulaCode body04).length <= bodyCodeBound)
    (hcontext04 : formulaCodeSum
      (valuationContext body04.freeVariables valuation) <= contextCodeBound)
    (hterminal : terminalSmall <= terminalLarge) :
    explicitBoundedWitnessHybridStructuralPayloadEnvelope valuation bound
        body04 values04 terminalSmall <=
      explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity04
        contextCodeBound numericBound bodyCodeBound terminalLarge := by
  let body03 : ArithmeticSemiformula Nat 3 :=
    body04.bexsLTSucc
      (closedShift 3 (shortBinaryNumeralTerm bound))
  let body02 : ArithmeticSemiformula Nat 2 :=
    body03.bexsLTSucc
      (closedShift 2 (shortBinaryNumeralTerm bound))
  let body01 : ArithmeticSemiformula Nat 1 :=
    body02.bexsLTSucc
      (closedShift 1 (shortBinaryNumeralTerm bound))
  let values03 : Fin 3 -> Nat := fun index => values04 index.succ
  let values02 : Fin 2 -> Nat := fun index => values03 index.succ
  let values01 : Fin 1 -> Nat := fun index => values02 index.succ
  let bodyCode03 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 3 numericBound
      bodyCodeBound
  let bodyCode02 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 2 numericBound
      bodyCode03
  let bodyCode01 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 numericBound
      bodyCode02
  let resource01 :=
    terminalLarge +
      explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial
        contextCodeBound numericBound bodyCodeBound
  let resource02 :=
    resource01 +
      explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial
        contextCodeBound numericBound bodyCode03
  let resource03 :=
    resource02 +
      explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial
        contextCodeBound numericBound bodyCode02
  let resource04 :=
    resource03 +
      explicitBoundedWitnessHybridHeadFullyFixedPayloadPolynomial
        contextCodeBound numericBound bodyCode01
  have hvalues03 : forall index, values03 index <= bound :=
    fun index => hvalues04 index.succ
  have hvalues02 : forall index, values02 index <= bound :=
    fun index => hvalues03 index.succ
  have hvalues01 : forall index, values01 index <= bound :=
    fun index => hvalues02 index.succ
  have hbody03 : (binaryFormulaCode body03).length <= bodyCode03 := by
    exact recursive_body_code_le_fixed body04 hbound hbody04
  have hbody02 : (binaryFormulaCode body02).length <= bodyCode02 := by
    exact recursive_body_code_le_fixed body03 hbound hbody03
  have hbody01 : (binaryFormulaCode body01).length <= bodyCode01 := by
    exact recursive_body_code_le_fixed body02 hbound hbody02
  have hcontext03 :
      formulaCodeSum (valuationContext body03.freeVariables valuation) <=
        contextCodeBound := by
    exact recursive_body_context_le valuation body04 hcontext04
  have hcontext02 :
      formulaCodeSum (valuationContext body02.freeVariables valuation) <=
        contextCodeBound := by
    exact recursive_body_context_le valuation body03 hcontext03
  have hcontext01 :
      formulaCodeSum (valuationContext body01.freeVariables valuation) <=
        contextCodeBound := by
    exact recursive_body_context_le valuation body02 hcontext02
  have hhead04 :
      explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope valuation bound
          body04 values04 terminalSmall <= resource01 := by
    exact head_le_fixed_of_terminal valuation contextCodeBound bound
      numericBound bodyCodeBound body04 values04 hvalues04 hbound hbody04
      hcontext04 hterminal
  have hhead03 :
      explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope valuation bound
          body03 values03
          (explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope valuation
            bound body04 values04 terminalSmall) <= resource02 := by
    exact head_le_fixed_of_terminal valuation contextCodeBound bound
      numericBound bodyCode03 body03 values03 hvalues03 hbound hbody03
      hcontext03 hhead04
  have hhead02 :
      explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope valuation bound
          body02 values02
          (explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope valuation
            bound body03 values03
            (explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope valuation
              bound body04 values04 terminalSmall)) <= resource03 := by
    exact head_le_fixed_of_terminal valuation contextCodeBound bound
      numericBound bodyCode02 body02 values02 hvalues02 hbound hbody02
      hcontext02 hhead03
  have hhead01 :
      explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope valuation bound
          body01 values01
          (explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope valuation
            bound body02 values02
            (explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope valuation
              bound body03 values03
              (explicitBoundedWitnessHybridHeadStructuralPayloadEnvelope
                valuation bound body04 values04 terminalSmall))) <=
        resource04 := by
    exact head_le_fixed_of_terminal valuation contextCodeBound bound
      numericBound bodyCode01 body01 values01 hvalues01 hbound hbody01
      hcontext01 hhead02
  simpa only [explicitBoundedWitnessHybridStructuralPayloadEnvelope, body03,
    body02, body01, values03, values02, values01,
    explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity04,
    bodyCode03, bodyCode02, bodyCode01, resource01, resource02, resource03,
    resource04] using hhead01

#print axioms
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity04_mono_context
#print axioms
  explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity04

end FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity04Bounds
