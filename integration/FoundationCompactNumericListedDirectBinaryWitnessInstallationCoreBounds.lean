import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-!
# Fixed arity-two hybrid witness installation core

This isolates the composition of the transparent witness builder with the
fully fixed arity-two envelope.  Domain-specific callers only supply the real
terminal, its payload bound, the open-body code bound, and the context bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectBinaryWitnessInstallationCoreBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

theorem installBinaryWitness_structuralPayloadBound_le_fullyFixed
    (valuation : Nat -> Nat)
    (bound numericBound bodyCodeBound terminalResource : Nat)
    (body : ArithmeticSemiformula Nat 2)
    (values : Fin 2 -> Nat)
    (hvalues : forall coordinate, values coordinate <= bound)
    (hbound : bound <= numericBound)
    (hbody :
      (FoundationSuccinctFiniteConsistencyTarget.binaryFormulaCode body).length <=
        bodyCodeBound)
    (hcontext :
      formulaCodeSum
        (valuationContext body.freeVariables valuation) <= 0)
    (terminal :
      CheckedHybridValuationBoundedFormulaCertificate valuation
        (body ⇜ fun coordinate =>
          FoundationCompactPABinaryNumeralAddition.shortBinaryNumeralTerm
            (values coordinate)))
    (hterminal :
      hybridFormulaStructuralPayloadBound terminal <= terminalResource) :
    hybridFormulaStructuralPayloadBound
        (buildExplicitBoundedWitnessHybridCertificate bound body values hvalues
          terminal) <=
      explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02 0
        numericBound bodyCodeBound terminalResource := by
  have hbuilt :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      bound body values hvalues terminal terminalResource hterminal
  have hfixed :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity02
      valuation 0 bound numericBound bodyCodeBound body values hvalues hbound
      hbody hcontext (le_refl terminalResource)
  exact hbuilt.trans hfixed

#print axioms installBinaryWitness_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectBinaryWitnessInstallationCoreBounds
