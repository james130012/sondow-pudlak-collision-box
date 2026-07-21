import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler

/-! # Fixed arity-nine coordinates for the public direct compiler -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity09

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

theorem compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity09
    {valuation : Nat -> Nat}
    (contextCodeBound bound bodyCodeBound : Nat)
    (body : ArithmeticSemiformula Nat 9)
    (values : Fin 9 -> Nat)
    (hvalues : forall index, values index <= bound)
    (hbody : (binaryFormulaCode body).length <= bodyCodeBound)
    (hcontext : formulaCodeSum
      (valuationContext body.freeVariables valuation) <= contextCodeBound)
    (terminalResource : Nat)
    (terminal : CertifiedPAContextProof
      (valuationContext
        (body ⇜ fun index =>
          shortBinaryNumeralTerm (values index)).freeVariables valuation)
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)))
    (hterminal : terminal.payloadLength <= terminalResource) :
    let compilation :=
      compileExplicitBoundedWitnessDirectPublicWithResource
        contextCodeBound bound bodyCodeBound body values hvalues hbody hcontext
        terminalResource terminal hterminal
    compilation.formula =
        explicitBoundedWitnessFormula
          (shortBinaryNumeralTerm bound) 9 body ∧
      compilation.payloadResource =
        explicitBoundedWitnessDirectPublicPayloadEnvelope 9
          contextCodeBound bound bodyCodeBound terminalResource := by
  constructor <;> rfl

#print axioms
  compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity09

end FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity09
