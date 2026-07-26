import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicUniformResourceCompiler

/-! # Arity-twenty-seven coordinates for the uniform-resource compiler -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactPAExplicitBoundedWitnessDirectPublicUniformResourceCompilerArity27

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicUniformResourceCompiler
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

theorem
    compileExplicitBoundedWitnessDirectPublicWithUniformResource_coordinates_arity27
    {valuation : Nat -> Nat}
    (contextCodeBound formulaBound resourceBound bodyCodeBound : Nat)
    (hbound : formulaBound <= resourceBound)
    (body : ArithmeticSemiformula Nat 27)
    (values : Fin 27 -> Nat)
    (hvalues : forall index, values index <= formulaBound)
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
      compileExplicitBoundedWitnessDirectPublicWithUniformResource
        contextCodeBound formulaBound resourceBound bodyCodeBound hbound body
        values hvalues hbody hcontext terminalResource terminal hterminal
    compilation.formula =
        explicitBoundedWitnessFormula
          (shortBinaryNumeralTerm formulaBound) 27 body ∧
      compilation.payloadResource =
        explicitBoundedWitnessDirectPublicPayloadEnvelope 27 contextCodeBound
          resourceBound bodyCodeBound terminalResource := by
  constructor <;> rfl

#print axioms
  compileExplicitBoundedWitnessDirectPublicWithUniformResource_coordinates_arity27

end FoundationCompactPAExplicitBoundedWitnessDirectPublicUniformResourceCompilerArity27
