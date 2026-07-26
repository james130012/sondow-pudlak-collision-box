import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity18
import integration.FoundationCompactPADirectConnectiveTransparentBounds

/-! # Opaque fixed-arity entry point for eighteen public bounded witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerOpaqueArity18

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity18
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

opaque compileExplicitBoundedWitnessDirectPublicOpaqueArity18
    {valuation : Nat -> Nat}
    (contextCodeBound bound bodyCodeBound : Nat)
    (body : ArithmeticSemiformula Nat 18)
    (values : Fin 18 -> Nat)
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
    ExplicitBoundedWitnessDirectCompilation valuation :=
  compileExplicitBoundedWitnessDirectPublicWithResource
    contextCodeBound bound bodyCodeBound body values hvalues hbody hcontext
    terminalResource terminal hterminal

opaque compileExplicitBoundedWitnessDirectPublicFromTerminalBoundOpaqueArity18
    {valuation : Nat -> Nat}
    (contextCodeBound bound bodyCodeBound : Nat)
    (body : ArithmeticSemiformula Nat 18)
    (values : Fin 18 -> Nat)
    (hvalues : forall index, values index <= bound)
    (hbody : (binaryFormulaCode body).length <= bodyCodeBound)
    (hcontext : formulaCodeSum
      (valuationContext body.freeVariables valuation) <= contextCodeBound)
    (terminalResource : Nat)
    (terminal : ExplicitDirectFormulaBound valuation
      (body ⇜ fun index => shortBinaryNumeralTerm (values index))
      terminalResource) :
    ExplicitBoundedWitnessDirectCompilation valuation := by
  exact compileExplicitBoundedWitnessDirectPublicOpaqueArity18
    contextCodeBound bound bodyCodeBound body values hvalues hbody hcontext
    terminalResource terminal.proof terminal.payloadLength_le

structure CertifiedPublicBoundedWitnessCompilationArity18
    (valuation : Nat -> Nat)
    (contextCodeBound bound bodyCodeBound : Nat)
    (body : ArithmeticSemiformula Nat 18)
    (values : Fin 18 -> Nat)
    (terminalResource : Nat) where
  compilation : ExplicitBoundedWitnessDirectCompilation valuation
  formula_eq : compilation.formula =
    explicitBoundedWitnessFormula (shortBinaryNumeralTerm bound) 18 body
  resource_eq : compilation.payloadResource =
    explicitBoundedWitnessDirectPublicPayloadEnvelope 18
      contextCodeBound bound bodyCodeBound terminalResource

opaque compileExplicitBoundedWitnessDirectPublicCertifiedOpaqueArity18
    {valuation : Nat -> Nat}
    (contextCodeBound bound bodyCodeBound : Nat)
    (body : ArithmeticSemiformula Nat 18)
    (values : Fin 18 -> Nat)
    (hvalues : forall index, values index <= bound)
    (hbody : (binaryFormulaCode body).length <= bodyCodeBound)
    (hcontext : formulaCodeSum
      (valuationContext body.freeVariables valuation) <= contextCodeBound)
    (terminalResource : Nat)
    (terminal : ExplicitDirectFormulaBound valuation
      (body ⇜ fun index => shortBinaryNumeralTerm (values index))
      terminalResource) :
    CertifiedPublicBoundedWitnessCompilationArity18 valuation
      contextCodeBound bound bodyCodeBound body values terminalResource := by
  let compilation :=
    compileExplicitBoundedWitnessDirectPublicWithResource
      contextCodeBound bound bodyCodeBound body values hvalues hbody hcontext
      terminalResource terminal.proof terminal.payloadLength_le
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity18
      contextCodeBound bound bodyCodeBound body values hvalues hbody hcontext
      terminalResource terminal.proof terminal.payloadLength_le
  exact
    { compilation := compilation
      formula_eq := hcoordinates.1
      resource_eq := hcoordinates.2 }

end FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerOpaqueArity18
