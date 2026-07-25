import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity27
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
import integration.FoundationCompactPADirectConnectiveTransparentBounds
import integration.FoundationCompactPAValuationTermCompilerPublicBounds

/-! # Packaged public direct bound for twenty-seven bounded witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactPAExplicitBoundedWitnessDirectPublicBoundArity27

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity27
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

@[irreducible] noncomputable def
    compileExplicitBoundedWitnessDirectPublicBoundArity27
    {valuation : Nat -> Nat}
    (contextCodeBound bound bodyCodeBound : Nat)
    (body : ArithmeticSemiformula Nat 27)
    (values : Fin 27 -> Nat)
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
    ExplicitDirectFormulaBound valuation
      (explicitBoundedWitnessFormula (shortBinaryNumeralTerm bound) 27 body)
      (explicitBoundedWitnessDirectPublicPayloadEnvelope 27 contextCodeBound
        bound bodyCodeBound terminalResource) := by
  let sourceFormula :=
    explicitBoundedWitnessFormula (shortBinaryNumeralTerm bound) 27 body
  let compilation := compileExplicitBoundedWitnessDirectPublicWithResource
    contextCodeBound bound bodyCodeBound body values hvalues hbody hcontext
      terminalResource terminal hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity27
      contextCodeBound bound bodyCodeBound body values hvalues hbody hcontext
        terminalResource terminal hterminal
  let proof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  refine ⟨proof, ?_⟩
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  simpa only [sourceFormula, compilation, proof] using hcoordinates.2

#print axioms compileExplicitBoundedWitnessDirectPublicBoundArity27

end FoundationCompactPAExplicitBoundedWitnessDirectPublicBoundArity27
