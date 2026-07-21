import integration.FoundationCompactPAExplicitBoundedWitnessDirectUniformCompiler

/-! # Fixed arity-fourteen coordinates for the intrinsic uniform compiler -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformArity14

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectUniformCompiler
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

theorem compileExplicitBoundedWitnessDirectUniformWithResource_coordinates_arity14
    {valuation : Nat -> Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat 14)
    (values : Fin 14 -> Nat)
    (hvalues : forall index, values index <= bound)
    (terminalResource : Nat)
    (terminal : CertifiedPAContextProof
      (valuationContext
        (body ⇜ fun index =>
          shortBinaryNumeralTerm (values index)).freeVariables valuation)
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)))
    (hterminal : terminal.payloadLength <= terminalResource) :
    let compilation :=
      compileExplicitBoundedWitnessDirectUniformWithResource bound body values
        hvalues terminalResource terminal hterminal
    compilation.formula =
        explicitBoundedWitnessFormula
          (shortBinaryNumeralTerm bound) 14 body ∧
      compilation.payloadResource =
        explicitBoundedWitnessDirectUniformPayloadEnvelope
          valuation bound body terminalResource := by
  constructor <;> rfl

#print axioms
  compileExplicitBoundedWitnessDirectUniformWithResource_coordinates_arity14

end FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformArity14
