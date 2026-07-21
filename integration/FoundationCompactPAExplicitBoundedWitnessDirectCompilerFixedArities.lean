import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds

/-!
# Fixed-arity coordinates for direct bounded-witness compilation

The project uses concrete witness blocks.  Reducing those fixed arities keeps
the formula/resource coordinate check small and avoids a kernel-wide dependent
recursion over arbitrary formulas.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option Elab.async false

namespace FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds

/-- Explicit values and the independently compiled terminal used by a bounded
witness block.  Concrete graph constructors build this record internally. -/
structure ExplicitBoundedWitnessHybridTerminal
    (valuation : Nat -> Nat) {k : Nat}
    (bound : Nat) (body : ArithmeticSemiformula Nat k) where
  values : Fin k -> Nat
  values_le : ∀ index, values index ≤ bound
  terminal : CheckedHybridValuationBoundedFormulaCertificate valuation
    (body ⇜ fun index => shortBinaryNumeralTerm (values index))

theorem compileExplicitBoundedWitnessDirectWithResource_coordinates_arity4
    {valuation : Nat -> Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat 4)
    (values : Fin 4 -> Nat)
    (hbounds : ∀ index, values index ≤ bound)
    (terminalResource : Nat)
    (terminal : CertifiedPAContextProof
      (valuationContext
        (body ⇜ fun index =>
          shortBinaryNumeralTerm (values index)).freeVariables valuation)
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)))
    (hterminal : terminal.payloadLength ≤ terminalResource) :
    let compilation := compileExplicitBoundedWitnessDirectWithResource
      bound body values hbounds terminalResource terminal hterminal
    compilation.formula =
        explicitBoundedWitnessFormula
          (shortBinaryNumeralTerm bound) 4 body ∧
      compilation.payloadResource =
        explicitBoundedWitnessDirectPayloadEnvelope
          valuation bound body values terminalResource := by
  constructor <;> rfl

theorem compileExplicitBoundedWitnessDirectWithResource_coordinates_arity9
    {valuation : Nat -> Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat 9)
    (values : Fin 9 -> Nat)
    (hbounds : ∀ index, values index ≤ bound)
    (terminalResource : Nat)
    (terminal : CertifiedPAContextProof
      (valuationContext
        (body ⇜ fun index =>
          shortBinaryNumeralTerm (values index)).freeVariables valuation)
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)))
    (hterminal : terminal.payloadLength ≤ terminalResource) :
    let compilation := compileExplicitBoundedWitnessDirectWithResource
      bound body values hbounds terminalResource terminal hterminal
    compilation.formula =
        explicitBoundedWitnessFormula
          (shortBinaryNumeralTerm bound) 9 body ∧
      compilation.payloadResource =
        explicitBoundedWitnessDirectPayloadEnvelope
          valuation bound body values terminalResource := by
  constructor <;> rfl

theorem compileExplicitBoundedWitnessDirectWithResource_coordinates_arity14
    {valuation : Nat -> Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat 14)
    (values : Fin 14 -> Nat)
    (hbounds : ∀ index, values index ≤ bound)
    (terminalResource : Nat)
    (terminal : CertifiedPAContextProof
      (valuationContext
        (body ⇜ fun index =>
          shortBinaryNumeralTerm (values index)).freeVariables valuation)
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)))
    (hterminal : terminal.payloadLength ≤ terminalResource) :
    let compilation := compileExplicitBoundedWitnessDirectWithResource
      bound body values hbounds terminalResource terminal hterminal
    compilation.formula =
        explicitBoundedWitnessFormula
          (shortBinaryNumeralTerm bound) 14 body ∧
      compilation.payloadResource =
        explicitBoundedWitnessDirectPayloadEnvelope
          valuation bound body values terminalResource := by
  constructor <;> rfl

noncomputable def castValuationContextProof
    {valuation : Nat -> Nat} {source target : ValuationFormula}
    (hformula : source = target)
    (proof : CertifiedPAContextProof
      (valuationContext source.freeVariables valuation) source) :
    CertifiedPAContextProof
      (valuationContext target.freeVariables valuation) target := by
  let atSourceContext : CertifiedPAContextProof
      (valuationContext source.freeVariables valuation) target :=
    CertifiedPAContextProof.cast hformula proof
  have hcontext :
      valuationContext source.freeVariables valuation =
        valuationContext target.freeVariables valuation :=
    congrArg (fun formula =>
      valuationContext formula.freeVariables valuation) hformula
  exact CertifiedPAContextProof.castContext hcontext atSourceContext

theorem castValuationContextProof_payloadLength_eq
    {valuation : Nat -> Nat} {source target : ValuationFormula}
    (hformula : source = target)
    (proof : CertifiedPAContextProof
      (valuationContext source.freeVariables valuation) source) :
    (castValuationContextProof hformula proof).payloadLength =
      proof.payloadLength := by
  let atSourceContext : CertifiedPAContextProof
      (valuationContext source.freeVariables valuation) target :=
    CertifiedPAContextProof.cast hformula proof
  have hcontext :
      valuationContext source.freeVariables valuation =
        valuationContext target.freeVariables valuation :=
    congrArg (fun formula =>
      valuationContext formula.freeVariables valuation) hformula
  calc
    (castValuationContextProof hformula proof).payloadLength =
        atSourceContext.payloadLength := by
      exact CertifiedPAContextProof.castContext_payloadLength
        hcontext atSourceContext
    _ = proof.payloadLength :=
      CertifiedPAContextProof.cast_payloadLength hformula proof

/-- Transport the internally compiled formula to its audited public target. -/
noncomputable def castDirectCompilationProof
    {valuation : Nat -> Nat}
    (compilation : ExplicitBoundedWitnessDirectCompilation valuation)
    (target : ValuationFormula)
    (hformula : compilation.formula = target) :
    CertifiedPAContextProof
      (valuationContext target.freeVariables valuation) target := by
  let atSourceContext : CertifiedPAContextProof
      (valuationContext compilation.formula.freeVariables valuation)
      target :=
    CertifiedPAContextProof.cast hformula compilation.proof
  have hcontext :
      valuationContext compilation.formula.freeVariables valuation =
        valuationContext target.freeVariables valuation :=
    congrArg (fun formula =>
      valuationContext formula.freeVariables valuation) hformula
  exact CertifiedPAContextProof.castContext hcontext atSourceContext

theorem castDirectCompilationProof_payloadLength_eq
    {valuation : Nat -> Nat}
    (compilation : ExplicitBoundedWitnessDirectCompilation valuation)
    (target : ValuationFormula)
    (hformula : compilation.formula = target) :
    (castDirectCompilationProof compilation target hformula).payloadLength =
      compilation.proof.payloadLength := by
  let atSourceContext : CertifiedPAContextProof
      (valuationContext compilation.formula.freeVariables valuation)
      target :=
    CertifiedPAContextProof.cast hformula compilation.proof
  have hcontext :
      valuationContext compilation.formula.freeVariables valuation =
        valuationContext target.freeVariables valuation :=
    congrArg (fun formula =>
      valuationContext formula.freeVariables valuation) hformula
  calc
    (castDirectCompilationProof compilation target hformula).payloadLength =
        atSourceContext.payloadLength := by
      exact CertifiedPAContextProof.castContext_payloadLength
        hcontext atSourceContext
    _ = compilation.proof.payloadLength :=
      CertifiedPAContextProof.cast_payloadLength
        hformula compilation.proof

theorem castDirectCompilationProof_payloadLength_le
    {valuation : Nat -> Nat}
    (compilation : ExplicitBoundedWitnessDirectCompilation valuation)
    (target : ValuationFormula)
    (hformula : compilation.formula = target)
    (targetResource : Nat)
    (hresource : compilation.payloadResource = targetResource) :
    (castDirectCompilationProof compilation target hformula).payloadLength ≤
      targetResource := by
  rw [castDirectCompilationProof_payloadLength_eq, ← hresource]
  exact compilation.payloadLength_le

noncomputable def compileExplicitBoundedWitnessDirectArity4
    {valuation : Nat -> Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat 4)
    (values : Fin 4 -> Nat)
    (hbounds : ∀ index, values index ≤ bound)
    (terminalResource : Nat)
    (terminal : CertifiedPAContextProof
      (valuationContext
        (body ⇜ fun index =>
          shortBinaryNumeralTerm (values index)).freeVariables valuation)
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)))
    (hterminal : terminal.payloadLength ≤ terminalResource) :
    CertifiedPAContextProof
      (valuationContext
        (explicitBoundedWitnessFormula
          (shortBinaryNumeralTerm bound) 4 body).freeVariables valuation)
      (explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm bound) 4 body) := by
  let compilation := compileExplicitBoundedWitnessDirectWithResource
    bound body values hbounds terminalResource terminal hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectWithResource_coordinates_arity4
      bound body values hbounds terminalResource terminal hterminal
  exact castDirectCompilationProof compilation _ hcoordinates.1

theorem compileExplicitBoundedWitnessDirectArity4_payloadLength_le
    {valuation : Nat -> Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat 4)
    (values : Fin 4 -> Nat)
    (hbounds : ∀ index, values index ≤ bound)
    (terminalResource : Nat)
    (terminal : CertifiedPAContextProof
      (valuationContext
        (body ⇜ fun index =>
          shortBinaryNumeralTerm (values index)).freeVariables valuation)
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)))
    (hterminal : terminal.payloadLength ≤ terminalResource) :
    (compileExplicitBoundedWitnessDirectArity4 bound body values hbounds
      terminalResource terminal hterminal).payloadLength ≤
      explicitBoundedWitnessDirectPayloadEnvelope
        valuation bound body values terminalResource := by
  let compilation := compileExplicitBoundedWitnessDirectWithResource
    bound body values hbounds terminalResource terminal hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectWithResource_coordinates_arity4
      bound body values hbounds terminalResource terminal hterminal
  change (castDirectCompilationProof compilation _ hcoordinates.1).payloadLength ≤ _
  exact castDirectCompilationProof_payloadLength_le compilation _
    hcoordinates.1 _ hcoordinates.2

noncomputable def compileExplicitBoundedWitnessDirectArity9
    {valuation : Nat -> Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat 9)
    (values : Fin 9 -> Nat)
    (hbounds : ∀ index, values index ≤ bound)
    (terminalResource : Nat)
    (terminal : CertifiedPAContextProof
      (valuationContext
        (body ⇜ fun index =>
          shortBinaryNumeralTerm (values index)).freeVariables valuation)
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)))
    (hterminal : terminal.payloadLength ≤ terminalResource) :
    CertifiedPAContextProof
      (valuationContext
        (explicitBoundedWitnessFormula
          (shortBinaryNumeralTerm bound) 9 body).freeVariables valuation)
      (explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm bound) 9 body) := by
  let compilation := compileExplicitBoundedWitnessDirectWithResource
    bound body values hbounds terminalResource terminal hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectWithResource_coordinates_arity9
      bound body values hbounds terminalResource terminal hterminal
  exact castDirectCompilationProof compilation _ hcoordinates.1

theorem compileExplicitBoundedWitnessDirectArity9_payloadLength_le
    {valuation : Nat -> Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat 9)
    (values : Fin 9 -> Nat)
    (hbounds : ∀ index, values index ≤ bound)
    (terminalResource : Nat)
    (terminal : CertifiedPAContextProof
      (valuationContext
        (body ⇜ fun index =>
          shortBinaryNumeralTerm (values index)).freeVariables valuation)
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)))
    (hterminal : terminal.payloadLength ≤ terminalResource) :
    (compileExplicitBoundedWitnessDirectArity9 bound body values hbounds
      terminalResource terminal hterminal).payloadLength ≤
      explicitBoundedWitnessDirectPayloadEnvelope
        valuation bound body values terminalResource := by
  let compilation := compileExplicitBoundedWitnessDirectWithResource
    bound body values hbounds terminalResource terminal hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectWithResource_coordinates_arity9
      bound body values hbounds terminalResource terminal hterminal
  change (castDirectCompilationProof compilation _ hcoordinates.1).payloadLength ≤ _
  exact castDirectCompilationProof_payloadLength_le compilation _
    hcoordinates.1 _ hcoordinates.2

noncomputable def compileExplicitBoundedWitnessDirectArity14
    {valuation : Nat -> Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat 14)
    (values : Fin 14 -> Nat)
    (hbounds : ∀ index, values index ≤ bound)
    (terminalResource : Nat)
    (terminal : CertifiedPAContextProof
      (valuationContext
        (body ⇜ fun index =>
          shortBinaryNumeralTerm (values index)).freeVariables valuation)
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)))
    (hterminal : terminal.payloadLength ≤ terminalResource) :
    CertifiedPAContextProof
      (valuationContext
        (explicitBoundedWitnessFormula
          (shortBinaryNumeralTerm bound) 14 body).freeVariables valuation)
      (explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm bound) 14 body) := by
  let compilation := compileExplicitBoundedWitnessDirectWithResource
    bound body values hbounds terminalResource terminal hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectWithResource_coordinates_arity14
      bound body values hbounds terminalResource terminal hterminal
  exact castDirectCompilationProof compilation _ hcoordinates.1

theorem compileExplicitBoundedWitnessDirectArity14_payloadLength_le
    {valuation : Nat -> Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat 14)
    (values : Fin 14 -> Nat)
    (hbounds : ∀ index, values index ≤ bound)
    (terminalResource : Nat)
    (terminal : CertifiedPAContextProof
      (valuationContext
        (body ⇜ fun index =>
          shortBinaryNumeralTerm (values index)).freeVariables valuation)
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)))
    (hterminal : terminal.payloadLength ≤ terminalResource) :
    (compileExplicitBoundedWitnessDirectArity14 bound body values hbounds
      terminalResource terminal hterminal).payloadLength ≤
      explicitBoundedWitnessDirectPayloadEnvelope
        valuation bound body values terminalResource := by
  let compilation := compileExplicitBoundedWitnessDirectWithResource
    bound body values hbounds terminalResource terminal hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectWithResource_coordinates_arity14
      bound body values hbounds terminalResource terminal hterminal
  change (castDirectCompilationProof compilation _ hcoordinates.1).payloadLength ≤ _
  exact castDirectCompilationProof_payloadLength_le compilation _
    hcoordinates.1 _ hcoordinates.2

def explicitBoundedWitnessDirectHybridPayloadEnvelope
    {valuation : Nat -> Nat} {k : Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat k)
    (values : Fin k -> Nat)
    (terminal : CheckedHybridValuationBoundedFormulaCertificate valuation
      (body ⇜ fun index => shortBinaryNumeralTerm (values index))) : Nat :=
  explicitBoundedWitnessDirectPayloadEnvelope valuation bound body values
    (hybridFormulaStructuralPayloadBound terminal)

noncomputable def compileExplicitBoundedWitnessDirectArity9FromHybrid
    {valuation : Nat -> Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat 9)
    (values : Fin 9 -> Nat)
    (hbounds : ∀ index, values index ≤ bound)
    (terminal : CheckedHybridValuationBoundedFormulaCertificate valuation
      (body ⇜ fun index => shortBinaryNumeralTerm (values index))) :
    CertifiedPAContextProof
      (valuationContext
        (explicitBoundedWitnessFormula
          (shortBinaryNumeralTerm bound) 9 body).freeVariables valuation)
      (explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm bound) 9 body) :=
  compileExplicitBoundedWitnessDirectArity9 bound body values hbounds
    (hybridFormulaStructuralPayloadBound terminal) terminal.compile
    (compile_payloadLength_le_structuralPayloadBound terminal)

theorem compileExplicitBoundedWitnessDirectArity9FromHybrid_payloadLength_le
    {valuation : Nat -> Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat 9)
    (values : Fin 9 -> Nat)
    (hbounds : ∀ index, values index ≤ bound)
    (terminal : CheckedHybridValuationBoundedFormulaCertificate valuation
      (body ⇜ fun index => shortBinaryNumeralTerm (values index))) :
    (compileExplicitBoundedWitnessDirectArity9FromHybrid
      bound body values hbounds terminal).payloadLength ≤
      explicitBoundedWitnessDirectHybridPayloadEnvelope
        bound body values terminal := by
  exact compileExplicitBoundedWitnessDirectArity9_payloadLength_le
    bound body values hbounds
    (hybridFormulaStructuralPayloadBound terminal) terminal.compile
    (compile_payloadLength_le_structuralPayloadBound terminal)

noncomputable def compileExplicitBoundedWitnessDirectArity14FromHybrid
    {valuation : Nat -> Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat 14)
    (values : Fin 14 -> Nat)
    (hbounds : ∀ index, values index ≤ bound)
    (terminal : CheckedHybridValuationBoundedFormulaCertificate valuation
      (body ⇜ fun index => shortBinaryNumeralTerm (values index))) :
    CertifiedPAContextProof
      (valuationContext
        (explicitBoundedWitnessFormula
          (shortBinaryNumeralTerm bound) 14 body).freeVariables valuation)
      (explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm bound) 14 body) :=
  compileExplicitBoundedWitnessDirectArity14 bound body values hbounds
    (hybridFormulaStructuralPayloadBound terminal) terminal.compile
    (compile_payloadLength_le_structuralPayloadBound terminal)

theorem compileExplicitBoundedWitnessDirectArity14FromHybrid_payloadLength_le
    {valuation : Nat -> Nat}
    (bound : Nat)
    (body : ArithmeticSemiformula Nat 14)
    (values : Fin 14 -> Nat)
    (hbounds : ∀ index, values index ≤ bound)
    (terminal : CheckedHybridValuationBoundedFormulaCertificate valuation
      (body ⇜ fun index => shortBinaryNumeralTerm (values index))) :
    (compileExplicitBoundedWitnessDirectArity14FromHybrid
      bound body values hbounds terminal).payloadLength ≤
      explicitBoundedWitnessDirectHybridPayloadEnvelope
        bound body values terminal := by
  exact compileExplicitBoundedWitnessDirectArity14_payloadLength_le
    bound body values hbounds
    (hybridFormulaStructuralPayloadBound terminal) terminal.compile
    (compile_payloadLength_le_structuralPayloadBound terminal)

#print axioms compileExplicitBoundedWitnessDirectWithResource_coordinates_arity9
#print axioms compileExplicitBoundedWitnessDirectWithResource_coordinates_arity14
#print axioms castValuationContextProof_payloadLength_eq
#print axioms castDirectCompilationProof_payloadLength_le
#print axioms compileExplicitBoundedWitnessDirectWithResource_coordinates_arity4
#print axioms compileExplicitBoundedWitnessDirectArity4
#print axioms compileExplicitBoundedWitnessDirectArity4_payloadLength_le
#print axioms compileExplicitBoundedWitnessDirectArity9
#print axioms compileExplicitBoundedWitnessDirectArity9_payloadLength_le
#print axioms compileExplicitBoundedWitnessDirectArity14
#print axioms compileExplicitBoundedWitnessDirectArity14_payloadLength_le
#print axioms compileExplicitBoundedWitnessDirectArity9FromHybrid
#print axioms compileExplicitBoundedWitnessDirectArity9FromHybrid_payloadLength_le
#print axioms compileExplicitBoundedWitnessDirectArity14FromHybrid
#print axioms compileExplicitBoundedWitnessDirectArity14FromHybrid_payloadLength_le

end FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
