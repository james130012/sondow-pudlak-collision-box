import integration.FoundationCompactPAHybridValuationSigmaOneFormulaBuilder
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
import integration.FoundationCompactPAValuationSigmaOneFormulaCompiler

/-!
# Explicit-witness hybrid builders for Sigma-one formulas

This file separates witness selection from proof compilation.  A caller must
provide every unbounded existential witness explicitly and terminate the chain
with an actual checked hybrid certificate for a true Sigma-zero body.  The
builder never extracts a witness from semantic existential truth and never
selects an inhabitant from an opaque existence claim.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAExplicitWitnessHybridSigmaOneFormulaBuilder

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

abbrev ExplicitHybridCertificate :=
  CheckedHybridValuationBoundedFormulaCertificate

/--
An explicit witness chain.  `boundedBody` is the only terminal constructor;
`existsWitness` records exactly the witness used at the next existential layer.
The terminal certificate is data, not an existentially specified proof.
-/
inductive ExplicitWitnessHybridSigmaOnePayload
    (valuation : Nat -> Nat) : ValuationFormula -> Type
  | boundedBody
      (body : ValuationFormula)
      (hhierarchy : Hierarchy Polarity.sigma 0 body)
      (htruth : formulaValue valuation body)
      (bodyCertificate : ExplicitHybridCertificate valuation body) :
      ExplicitWitnessHybridSigmaOnePayload valuation body
  | existsWitness
      (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
      (witness : Nat)
      (bodyPayload : ExplicitWitnessHybridSigmaOnePayload valuation
        (body/[shortBinaryNumeralTerm witness])) :
      ExplicitWitnessHybridSigmaOnePayload valuation (∃⁰ body)

namespace ExplicitWitnessHybridSigmaOnePayload

/-- Build the checked hybrid certificate by introducing the supplied witnesses. -/
def certificate
    {valuation : Nat -> Nat} {formula : ValuationFormula} :
    ExplicitWitnessHybridSigmaOnePayload valuation formula ->
      ExplicitHybridCertificate valuation formula
  | .boundedBody _ _ _ bodyCertificate => bodyCertificate
  | .existsWitness body witness bodyPayload =>
      .existsWitness body witness bodyPayload.certificate

/-- Semantic truth follows from the terminal truth and the supplied witnesses. -/
theorem truth
    {valuation : Nat -> Nat} {formula : ValuationFormula}
    (payload : ExplicitWitnessHybridSigmaOnePayload valuation formula) :
    formulaValue valuation formula := by
  induction payload with
  | boundedBody body hhierarchy htruth bodyCertificate =>
      exact htruth
  | existsWitness body witness bodyPayload inductionHypothesis =>
      have hwitness : LO.FirstOrder.Semiformula.Eval ![witness] valuation body :=
        (formulaValue_shortBinarySubstitution
          valuation body witness).mp inductionHypothesis
      simpa [formulaValue] using
        (show ∃ value : Nat,
            LO.FirstOrder.Semiformula.Eval ![value] valuation body from
          ⟨witness, hwitness⟩)

/-- Compile the explicitly assembled certificate to a genuine certified PA proof. -/
noncomputable def compile
    {valuation : Nat -> Nat} {formula : ValuationFormula}
    (payload : ExplicitWitnessHybridSigmaOnePayload valuation formula) :
    CertifiedPAContextProof
      (valuationContext formula.freeVariables valuation) formula :=
  payload.certificate.compile

/-- Number of explicit unbounded existential introductions. -/
def witnessCount
    {valuation : Nat -> Nat} {formula : ValuationFormula} :
    ExplicitWitnessHybridSigmaOnePayload valuation formula -> Nat
  | .boundedBody _ _ _ _ => 0
  | .existsWitness _ _ bodyPayload => bodyPayload.witnessCount + 1

/--
Proof-free recursive resource for the complete explicit payload.  The terminal
body is charged by its independently proved hybrid structural resource; every
existential layer adds its concrete weakening and introduction costs.
-/
def compilePayloadResource
    {valuation : Nat -> Nat} {formula : ValuationFormula} :
    ExplicitWitnessHybridSigmaOnePayload valuation formula -> Nat
  | .boundedBody _ _ _ bodyCertificate =>
      hybridFormulaStructuralPayloadBound bodyCertificate
  | .existsWitness body witness bodyPayload =>
      bodyPayload.compilePayloadResource +
        FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
          (insert (body/[shortBinaryNumeralTerm witness])
            (valuationContext (∃⁰ body).freeVariables valuation)) +
        CertifiedPAContextProof.existsIntroFullAssemblyCost
          (valuationContext (∃⁰ body).freeVariables valuation)
          body (shortBinaryNumeralTerm witness)

/--
Every explicit existential layer preserves a terminal structural payload
bound after adding its concrete weakening and introduction costs.
-/
theorem compile_payloadLength_le_compilePayloadResource
    {valuation : Nat -> Nat} {formula : ValuationFormula}
    (payload : ExplicitWitnessHybridSigmaOnePayload valuation formula) :
    payload.compile.payloadLength <=
      payload.compilePayloadResource := by
  induction payload with
  | boundedBody body hhierarchy htruth bodyCertificate =>
      exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
        bodyCertificate
  | existsWitness body witness bodyPayload inductionHypothesis =>
      let bodyRaw := bodyPayload.certificate.compile
      have hvariables :
          (body/[shortBinaryNumeralTerm witness]).freeVariables ⊆
            (∃⁰ body).freeVariables :=
        (shortBinarySubstitution_freeVariables_subset body witness).trans
          (by simp)
      let bodyProof := CertifiedPAContextProof.weakenContext bodyRaw
        (valuationContext_mono valuation hvariables)
      have hbodyCompiled : bodyRaw.payloadLength <=
          bodyPayload.compilePayloadResource := inductionHypothesis
      have hweaken := CertifiedPAContextProof.weakenContext_payloadLength_le
        bodyRaw (valuationContext_mono valuation hvariables)
      have hbodyProof : bodyProof.payloadLength <= bodyRaw.payloadLength +
          FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
            (insert (body/[shortBinaryNumeralTerm witness])
              (valuationContext (∃⁰ body).freeVariables valuation)) := by
        exact hweaken
      have hexists := CertifiedPAContextProof.existsIntro_payloadLength_le
        (shortBinaryNumeralTerm witness) bodyProof
      change (CertifiedPAContextProof.existsIntro
          (shortBinaryNumeralTerm witness) bodyProof).payloadLength <= _
      simp only [compilePayloadResource]
      omega

end ExplicitWitnessHybridSigmaOnePayload

/--
An arbitrary-arity existential closure supplied as an explicit nested payload.
For `∃⁰* body`, the outer payload constructor supplies the witness for the
highest remaining de Bruijn coordinate; descending the payload reaches `#0`
last.  The index enforces the substitutions at every intermediate layer.
-/
abbrev ExplicitWitnessHybridExsClosurePayload
    (valuation : Nat -> Nat) {arity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat arity) :=
  ExplicitWitnessHybridSigmaOnePayload valuation (∃⁰* body)

/-- Build a certificate for an arbitrary explicit existential closure. -/
def buildExplicitWitnessHybridExsClosure
    {valuation : Nat -> Nat} {arity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat arity)
    (payload : ExplicitWitnessHybridExsClosurePayload valuation body) :
    ExplicitHybridCertificate valuation (∃⁰* body) :=
  payload.certificate

/-- Truth endpoint for an arbitrary explicit existential closure. -/
theorem explicitWitnessHybridExsClosure_truth
    {valuation : Nat -> Nat} {arity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat arity)
    (payload : ExplicitWitnessHybridExsClosurePayload valuation body) :
    formulaValue valuation (∃⁰* body) :=
  payload.truth

/-- Proof-producing endpoint for an arbitrary explicit existential closure. -/
noncomputable def compileExplicitWitnessHybridExsClosure
    {valuation : Nat -> Nat} {arity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat arity)
    (payload : ExplicitWitnessHybridExsClosurePayload valuation body) :
    CertifiedPAContextProof
      (valuationContext (∃⁰* body).freeVariables valuation) (∃⁰* body) :=
  payload.compile

theorem compileExplicitWitnessHybridExsClosure_payloadLength_le
    {valuation : Nat -> Nat} {arity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat arity)
    (payload : ExplicitWitnessHybridExsClosurePayload valuation body) :
    (compileExplicitWitnessHybridExsClosure body payload).payloadLength <=
      payload.compilePayloadResource :=
  payload.compile_payloadLength_le_compilePayloadResource

/-- Public certificate endpoint for an explicit witness payload. -/
def buildExplicitWitnessHybridSigmaOne
    {valuation : Nat -> Nat} {formula : ValuationFormula}
    (payload : ExplicitWitnessHybridSigmaOnePayload valuation formula) :
    ExplicitHybridCertificate valuation formula :=
  payload.certificate

/-- Public proof-producing endpoint for an explicit witness payload. -/
noncomputable def compileExplicitWitnessHybridSigmaOne
    {valuation : Nat -> Nat} {formula : ValuationFormula}
    (payload : ExplicitWitnessHybridSigmaOnePayload valuation formula) :
    CertifiedPAContextProof
      (valuationContext formula.freeVariables valuation) formula :=
  payload.compile

theorem compileExplicitWitnessHybridSigmaOne_payloadLength_le
    {valuation : Nat -> Nat} {formula : ValuationFormula}
    (payload : ExplicitWitnessHybridSigmaOnePayload valuation formula) :
    (compileExplicitWitnessHybridSigmaOne payload).payloadLength <=
      payload.compilePayloadResource :=
  payload.compile_payloadLength_le_compilePayloadResource

#print axioms ExplicitWitnessHybridSigmaOnePayload.certificate
#print axioms ExplicitWitnessHybridSigmaOnePayload.truth
#print axioms compileExplicitWitnessHybridExsClosure
#print axioms compileExplicitWitnessHybridExsClosure_payloadLength_le
#print axioms compileExplicitWitnessHybridSigmaOne
#print axioms compileExplicitWitnessHybridSigmaOne_payloadLength_le

end FoundationCompactPAExplicitWitnessHybridSigmaOneFormulaBuilder
