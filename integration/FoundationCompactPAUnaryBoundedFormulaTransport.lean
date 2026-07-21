import integration.FoundationCompactCertifiedContextConnectives
import integration.FoundationCompactPAUnaryAtomicTransport
import integration.FoundationCompactPAClosedAtomicCompilerBounds

/-!
# Proof-free bounded-formula transport under one parameter equality

The certificate stores checked closed atomic truth, connective choices, and
explicit existential witnesses.  It stores no PA derivation, proof code, or
proof-length premise.  Compilation constructs a real contextual PA proof of
the target formula from the local equality assumption.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAUnaryBoundedFormulaTransport

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAClosedAtomicCompiler
open FoundationCompactPAClosedAtomicCompiler.ClosedPATerm
open FoundationCompactPAClosedAtomicCompiler.ClosedPATerm.ClosedPAAtomicLiteral
open FoundationCompactPAClosedAtomicCompilerBounds
open FoundationCompactPAClosedAtomicCompilerBounds.ClosedPATerm
open FoundationCompactPAClosedAtomicCompilerBounds.ClosedPATerm.ClosedPAAtomicLiteralBounds
open FoundationCompactPAUnaryTermEqualityImplication
open FoundationCompactPAUnaryAtomicTransport

/-- A proof-free certificate that a closed target formula follows after
replacing one closed parameter by an equal one.  Atomic constructors expose
the exact unary atom and independently checked closed source literal. -/
inductive CheckedUnaryReplacementCertificate
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition → Type
  | verum : CheckedUnaryReplacementCertificate left right
      (⊤ : LO.FirstOrder.ArithmeticProposition)
  | positiveAtomic
      (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
      (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
      (literal : ClosedPAAtomicLiteral)
      (sourceFormula : literal.formula =
        unaryRelationFormula relationSymbol arguments left)
      (hvalue : literal.Truth) :
      CheckedUnaryReplacementCertificate left right
        (unaryRelationFormula relationSymbol arguments right)
  | negativeAtomic
      (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
      (arguments : Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1)
      (literal : ClosedPAAtomicLiteral)
      (sourceFormula : literal.formula =
        ∼unaryRelationFormula relationSymbol arguments left)
      (hvalue : literal.Truth) :
      CheckedUnaryReplacementCertificate left right
        (∼unaryRelationFormula relationSymbol arguments right)
  | conjunction
      {leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition}
      (leftCertificate : CheckedUnaryReplacementCertificate
        left right leftFormula)
      (rightCertificate : CheckedUnaryReplacementCertificate
        left right rightFormula) :
      CheckedUnaryReplacementCertificate left right
        (leftFormula ⋏ rightFormula)
  | disjunctionLeft
      {leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition}
      (leftCertificate : CheckedUnaryReplacementCertificate
        left right leftFormula) :
      CheckedUnaryReplacementCertificate left right
        (leftFormula ⋎ rightFormula)
  | disjunctionRight
      {leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition}
      (rightCertificate : CheckedUnaryReplacementCertificate
        left right rightFormula) :
      CheckedUnaryReplacementCertificate left right
        (leftFormula ⋎ rightFormula)
  | existsWitness
      (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
      (witness : ClosedPATerm)
      (bodyCertificate : CheckedUnaryReplacementCertificate
        left right (body/[witness.term])) :
      CheckedUnaryReplacementCertificate left right (∃⁰ body)

namespace CheckedUnaryReplacementCertificate

noncomputable def compileUnderAssumption
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0} :
    {formula : LO.FirstOrder.ArithmeticProposition} →
    CheckedUnaryReplacementCertificate left right formula →
    CertifiedPAContextProof (parameterEqualityContext left right) formula
  | _, .verum =>
      CertifiedPAContextProof.weakenCertified
        (parameterEqualityContext left right) CertifiedPAProof.verumProof
  | _, .positiveAtomic relationSymbol arguments literal sourceFormula hvalue =>
      positiveTransportUnderAssumption relationSymbol arguments left right
        (CertifiedPAProof.cast sourceFormula (literal.compile hvalue))
  | _, .negativeAtomic relationSymbol arguments literal sourceFormula hvalue =>
      negativeTransportUnderAssumption relationSymbol arguments left right
        (CertifiedPAProof.cast sourceFormula (literal.compile hvalue))
  | _, .conjunction leftCertificate rightCertificate =>
      CertifiedPAContextProof.conjunction
        leftCertificate.compileUnderAssumption
        rightCertificate.compileUnderAssumption
  | _, .disjunctionLeft leftCertificate =>
      CertifiedPAContextProof.disjunctionLeft
        leftCertificate.compileUnderAssumption
  | _, .disjunctionRight rightCertificate =>
      CertifiedPAContextProof.disjunctionRight
        rightCertificate.compileUnderAssumption
  | _, .existsWitness body witness bodyCertificate =>
      CertifiedPAContextProof.existsIntro witness.term
        bodyCertificate.compileUnderAssumption

/-- Formula-specific full-payload bound obtained by charging every proof and
certificate constructor used by `compileUnderAssumption`. -/
def structuralPayloadBound
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0} :
    {formula : LO.FirstOrder.ArithmeticProposition} →
    CheckedUnaryReplacementCertificate left right formula → Nat
  | _, .verum =>
      CertifiedPAProof.verumProof.payloadLength +
        FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
          (insert (⊤ : LO.FirstOrder.ArithmeticProposition)
            (parameterEqualityContext left right))
  | _, .positiveAtomic relationSymbol arguments literal _ _ =>
      positiveTransportUnderAssumptionStructuralPayloadBound
        relationSymbol arguments left right
        (ClosedPAAtomicLiteralBounds.payloadPolynomial literal)
  | _, .negativeAtomic relationSymbol arguments literal _ _ =>
      negativeTransportUnderAssumptionStructuralPayloadBound
        relationSymbol arguments left right
        (ClosedPAAtomicLiteralBounds.payloadPolynomial literal)
  | _, .conjunction (leftFormula := leftFormula)
      (rightFormula := rightFormula) leftCertificate rightCertificate =>
      structuralPayloadBound leftCertificate +
        structuralPayloadBound rightCertificate +
        CertifiedPAContextProof.conjunctionFullAssemblyCost
          (parameterEqualityContext left right)
          leftFormula rightFormula
  | _, .disjunctionLeft (leftFormula := leftFormula)
      (rightFormula := rightFormula) leftCertificate =>
      structuralPayloadBound leftCertificate +
        CertifiedPAContextProof.disjunctionFullAssemblyCost
          (parameterEqualityContext left right)
          leftFormula rightFormula
  | _, .disjunctionRight (leftFormula := leftFormula)
      (rightFormula := rightFormula) rightCertificate =>
      structuralPayloadBound rightCertificate +
        CertifiedPAContextProof.disjunctionFullAssemblyCost
          (parameterEqualityContext left right)
          leftFormula rightFormula
  | _, .existsWitness body witness bodyCertificate =>
      structuralPayloadBound bodyCertificate +
        CertifiedPAContextProof.existsIntroFullAssemblyCost
          (parameterEqualityContext left right) body witness.term

theorem compileUnderAssumption_payloadLength_le_structuralPayloadBound
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula) :
    certificate.compileUnderAssumption.payloadLength <=
      certificate.structuralPayloadBound := by
  induction certificate with
  | verum =>
      exact CertifiedPAContextProof.weakenCertified_payloadLength_le
        (parameterEqualityContext left right) CertifiedPAProof.verumProof
  | positiveAtomic relationSymbol arguments literal sourceFormula hvalue =>
      let sourceProof := CertifiedPAProof.cast sourceFormula
        (literal.compile hvalue)
      have hsourceRaw :=
        ClosedPAAtomicLiteralBounds.compile_payloadLength_le_polynomial
          literal hvalue
      have hsource : sourceProof.payloadLength <=
          ClosedPAAtomicLiteralBounds.payloadPolynomial literal := by
        simpa only [sourceProof, CertifiedPAProof.cast_payloadLength] using
          hsourceRaw
      have htransport := positiveTransportUnderAssumption_payloadLength_le
        relationSymbol arguments left right sourceProof
      exact htransport.trans
        (positiveTransportUnderAssumptionStructuralPayloadBound_mono_source
          relationSymbol arguments left right hsource)
  | negativeAtomic relationSymbol arguments literal sourceFormula hvalue =>
      let sourceProof := CertifiedPAProof.cast sourceFormula
        (literal.compile hvalue)
      have hsourceRaw :=
        ClosedPAAtomicLiteralBounds.compile_payloadLength_le_polynomial
          literal hvalue
      have hsource : sourceProof.payloadLength <=
          ClosedPAAtomicLiteralBounds.payloadPolynomial literal := by
        simpa only [sourceProof, CertifiedPAProof.cast_payloadLength] using
          hsourceRaw
      have htransport := negativeTransportUnderAssumption_payloadLength_le
        relationSymbol arguments left right sourceProof
      exact htransport.trans
        (negativeTransportUnderAssumptionStructuralPayloadBound_mono_source
          relationSymbol arguments left right hsource)
  | conjunction leftCertificate rightCertificate ihLeft ihRight =>
      have hconstructor := CertifiedPAContextProof.conjunction_payloadLength_le
        leftCertificate.compileUnderAssumption
        rightCertificate.compileUnderAssumption
      simp only [compileUnderAssumption, structuralPayloadBound]
      omega
  | disjunctionLeft leftCertificate ihLeft =>
      simp only [compileUnderAssumption, structuralPayloadBound]
      apply le_trans
        (CertifiedPAContextProof.disjunctionLeft_payloadLength_le
          leftCertificate.compileUnderAssumption)
      omega
  | disjunctionRight rightCertificate ihRight =>
      simp only [compileUnderAssumption, structuralPayloadBound]
      apply le_trans
        (CertifiedPAContextProof.disjunctionRight_payloadLength_le
          rightCertificate.compileUnderAssumption)
      omega
  | existsWitness body witness bodyCertificate ihBody =>
      have hconstructor := CertifiedPAContextProof.existsIntro_payloadLength_le
        witness.term bodyCertificate.compileUnderAssumption
      simp only [compileUnderAssumption, structuralPayloadBound]
      omega

def prove
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula) :
    CertifiedPAProof (parameterEqualityFormula left right 🡒 formula) :=
  CertifiedPAContextProof.discharge
    (parameterEqualityFormula left right) formula
    certificate.compileUnderAssumption

def proofStructuralPayloadBound
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula) : Nat :=
  certificate.structuralPayloadBound +
    CertifiedPAContextProof.dischargeFullAssemblyCost
      (parameterEqualityFormula left right) formula

theorem prove_payloadLength_le_structuralPayloadBound
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula) :
    certificate.prove.payloadLength <=
      certificate.proofStructuralPayloadBound := by
  have hcontext :=
    compileUnderAssumption_payloadLength_le_structuralPayloadBound certificate
  have hdischarge := CertifiedPAContextProof.discharge_payloadLength_le
    (parameterEqualityFormula left right) formula
    certificate.compileUnderAssumption
  unfold prove proofStructuralPayloadBound
  exact hdischarge.trans (Nat.add_le_add_right hcontext _)

theorem prove_verifier_eq_true
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula) :
    listedCompactCertifiedPAProofVerifier certificate.prove.code
      (compactFormulaCode
        (parameterEqualityFormula left right 🡒 formula)) = true :=
  certificate.prove.verifier_eq_true

theorem prove_checked_structuralPayloadBound
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula) :
    listedCompactCertifiedPAProofVerifier certificate.prove.code
        (compactFormulaCode
          (parameterEqualityFormula left right 🡒 formula)) = true ∧
      certificate.prove.payloadLength <=
        certificate.proofStructuralPayloadBound :=
  ⟨prove_verifier_eq_true certificate,
    prove_payloadLength_le_structuralPayloadBound certificate⟩

#print axioms compileUnderAssumption_payloadLength_le_structuralPayloadBound
#print axioms prove_checked_structuralPayloadBound

end CheckedUnaryReplacementCertificate

end FoundationCompactPAUnaryBoundedFormulaTransport
