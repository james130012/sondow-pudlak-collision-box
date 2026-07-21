import integration.FoundationCompactPAQuantitativeCompilerCore

/-!
# Quantitative certified PA induction

For a body with no free parameters, this module turns certified proofs of the
zero case and the universally quantified successor step into a certified
proof of the universal conclusion.  The PA induction axiom is an explicit
one-node proof and both modus-ponens nodes are retained in the payload.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPACertifiedInduction

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactListedCertifiedVerifier
open FoundationCompactCertifiedModusPonens
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof

def inductionZeroTerm : LO.FirstOrder.ArithmeticSemiterm Nat 0 := ‘0’

def inductionStepFormula
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    LO.FirstOrder.ArithmeticProposition :=
  “∀ x, !body x → !body (x + 1)”

theorem substitutionByBoundVariable_eq_self
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    body/[#0] = body := by
  apply Semiformula.rew_eq_self_of
  · intro index
    have hindex : index = 0 := Fin.eq_zero index
    subst index
    simp
  · intro index hindex
    simp

theorem substitution_freeVariables_eq_empty
    {n : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hbody : body.freeVariables = ∅)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat n)
    (hwitness : witness.freeVariables = ∅) :
    (body/[witness]).freeVariables = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro index hindex
  rcases Semiformula.fvar?_rew hindex with hbound | hfree
  · rcases hbound with ⟨position, hposition⟩
    have hpositionZero : position = 0 := Fin.eq_zero position
    subst position
    have : index ∈ witness.freeVariables := by
      simpa using hposition
    rw [hwitness] at this
    simp at this
  · rcases hfree with ⟨sourceIndex, hsource, himage⟩
    have : sourceIndex ∈ body.freeVariables := hsource
    rw [hbody] at this
    simp at this

theorem succInd_formula
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    succInd body =
      (body/[inductionZeroTerm] 🡒
        inductionStepFormula body 🡒 ∀⁰ body) := by
  simp only [succInd, inductionZeroTerm, inductionStepFormula]
  rw [substitutionByBoundVariable_eq_self]

theorem succInd_freeVariables_eq_empty
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hclosed : body.freeVariables = ∅) :
    (succInd body).freeVariables = ∅ := by
  let selfTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1 := #0
  let successorTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1 := ‘#0 + 1’
  have hzero : (body/[inductionZeroTerm]).freeVariables = ∅ :=
    substitution_freeVariables_eq_empty body hclosed inductionZeroTerm
      (by rfl)
  have hself : (body/[selfTerm]).freeVariables = ∅ :=
    substitution_freeVariables_eq_empty body hclosed selfTerm (by rfl)
  have hsucc : (body/[successorTerm]).freeVariables = ∅ :=
    substitution_freeVariables_eq_empty body hclosed successorTerm (by rfl)
  simp only [succInd, Semiformula.freeVariables_imp,
    Semiformula.freeVariables_all]
  rw [show (body/[‘0’]).freeVariables = ∅ by
        simpa only [inductionZeroTerm] using hzero,
      show (body/[#0]).freeVariables = ∅ by
        simpa only [selfTerm] using hself,
      show (body/[‘(#0 + 1)’]).freeVariables = ∅ by
        simpa only [successorTerm] using hsucc]
  simp

theorem inductionAxiom_formula
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hclosed : body.freeVariables = ∅) :
    (Rewriting.emb (PAAxiomCertificate.induction body).sentence :
        LO.FirstOrder.ArithmeticProposition) =
      (body/[inductionZeroTerm] 🡒
        inductionStepFormula body 🡒 ∀⁰ body) := by
  rw [show (Rewriting.emb (PAAxiomCertificate.induction body).sentence :
      LO.FirstOrder.ArithmeticProposition) =
      (succInd body).univCl' by
    simp only [PAAxiomCertificate.sentence,
      Semiformula.coe_univCl_eq_univCl']]
  rw [Semiformula.univCl'_eq_self_of
    (succInd body) (succInd_freeVariables_eq_empty body hclosed)]
  exact succInd_formula body

def inductionAxiomProof
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hclosed : body.freeVariables = ∅) :
    CertifiedPAProof
      (body/[inductionZeroTerm] 🡒
        inductionStepFormula body 🡒 ∀⁰ body) :=
  CertifiedPAProof.cast (inductionAxiom_formula body hclosed)
    (CertifiedPAProof.ofAxiom (.induction body))

def proveInduction
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hclosed : body.freeVariables = ∅)
    (zeroProof : CertifiedPAProof (body/[inductionZeroTerm]))
    (stepProof : CertifiedPAProof (inductionStepFormula body)) :
    CertifiedPAProof (∀⁰ body) :=
  CertifiedPAProof.modusPonens
    (CertifiedPAProof.modusPonens
      (inductionAxiomProof body hclosed) zeroProof)
    stepProof

def inductionStructuralPayloadBound
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (zeroPayloadLength stepPayloadLength : Nat) : Nat :=
  let zeroFormula := body/[inductionZeroTerm]
  let stepFormula := inductionStepFormula body
  let conclusionFormula := (∀⁰ body : LO.FirstOrder.ArithmeticProposition)
  let intermediateFormula := stepFormula 🡒 conclusionFormula
  let axiomBound := 32 + 10 * CertifiedPAProof.axiomSyntaxBudget
    (.induction body)
  let firstBound := axiomBound + zeroPayloadLength + 240 +
    34 * FoundationCompactCertifiedModusPonens.modusPonensSyntaxBudget
      zeroFormula intermediateFormula
  firstBound + stepPayloadLength + 240 +
    34 * FoundationCompactCertifiedModusPonens.modusPonensSyntaxBudget
      stepFormula conclusionFormula

theorem proveInduction_payloadLength_le_structuralPayloadBound
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hclosed : body.freeVariables = ∅)
    (zeroProof : CertifiedPAProof (body/[inductionZeroTerm]))
    (stepProof : CertifiedPAProof (inductionStepFormula body)) :
    (proveInduction body hclosed zeroProof stepProof).payloadLength <=
      inductionStructuralPayloadBound body
        zeroProof.payloadLength stepProof.payloadLength := by
  let axiomProof := inductionAxiomProof body hclosed
  let firstProof := CertifiedPAProof.modusPonens axiomProof zeroProof
  let result := CertifiedPAProof.modusPonens firstProof stepProof
  let zeroFormula := body/[inductionZeroTerm]
  let stepFormula := inductionStepFormula body
  let conclusionFormula := (∀⁰ body : LO.FirstOrder.ArithmeticProposition)
  let intermediateFormula := stepFormula 🡒 conclusionFormula
  let axiomBound := 32 + 10 * CertifiedPAProof.axiomSyntaxBudget
    (.induction body)
  let firstBound := axiomBound + zeroProof.payloadLength + 240 +
    34 * FoundationCompactCertifiedModusPonens.modusPonensSyntaxBudget
      zeroFormula intermediateFormula
  have haxiomRaw := CertifiedPAProof.ofAxiom_payloadLength_le
    (PAAxiomCertificate.induction body)
  have haxiom : axiomProof.payloadLength <= axiomBound := by
    simpa only [axiomProof, inductionAxiomProof,
      axiomBound, CertifiedPAProof.cast_payloadLength] using haxiomRaw
  have hfirst := CertifiedPAProof.modusPonens_payloadLength_le
    axiomProof zeroProof
  have hsecond := CertifiedPAProof.modusPonens_payloadLength_le
    firstProof stepProof
  have hfirstBound : firstProof.payloadLength <= firstBound := by
    calc
      firstProof.payloadLength <= axiomProof.payloadLength +
          zeroProof.payloadLength + 240 +
          34 * FoundationCompactCertifiedModusPonens.modusPonensSyntaxBudget
            zeroFormula intermediateFormula := by
        simpa only [firstProof, zeroFormula, intermediateFormula,
          stepFormula, conclusionFormula] using hfirst
      _ <= axiomBound + zeroProof.payloadLength + 240 +
          34 * FoundationCompactCertifiedModusPonens.modusPonensSyntaxBudget
            zeroFormula intermediateFormula :=
        Nat.add_le_add_right
          (Nat.add_le_add_right
            (Nat.add_le_add_right haxiom zeroProof.payloadLength) 240) _
      _ = firstBound := by rfl
  have hresult : proveInduction body hclosed zeroProof stepProof = result := by
    rfl
  rw [hresult]
  calc
    result.payloadLength <= firstProof.payloadLength +
        stepProof.payloadLength + 240 +
        34 * FoundationCompactCertifiedModusPonens.modusPonensSyntaxBudget
          stepFormula conclusionFormula := by
      simpa only [result, stepFormula, conclusionFormula] using hsecond
    _ <= firstBound + stepProof.payloadLength + 240 +
        34 * FoundationCompactCertifiedModusPonens.modusPonensSyntaxBudget
          stepFormula conclusionFormula :=
      Nat.add_le_add_right
        (Nat.add_le_add_right
          (Nat.add_le_add_right hfirstBound stepProof.payloadLength) 240) _
    _ = inductionStructuralPayloadBound body
        zeroProof.payloadLength stepProof.payloadLength := by
      rfl

theorem proveInduction_verifier_eq_true
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hclosed : body.freeVariables = ∅)
    (zeroProof : CertifiedPAProof (body/[inductionZeroTerm]))
    (stepProof : CertifiedPAProof (inductionStepFormula body)) :
    listedCompactCertifiedPAProofVerifier
      (proveInduction body hclosed zeroProof stepProof).code
      (compactFormulaCode (∀⁰ body)) = true :=
  (proveInduction body hclosed zeroProof stepProof).verifier_eq_true

theorem proveInduction_checked_structuralPayloadBound
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hclosed : body.freeVariables = ∅)
    (zeroProof : CertifiedPAProof (body/[inductionZeroTerm]))
    (stepProof : CertifiedPAProof (inductionStepFormula body)) :
    listedCompactCertifiedPAProofVerifier
        (proveInduction body hclosed zeroProof stepProof).code
        (compactFormulaCode (∀⁰ body)) = true ∧
      (proveInduction body hclosed zeroProof stepProof).payloadLength <=
        inductionStructuralPayloadBound body
          zeroProof.payloadLength stepProof.payloadLength :=
  ⟨proveInduction_verifier_eq_true body hclosed zeroProof stepProof,
    proveInduction_payloadLength_le_structuralPayloadBound
      body hclosed zeroProof stepProof⟩

#print axioms proveInduction_checked_structuralPayloadBound

end FoundationCompactPACertifiedInduction
