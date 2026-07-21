import integration.FoundationCompactPAQuantitativeCompilerCore

/-!
# Quantitative certified PA equality transitivity

This file instantiates the real PA equality-transitivity axiom three times and
applies the already checked modus-ponens compiler twice.  The output is an
actual proof-plus-certificate payload, not an assumed transitivity interface.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAQuantitativeEqualityTransitivity

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationComputableCompactPAProofEncoder
open FoundationCompactListedCertifiedVerifier
open FoundationCompactCertifiedModusPonens
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof

def equalityTransitivityOuterBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰ ∀⁰ (#2 = #1 → #1 = #0 → #2 = #0)”

def equalityTransitivityAxiomProof :
    CertifiedPAProof (∀⁰ equalityTransitivityOuterBody) := by
  simpa [equalityTransitivityOuterBody,
    PAAxiomCertificate.sentence] using (ofAxiom .eqTrans)

def equalityTransitivityAfterFirst
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :=
  specialize equalityTransitivityAxiomProof left

def equalityTransitivityMiddleBody
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰
    (!!(Rew.bShift (Rew.bShift left)) = #1 →
      #1 = #0 →
      !!(Rew.bShift (Rew.bShift left)) = #0)”

theorem equalityTransitivityAfterFirst_formula
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    equalityTransitivityOuterBody/[left] =
      ∀⁰ equalityTransitivityMiddleBody left := by
  have htwo :
      (Rew.subst ![left]).q.q
          (#2 : LO.FirstOrder.ArithmeticSemiterm Nat 3) =
        Rew.bShift (Rew.bShift left) := by
    have hinner :
        (Rew.subst ![left]).q
            (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2) =
          Rew.bShift left := by
      simpa using
        (Rew.q_bvar_succ (Rew.subst ![left]) (0 : Fin 1))
    calc
      (Rew.subst ![left]).q.q
          (#2 : LO.FirstOrder.ArithmeticSemiterm Nat 3) =
          Rew.bShift
            ((Rew.subst ![left]).q
              (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2)) := by
        simpa using
          (Rew.q_bvar_succ
            ((Rew.subst ![left]).q) (1 : Fin 2))
      _ = Rew.bShift (Rew.bShift left) := by rw [hinner]
  have hone :
      (Rew.subst ![left]).q.q
          (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 3) =
        (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2) := by
    calc
      (Rew.subst ![left]).q.q
          (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 3) =
          Rew.bShift
            ((Rew.subst ![left]).q
              (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2)) := by
        simpa using
          (Rew.q_bvar_succ
            ((Rew.subst ![left]).q) (0 : Fin 2))
      _ = (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2) := by simp
  simp [equalityTransitivityOuterBody,
    equalityTransitivityMiddleBody, htwo, hone]

def equalityTransitivityAfterFirstAsUniversal
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof (∀⁰ equalityTransitivityMiddleBody left) :=
  cast (equalityTransitivityAfterFirst_formula left)
    (equalityTransitivityAfterFirst left)

def equalityTransitivityAfterSecondRaw
    (left middle : LO.FirstOrder.ArithmeticSemiterm Nat 0) :=
  specialize (equalityTransitivityAfterFirstAsUniversal left) middle

def equalityTransitivityInnerBody
    (left middle : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!!(Rew.bShift left) = !!(Rew.bShift middle) →
    !!(Rew.bShift middle) = #0 →
    !!(Rew.bShift left) = #0”

theorem equalityTransitivityAfterSecond_formula
    (left middle : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (equalityTransitivityMiddleBody left)/[middle] =
      ∀⁰ equalityTransitivityInnerBody left middle := by
  have hmiddle :
      (Rew.subst ![middle]).q
          (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2) =
        Rew.bShift middle := by
    simpa using
      (Rew.q_bvar_succ (Rew.subst ![middle]) (0 : Fin 1))
  simp [equalityTransitivityMiddleBody,
    equalityTransitivityInnerBody, hmiddle]

def equalityTransitivityAfterSecondAsUniversal
    (left middle : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof (∀⁰ equalityTransitivityInnerBody left middle) :=
  cast (equalityTransitivityAfterSecond_formula left middle)
    (equalityTransitivityAfterSecondRaw left middle)

def equalityTransitivityImplicationRaw
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :=
  specialize (equalityTransitivityAfterSecondAsUniversal left middle) right

theorem equalityTransitivityImplicationRaw_formula
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (equalityTransitivityInnerBody left middle)/[right] =
      (“!!left = !!middle → !!middle = !!right → !!left = !!right” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [equalityTransitivityInnerBody]

def equalityTransitivityImplication
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!left = !!middle → !!middle = !!right → !!left = !!right” :
        LO.FirstOrder.ArithmeticProposition) :=
  cast (equalityTransitivityImplicationRaw_formula left middle right)
    (equalityTransitivityImplicationRaw left middle right)

theorem equalityTransitivityImplication_payloadLength_le
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (equalityTransitivityImplication left middle right).payloadLength <=
      equalityTransitivityAxiomProof.payloadLength +
        specializationCost equalityTransitivityOuterBody left +
        specializationCost (equalityTransitivityMiddleBody left) middle +
        specializationCost
          (equalityTransitivityInnerBody left middle) right := by
  have hfirst := specialize_payloadLength_le_cost
    equalityTransitivityAxiomProof left
  have hsecond := specialize_payloadLength_le_cost
    (equalityTransitivityAfterFirstAsUniversal left) middle
  have hthird := specialize_payloadLength_le_cost
    (equalityTransitivityAfterSecondAsUniversal left middle) right
  have hfirstCast :
      (equalityTransitivityAfterFirstAsUniversal left).payloadLength =
        (equalityTransitivityAfterFirst left).payloadLength := by
    change
      (cast (equalityTransitivityAfterFirst_formula left)
        (equalityTransitivityAfterFirst left)).payloadLength = _
    exact cast_payloadLength _ _
  have hsecondCast :
      (equalityTransitivityAfterSecondAsUniversal left middle).payloadLength =
        (equalityTransitivityAfterSecondRaw left middle).payloadLength := by
    change
      (cast (equalityTransitivityAfterSecond_formula left middle)
        (equalityTransitivityAfterSecondRaw left middle)).payloadLength = _
    exact cast_payloadLength _ _
  have himplicationCast :
      (equalityTransitivityImplication left middle right).payloadLength =
        (equalityTransitivityImplicationRaw left middle right).payloadLength := by
    change
      (cast (equalityTransitivityImplicationRaw_formula left middle right)
        (equalityTransitivityImplicationRaw left middle right)).payloadLength = _
    exact cast_payloadLength _ _
  have hfirstUniversal :
      (equalityTransitivityAfterFirstAsUniversal left).payloadLength <=
        equalityTransitivityAxiomProof.payloadLength +
          specializationCost equalityTransitivityOuterBody left := by
    calc
      (equalityTransitivityAfterFirstAsUniversal left).payloadLength =
          (equalityTransitivityAfterFirst left).payloadLength := hfirstCast
      _ = (specialize equalityTransitivityAxiomProof left).payloadLength := rfl
      _ <= _ := hfirst
  have hsecondUniversal :
      (equalityTransitivityAfterSecondAsUniversal left middle).payloadLength <=
        equalityTransitivityAxiomProof.payloadLength +
          specializationCost equalityTransitivityOuterBody left +
          specializationCost (equalityTransitivityMiddleBody left) middle := by
    calc
      (equalityTransitivityAfterSecondAsUniversal left middle).payloadLength =
          (equalityTransitivityAfterSecondRaw left middle).payloadLength :=
        hsecondCast
      _ = (specialize (equalityTransitivityAfterFirstAsUniversal left)
          middle).payloadLength := rfl
      _ <= (equalityTransitivityAfterFirstAsUniversal left).payloadLength +
          specializationCost (equalityTransitivityMiddleBody left) middle :=
        hsecond
      _ <= (equalityTransitivityAxiomProof.payloadLength +
            specializationCost equalityTransitivityOuterBody left) +
          specializationCost (equalityTransitivityMiddleBody left) middle :=
        Nat.add_le_add_right hfirstUniversal _
      _ = _ := by omega
  rw [himplicationCast]
  calc
    (equalityTransitivityImplicationRaw left middle right).payloadLength =
        (specialize
          (equalityTransitivityAfterSecondAsUniversal left middle)
          right).payloadLength := rfl
    _ <= (equalityTransitivityAfterSecondAsUniversal left middle).payloadLength +
        specializationCost
          (equalityTransitivityInnerBody left middle) right := hthird
    _ <= (equalityTransitivityAxiomProof.payloadLength +
          specializationCost equalityTransitivityOuterBody left +
          specializationCost (equalityTransitivityMiddleBody left) middle) +
        specializationCost
          (equalityTransitivityInnerBody left middle) right :=
      Nat.add_le_add_right hsecondUniversal _
    _ = _ := by omega

def equalityTransitivityAfterLeft
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (leftProof : CertifiedPAProof
      (“!!left = !!middle” : LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!middle = !!right → !!left = !!right” :
        LO.FirstOrder.ArithmeticProposition) :=
  modusPonens (equalityTransitivityImplication left middle right) leftProof

/-- Compose two certified equality proofs into a real certified PA proof. -/
def proveEqualityTransitivity
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (leftProof : CertifiedPAProof
      (“!!left = !!middle” : LO.FirstOrder.ArithmeticProposition))
    (rightProof : CertifiedPAProof
      (“!!middle = !!right” : LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition) :=
  modusPonens
    (equalityTransitivityAfterLeft left middle right leftProof)
    rightProof

theorem proveEqualityTransitivity_verifier_eq_true
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (leftProof : CertifiedPAProof
      (“!!left = !!middle” : LO.FirstOrder.ArithmeticProposition))
    (rightProof : CertifiedPAProof
      (“!!middle = !!right” : LO.FirstOrder.ArithmeticProposition)) :
    listedCompactCertifiedPAProofVerifier
      (proveEqualityTransitivity left middle right
        leftProof rightProof).code
      (compactFormulaCode (“!!left = !!right” :
        LO.FirstOrder.ArithmeticProposition)) = true :=
  (proveEqualityTransitivity left middle right
    leftProof rightProof).verifier_eq_true

def equalityTransitivityFirstMPSyntaxBudget
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  modusPonensSyntaxBudget
    (“!!left = !!middle” : LO.FirstOrder.ArithmeticProposition)
    (“!!middle = !!right → !!left = !!right” :
      LO.FirstOrder.ArithmeticProposition)

def equalityTransitivitySecondMPSyntaxBudget
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  modusPonensSyntaxBudget
    (“!!middle = !!right” : LO.FirstOrder.ArithmeticProposition)
    (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)

theorem proveEqualityTransitivity_payloadLength_le
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (leftProof : CertifiedPAProof
      (“!!left = !!middle” : LO.FirstOrder.ArithmeticProposition))
    (rightProof : CertifiedPAProof
      (“!!middle = !!right” : LO.FirstOrder.ArithmeticProposition)) :
    (proveEqualityTransitivity left middle right
      leftProof rightProof).payloadLength <=
      (equalityTransitivityImplication left middle right).payloadLength +
        leftProof.payloadLength + rightProof.payloadLength + 480 +
        34 * equalityTransitivityFirstMPSyntaxBudget left middle right +
        34 * equalityTransitivitySecondMPSyntaxBudget left middle right := by
  have hfirst := modusPonens_payloadLength_le
    (equalityTransitivityImplication left middle right) leftProof
  have hsecond := modusPonens_payloadLength_le
    (equalityTransitivityAfterLeft left middle right leftProof) rightProof
  have hfirstAfter :
      (equalityTransitivityAfterLeft left middle right
        leftProof).payloadLength <=
        (equalityTransitivityImplication left middle right).payloadLength +
          leftProof.payloadLength + 240 +
          34 * equalityTransitivityFirstMPSyntaxBudget
            left middle right := by
    simpa only [equalityTransitivityAfterLeft,
      equalityTransitivityFirstMPSyntaxBudget] using hfirst
  change
    (modusPonens
      (equalityTransitivityAfterLeft left middle right leftProof)
      rightProof).payloadLength <= _
  calc
    (modusPonens
      (equalityTransitivityAfterLeft left middle right leftProof)
      rightProof).payloadLength <=
        (equalityTransitivityAfterLeft left middle right
          leftProof).payloadLength + rightProof.payloadLength + 240 +
          34 * equalityTransitivitySecondMPSyntaxBudget
            left middle right := hsecond
    _ = (equalityTransitivityAfterLeft left middle right
          leftProof).payloadLength +
        (rightProof.payloadLength + 240 +
          34 * equalityTransitivitySecondMPSyntaxBudget
            left middle right) := by omega
    _ <= ((equalityTransitivityImplication left middle right).payloadLength +
          leftProof.payloadLength + 240 +
          34 * equalityTransitivityFirstMPSyntaxBudget
            left middle right) +
        (rightProof.payloadLength + 240 +
          34 * equalityTransitivitySecondMPSyntaxBudget
            left middle right) :=
      Nat.add_le_add_right hfirstAfter _
    _ = _ := by omega

#print axioms equalityTransitivityImplication_payloadLength_le
#print axioms proveEqualityTransitivity_verifier_eq_true
#print axioms proveEqualityTransitivity_payloadLength_le

end FoundationCompactPAQuantitativeEqualityTransitivity
