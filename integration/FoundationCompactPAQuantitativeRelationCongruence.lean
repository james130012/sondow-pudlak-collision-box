import integration.FoundationCompactPAQuantitativeCompilerCore

/-!
# Quantitative certified PA congruence for binary relations

This file instantiates the real PA relation-extensionality axiom for a binary
relation symbol.  Two certified equalities are combined with the terminal
truth formula required by `Matrix.conj`; one checked modus-ponens step then
produces the implication transporting the relation from the left terms to
the equal right terms.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAQuantitativeRelationCongruence

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationComputableCompactPAProofEncoder
open FoundationCompactListedCertifiedVerifier
open FoundationCompactCertifiedModusPonens
open FoundationCompactCertifiedConjunction
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof

def binaryRelationExtMatrix
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2) :
    LO.FirstOrder.ArithmeticSemiformula Nat 4 :=
  ((“#0 = #2” : LO.FirstOrder.ArithmeticSemiformula Nat 4) ⋏
      ((“#1 = #3” : LO.FirstOrder.ArithmeticSemiformula Nat 4) ⋏ ⊤)) 🡒
    (LO.FirstOrder.Semiformula.rel relationSymbol ![#0, #1] 🡒
      LO.FirstOrder.Semiformula.rel relationSymbol ![#2, #3])

def binaryRelationExtOuterBody
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  ∀⁰ ∀⁰ ∀⁰ binaryRelationExtMatrix relationSymbol

theorem binaryRelationExtAxiom_formula
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2) :
    (Rewriting.emb (PAAxiomCertificate.eqRelExt relationSymbol).sentence :
        LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ binaryRelationExtOuterBody relationSymbol := by
  have hcastZero :
      (0 : Fin 2).addCast 2 = (0 : Fin 4) := rfl
  have hcastOne :
      (1 : Fin 2).addCast 2 = (1 : Fin 4) := rfl
  have haddZero :
      (0 : Fin 2).addNat 2 = (2 : Fin 4) := rfl
  have haddOne :
      (1 : Fin 2).addNat 2 = (3 : Fin 4) := rfl
  simp [binaryRelationExtOuterBody, binaryRelationExtMatrix,
    LO.FirstOrder.Theory.Eq.relExt, allClosure, Matrix.conj,
    Matrix.fun_eq_vec_two, hcastZero, hcastOne, haddZero, haddOne,
    PAAxiomCertificate.sentence]

def binaryRelationExtAxiomProof
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2) :
    CertifiedPAProof (∀⁰ binaryRelationExtOuterBody relationSymbol) :=
  cast (binaryRelationExtAxiom_formula relationSymbol)
    (ofAxiom (.eqRelExt relationSymbol))

def binaryRelationExtAfterRightSecondMatrix
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 3 :=
  ((“#0 = #2” : LO.FirstOrder.ArithmeticSemiformula Nat 3) ⋏
      ((“#1 = !!(Rew.bShift (Rew.bShift (Rew.bShift rightSecond)))” :
        LO.FirstOrder.ArithmeticSemiformula Nat 3) ⋏ ⊤)) 🡒
    (LO.FirstOrder.Semiformula.rel relationSymbol ![#0, #1] 🡒
      LO.FirstOrder.Semiformula.rel relationSymbol
        ![#2, Rew.bShift (Rew.bShift (Rew.bShift rightSecond))])

def binaryRelationExtRightFirstBody
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  ∀⁰ ∀⁰ binaryRelationExtAfterRightSecondMatrix relationSymbol rightSecond

theorem binaryRelationExtAfterRightSecond_formula
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryRelationExtOuterBody relationSymbol)/[rightSecond] =
      ∀⁰ binaryRelationExtRightFirstBody relationSymbol rightSecond := by
  have hone :
      (Rew.subst ![rightSecond]).q.q.q
          (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 4) =
        (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 3) := by
    calc
      (Rew.subst ![rightSecond]).q.q.q
          (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 4) =
          Rew.bShift
            ((Rew.subst ![rightSecond]).q.q
              (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 3)) := by
        simpa using
          (Rew.q_bvar_succ
            ((Rew.subst ![rightSecond]).q.q) (0 : Fin 3))
      _ = (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 3) := by simp
  have htwo :
      (Rew.subst ![rightSecond]).q.q.q
          (#2 : LO.FirstOrder.ArithmeticSemiterm Nat 4) =
        (#2 : LO.FirstOrder.ArithmeticSemiterm Nat 3) := by
    have hinner :
        (Rew.subst ![rightSecond]).q.q
            (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 3) =
          (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2) := by
      calc
        (Rew.subst ![rightSecond]).q.q
            (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 3) =
            Rew.bShift
              ((Rew.subst ![rightSecond]).q
                (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2)) := by
          simpa using
            (Rew.q_bvar_succ
              ((Rew.subst ![rightSecond]).q) (0 : Fin 2))
        _ = (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2) := by simp
    calc
      (Rew.subst ![rightSecond]).q.q.q
          (#2 : LO.FirstOrder.ArithmeticSemiterm Nat 4) =
          Rew.bShift
            ((Rew.subst ![rightSecond]).q.q
              (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 3)) := by
        simpa using
          (Rew.q_bvar_succ
            ((Rew.subst ![rightSecond]).q.q) (1 : Fin 3))
      _ = (#2 : LO.FirstOrder.ArithmeticSemiterm Nat 3) := by
        rw [hinner]
        rfl
  have hthree :
      (Rew.subst ![rightSecond]).q.q.q
          (#3 : LO.FirstOrder.ArithmeticSemiterm Nat 4) =
        Rew.bShift (Rew.bShift (Rew.bShift rightSecond)) := by
    have hinner :
        (Rew.subst ![rightSecond]).q.q
            (#2 : LO.FirstOrder.ArithmeticSemiterm Nat 3) =
          Rew.bShift (Rew.bShift rightSecond) := by
      have honeInner :
          (Rew.subst ![rightSecond]).q
              (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2) =
            Rew.bShift rightSecond := by
        simpa using
          (Rew.q_bvar_succ
            (Rew.subst ![rightSecond]) (0 : Fin 1))
      calc
        (Rew.subst ![rightSecond]).q.q
            (#2 : LO.FirstOrder.ArithmeticSemiterm Nat 3) =
            Rew.bShift
              ((Rew.subst ![rightSecond]).q
                (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2)) := by
          simpa using
            (Rew.q_bvar_succ
              ((Rew.subst ![rightSecond]).q) (1 : Fin 2))
        _ = Rew.bShift (Rew.bShift rightSecond) := by rw [honeInner]
    calc
      (Rew.subst ![rightSecond]).q.q.q
          (#3 : LO.FirstOrder.ArithmeticSemiterm Nat 4) =
          Rew.bShift
            ((Rew.subst ![rightSecond]).q.q
              (#2 : LO.FirstOrder.ArithmeticSemiterm Nat 3)) := by
        simpa using
          (Rew.q_bvar_succ
            ((Rew.subst ![rightSecond]).q.q) (2 : Fin 3))
      _ = Rew.bShift (Rew.bShift (Rew.bShift rightSecond)) := by
        rw [hinner]
  simp [binaryRelationExtOuterBody, binaryRelationExtMatrix,
    binaryRelationExtRightFirstBody,
    binaryRelationExtAfterRightSecondMatrix, hone, htwo, hthree]

def binaryRelationExtAfterRightSecondRaw
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :=
  specialize (binaryRelationExtAxiomProof relationSymbol) rightSecond

def binaryRelationExtAfterRightSecond
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (∀⁰ binaryRelationExtRightFirstBody relationSymbol rightSecond) :=
  cast (binaryRelationExtAfterRightSecond_formula relationSymbol rightSecond)
    (binaryRelationExtAfterRightSecondRaw relationSymbol rightSecond)

def binaryRelationExtAfterRightFirstMatrix
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (rightFirst rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 2 :=
  ((“#0 = !!(Rew.bShift (Rew.bShift rightFirst))” :
      LO.FirstOrder.ArithmeticSemiformula Nat 2) ⋏
      ((“#1 = !!(Rew.bShift (Rew.bShift rightSecond))” :
        LO.FirstOrder.ArithmeticSemiformula Nat 2) ⋏ ⊤)) 🡒
    (LO.FirstOrder.Semiformula.rel relationSymbol ![#0, #1] 🡒
      LO.FirstOrder.Semiformula.rel relationSymbol
        ![Rew.bShift (Rew.bShift rightFirst),
          Rew.bShift (Rew.bShift rightSecond)])

def binaryRelationExtLeftSecondBody
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (rightFirst rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  ∀⁰ binaryRelationExtAfterRightFirstMatrix relationSymbol
    rightFirst rightSecond

theorem binaryRelationExtAfterRightFirst_formula
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (rightFirst rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryRelationExtRightFirstBody relationSymbol rightSecond)/[rightFirst] =
      ∀⁰ binaryRelationExtLeftSecondBody relationSymbol
        rightFirst rightSecond := by
  have hone :
      (Rew.subst ![rightFirst]).q.q
          (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 3) =
        (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2) := by
    calc
      (Rew.subst ![rightFirst]).q.q
          (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 3) =
          Rew.bShift
            ((Rew.subst ![rightFirst]).q
              (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2)) := by
        simpa using
          (Rew.q_bvar_succ
            ((Rew.subst ![rightFirst]).q) (0 : Fin 2))
      _ = (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2) := by simp
  have htwo :
      (Rew.subst ![rightFirst]).q.q
          (#2 : LO.FirstOrder.ArithmeticSemiterm Nat 3) =
        Rew.bShift (Rew.bShift rightFirst) := by
    have hinner :
        (Rew.subst ![rightFirst]).q
            (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2) =
          Rew.bShift rightFirst := by
      simpa using
        (Rew.q_bvar_succ
          (Rew.subst ![rightFirst]) (0 : Fin 1))
    calc
      (Rew.subst ![rightFirst]).q.q
          (#2 : LO.FirstOrder.ArithmeticSemiterm Nat 3) =
          Rew.bShift
            ((Rew.subst ![rightFirst]).q
              (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2)) := by
        simpa using
          (Rew.q_bvar_succ
            ((Rew.subst ![rightFirst]).q) (1 : Fin 2))
      _ = Rew.bShift (Rew.bShift rightFirst) := by rw [hinner]
  simp [binaryRelationExtRightFirstBody,
    binaryRelationExtAfterRightSecondMatrix,
    binaryRelationExtLeftSecondBody,
    binaryRelationExtAfterRightFirstMatrix, hone, htwo]

def binaryRelationExtAfterRightFirstRaw
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (rightFirst rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :=
  specialize (binaryRelationExtAfterRightSecond relationSymbol rightSecond)
    rightFirst

def binaryRelationExtAfterRightFirst
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (rightFirst rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (∀⁰ binaryRelationExtLeftSecondBody relationSymbol
        rightFirst rightSecond) :=
  cast (binaryRelationExtAfterRightFirst_formula relationSymbol
      rightFirst rightSecond)
    (binaryRelationExtAfterRightFirstRaw relationSymbol rightFirst rightSecond)

def binaryRelationExtAfterLeftSecondMatrix
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  ((“#0 = !!(Rew.bShift rightFirst)” :
      LO.FirstOrder.ArithmeticSemiformula Nat 1) ⋏
      ((“!!(Rew.bShift leftSecond) = !!(Rew.bShift rightSecond)” :
        LO.FirstOrder.ArithmeticSemiformula Nat 1) ⋏ ⊤)) 🡒
    (LO.FirstOrder.Semiformula.rel relationSymbol
        ![#0, Rew.bShift leftSecond] 🡒
      LO.FirstOrder.Semiformula.rel relationSymbol
        ![Rew.bShift rightFirst, Rew.bShift rightSecond])

theorem binaryRelationExtAfterLeftSecond_formula
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryRelationExtLeftSecondBody relationSymbol
        rightFirst rightSecond)/[leftSecond] =
      ∀⁰ binaryRelationExtAfterLeftSecondMatrix relationSymbol
        leftSecond rightFirst rightSecond := by
  have hone :
      (Rew.subst ![leftSecond]).q
          (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2) =
        Rew.bShift leftSecond := by
    simpa using
      (Rew.q_bvar_succ
        (Rew.subst ![leftSecond]) (0 : Fin 1))
  simp [binaryRelationExtLeftSecondBody,
    binaryRelationExtAfterRightFirstMatrix,
    binaryRelationExtAfterLeftSecondMatrix, hone]

def binaryRelationExtAfterLeftSecondRaw
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :=
  specialize (binaryRelationExtAfterRightFirst relationSymbol
    rightFirst rightSecond) leftSecond

def binaryRelationExtAfterLeftSecond
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (∀⁰ binaryRelationExtAfterLeftSecondMatrix relationSymbol
        leftSecond rightFirst rightSecond) :=
  cast (binaryRelationExtAfterLeftSecond_formula relationSymbol
      leftSecond rightFirst rightSecond)
    (binaryRelationExtAfterLeftSecondRaw relationSymbol leftSecond
      rightFirst rightSecond)

def binaryRelationFormula
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (first second : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  LO.FirstOrder.Semiformula.rel relationSymbol ![first, second]

def binaryRelationCongruenceAntecedent
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  (“!!leftFirst = !!rightFirst” : LO.FirstOrder.ArithmeticProposition) ⋏
    ((“!!leftSecond = !!rightSecond” :
      LO.FirstOrder.ArithmeticProposition) ⋏ ⊤)

def binaryRelationCongruenceConclusion
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  binaryRelationFormula relationSymbol leftFirst leftSecond 🡒
    binaryRelationFormula relationSymbol rightFirst rightSecond

theorem binaryRelationExtFinal_formula
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryRelationExtAfterLeftSecondMatrix relationSymbol leftSecond
        rightFirst rightSecond)/[leftFirst] =
      (binaryRelationCongruenceAntecedent leftFirst leftSecond
          rightFirst rightSecond 🡒
        binaryRelationCongruenceConclusion relationSymbol leftFirst leftSecond
          rightFirst rightSecond) := by
  simp [binaryRelationExtAfterLeftSecondMatrix,
    binaryRelationCongruenceAntecedent,
    binaryRelationCongruenceConclusion, binaryRelationFormula]

def binaryRelationExtImplicationRaw
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :=
  specialize (binaryRelationExtAfterLeftSecond relationSymbol leftSecond
    rightFirst rightSecond) leftFirst

def binaryRelationExtImplication
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (binaryRelationCongruenceAntecedent leftFirst leftSecond
          rightFirst rightSecond 🡒
        binaryRelationCongruenceConclusion relationSymbol leftFirst leftSecond
          rightFirst rightSecond) :=
  cast (binaryRelationExtFinal_formula relationSymbol leftFirst leftSecond
      rightFirst rightSecond)
    (binaryRelationExtImplicationRaw relationSymbol leftFirst leftSecond
      rightFirst rightSecond)

theorem binaryRelationExtAxiomProof_payloadLength_le
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2) :
    (binaryRelationExtAxiomProof relationSymbol).payloadLength <=
      32 + 10 * axiomSyntaxBudget (.eqRelExt relationSymbol) := by
  calc
    (binaryRelationExtAxiomProof relationSymbol).payloadLength =
        (ofAxiom (.eqRelExt relationSymbol)).payloadLength := by
      change
        (cast (binaryRelationExtAxiom_formula relationSymbol)
          (ofAxiom (.eqRelExt relationSymbol))).payloadLength = _
      exact cast_payloadLength _ _
    _ <= _ := ofAxiom_payloadLength_le (.eqRelExt relationSymbol)

theorem binaryRelationExtImplication_payloadLength_le
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryRelationExtImplication relationSymbol leftFirst leftSecond
      rightFirst rightSecond).payloadLength <=
        (binaryRelationExtAxiomProof relationSymbol).payloadLength +
          specializationCost
            (binaryRelationExtOuterBody relationSymbol) rightSecond +
          specializationCost
            (binaryRelationExtRightFirstBody relationSymbol rightSecond)
            rightFirst +
          specializationCost
            (binaryRelationExtLeftSecondBody relationSymbol
              rightFirst rightSecond) leftSecond +
          specializationCost
            (binaryRelationExtAfterLeftSecondMatrix relationSymbol
              leftSecond rightFirst rightSecond) leftFirst := by
  have hfirst := specialize_payloadLength_le_cost
    (binaryRelationExtAxiomProof relationSymbol) rightSecond
  have hsecond := specialize_payloadLength_le_cost
    (binaryRelationExtAfterRightSecond relationSymbol rightSecond) rightFirst
  have hthird := specialize_payloadLength_le_cost
    (binaryRelationExtAfterRightFirst relationSymbol rightFirst rightSecond)
    leftSecond
  have hfourth := specialize_payloadLength_le_cost
    (binaryRelationExtAfterLeftSecond relationSymbol leftSecond
      rightFirst rightSecond) leftFirst
  have hfirstCast :
      (binaryRelationExtAfterRightSecond relationSymbol
        rightSecond).payloadLength =
      (binaryRelationExtAfterRightSecondRaw relationSymbol
        rightSecond).payloadLength := by
    change
      (cast
        (binaryRelationExtAfterRightSecond_formula relationSymbol rightSecond)
        (binaryRelationExtAfterRightSecondRaw relationSymbol
          rightSecond)).payloadLength = _
    exact cast_payloadLength _ _
  have hsecondCast :
      (binaryRelationExtAfterRightFirst relationSymbol rightFirst
        rightSecond).payloadLength =
      (binaryRelationExtAfterRightFirstRaw relationSymbol rightFirst
        rightSecond).payloadLength := by
    change
      (cast
        (binaryRelationExtAfterRightFirst_formula relationSymbol
          rightFirst rightSecond)
        (binaryRelationExtAfterRightFirstRaw relationSymbol rightFirst
          rightSecond)).payloadLength = _
    exact cast_payloadLength _ _
  have hthirdCast :
      (binaryRelationExtAfterLeftSecond relationSymbol leftSecond
        rightFirst rightSecond).payloadLength =
      (binaryRelationExtAfterLeftSecondRaw relationSymbol leftSecond
        rightFirst rightSecond).payloadLength := by
    change
      (cast
        (binaryRelationExtAfterLeftSecond_formula relationSymbol leftSecond
          rightFirst rightSecond)
        (binaryRelationExtAfterLeftSecondRaw relationSymbol leftSecond
          rightFirst rightSecond)).payloadLength = _
    exact cast_payloadLength _ _
  have hfinalCast :
      (binaryRelationExtImplication relationSymbol leftFirst leftSecond
        rightFirst rightSecond).payloadLength =
      (binaryRelationExtImplicationRaw relationSymbol leftFirst leftSecond
        rightFirst rightSecond).payloadLength := by
    change
      (cast
        (binaryRelationExtFinal_formula relationSymbol leftFirst leftSecond
          rightFirst rightSecond)
        (binaryRelationExtImplicationRaw relationSymbol leftFirst leftSecond
          rightFirst rightSecond)).payloadLength = _
    exact cast_payloadLength _ _
  have hfirstBound :
      (binaryRelationExtAfterRightSecond relationSymbol
        rightSecond).payloadLength <=
        (binaryRelationExtAxiomProof relationSymbol).payloadLength +
          specializationCost
            (binaryRelationExtOuterBody relationSymbol) rightSecond := by
    calc
      (binaryRelationExtAfterRightSecond relationSymbol
          rightSecond).payloadLength =
          (binaryRelationExtAfterRightSecondRaw relationSymbol
            rightSecond).payloadLength := hfirstCast
      _ = (specialize (binaryRelationExtAxiomProof relationSymbol)
          rightSecond).payloadLength := rfl
      _ <= _ := hfirst
  have hsecondBound :
      (binaryRelationExtAfterRightFirst relationSymbol rightFirst
        rightSecond).payloadLength <=
        (binaryRelationExtAxiomProof relationSymbol).payloadLength +
          specializationCost
            (binaryRelationExtOuterBody relationSymbol) rightSecond +
          specializationCost
            (binaryRelationExtRightFirstBody relationSymbol rightSecond)
            rightFirst := by
    calc
      (binaryRelationExtAfterRightFirst relationSymbol rightFirst
          rightSecond).payloadLength =
          (binaryRelationExtAfterRightFirstRaw relationSymbol rightFirst
            rightSecond).payloadLength := hsecondCast
      _ = (specialize
          (binaryRelationExtAfterRightSecond relationSymbol rightSecond)
          rightFirst).payloadLength := rfl
      _ <= (binaryRelationExtAfterRightSecond relationSymbol
          rightSecond).payloadLength +
          specializationCost
            (binaryRelationExtRightFirstBody relationSymbol rightSecond)
            rightFirst := hsecond
      _ <= ((binaryRelationExtAxiomProof relationSymbol).payloadLength +
            specializationCost
              (binaryRelationExtOuterBody relationSymbol) rightSecond) +
          specializationCost
            (binaryRelationExtRightFirstBody relationSymbol rightSecond)
            rightFirst := Nat.add_le_add_right hfirstBound _
      _ = _ := by omega
  have hthirdBound :
      (binaryRelationExtAfterLeftSecond relationSymbol leftSecond
        rightFirst rightSecond).payloadLength <=
        (binaryRelationExtAxiomProof relationSymbol).payloadLength +
          specializationCost
            (binaryRelationExtOuterBody relationSymbol) rightSecond +
          specializationCost
            (binaryRelationExtRightFirstBody relationSymbol rightSecond)
            rightFirst +
          specializationCost
            (binaryRelationExtLeftSecondBody relationSymbol
              rightFirst rightSecond) leftSecond := by
    calc
      (binaryRelationExtAfterLeftSecond relationSymbol leftSecond
          rightFirst rightSecond).payloadLength =
          (binaryRelationExtAfterLeftSecondRaw relationSymbol leftSecond
            rightFirst rightSecond).payloadLength := hthirdCast
      _ = (specialize
          (binaryRelationExtAfterRightFirst relationSymbol
            rightFirst rightSecond) leftSecond).payloadLength := rfl
      _ <= (binaryRelationExtAfterRightFirst relationSymbol
          rightFirst rightSecond).payloadLength +
          specializationCost
            (binaryRelationExtLeftSecondBody relationSymbol
              rightFirst rightSecond) leftSecond := hthird
      _ <= ((binaryRelationExtAxiomProof relationSymbol).payloadLength +
            specializationCost
              (binaryRelationExtOuterBody relationSymbol) rightSecond +
            specializationCost
              (binaryRelationExtRightFirstBody relationSymbol rightSecond)
              rightFirst) +
          specializationCost
            (binaryRelationExtLeftSecondBody relationSymbol
              rightFirst rightSecond) leftSecond :=
        Nat.add_le_add_right hsecondBound _
      _ = _ := by omega
  rw [hfinalCast]
  calc
    (binaryRelationExtImplicationRaw relationSymbol leftFirst leftSecond
        rightFirst rightSecond).payloadLength =
        (specialize
          (binaryRelationExtAfterLeftSecond relationSymbol leftSecond
            rightFirst rightSecond) leftFirst).payloadLength := rfl
    _ <= (binaryRelationExtAfterLeftSecond relationSymbol leftSecond
        rightFirst rightSecond).payloadLength +
        specializationCost
          (binaryRelationExtAfterLeftSecondMatrix relationSymbol
            leftSecond rightFirst rightSecond) leftFirst := hfourth
    _ <= ((binaryRelationExtAxiomProof relationSymbol).payloadLength +
          specializationCost
            (binaryRelationExtOuterBody relationSymbol) rightSecond +
          specializationCost
            (binaryRelationExtRightFirstBody relationSymbol rightSecond)
            rightFirst +
          specializationCost
            (binaryRelationExtLeftSecondBody relationSymbol
              rightFirst rightSecond) leftSecond) +
        specializationCost
          (binaryRelationExtAfterLeftSecondMatrix relationSymbol
            leftSecond rightFirst rightSecond) leftFirst :=
      Nat.add_le_add_right hthirdBound _
    _ = _ := by omega

def binaryRelationCongruenceAntecedentProof
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (binaryRelationCongruenceAntecedent leftFirst leftSecond
        rightFirst rightSecond) := by
  simpa [binaryRelationCongruenceAntecedent] using
    conjunction firstProof (conjunction secondProof verumProof)

/-- The generic proof-producing congruence compiler for a binary PA relation. -/
def proveBinaryRelationTransportImplication
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (binaryRelationCongruenceConclusion relationSymbol leftFirst leftSecond
        rightFirst rightSecond) :=
  modusPonens
    (binaryRelationExtImplication relationSymbol leftFirst leftSecond
      rightFirst rightSecond)
    (binaryRelationCongruenceAntecedentProof leftFirst leftSecond
      rightFirst rightSecond firstProof secondProof)

theorem proveBinaryRelationTransportImplication_verifier_eq_true
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    listedCompactCertifiedPAProofVerifier
      (proveBinaryRelationTransportImplication relationSymbol
        leftFirst leftSecond rightFirst rightSecond firstProof secondProof).code
      (compactFormulaCode
        (binaryRelationCongruenceConclusion relationSymbol
          leftFirst leftSecond rightFirst rightSecond)) = true :=
  (proveBinaryRelationTransportImplication relationSymbol
    leftFirst leftSecond rightFirst rightSecond
    firstProof secondProof).verifier_eq_true

def binaryRelationCongruenceInnerConjunctionSyntaxBudget
    (leftSecond rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  conjunctionSyntaxBudget
    (“!!leftSecond = !!rightSecond” :
      LO.FirstOrder.ArithmeticProposition)
    (⊤ : LO.FirstOrder.ArithmeticProposition)

def binaryRelationCongruenceOuterConjunctionSyntaxBudget
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  conjunctionSyntaxBudget
    (“!!leftFirst = !!rightFirst” :
      LO.FirstOrder.ArithmeticProposition)
    ((“!!leftSecond = !!rightSecond” :
      LO.FirstOrder.ArithmeticProposition) ⋏ ⊤)

def binaryRelationCongruenceMPSyntaxBudget
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  modusPonensSyntaxBudget
    (binaryRelationCongruenceAntecedent leftFirst leftSecond
      rightFirst rightSecond)
    (binaryRelationCongruenceConclusion relationSymbol leftFirst leftSecond
      rightFirst rightSecond)

theorem proveBinaryRelationTransportImplication_payloadLength_le
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    (proveBinaryRelationTransportImplication relationSymbol
      leftFirst leftSecond rightFirst rightSecond
      firstProof secondProof).payloadLength <=
        (binaryRelationExtImplication relationSymbol leftFirst leftSecond
          rightFirst rightSecond).payloadLength +
        firstProof.payloadLength + secondProof.payloadLength + 576 +
        9 * verumSyntaxBudget +
        11 * binaryRelationCongruenceInnerConjunctionSyntaxBudget
          leftSecond rightSecond +
        11 * binaryRelationCongruenceOuterConjunctionSyntaxBudget
          leftFirst leftSecond rightFirst rightSecond +
        34 * binaryRelationCongruenceMPSyntaxBudget relationSymbol
          leftFirst leftSecond rightFirst rightSecond := by
  have htruth := verumProof_payloadLength_le
  have hinner := conjunction_payloadLength_le secondProof verumProof
  have houter := conjunction_payloadLength_le firstProof
    (conjunction secondProof verumProof)
  have himplication := modusPonens_payloadLength_le
    (binaryRelationExtImplication relationSymbol leftFirst leftSecond
      rightFirst rightSecond)
    (binaryRelationCongruenceAntecedentProof leftFirst leftSecond
      rightFirst rightSecond firstProof secondProof)
  have hinnerBound :
      (conjunction secondProof verumProof).payloadLength <=
        secondProof.payloadLength + 48 + 9 * verumSyntaxBudget + 144 +
          11 * binaryRelationCongruenceInnerConjunctionSyntaxBudget
            leftSecond rightSecond := by
    calc
      (conjunction secondProof verumProof).payloadLength <=
          secondProof.payloadLength + verumProof.payloadLength + 144 +
            11 * binaryRelationCongruenceInnerConjunctionSyntaxBudget
              leftSecond rightSecond := by
        simpa [binaryRelationCongruenceInnerConjunctionSyntaxBudget] using
          hinner
      _ <= secondProof.payloadLength +
          (48 + 9 * verumSyntaxBudget) + 144 +
            11 * binaryRelationCongruenceInnerConjunctionSyntaxBudget
              leftSecond rightSecond := by omega
      _ = _ := by omega
  have hantecedent :
      (binaryRelationCongruenceAntecedentProof leftFirst leftSecond
        rightFirst rightSecond firstProof secondProof).payloadLength <=
        firstProof.payloadLength + secondProof.payloadLength + 336 +
          9 * verumSyntaxBudget +
          11 * binaryRelationCongruenceInnerConjunctionSyntaxBudget
            leftSecond rightSecond +
          11 * binaryRelationCongruenceOuterConjunctionSyntaxBudget
            leftFirst leftSecond rightFirst rightSecond := by
    change
      (conjunction firstProof
        (conjunction secondProof verumProof)).payloadLength <= _
    calc
      (conjunction firstProof
          (conjunction secondProof verumProof)).payloadLength <=
          firstProof.payloadLength +
            (conjunction secondProof verumProof).payloadLength + 144 +
            11 * binaryRelationCongruenceOuterConjunctionSyntaxBudget
              leftFirst leftSecond rightFirst rightSecond := by
        simpa [binaryRelationCongruenceOuterConjunctionSyntaxBudget] using
          houter
      _ <= firstProof.payloadLength +
          (secondProof.payloadLength + 48 + 9 * verumSyntaxBudget + 144 +
            11 * binaryRelationCongruenceInnerConjunctionSyntaxBudget
              leftSecond rightSecond) + 144 +
            11 * binaryRelationCongruenceOuterConjunctionSyntaxBudget
              leftFirst leftSecond rightFirst rightSecond := by omega
      _ = _ := by omega
  change
    (modusPonens
      (binaryRelationExtImplication relationSymbol leftFirst leftSecond
        rightFirst rightSecond)
      (binaryRelationCongruenceAntecedentProof leftFirst leftSecond
        rightFirst rightSecond firstProof secondProof)).payloadLength <= _
  calc
    (modusPonens
      (binaryRelationExtImplication relationSymbol leftFirst leftSecond
        rightFirst rightSecond)
      (binaryRelationCongruenceAntecedentProof leftFirst leftSecond
        rightFirst rightSecond firstProof secondProof)).payloadLength <=
        (binaryRelationExtImplication relationSymbol leftFirst leftSecond
          rightFirst rightSecond).payloadLength +
        (binaryRelationCongruenceAntecedentProof leftFirst leftSecond
          rightFirst rightSecond firstProof secondProof).payloadLength + 240 +
        34 * binaryRelationCongruenceMPSyntaxBudget relationSymbol
          leftFirst leftSecond rightFirst rightSecond := by
      simpa [binaryRelationCongruenceMPSyntaxBudget] using himplication
    _ <= (binaryRelationExtImplication relationSymbol leftFirst leftSecond
          rightFirst rightSecond).payloadLength +
        (firstProof.payloadLength + secondProof.payloadLength + 336 +
          9 * verumSyntaxBudget +
          11 * binaryRelationCongruenceInnerConjunctionSyntaxBudget
            leftSecond rightSecond +
          11 * binaryRelationCongruenceOuterConjunctionSyntaxBudget
            leftFirst leftSecond rightFirst rightSecond) + 240 +
        34 * binaryRelationCongruenceMPSyntaxBudget relationSymbol
          leftFirst leftSecond rightFirst rightSecond := by omega
    _ = _ := by omega

def binaryRelationTransportFullPayloadBound
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstPayloadLength secondPayloadLength : Nat) : Nat :=
  firstPayloadLength + secondPayloadLength + 608 +
    10 * axiomSyntaxBudget (.eqRelExt relationSymbol) +
    specializationCost
      (binaryRelationExtOuterBody relationSymbol) rightSecond +
    specializationCost
      (binaryRelationExtRightFirstBody relationSymbol rightSecond)
      rightFirst +
    specializationCost
      (binaryRelationExtLeftSecondBody relationSymbol
        rightFirst rightSecond) leftSecond +
    specializationCost
      (binaryRelationExtAfterLeftSecondMatrix relationSymbol
        leftSecond rightFirst rightSecond) leftFirst +
    9 * verumSyntaxBudget +
    11 * binaryRelationCongruenceInnerConjunctionSyntaxBudget
      leftSecond rightSecond +
    11 * binaryRelationCongruenceOuterConjunctionSyntaxBudget
      leftFirst leftSecond rightFirst rightSecond +
    34 * binaryRelationCongruenceMPSyntaxBudget relationSymbol
      leftFirst leftSecond rightFirst rightSecond

theorem proveBinaryRelationTransportImplication_full_payloadLength_le
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    (proveBinaryRelationTransportImplication relationSymbol
      leftFirst leftSecond rightFirst rightSecond
      firstProof secondProof).payloadLength <=
      binaryRelationTransportFullPayloadBound relationSymbol
        leftFirst leftSecond rightFirst rightSecond
        firstProof.payloadLength secondProof.payloadLength := by
  have hproof := proveBinaryRelationTransportImplication_payloadLength_le
    relationSymbol leftFirst leftSecond rightFirst rightSecond
    firstProof secondProof
  have himplication := binaryRelationExtImplication_payloadLength_le
    relationSymbol leftFirst leftSecond rightFirst rightSecond
  have haxiom := binaryRelationExtAxiomProof_payloadLength_le relationSymbol
  simp only [binaryRelationTransportFullPayloadBound]
  omega

#print axioms proveBinaryRelationTransportImplication_verifier_eq_true
#print axioms proveBinaryRelationTransportImplication_full_payloadLength_le

end FoundationCompactPAQuantitativeRelationCongruence
