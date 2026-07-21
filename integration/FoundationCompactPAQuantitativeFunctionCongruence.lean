import integration.FoundationCompactPAQuantitativeCompilerCore

/-!
# Quantitative certified PA congruence for binary functions

This file instantiates the real PA function-extensionality axiom for a binary
function symbol.  Two certified equalities are combined with the terminal
truth formula required by `Matrix.conj`; one checked modus-ponens step then
produces the corresponding equality of function applications.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAQuantitativeFunctionCongruence

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

def binaryFunctionExtMatrix
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2) :
    LO.FirstOrder.ArithmeticSemiformula Nat 4 :=
  ((“#0 = #2” : LO.FirstOrder.ArithmeticSemiformula Nat 4) ⋏
      ((“#1 = #3” : LO.FirstOrder.ArithmeticSemiformula Nat 4) ⋏ ⊤)) 🡒
    (“!!(LO.FirstOrder.Semiterm.func functionSymbol ![#0, #1]) =
      !!(LO.FirstOrder.Semiterm.func functionSymbol ![#2, #3])” :
      LO.FirstOrder.ArithmeticSemiformula Nat 4)

def binaryFunctionExtOuterBody
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  ∀⁰ ∀⁰ ∀⁰ binaryFunctionExtMatrix functionSymbol

theorem binaryFunctionExtAxiom_formula
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2) :
    (Rewriting.emb (PAAxiomCertificate.eqFuncExt functionSymbol).sentence :
        LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ binaryFunctionExtOuterBody functionSymbol := by
  have hcastZero :
      (0 : Fin 2).addCast 2 = (0 : Fin 4) := rfl
  have hcastOne :
      (1 : Fin 2).addCast 2 = (1 : Fin 4) := rfl
  have haddZero :
      (0 : Fin 2).addNat 2 = (2 : Fin 4) := rfl
  have haddOne :
      (1 : Fin 2).addNat 2 = (3 : Fin 4) := rfl
  simp [binaryFunctionExtOuterBody, binaryFunctionExtMatrix,
    LO.FirstOrder.Theory.Eq.funcExt, allClosure, Matrix.conj,
    Matrix.fun_eq_vec_two, hcastZero, hcastOne, haddZero, haddOne,
    PAAxiomCertificate.sentence]

def binaryFunctionExtAxiomProof
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2) :
    CertifiedPAProof (∀⁰ binaryFunctionExtOuterBody functionSymbol) :=
  cast (binaryFunctionExtAxiom_formula functionSymbol)
    (ofAxiom (.eqFuncExt functionSymbol))

def binaryFunctionExtAfterRightSecondMatrix
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 3 :=
  ((“#0 = #2” : LO.FirstOrder.ArithmeticSemiformula Nat 3) ⋏
      ((“#1 = !!(Rew.bShift (Rew.bShift (Rew.bShift rightSecond)))” :
        LO.FirstOrder.ArithmeticSemiformula Nat 3) ⋏ ⊤)) 🡒
    (“!!(LO.FirstOrder.Semiterm.func functionSymbol ![#0, #1]) =
      !!(LO.FirstOrder.Semiterm.func functionSymbol
        ![#2, Rew.bShift (Rew.bShift (Rew.bShift rightSecond))])” :
      LO.FirstOrder.ArithmeticSemiformula Nat 3)

def binaryFunctionExtRightFirstBody
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  ∀⁰ ∀⁰ binaryFunctionExtAfterRightSecondMatrix functionSymbol rightSecond

theorem binaryFunctionExtAfterRightSecond_formula
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryFunctionExtOuterBody functionSymbol)/[rightSecond] =
      ∀⁰ binaryFunctionExtRightFirstBody functionSymbol rightSecond := by
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
  simp [binaryFunctionExtOuterBody, binaryFunctionExtMatrix,
    binaryFunctionExtRightFirstBody,
    binaryFunctionExtAfterRightSecondMatrix, hone, htwo, hthree]

def binaryFunctionExtAfterRightSecondRaw
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :=
  specialize (binaryFunctionExtAxiomProof functionSymbol) rightSecond

def binaryFunctionExtAfterRightSecond
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (∀⁰ binaryFunctionExtRightFirstBody functionSymbol rightSecond) :=
  cast (binaryFunctionExtAfterRightSecond_formula functionSymbol rightSecond)
    (binaryFunctionExtAfterRightSecondRaw functionSymbol rightSecond)

def binaryFunctionExtAfterRightFirstMatrix
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (rightFirst rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 2 :=
  ((“#0 = !!(Rew.bShift (Rew.bShift rightFirst))” :
      LO.FirstOrder.ArithmeticSemiformula Nat 2) ⋏
      ((“#1 = !!(Rew.bShift (Rew.bShift rightSecond))” :
        LO.FirstOrder.ArithmeticSemiformula Nat 2) ⋏ ⊤)) 🡒
    (“!!(LO.FirstOrder.Semiterm.func functionSymbol
        ![#0, #1]) =
      !!(LO.FirstOrder.Semiterm.func functionSymbol
        ![Rew.bShift (Rew.bShift rightFirst),
          Rew.bShift (Rew.bShift rightSecond)])” :
      LO.FirstOrder.ArithmeticSemiformula Nat 2)

def binaryFunctionExtLeftSecondBody
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (rightFirst rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  ∀⁰ binaryFunctionExtAfterRightFirstMatrix functionSymbol
    rightFirst rightSecond

theorem binaryFunctionExtAfterRightFirst_formula
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (rightFirst rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryFunctionExtRightFirstBody functionSymbol rightSecond)/[rightFirst] =
      ∀⁰ binaryFunctionExtLeftSecondBody functionSymbol
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
  simp [binaryFunctionExtRightFirstBody,
    binaryFunctionExtAfterRightSecondMatrix,
    binaryFunctionExtLeftSecondBody,
    binaryFunctionExtAfterRightFirstMatrix, hone, htwo]

def binaryFunctionExtAfterRightFirstRaw
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (rightFirst rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :=
  specialize (binaryFunctionExtAfterRightSecond functionSymbol rightSecond)
    rightFirst

def binaryFunctionExtAfterRightFirst
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (rightFirst rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (∀⁰ binaryFunctionExtLeftSecondBody functionSymbol
        rightFirst rightSecond) :=
  cast (binaryFunctionExtAfterRightFirst_formula functionSymbol
      rightFirst rightSecond)
    (binaryFunctionExtAfterRightFirstRaw functionSymbol rightFirst rightSecond)

def binaryFunctionExtAfterLeftSecondMatrix
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  ((“#0 = !!(Rew.bShift rightFirst)” :
      LO.FirstOrder.ArithmeticSemiformula Nat 1) ⋏
      ((“!!(Rew.bShift leftSecond) = !!(Rew.bShift rightSecond)” :
        LO.FirstOrder.ArithmeticSemiformula Nat 1) ⋏ ⊤)) 🡒
    (“!!(LO.FirstOrder.Semiterm.func functionSymbol
        ![#0, Rew.bShift leftSecond]) =
      !!(LO.FirstOrder.Semiterm.func functionSymbol
        ![Rew.bShift rightFirst, Rew.bShift rightSecond])” :
      LO.FirstOrder.ArithmeticSemiformula Nat 1)

theorem binaryFunctionExtAfterLeftSecond_formula
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryFunctionExtLeftSecondBody functionSymbol
        rightFirst rightSecond)/[leftSecond] =
      ∀⁰ binaryFunctionExtAfterLeftSecondMatrix functionSymbol
        leftSecond rightFirst rightSecond := by
  have hone :
      (Rew.subst ![leftSecond]).q
          (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2) =
        Rew.bShift leftSecond := by
    simpa using
      (Rew.q_bvar_succ
        (Rew.subst ![leftSecond]) (0 : Fin 1))
  simp [binaryFunctionExtLeftSecondBody,
    binaryFunctionExtAfterRightFirstMatrix,
    binaryFunctionExtAfterLeftSecondMatrix, hone]

def binaryFunctionExtAfterLeftSecondRaw
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :=
  specialize (binaryFunctionExtAfterRightFirst functionSymbol
    rightFirst rightSecond) leftSecond

def binaryFunctionExtAfterLeftSecond
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (∀⁰ binaryFunctionExtAfterLeftSecondMatrix functionSymbol
        leftSecond rightFirst rightSecond) :=
  cast (binaryFunctionExtAfterLeftSecond_formula functionSymbol
      leftSecond rightFirst rightSecond)
    (binaryFunctionExtAfterLeftSecondRaw functionSymbol leftSecond
      rightFirst rightSecond)

def binaryFunctionTerm
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (first second : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  LO.FirstOrder.Semiterm.func functionSymbol ![first, second]

def binaryFunctionCongruenceAntecedent
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  (“!!leftFirst = !!rightFirst” : LO.FirstOrder.ArithmeticProposition) ⋏
    ((“!!leftSecond = !!rightSecond” :
      LO.FirstOrder.ArithmeticProposition) ⋏ ⊤)

def binaryFunctionCongruenceConclusion
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  “!!(binaryFunctionTerm functionSymbol leftFirst leftSecond) =
    !!(binaryFunctionTerm functionSymbol rightFirst rightSecond)”

theorem binaryFunctionExtFinal_formula
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryFunctionExtAfterLeftSecondMatrix functionSymbol leftSecond
        rightFirst rightSecond)/[leftFirst] =
      (binaryFunctionCongruenceAntecedent leftFirst leftSecond
          rightFirst rightSecond 🡒
        binaryFunctionCongruenceConclusion functionSymbol leftFirst leftSecond
          rightFirst rightSecond) := by
  simp [binaryFunctionExtAfterLeftSecondMatrix,
    binaryFunctionCongruenceAntecedent,
    binaryFunctionCongruenceConclusion, binaryFunctionTerm]

def binaryFunctionExtImplicationRaw
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :=
  specialize (binaryFunctionExtAfterLeftSecond functionSymbol leftSecond
    rightFirst rightSecond) leftFirst

def binaryFunctionExtImplication
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (binaryFunctionCongruenceAntecedent leftFirst leftSecond
          rightFirst rightSecond 🡒
        binaryFunctionCongruenceConclusion functionSymbol leftFirst leftSecond
          rightFirst rightSecond) :=
  cast (binaryFunctionExtFinal_formula functionSymbol leftFirst leftSecond
      rightFirst rightSecond)
    (binaryFunctionExtImplicationRaw functionSymbol leftFirst leftSecond
      rightFirst rightSecond)

theorem binaryFunctionExtAxiomProof_payloadLength_le
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2) :
    (binaryFunctionExtAxiomProof functionSymbol).payloadLength <=
      32 + 10 * axiomSyntaxBudget (.eqFuncExt functionSymbol) := by
  calc
    (binaryFunctionExtAxiomProof functionSymbol).payloadLength =
        (ofAxiom (.eqFuncExt functionSymbol)).payloadLength := by
      change
        (cast (binaryFunctionExtAxiom_formula functionSymbol)
          (ofAxiom (.eqFuncExt functionSymbol))).payloadLength = _
      exact cast_payloadLength _ _
    _ <= _ := ofAxiom_payloadLength_le (.eqFuncExt functionSymbol)

theorem binaryFunctionExtImplication_payloadLength_le
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryFunctionExtImplication functionSymbol leftFirst leftSecond
      rightFirst rightSecond).payloadLength <=
        (binaryFunctionExtAxiomProof functionSymbol).payloadLength +
          specializationCost
            (binaryFunctionExtOuterBody functionSymbol) rightSecond +
          specializationCost
            (binaryFunctionExtRightFirstBody functionSymbol rightSecond)
            rightFirst +
          specializationCost
            (binaryFunctionExtLeftSecondBody functionSymbol
              rightFirst rightSecond) leftSecond +
          specializationCost
            (binaryFunctionExtAfterLeftSecondMatrix functionSymbol
              leftSecond rightFirst rightSecond) leftFirst := by
  have hfirst := specialize_payloadLength_le_cost
    (binaryFunctionExtAxiomProof functionSymbol) rightSecond
  have hsecond := specialize_payloadLength_le_cost
    (binaryFunctionExtAfterRightSecond functionSymbol rightSecond) rightFirst
  have hthird := specialize_payloadLength_le_cost
    (binaryFunctionExtAfterRightFirst functionSymbol rightFirst rightSecond)
    leftSecond
  have hfourth := specialize_payloadLength_le_cost
    (binaryFunctionExtAfterLeftSecond functionSymbol leftSecond
      rightFirst rightSecond) leftFirst
  have hfirstCast :
      (binaryFunctionExtAfterRightSecond functionSymbol
        rightSecond).payloadLength =
      (binaryFunctionExtAfterRightSecondRaw functionSymbol
        rightSecond).payloadLength := by
    change
      (cast
        (binaryFunctionExtAfterRightSecond_formula functionSymbol rightSecond)
        (binaryFunctionExtAfterRightSecondRaw functionSymbol
          rightSecond)).payloadLength = _
    exact cast_payloadLength _ _
  have hsecondCast :
      (binaryFunctionExtAfterRightFirst functionSymbol rightFirst
        rightSecond).payloadLength =
      (binaryFunctionExtAfterRightFirstRaw functionSymbol rightFirst
        rightSecond).payloadLength := by
    change
      (cast
        (binaryFunctionExtAfterRightFirst_formula functionSymbol
          rightFirst rightSecond)
        (binaryFunctionExtAfterRightFirstRaw functionSymbol rightFirst
          rightSecond)).payloadLength = _
    exact cast_payloadLength _ _
  have hthirdCast :
      (binaryFunctionExtAfterLeftSecond functionSymbol leftSecond
        rightFirst rightSecond).payloadLength =
      (binaryFunctionExtAfterLeftSecondRaw functionSymbol leftSecond
        rightFirst rightSecond).payloadLength := by
    change
      (cast
        (binaryFunctionExtAfterLeftSecond_formula functionSymbol leftSecond
          rightFirst rightSecond)
        (binaryFunctionExtAfterLeftSecondRaw functionSymbol leftSecond
          rightFirst rightSecond)).payloadLength = _
    exact cast_payloadLength _ _
  have hfinalCast :
      (binaryFunctionExtImplication functionSymbol leftFirst leftSecond
        rightFirst rightSecond).payloadLength =
      (binaryFunctionExtImplicationRaw functionSymbol leftFirst leftSecond
        rightFirst rightSecond).payloadLength := by
    change
      (cast
        (binaryFunctionExtFinal_formula functionSymbol leftFirst leftSecond
          rightFirst rightSecond)
        (binaryFunctionExtImplicationRaw functionSymbol leftFirst leftSecond
          rightFirst rightSecond)).payloadLength = _
    exact cast_payloadLength _ _
  have hfirstBound :
      (binaryFunctionExtAfterRightSecond functionSymbol
        rightSecond).payloadLength <=
        (binaryFunctionExtAxiomProof functionSymbol).payloadLength +
          specializationCost
            (binaryFunctionExtOuterBody functionSymbol) rightSecond := by
    calc
      (binaryFunctionExtAfterRightSecond functionSymbol
          rightSecond).payloadLength =
          (binaryFunctionExtAfterRightSecondRaw functionSymbol
            rightSecond).payloadLength := hfirstCast
      _ = (specialize (binaryFunctionExtAxiomProof functionSymbol)
          rightSecond).payloadLength := rfl
      _ <= _ := hfirst
  have hsecondBound :
      (binaryFunctionExtAfterRightFirst functionSymbol rightFirst
        rightSecond).payloadLength <=
        (binaryFunctionExtAxiomProof functionSymbol).payloadLength +
          specializationCost
            (binaryFunctionExtOuterBody functionSymbol) rightSecond +
          specializationCost
            (binaryFunctionExtRightFirstBody functionSymbol rightSecond)
            rightFirst := by
    calc
      (binaryFunctionExtAfterRightFirst functionSymbol rightFirst
          rightSecond).payloadLength =
          (binaryFunctionExtAfterRightFirstRaw functionSymbol rightFirst
            rightSecond).payloadLength := hsecondCast
      _ = (specialize
          (binaryFunctionExtAfterRightSecond functionSymbol rightSecond)
          rightFirst).payloadLength := rfl
      _ <= (binaryFunctionExtAfterRightSecond functionSymbol
          rightSecond).payloadLength +
          specializationCost
            (binaryFunctionExtRightFirstBody functionSymbol rightSecond)
            rightFirst := hsecond
      _ <= ((binaryFunctionExtAxiomProof functionSymbol).payloadLength +
            specializationCost
              (binaryFunctionExtOuterBody functionSymbol) rightSecond) +
          specializationCost
            (binaryFunctionExtRightFirstBody functionSymbol rightSecond)
            rightFirst := Nat.add_le_add_right hfirstBound _
      _ = _ := by omega
  have hthirdBound :
      (binaryFunctionExtAfterLeftSecond functionSymbol leftSecond
        rightFirst rightSecond).payloadLength <=
        (binaryFunctionExtAxiomProof functionSymbol).payloadLength +
          specializationCost
            (binaryFunctionExtOuterBody functionSymbol) rightSecond +
          specializationCost
            (binaryFunctionExtRightFirstBody functionSymbol rightSecond)
            rightFirst +
          specializationCost
            (binaryFunctionExtLeftSecondBody functionSymbol
              rightFirst rightSecond) leftSecond := by
    calc
      (binaryFunctionExtAfterLeftSecond functionSymbol leftSecond
          rightFirst rightSecond).payloadLength =
          (binaryFunctionExtAfterLeftSecondRaw functionSymbol leftSecond
            rightFirst rightSecond).payloadLength := hthirdCast
      _ = (specialize
          (binaryFunctionExtAfterRightFirst functionSymbol
            rightFirst rightSecond) leftSecond).payloadLength := rfl
      _ <= (binaryFunctionExtAfterRightFirst functionSymbol
          rightFirst rightSecond).payloadLength +
          specializationCost
            (binaryFunctionExtLeftSecondBody functionSymbol
              rightFirst rightSecond) leftSecond := hthird
      _ <= ((binaryFunctionExtAxiomProof functionSymbol).payloadLength +
            specializationCost
              (binaryFunctionExtOuterBody functionSymbol) rightSecond +
            specializationCost
              (binaryFunctionExtRightFirstBody functionSymbol rightSecond)
              rightFirst) +
          specializationCost
            (binaryFunctionExtLeftSecondBody functionSymbol
              rightFirst rightSecond) leftSecond :=
        Nat.add_le_add_right hsecondBound _
      _ = _ := by omega
  rw [hfinalCast]
  calc
    (binaryFunctionExtImplicationRaw functionSymbol leftFirst leftSecond
        rightFirst rightSecond).payloadLength =
        (specialize
          (binaryFunctionExtAfterLeftSecond functionSymbol leftSecond
            rightFirst rightSecond) leftFirst).payloadLength := rfl
    _ <= (binaryFunctionExtAfterLeftSecond functionSymbol leftSecond
        rightFirst rightSecond).payloadLength +
        specializationCost
          (binaryFunctionExtAfterLeftSecondMatrix functionSymbol
            leftSecond rightFirst rightSecond) leftFirst := hfourth
    _ <= ((binaryFunctionExtAxiomProof functionSymbol).payloadLength +
          specializationCost
            (binaryFunctionExtOuterBody functionSymbol) rightSecond +
          specializationCost
            (binaryFunctionExtRightFirstBody functionSymbol rightSecond)
            rightFirst +
          specializationCost
            (binaryFunctionExtLeftSecondBody functionSymbol
              rightFirst rightSecond) leftSecond) +
        specializationCost
          (binaryFunctionExtAfterLeftSecondMatrix functionSymbol
            leftSecond rightFirst rightSecond) leftFirst :=
      Nat.add_le_add_right hthirdBound _
    _ = _ := by omega

def binaryFunctionCongruenceAntecedentProof
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (binaryFunctionCongruenceAntecedent leftFirst leftSecond
        rightFirst rightSecond) := by
  simpa [binaryFunctionCongruenceAntecedent] using
    conjunction firstProof (conjunction secondProof verumProof)

/-- The generic proof-producing congruence compiler for a binary PA function. -/
def proveBinaryFunctionCongruence
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (binaryFunctionCongruenceConclusion functionSymbol leftFirst leftSecond
        rightFirst rightSecond) :=
  modusPonens
    (binaryFunctionExtImplication functionSymbol leftFirst leftSecond
      rightFirst rightSecond)
    (binaryFunctionCongruenceAntecedentProof leftFirst leftSecond
      rightFirst rightSecond firstProof secondProof)

theorem binaryFunctionCongruenceConclusion_add_formula
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryFunctionCongruenceConclusion Language.Add.add
        leftFirst leftSecond rightFirst rightSecond =
      (“!!leftFirst + !!leftSecond = !!rightFirst + !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [binaryFunctionCongruenceConclusion, binaryFunctionTerm,
    Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Matrix.fun_eq_vec_two]

def proveAddCongruence
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!leftFirst + !!leftSecond = !!rightFirst + !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition) :=
  cast (binaryFunctionCongruenceConclusion_add_formula leftFirst leftSecond
      rightFirst rightSecond)
    (proveBinaryFunctionCongruence Language.Add.add leftFirst leftSecond
      rightFirst rightSecond firstProof secondProof)

theorem binaryFunctionCongruenceConclusion_mul_formula
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryFunctionCongruenceConclusion Language.Mul.mul
        leftFirst leftSecond rightFirst rightSecond =
      (“!!leftFirst * !!leftSecond = !!rightFirst * !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [binaryFunctionCongruenceConclusion, binaryFunctionTerm,
    Semiterm.Operator.operator, Semiterm.Operator.Mul.term_eq,
    Matrix.fun_eq_vec_two]

def proveMulCongruence
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!leftFirst * !!leftSecond = !!rightFirst * !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition) :=
  cast (binaryFunctionCongruenceConclusion_mul_formula leftFirst leftSecond
      rightFirst rightSecond)
    (proveBinaryFunctionCongruence Language.Mul.mul leftFirst leftSecond
      rightFirst rightSecond firstProof secondProof)

theorem proveBinaryFunctionCongruence_verifier_eq_true
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    listedCompactCertifiedPAProofVerifier
      (proveBinaryFunctionCongruence functionSymbol leftFirst leftSecond
        rightFirst rightSecond firstProof secondProof).code
      (compactFormulaCode
        (binaryFunctionCongruenceConclusion functionSymbol leftFirst leftSecond
          rightFirst rightSecond)) = true :=
  (proveBinaryFunctionCongruence functionSymbol leftFirst leftSecond
    rightFirst rightSecond firstProof secondProof).verifier_eq_true

def binaryFunctionCongruenceInnerConjunctionSyntaxBudget
    (leftSecond rightSecond : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  conjunctionSyntaxBudget
    (“!!leftSecond = !!rightSecond” :
      LO.FirstOrder.ArithmeticProposition)
    (⊤ : LO.FirstOrder.ArithmeticProposition)

def binaryFunctionCongruenceOuterConjunctionSyntaxBudget
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  conjunctionSyntaxBudget
    (“!!leftFirst = !!rightFirst” :
      LO.FirstOrder.ArithmeticProposition)
    ((“!!leftSecond = !!rightSecond” :
      LO.FirstOrder.ArithmeticProposition) ⋏ ⊤)

def binaryFunctionCongruenceMPSyntaxBudget
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  modusPonensSyntaxBudget
    (binaryFunctionCongruenceAntecedent leftFirst leftSecond
      rightFirst rightSecond)
    (binaryFunctionCongruenceConclusion functionSymbol leftFirst leftSecond
      rightFirst rightSecond)

theorem proveBinaryFunctionCongruence_payloadLength_le
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    (proveBinaryFunctionCongruence functionSymbol leftFirst leftSecond
      rightFirst rightSecond firstProof secondProof).payloadLength <=
        (binaryFunctionExtImplication functionSymbol leftFirst leftSecond
          rightFirst rightSecond).payloadLength +
        firstProof.payloadLength + secondProof.payloadLength + 576 +
        9 * verumSyntaxBudget +
        11 * binaryFunctionCongruenceInnerConjunctionSyntaxBudget
          leftSecond rightSecond +
        11 * binaryFunctionCongruenceOuterConjunctionSyntaxBudget
          leftFirst leftSecond rightFirst rightSecond +
        34 * binaryFunctionCongruenceMPSyntaxBudget functionSymbol
          leftFirst leftSecond rightFirst rightSecond := by
  have htruth := verumProof_payloadLength_le
  have hinner := conjunction_payloadLength_le secondProof verumProof
  have houter := conjunction_payloadLength_le firstProof
    (conjunction secondProof verumProof)
  have himplication := modusPonens_payloadLength_le
    (binaryFunctionExtImplication functionSymbol leftFirst leftSecond
      rightFirst rightSecond)
    (binaryFunctionCongruenceAntecedentProof leftFirst leftSecond
      rightFirst rightSecond firstProof secondProof)
  have hinnerBound :
      (conjunction secondProof verumProof).payloadLength <=
        secondProof.payloadLength + 48 + 9 * verumSyntaxBudget + 144 +
          11 * binaryFunctionCongruenceInnerConjunctionSyntaxBudget
            leftSecond rightSecond := by
    calc
      (conjunction secondProof verumProof).payloadLength <=
          secondProof.payloadLength + verumProof.payloadLength + 144 +
            11 * binaryFunctionCongruenceInnerConjunctionSyntaxBudget
              leftSecond rightSecond := by
        simpa [binaryFunctionCongruenceInnerConjunctionSyntaxBudget] using
          hinner
      _ <= secondProof.payloadLength +
          (48 + 9 * verumSyntaxBudget) + 144 +
            11 * binaryFunctionCongruenceInnerConjunctionSyntaxBudget
              leftSecond rightSecond := by omega
      _ = _ := by omega
  have hantecedent :
      (binaryFunctionCongruenceAntecedentProof leftFirst leftSecond
        rightFirst rightSecond firstProof secondProof).payloadLength <=
        firstProof.payloadLength + secondProof.payloadLength + 336 +
          9 * verumSyntaxBudget +
          11 * binaryFunctionCongruenceInnerConjunctionSyntaxBudget
            leftSecond rightSecond +
          11 * binaryFunctionCongruenceOuterConjunctionSyntaxBudget
            leftFirst leftSecond rightFirst rightSecond := by
    change
      (conjunction firstProof
        (conjunction secondProof verumProof)).payloadLength <= _
    calc
      (conjunction firstProof
          (conjunction secondProof verumProof)).payloadLength <=
          firstProof.payloadLength +
            (conjunction secondProof verumProof).payloadLength + 144 +
            11 * binaryFunctionCongruenceOuterConjunctionSyntaxBudget
              leftFirst leftSecond rightFirst rightSecond := by
        simpa [binaryFunctionCongruenceOuterConjunctionSyntaxBudget] using
          houter
      _ <= firstProof.payloadLength +
          (secondProof.payloadLength + 48 + 9 * verumSyntaxBudget + 144 +
            11 * binaryFunctionCongruenceInnerConjunctionSyntaxBudget
              leftSecond rightSecond) + 144 +
            11 * binaryFunctionCongruenceOuterConjunctionSyntaxBudget
              leftFirst leftSecond rightFirst rightSecond := by
        omega
      _ = _ := by omega
  change
    (modusPonens
      (binaryFunctionExtImplication functionSymbol leftFirst leftSecond
        rightFirst rightSecond)
      (binaryFunctionCongruenceAntecedentProof leftFirst leftSecond
        rightFirst rightSecond firstProof secondProof)).payloadLength <= _
  calc
    (modusPonens
      (binaryFunctionExtImplication functionSymbol leftFirst leftSecond
        rightFirst rightSecond)
      (binaryFunctionCongruenceAntecedentProof leftFirst leftSecond
        rightFirst rightSecond firstProof secondProof)).payloadLength <=
        (binaryFunctionExtImplication functionSymbol leftFirst leftSecond
          rightFirst rightSecond).payloadLength +
        (binaryFunctionCongruenceAntecedentProof leftFirst leftSecond
          rightFirst rightSecond firstProof secondProof).payloadLength + 240 +
        34 * binaryFunctionCongruenceMPSyntaxBudget functionSymbol
          leftFirst leftSecond rightFirst rightSecond := by
      simpa [binaryFunctionCongruenceMPSyntaxBudget] using himplication
    _ <= (binaryFunctionExtImplication functionSymbol leftFirst leftSecond
          rightFirst rightSecond).payloadLength +
        (firstProof.payloadLength + secondProof.payloadLength + 336 +
          9 * verumSyntaxBudget +
          11 * binaryFunctionCongruenceInnerConjunctionSyntaxBudget
            leftSecond rightSecond +
          11 * binaryFunctionCongruenceOuterConjunctionSyntaxBudget
            leftFirst leftSecond rightFirst rightSecond) + 240 +
        34 * binaryFunctionCongruenceMPSyntaxBudget functionSymbol
          leftFirst leftSecond rightFirst rightSecond := by omega
    _ = _ := by omega

theorem proveBinaryFunctionCongruence_full_payloadLength_le
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    (proveBinaryFunctionCongruence functionSymbol leftFirst leftSecond
      rightFirst rightSecond firstProof secondProof).payloadLength <=
        firstProof.payloadLength + secondProof.payloadLength + 608 +
        10 * axiomSyntaxBudget (.eqFuncExt functionSymbol) +
        specializationCost
          (binaryFunctionExtOuterBody functionSymbol) rightSecond +
        specializationCost
          (binaryFunctionExtRightFirstBody functionSymbol rightSecond)
          rightFirst +
        specializationCost
          (binaryFunctionExtLeftSecondBody functionSymbol
            rightFirst rightSecond) leftSecond +
        specializationCost
          (binaryFunctionExtAfterLeftSecondMatrix functionSymbol
            leftSecond rightFirst rightSecond) leftFirst +
        9 * verumSyntaxBudget +
        11 * binaryFunctionCongruenceInnerConjunctionSyntaxBudget
          leftSecond rightSecond +
        11 * binaryFunctionCongruenceOuterConjunctionSyntaxBudget
          leftFirst leftSecond rightFirst rightSecond +
        34 * binaryFunctionCongruenceMPSyntaxBudget functionSymbol
          leftFirst leftSecond rightFirst rightSecond := by
  have hproof := proveBinaryFunctionCongruence_payloadLength_le
    functionSymbol leftFirst leftSecond rightFirst rightSecond
      firstProof secondProof
  have himplication := binaryFunctionExtImplication_payloadLength_le
    functionSymbol leftFirst leftSecond rightFirst rightSecond
  have haxiom := binaryFunctionExtAxiomProof_payloadLength_le functionSymbol
  omega

def binaryFunctionCongruenceFullPayloadBound
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstPayloadLength secondPayloadLength : Nat) : Nat :=
  firstPayloadLength + secondPayloadLength + 608 +
    10 * axiomSyntaxBudget (.eqFuncExt functionSymbol) +
    specializationCost
      (binaryFunctionExtOuterBody functionSymbol) rightSecond +
    specializationCost
      (binaryFunctionExtRightFirstBody functionSymbol rightSecond)
      rightFirst +
    specializationCost
      (binaryFunctionExtLeftSecondBody functionSymbol
        rightFirst rightSecond) leftSecond +
    specializationCost
      (binaryFunctionExtAfterLeftSecondMatrix functionSymbol
        leftSecond rightFirst rightSecond) leftFirst +
    9 * verumSyntaxBudget +
    11 * binaryFunctionCongruenceInnerConjunctionSyntaxBudget
      leftSecond rightSecond +
    11 * binaryFunctionCongruenceOuterConjunctionSyntaxBudget
      leftFirst leftSecond rightFirst rightSecond +
    34 * binaryFunctionCongruenceMPSyntaxBudget functionSymbol
      leftFirst leftSecond rightFirst rightSecond

theorem proveAddCongruence_verifier_eq_true
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    listedCompactCertifiedPAProofVerifier
      (proveAddCongruence leftFirst leftSecond rightFirst rightSecond
        firstProof secondProof).code
      (compactFormulaCode
        (“!!leftFirst + !!leftSecond = !!rightFirst + !!rightSecond” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  (proveAddCongruence leftFirst leftSecond rightFirst rightSecond
    firstProof secondProof).verifier_eq_true

theorem proveMulCongruence_verifier_eq_true
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    listedCompactCertifiedPAProofVerifier
      (proveMulCongruence leftFirst leftSecond rightFirst rightSecond
        firstProof secondProof).code
      (compactFormulaCode
        (“!!leftFirst * !!leftSecond = !!rightFirst * !!rightSecond” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  (proveMulCongruence leftFirst leftSecond rightFirst rightSecond
    firstProof secondProof).verifier_eq_true

theorem proveAddCongruence_payloadLength_le
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    (proveAddCongruence leftFirst leftSecond rightFirst rightSecond
      firstProof secondProof).payloadLength <=
        binaryFunctionCongruenceFullPayloadBound Language.Add.add
          leftFirst leftSecond rightFirst rightSecond
          firstProof.payloadLength secondProof.payloadLength := by
  calc
    (proveAddCongruence leftFirst leftSecond rightFirst rightSecond
        firstProof secondProof).payloadLength =
        (proveBinaryFunctionCongruence Language.Add.add leftFirst leftSecond
          rightFirst rightSecond firstProof secondProof).payloadLength := by
      change
        (cast
          (binaryFunctionCongruenceConclusion_add_formula leftFirst leftSecond
            rightFirst rightSecond)
          (proveBinaryFunctionCongruence Language.Add.add leftFirst leftSecond
            rightFirst rightSecond firstProof secondProof)).payloadLength = _
      exact cast_payloadLength _ _
    _ <= _ := by
      simpa [binaryFunctionCongruenceFullPayloadBound] using
        (proveBinaryFunctionCongruence_full_payloadLength_le
          Language.Add.add leftFirst leftSecond rightFirst rightSecond
          firstProof secondProof)

theorem proveMulCongruence_payloadLength_le
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstProof : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondProof : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    (proveMulCongruence leftFirst leftSecond rightFirst rightSecond
      firstProof secondProof).payloadLength <=
        binaryFunctionCongruenceFullPayloadBound Language.Mul.mul
          leftFirst leftSecond rightFirst rightSecond
          firstProof.payloadLength secondProof.payloadLength := by
  calc
    (proveMulCongruence leftFirst leftSecond rightFirst rightSecond
        firstProof secondProof).payloadLength =
        (proveBinaryFunctionCongruence Language.Mul.mul leftFirst leftSecond
          rightFirst rightSecond firstProof secondProof).payloadLength := by
      change
        (cast
          (binaryFunctionCongruenceConclusion_mul_formula leftFirst leftSecond
            rightFirst rightSecond)
          (proveBinaryFunctionCongruence Language.Mul.mul leftFirst leftSecond
            rightFirst rightSecond firstProof secondProof)).payloadLength = _
      exact cast_payloadLength _ _
    _ <= _ := by
      simpa [binaryFunctionCongruenceFullPayloadBound] using
        (proveBinaryFunctionCongruence_full_payloadLength_le
          Language.Mul.mul leftFirst leftSecond rightFirst rightSecond
          firstProof secondProof)

#print axioms binaryFunctionExtImplication_payloadLength_le
#print axioms proveBinaryFunctionCongruence_verifier_eq_true
#print axioms proveBinaryFunctionCongruence_full_payloadLength_le
#print axioms proveAddCongruence_verifier_eq_true
#print axioms proveMulCongruence_verifier_eq_true
#print axioms proveAddCongruence_payloadLength_le
#print axioms proveMulCongruence_payloadLength_le


end FoundationCompactPAQuantitativeFunctionCongruence
