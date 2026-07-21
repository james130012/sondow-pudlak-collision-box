import integration.FoundationCompactPAQuantitativeRelationCongruence
import integration.FoundationCompactPABinaryNumeralAdditionBounds
import integration.FoundationCompactPABinaryNumeralMultiplicationBounds

/-!
# Quantitative certified PA order primitives

This file specializes the real `PA⁻` order axioms needed by the closed-atom
compiler.  It produces checked proofs of `0 < 1`, additive monotonicity, and
strict-order transitivity, with no semantic oracle or order certificate input.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAQuantitativeOrder

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAAxiomCertificate
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactCertifiedModusPonens
open FoundationCompactCertifiedConjunction
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABinaryNumeralMultiplication
open FoundationCompactPABinaryNumeralMultiplicationBounds
open FoundationCompactPAQuantitativeRelationCongruence

/-! ## The base strict-order axiom -/

theorem zeroLtOneAxiom_formula :
    (Rewriting.emb PAAxiomCertificate.zeroLtOne.sentence :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!paZeroTerm < !!paOneTerm” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [PAAxiomCertificate.sentence, paZeroTerm, paOneTerm,
    arithmeticOneTerm, Semiformula.Operator.lt_def,
    Semiterm.Operator.operator]
  constructor
  · change
      Rew.emb (LO.FirstOrder.Semiterm.func Language.Zero.zero ![]) =
        LO.FirstOrder.Semiterm.func Language.Zero.zero ![]
    simp
  · change
      Rew.emb (LO.FirstOrder.Semiterm.func Language.One.one ![]) =
        LO.FirstOrder.Semiterm.func Language.One.one ![]
    simp

def proveZeroLtOne :
    CertifiedPAProof
      (“!!paZeroTerm < !!paOneTerm” :
        LO.FirstOrder.ArithmeticProposition) :=
  CertifiedPAProof.cast zeroLtOneAxiom_formula (ofAxiom .zeroLtOne)

theorem proveZeroLtOne_payloadLength_le :
    proveZeroLtOne.payloadLength <=
      32 + 10 * axiomSyntaxBudget .zeroLtOne := by
  calc
    proveZeroLtOne.payloadLength =
        (ofAxiom .zeroLtOne).payloadLength := by
      exact cast_payloadLength _ _
    _ <= _ := ofAxiom_payloadLength_le .zeroLtOne

/-! ## Strict-order irreflexivity -/

def ltIrreflBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  ∼(“#0 < #0” : LO.FirstOrder.ArithmeticSemiformula Nat 1)

theorem ltIrreflAxiom_formula :
    (Rewriting.emb PAAxiomCertificate.ltIrrefl.sentence :
        LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ ltIrreflBody := by
  simp [ltIrreflBody, PAAxiomCertificate.sentence,
    PeanoMinus.Axiom.ltIrrefl]

def ltIrreflAxiomProof :
    CertifiedPAProof (∀⁰ ltIrreflBody) :=
  CertifiedPAProof.cast ltIrreflAxiom_formula (ofAxiom .ltIrrefl)

theorem ltIrreflFinal_formula
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    ltIrreflBody/[term] =
      ∼(“!!term < !!term” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [ltIrreflBody]

def proveLtIrrefl
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (∼(“!!term < !!term” :
        LO.FirstOrder.ArithmeticProposition)) :=
  CertifiedPAProof.cast (ltIrreflFinal_formula term)
    (specialize ltIrreflAxiomProof term)

theorem ltIrreflAxiomProof_payloadLength_le :
    ltIrreflAxiomProof.payloadLength <=
      32 + 10 * axiomSyntaxBudget .ltIrrefl := by
  calc
    ltIrreflAxiomProof.payloadLength =
        (ofAxiom .ltIrrefl).payloadLength := by
      exact cast_payloadLength _ _
    _ <= _ := ofAxiom_payloadLength_le .ltIrrefl

def ltIrreflFullPayloadBound
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  32 + 10 * axiomSyntaxBudget .ltIrrefl +
    specializationCost ltIrreflBody term

theorem proveLtIrrefl_payloadLength_le
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveLtIrrefl term).payloadLength <=
      ltIrreflFullPayloadBound term := by
  have hspecialize := specialize_payloadLength_le_cost
    ltIrreflAxiomProof term
  have haxiom := ltIrreflAxiomProof_payloadLength_le
  have hcast : (proveLtIrrefl term).payloadLength =
      (specialize ltIrreflAxiomProof term).payloadLength := by
    exact cast_payloadLength _ _
  rw [hcast]
  unfold ltIrreflFullPayloadBound
  omega

/-! ## Additive monotonicity -/

def addLtAddOuterBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰ ∀⁰ (#2 < #1 → #2 + #0 < #1 + #0)”

theorem addLtAddAxiom_formula :
    (Rewriting.emb PAAxiomCertificate.addLtAdd.sentence :
        LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ addLtAddOuterBody := by
  simp [addLtAddOuterBody, PAAxiomCertificate.sentence]

def addLtAddAxiomProof :
    CertifiedPAProof (∀⁰ addLtAddOuterBody) :=
  CertifiedPAProof.cast addLtAddAxiom_formula (ofAxiom .addLtAdd)

def addLtAddMiddleBody
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰
    (!!(Rew.bShift (Rew.bShift left)) < #1 →
      !!(Rew.bShift (Rew.bShift left)) + #0 < #1 + #0)”

theorem addLtAddAfterFirst_formula
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    addLtAddOuterBody/[left] = ∀⁰ addLtAddMiddleBody left := by
  simp [addLtAddOuterBody, addLtAddMiddleBody,
    substQQ_bvarOne, substQQ_bvarTwo]

def addLtAddInnerBody
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!!(Rew.bShift left) < !!(Rew.bShift right) →
    !!(Rew.bShift left) + #0 < !!(Rew.bShift right) + #0”

theorem addLtAddAfterSecond_formula
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (addLtAddMiddleBody left)/[right] =
      ∀⁰ addLtAddInnerBody left right := by
  simp [addLtAddMiddleBody, addLtAddInnerBody, substQ_bvarOne]

theorem addLtAddFinal_formula
    (left right shift : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (addLtAddInnerBody left right)/[shift] =
      ((“!!left < !!right” : LO.FirstOrder.ArithmeticProposition) 🡒
        (“!!left + !!shift < !!right + !!shift” :
          LO.FirstOrder.ArithmeticProposition)) := by
  simp [addLtAddInnerBody]

def addLtAddImplication
    (left right shift : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      ((“!!left < !!right” : LO.FirstOrder.ArithmeticProposition) 🡒
        (“!!left + !!shift < !!right + !!shift” :
          LO.FirstOrder.ArithmeticProposition)) :=
  specializeThriceWithCasts addLtAddAxiomProof left right shift
    (addLtAddAfterFirst_formula left)
    (addLtAddAfterSecond_formula left right)
    (addLtAddFinal_formula left right shift)

def proveAddLtAdd
    (left right shift : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (proof : CertifiedPAProof
      (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!left + !!shift < !!right + !!shift” :
        LO.FirstOrder.ArithmeticProposition) :=
  modusPonens (addLtAddImplication left right shift) proof

theorem addLtAddAxiomProof_payloadLength_le :
    addLtAddAxiomProof.payloadLength <=
      32 + 10 * axiomSyntaxBudget .addLtAdd := by
  calc
    addLtAddAxiomProof.payloadLength =
        (ofAxiom .addLtAdd).payloadLength := by
      exact cast_payloadLength _ _
    _ <= _ := ofAxiom_payloadLength_le .addLtAdd

theorem addLtAddImplication_payloadLength_le
    (left right shift : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (addLtAddImplication left right shift).payloadLength <=
      addLtAddAxiomProof.payloadLength +
        specializationCost addLtAddOuterBody left +
        specializationCost (addLtAddMiddleBody left) right +
        specializationCost (addLtAddInnerBody left right) shift :=
  specializeThriceWithCasts_payloadLength_le addLtAddAxiomProof
    left right shift
    (addLtAddAfterFirst_formula left)
    (addLtAddAfterSecond_formula left right)
    (addLtAddFinal_formula left right shift)

def addLtAddImplicationFullPayloadBound
    (left right shift : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  32 + 10 * axiomSyntaxBudget .addLtAdd +
    specializationCost addLtAddOuterBody left +
    specializationCost (addLtAddMiddleBody left) right +
    specializationCost (addLtAddInnerBody left right) shift

theorem addLtAddImplication_full_payloadLength_le
    (left right shift : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (addLtAddImplication left right shift).payloadLength <=
      addLtAddImplicationFullPayloadBound left right shift := by
  have himplication := addLtAddImplication_payloadLength_le left right shift
  have haxiom := addLtAddAxiomProof_payloadLength_le
  unfold addLtAddImplicationFullPayloadBound
  omega

theorem proveAddLtAdd_payloadLength_le
    (left right shift : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (proof : CertifiedPAProof
      (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)) :
    (proveAddLtAdd left right shift proof).payloadLength <=
      (addLtAddImplication left right shift).payloadLength +
      proof.payloadLength + 240 +
      34 * modusPonensSyntaxBudget
        (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)
        (“!!left + !!shift < !!right + !!shift” :
          LO.FirstOrder.ArithmeticProposition) :=
  modusPonens_payloadLength_le (addLtAddImplication left right shift) proof

/-! ## Multiplicative monotonicity -/

def mulLtMulOuterBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰ ∀⁰ ((#2 < #1 ∧ 0 < #0) → #2 * #0 < #1 * #0)”

theorem mulLtMulAxiom_formula :
    (Rewriting.emb PAAxiomCertificate.mulLtMul.sentence :
        LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ mulLtMulOuterBody := by
  simp [mulLtMulOuterBody, PAAxiomCertificate.sentence]

def mulLtMulAxiomProof :
    CertifiedPAProof (∀⁰ mulLtMulOuterBody) :=
  CertifiedPAProof.cast mulLtMulAxiom_formula (ofAxiom .mulLtMul)

def mulLtMulMiddleBody
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰
    ((!!(Rew.bShift (Rew.bShift left)) < #1 ∧ 0 < #0) →
      !!(Rew.bShift (Rew.bShift left)) * #0 < #1 * #0)”

theorem mulLtMulAfterFirst_formula
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    mulLtMulOuterBody/[left] = ∀⁰ mulLtMulMiddleBody left := by
  simp [mulLtMulOuterBody, mulLtMulMiddleBody,
    substQQ_bvarOne, substQQ_bvarTwo]

def mulLtMulInnerBody
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “((!!(Rew.bShift left) < !!(Rew.bShift right) ∧ 0 < #0) →
    !!(Rew.bShift left) * #0 < !!(Rew.bShift right) * #0)”

theorem mulLtMulAfterSecond_formula
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (mulLtMulMiddleBody left)/[right] =
      ∀⁰ mulLtMulInnerBody left right := by
  simp [mulLtMulMiddleBody, mulLtMulInnerBody, substQ_bvarOne]

theorem mulLtMulFinal_formula
    (left right factor : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (mulLtMulInnerBody left right)/[factor] =
      (((“!!left < !!right” : LO.FirstOrder.ArithmeticProposition) ⋏
          (“!!paZeroTerm < !!factor” :
            LO.FirstOrder.ArithmeticProposition)) 🡒
        (“!!left * !!factor < !!right * !!factor” :
          LO.FirstOrder.ArithmeticProposition)) := by
  simp [mulLtMulInnerBody, paZeroTerm, arithmeticZeroTerm,
    Semiterm.Operator.operator, Semiterm.Operator.Mul.term_eq,
    Matrix.fun_eq_vec_two]
  change
    (Rew.subst ![factor])
        ((Rew.subst ![])
          (Rew.emb
            (LO.FirstOrder.Semiterm.func Language.Zero.zero ![]))) =
      LO.FirstOrder.Semiterm.func Language.Zero.zero ![]
  simp

def mulLtMulImplication
    (left right factor : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (((“!!left < !!right” : LO.FirstOrder.ArithmeticProposition) ⋏
          (“!!paZeroTerm < !!factor” :
            LO.FirstOrder.ArithmeticProposition)) 🡒
        (“!!left * !!factor < !!right * !!factor” :
          LO.FirstOrder.ArithmeticProposition)) :=
  specializeThriceWithCasts mulLtMulAxiomProof left right factor
    (mulLtMulAfterFirst_formula left)
    (mulLtMulAfterSecond_formula left right)
    (mulLtMulFinal_formula left right factor)

def proveMulLtMul
    (left right factor : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (relationProof : CertifiedPAProof
      (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition))
    (positiveFactorProof : CertifiedPAProof
      (“!!paZeroTerm < !!factor” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!left * !!factor < !!right * !!factor” :
        LO.FirstOrder.ArithmeticProposition) :=
  modusPonens (mulLtMulImplication left right factor)
    (conjunction relationProof positiveFactorProof)

theorem mulLtMulAxiomProof_payloadLength_le :
    mulLtMulAxiomProof.payloadLength <=
      32 + 10 * axiomSyntaxBudget .mulLtMul := by
  calc
    mulLtMulAxiomProof.payloadLength =
        (ofAxiom .mulLtMul).payloadLength := by
      exact cast_payloadLength _ _
    _ <= _ := ofAxiom_payloadLength_le .mulLtMul

theorem mulLtMulImplication_payloadLength_le
    (left right factor : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (mulLtMulImplication left right factor).payloadLength <=
      mulLtMulAxiomProof.payloadLength +
        specializationCost mulLtMulOuterBody left +
        specializationCost (mulLtMulMiddleBody left) right +
        specializationCost (mulLtMulInnerBody left right) factor :=
  specializeThriceWithCasts_payloadLength_le mulLtMulAxiomProof
    left right factor
    (mulLtMulAfterFirst_formula left)
    (mulLtMulAfterSecond_formula left right)
    (mulLtMulFinal_formula left right factor)

def mulLtMulImplicationFullPayloadBound
    (left right factor : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  32 + 10 * axiomSyntaxBudget .mulLtMul +
    specializationCost mulLtMulOuterBody left +
    specializationCost (mulLtMulMiddleBody left) right +
    specializationCost (mulLtMulInnerBody left right) factor

theorem mulLtMulImplication_full_payloadLength_le
    (left right factor : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (mulLtMulImplication left right factor).payloadLength <=
      mulLtMulImplicationFullPayloadBound left right factor := by
  have himplication := mulLtMulImplication_payloadLength_le
    left right factor
  have haxiom := mulLtMulAxiomProof_payloadLength_le
  unfold mulLtMulImplicationFullPayloadBound
  omega

theorem proveMulLtMul_payloadLength_le
    (left right factor : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (relationProof : CertifiedPAProof
      (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition))
    (positiveFactorProof : CertifiedPAProof
      (“!!paZeroTerm < !!factor” :
        LO.FirstOrder.ArithmeticProposition)) :
    (proveMulLtMul left right factor
      relationProof positiveFactorProof).payloadLength <=
      (mulLtMulImplication left right factor).payloadLength +
        relationProof.payloadLength + positiveFactorProof.payloadLength +
        384 +
        11 * conjunctionSyntaxBudget
          (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)
          (“!!paZeroTerm < !!factor” :
            LO.FirstOrder.ArithmeticProposition) +
        34 * modusPonensSyntaxBudget
          ((“!!left < !!right” : LO.FirstOrder.ArithmeticProposition) ⋏
            (“!!paZeroTerm < !!factor” :
              LO.FirstOrder.ArithmeticProposition))
          (“!!left * !!factor < !!right * !!factor” :
            LO.FirstOrder.ArithmeticProposition) := by
  have hconjunction := conjunction_payloadLength_le
    relationProof positiveFactorProof
  have hmodus := modusPonens_payloadLength_le
    (mulLtMulImplication left right factor)
    (conjunction relationProof positiveFactorProof)
  change
    (modusPonens (mulLtMulImplication left right factor)
      (conjunction relationProof positiveFactorProof)).payloadLength <= _
  omega

/-! ## Strict-order transitivity -/

def ltTransOuterBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰ ∀⁰ ((#2 < #1 ∧ #1 < #0) → #2 < #0)”

theorem ltTransAxiom_formula :
    (Rewriting.emb PAAxiomCertificate.ltTrans.sentence :
        LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ ltTransOuterBody := by
  simp [ltTransOuterBody, PAAxiomCertificate.sentence]

def ltTransAxiomProof :
    CertifiedPAProof (∀⁰ ltTransOuterBody) :=
  CertifiedPAProof.cast ltTransAxiom_formula (ofAxiom .ltTrans)

def ltTransMiddleBody
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰
    ((!!(Rew.bShift (Rew.bShift left)) < #1 ∧ #1 < #0) →
      !!(Rew.bShift (Rew.bShift left)) < #0)”

theorem ltTransAfterFirst_formula
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    ltTransOuterBody/[left] = ∀⁰ ltTransMiddleBody left := by
  simp [ltTransOuterBody, ltTransMiddleBody,
    substQQ_bvarOne, substQQ_bvarTwo]

def ltTransInnerBody
    (left middle : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “((!!(Rew.bShift left) < !!(Rew.bShift middle) ∧
      !!(Rew.bShift middle) < #0) →
    !!(Rew.bShift left) < #0)”

theorem ltTransAfterSecond_formula
    (left middle : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (ltTransMiddleBody left)/[middle] =
      ∀⁰ ltTransInnerBody left middle := by
  simp [ltTransMiddleBody, ltTransInnerBody, substQ_bvarOne]

theorem ltTransFinal_formula
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (ltTransInnerBody left middle)/[right] =
      (((“!!left < !!middle” : LO.FirstOrder.ArithmeticProposition) ⋏
          (“!!middle < !!right” : LO.FirstOrder.ArithmeticProposition)) 🡒
        (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)) := by
  simp [ltTransInnerBody]

def ltTransImplication
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (((“!!left < !!middle” : LO.FirstOrder.ArithmeticProposition) ⋏
          (“!!middle < !!right” : LO.FirstOrder.ArithmeticProposition)) 🡒
        (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)) :=
  specializeThriceWithCasts ltTransAxiomProof left middle right
    (ltTransAfterFirst_formula left)
    (ltTransAfterSecond_formula left middle)
    (ltTransFinal_formula left middle right)

def proveLtTransitivity
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (leftProof : CertifiedPAProof
      (“!!left < !!middle” : LO.FirstOrder.ArithmeticProposition))
    (rightProof : CertifiedPAProof
      (“!!middle < !!right” : LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition) :=
  modusPonens (ltTransImplication left middle right)
    (conjunction leftProof rightProof)

theorem ltTransAxiomProof_payloadLength_le :
    ltTransAxiomProof.payloadLength <=
      32 + 10 * axiomSyntaxBudget .ltTrans := by
  calc
    ltTransAxiomProof.payloadLength =
        (ofAxiom .ltTrans).payloadLength := by
      exact cast_payloadLength _ _
    _ <= _ := ofAxiom_payloadLength_le .ltTrans

theorem ltTransImplication_payloadLength_le
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (ltTransImplication left middle right).payloadLength <=
      ltTransAxiomProof.payloadLength +
        specializationCost ltTransOuterBody left +
        specializationCost (ltTransMiddleBody left) middle +
        specializationCost (ltTransInnerBody left middle) right :=
  specializeThriceWithCasts_payloadLength_le ltTransAxiomProof
    left middle right
    (ltTransAfterFirst_formula left)
    (ltTransAfterSecond_formula left middle)
    (ltTransFinal_formula left middle right)

theorem proveLtTransitivity_payloadLength_le
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (leftProof : CertifiedPAProof
      (“!!left < !!middle” : LO.FirstOrder.ArithmeticProposition))
    (rightProof : CertifiedPAProof
      (“!!middle < !!right” : LO.FirstOrder.ArithmeticProposition)) :
    (proveLtTransitivity left middle right
      leftProof rightProof).payloadLength <=
      (ltTransImplication left middle right).payloadLength +
        leftProof.payloadLength + rightProof.payloadLength + 384 +
        11 * conjunctionSyntaxBudget
          (“!!left < !!middle” : LO.FirstOrder.ArithmeticProposition)
          (“!!middle < !!right” : LO.FirstOrder.ArithmeticProposition) +
        34 * modusPonensSyntaxBudget
          ((“!!left < !!middle” : LO.FirstOrder.ArithmeticProposition) ⋏
            (“!!middle < !!right” :
              LO.FirstOrder.ArithmeticProposition))
          (“!!left < !!right” :
            LO.FirstOrder.ArithmeticProposition) := by
  have hconjunction := conjunction_payloadLength_le leftProof rightProof
  have hmodus := modusPonens_payloadLength_le
    (ltTransImplication left middle right)
    (conjunction leftProof rightProof)
  change
    (modusPonens (ltTransImplication left middle right)
      (conjunction leftProof rightProof)).payloadLength <= _
  omega

def ltTransitivityFullPayloadBound
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (leftPayloadLength rightPayloadLength : Nat) : Nat :=
  32 + 10 * axiomSyntaxBudget .ltTrans +
    specializationCost ltTransOuterBody left +
    specializationCost (ltTransMiddleBody left) middle +
    specializationCost (ltTransInnerBody left middle) right +
    leftPayloadLength + rightPayloadLength + 384 +
    11 * conjunctionSyntaxBudget
      (“!!left < !!middle” : LO.FirstOrder.ArithmeticProposition)
      (“!!middle < !!right” : LO.FirstOrder.ArithmeticProposition) +
    34 * modusPonensSyntaxBudget
      ((“!!left < !!middle” : LO.FirstOrder.ArithmeticProposition) ⋏
        (“!!middle < !!right” : LO.FirstOrder.ArithmeticProposition))
      (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)

theorem proveLtTransitivity_full_payloadLength_le
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (leftProof : CertifiedPAProof
      (“!!left < !!middle” : LO.FirstOrder.ArithmeticProposition))
    (rightProof : CertifiedPAProof
      (“!!middle < !!right” : LO.FirstOrder.ArithmeticProposition)) :
    (proveLtTransitivity left middle right
      leftProof rightProof).payloadLength <=
      ltTransitivityFullPayloadBound left middle right
        leftProof.payloadLength rightProof.payloadLength := by
  have hproof := proveLtTransitivity_payloadLength_le
    left middle right leftProof rightProof
  have himplication := ltTransImplication_payloadLength_le left middle right
  have haxiom := ltTransAxiomProof_payloadLength_le
  unfold ltTransitivityFullPayloadBound
  omega

theorem ltTransitivityFullPayloadBound_mono_lengths
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    {leftLength rightLength leftBound rightBound : Nat}
    (hleft : leftLength <= leftBound)
    (hright : rightLength <= rightBound) :
    ltTransitivityFullPayloadBound left middle right
        leftLength rightLength <=
      ltTransitivityFullPayloadBound left middle right
        leftBound rightBound := by
  unfold ltTransitivityFullPayloadBound
  omega

/-! ## Relation transport and binary-numeral positivity -/

theorem binaryRelationFormula_lt_formula
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryRelationFormula Language.ORing.Rel.lt left right =
      (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition) := by
  simp [binaryRelationFormula, Semiformula.Operator.lt_def,
    Matrix.fun_eq_vec_two]
  rfl

theorem binaryRelationCongruenceConclusion_lt_formula
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryRelationCongruenceConclusion Language.ORing.Rel.lt
        leftFirst leftSecond rightFirst rightSecond =
      ((“!!leftFirst < !!leftSecond” :
          LO.FirstOrder.ArithmeticProposition) 🡒
        (“!!rightFirst < !!rightSecond” :
          LO.FirstOrder.ArithmeticProposition)) := by
  simp [binaryRelationCongruenceConclusion,
    binaryRelationFormula_lt_formula]

def proveLtTransport
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstEquality : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondEquality : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition))
    (relationProof : CertifiedPAProof
      (“!!leftFirst < !!leftSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!rightFirst < !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition) :=
  modusPonens
    (CertifiedPAProof.cast
      (binaryRelationCongruenceConclusion_lt_formula
        leftFirst leftSecond rightFirst rightSecond)
      (proveBinaryRelationTransportImplication Language.ORing.Rel.lt
        leftFirst leftSecond rightFirst rightSecond
        firstEquality secondEquality))
    relationProof

theorem proveLtTransport_payloadLength_le
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstEquality : CertifiedPAProof
      (“!!leftFirst = !!rightFirst” :
        LO.FirstOrder.ArithmeticProposition))
    (secondEquality : CertifiedPAProof
      (“!!leftSecond = !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition))
    (relationProof : CertifiedPAProof
      (“!!leftFirst < !!leftSecond” :
        LO.FirstOrder.ArithmeticProposition)) :
    (proveLtTransport leftFirst leftSecond rightFirst rightSecond
      firstEquality secondEquality relationProof).payloadLength <=
      binaryRelationTransportFullPayloadBound Language.ORing.Rel.lt
        leftFirst leftSecond rightFirst rightSecond
        firstEquality.payloadLength secondEquality.payloadLength +
      relationProof.payloadLength + 240 +
      34 * modusPonensSyntaxBudget
        (“!!leftFirst < !!leftSecond” :
          LO.FirstOrder.ArithmeticProposition)
        (“!!rightFirst < !!rightSecond” :
          LO.FirstOrder.ArithmeticProposition) := by
  let transportRaw :=
    proveBinaryRelationTransportImplication Language.ORing.Rel.lt
      leftFirst leftSecond rightFirst rightSecond
      firstEquality secondEquality
  let transport : CertifiedPAProof
      ((“!!leftFirst < !!leftSecond” :
          LO.FirstOrder.ArithmeticProposition) 🡒
        (“!!rightFirst < !!rightSecond” :
          LO.FirstOrder.ArithmeticProposition)) :=
    CertifiedPAProof.cast
      (binaryRelationCongruenceConclusion_lt_formula
        leftFirst leftSecond rightFirst rightSecond)
      transportRaw
  have hraw :=
    proveBinaryRelationTransportImplication_full_payloadLength_le
      Language.ORing.Rel.lt leftFirst leftSecond rightFirst rightSecond
      firstEquality secondEquality
  have hcast : transport.payloadLength = transportRaw.payloadLength := by
    dsimp only [transport]
    exact cast_payloadLength _ _
  have htransport : transport.payloadLength <=
      binaryRelationTransportFullPayloadBound Language.ORing.Rel.lt
        leftFirst leftSecond rightFirst rightSecond
        firstEquality.payloadLength secondEquality.payloadLength := by
    rw [hcast]
    exact hraw
  have hmodus := modusPonens_payloadLength_le transport relationProof
  change (modusPonens transport relationProof).payloadLength <= _
  omega

theorem binaryRelationTransportFullPayloadBound_mono_lengths
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    {firstLength secondLength firstBound secondBound : Nat}
    (hfirst : firstLength <= firstBound)
    (hsecond : secondLength <= secondBound) :
    binaryRelationTransportFullPayloadBound relationSymbol
        leftFirst leftSecond rightFirst rightSecond
        firstLength secondLength <=
      binaryRelationTransportFullPayloadBound relationSymbol
        leftFirst leftSecond rightFirst rightSecond
        firstBound secondBound := by
  unfold binaryRelationTransportFullPayloadBound
  omega

theorem addLtAddAsTerms_formula
    (left right shift : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (“!!left + !!shift < !!right + !!shift” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!(paAddTerm left shift) < !!(paAddTerm right shift)” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [paAddTerm]

def proveBinaryNumeralAddLtAdd
    (left right shift : Nat)
    (proof : CertifiedPAProof
      (“!!(shortBinaryNumeralTerm left) <
        !!(shortBinaryNumeralTerm right)” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(shortBinaryNumeralTerm (left + shift)) <
        !!(shortBinaryNumeralTerm (right + shift))” :
        LO.FirstOrder.ArithmeticProposition) := by
  let leftTerm := shortBinaryNumeralTerm left
  let rightTerm := shortBinaryNumeralTerm right
  let shiftTerm := shortBinaryNumeralTerm shift
  let leftSum := paAddTerm leftTerm shiftTerm
  let rightSum := paAddTerm rightTerm shiftTerm
  let shifted := CertifiedPAProof.cast
    (addLtAddAsTerms_formula leftTerm rightTerm shiftTerm)
    (proveAddLtAdd leftTerm rightTerm shiftTerm proof)
  exact proveLtTransport leftSum rightSum
    (shortBinaryNumeralTerm (left + shift))
    (shortBinaryNumeralTerm (right + shift))
    (proveBinaryNumeralAddition left shift)
    (proveBinaryNumeralAddition right shift)
    shifted

def binaryNumeralAddLtAddPayloadBound
    (left right shift relationPayloadLength : Nat) : Nat :=
  let leftTerm := shortBinaryNumeralTerm left
  let rightTerm := shortBinaryNumeralTerm right
  let shiftTerm := shortBinaryNumeralTerm shift
  let leftSum := paAddTerm leftTerm shiftTerm
  let rightSum := paAddTerm rightTerm shiftTerm
  let leftResult := shortBinaryNumeralTerm (left + shift)
  let rightResult := shortBinaryNumeralTerm (right + shift)
  let shiftedBound :=
    addLtAddImplicationFullPayloadBound leftTerm rightTerm shiftTerm +
      relationPayloadLength + 240 +
      34 * modusPonensSyntaxBudget
        (“!!leftTerm < !!rightTerm” :
          LO.FirstOrder.ArithmeticProposition)
        (“!!leftTerm + !!shiftTerm < !!rightTerm + !!shiftTerm” :
          LO.FirstOrder.ArithmeticProposition)
  binaryRelationTransportFullPayloadBound Language.ORing.Rel.lt
      leftSum rightSum leftResult rightResult
      (binaryNumeralAdditionPayloadPolynomial
        (Nat.size left + Nat.size shift))
      (binaryNumeralAdditionPayloadPolynomial
        (Nat.size right + Nat.size shift)) +
    shiftedBound + 240 +
    34 * modusPonensSyntaxBudget
      (“!!leftSum < !!rightSum” :
        LO.FirstOrder.ArithmeticProposition)
      (“!!leftResult < !!rightResult” :
        LO.FirstOrder.ArithmeticProposition)

theorem proveBinaryNumeralAddLtAdd_payloadLength_le
    (left right shift : Nat)
    (proof : CertifiedPAProof
      (“!!(shortBinaryNumeralTerm left) <
        !!(shortBinaryNumeralTerm right)” :
        LO.FirstOrder.ArithmeticProposition)) :
    (proveBinaryNumeralAddLtAdd left right shift proof).payloadLength <=
      binaryNumeralAddLtAddPayloadBound left right shift
        proof.payloadLength := by
  let leftTerm := shortBinaryNumeralTerm left
  let rightTerm := shortBinaryNumeralTerm right
  let shiftTerm := shortBinaryNumeralTerm shift
  let leftSum := paAddTerm leftTerm shiftTerm
  let rightSum := paAddTerm rightTerm shiftTerm
  let leftResult := shortBinaryNumeralTerm (left + shift)
  let rightResult := shortBinaryNumeralTerm (right + shift)
  let shifted : CertifiedPAProof
      (“!!leftSum < !!rightSum” :
        LO.FirstOrder.ArithmeticProposition) :=
    CertifiedPAProof.cast
      (addLtAddAsTerms_formula leftTerm rightTerm shiftTerm)
      (proveAddLtAdd leftTerm rightTerm shiftTerm proof)
  have himplication :=
    addLtAddImplication_full_payloadLength_le leftTerm rightTerm shiftTerm
  have hshiftedRaw :=
    proveAddLtAdd_payloadLength_le leftTerm rightTerm shiftTerm proof
  have hshiftedCast : shifted.payloadLength =
      (proveAddLtAdd leftTerm rightTerm shiftTerm proof).payloadLength := by
    dsimp only [shifted]
    exact cast_payloadLength
      (addLtAddAsTerms_formula leftTerm rightTerm shiftTerm)
      (proveAddLtAdd leftTerm rightTerm shiftTerm proof)
  have hshifted : shifted.payloadLength <=
      addLtAddImplicationFullPayloadBound leftTerm rightTerm shiftTerm +
        proof.payloadLength + 240 +
        34 * modusPonensSyntaxBudget
          (“!!leftTerm < !!rightTerm” :
            LO.FirstOrder.ArithmeticProposition)
          (“!!leftTerm + !!shiftTerm < !!rightTerm + !!shiftTerm” :
            LO.FirstOrder.ArithmeticProposition) := by
    rw [hshiftedCast]
    omega
  have hleftAddition :=
    proveBinaryNumeralAddition_payloadLength_le_polynomial left shift
  have hrightAddition :=
    proveBinaryNumeralAddition_payloadLength_le_polynomial right shift
  have htransport := proveLtTransport_payloadLength_le
    leftSum rightSum leftResult rightResult
    (proveBinaryNumeralAddition left shift)
    (proveBinaryNumeralAddition right shift) shifted
  have hrelationMonotone :=
    binaryRelationTransportFullPayloadBound_mono_lengths
      Language.ORing.Rel.lt leftSum rightSum leftResult rightResult
      hleftAddition hrightAddition
  have hfinal :
      (proveLtTransport leftSum rightSum leftResult rightResult
        (proveBinaryNumeralAddition left shift)
        (proveBinaryNumeralAddition right shift) shifted).payloadLength <=
        binaryRelationTransportFullPayloadBound Language.ORing.Rel.lt
          leftSum rightSum leftResult rightResult
          (binaryNumeralAdditionPayloadPolynomial
            (Nat.size left + Nat.size shift))
          (binaryNumeralAdditionPayloadPolynomial
            (Nat.size right + Nat.size shift)) +
        (addLtAddImplicationFullPayloadBound
            leftTerm rightTerm shiftTerm + proof.payloadLength + 240 +
          34 * modusPonensSyntaxBudget
            (“!!leftTerm < !!rightTerm” :
              LO.FirstOrder.ArithmeticProposition)
            (“!!leftTerm + !!shiftTerm < !!rightTerm + !!shiftTerm” :
              LO.FirstOrder.ArithmeticProposition)) + 240 +
        34 * modusPonensSyntaxBudget
          (“!!leftSum < !!rightSum” :
            LO.FirstOrder.ArithmeticProposition)
          (“!!leftResult < !!rightResult” :
            LO.FirstOrder.ArithmeticProposition) := by
    omega
  change
    (proveLtTransport leftSum rightSum leftResult rightResult
      (proveBinaryNumeralAddition left shift)
      (proveBinaryNumeralAddition right shift) shifted).payloadLength <= _
  simpa [binaryNumeralAddLtAddPayloadBound, leftTerm, rightTerm,
    shiftTerm, leftSum, rightSum, leftResult, rightResult] using hfinal

def paZeroEqualsBinaryZero_formula :
    (“!!paZeroTerm = !!paZeroTerm” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!paZeroTerm = !!(shortBinaryNumeralTerm 0)” :
        LO.FirstOrder.ArithmeticProposition) := by
  have hterm : shortBinaryNumeralTerm 0 = paZeroTerm := by
    simp [shortBinaryNumeralTerm,
      FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero,
      paZeroTerm]
  rw [hterm]

def provePaZeroEqualsBinaryZero :
    CertifiedPAProof
      (“!!paZeroTerm = !!(shortBinaryNumeralTerm 0)” :
        LO.FirstOrder.ArithmeticProposition) :=
  CertifiedPAProof.cast paZeroEqualsBinaryZero_formula
    (proveEqualityReflexivityAtTerm paZeroTerm)

def paOneEqualsBinaryOne_formula :
    (“!!paOneTerm = !!binaryOneAlgebraTerm” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!paOneTerm = !!(shortBinaryNumeralTerm 1)” :
        LO.FirstOrder.ArithmeticProposition) := by
  rw [binaryNumeralTerm_one_formula]

def provePaOneEqualsBinaryOne :
    CertifiedPAProof
      (“!!paOneTerm = !!(shortBinaryNumeralTerm 1)” :
        LO.FirstOrder.ArithmeticProposition) :=
  CertifiedPAProof.cast paOneEqualsBinaryOne_formula
    proveOneEqualsBinaryOneAlgebra

def proveZeroLtBinaryOne :
    CertifiedPAProof
      (“!!(shortBinaryNumeralTerm 0) <
        !!(shortBinaryNumeralTerm 1)” :
        LO.FirstOrder.ArithmeticProposition) :=
  proveLtTransport paZeroTerm paOneTerm
    (shortBinaryNumeralTerm 0) (shortBinaryNumeralTerm 1)
    provePaZeroEqualsBinaryZero provePaOneEqualsBinaryOne proveZeroLtOne

theorem provePaZeroEqualsBinaryZero_payloadLength_le :
    provePaZeroEqualsBinaryZero.payloadLength <=
      paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope 1) := by
  have hzero : PACompilerGeneratedTerm 1 1 paZeroTerm := .zero
  have hcode := generatedTerm_code_length_le_compiler hzero (by omega)
  have hproof := proveEqualityReflexivityAtTerm_payloadLength_le_primitive
    paZeroTerm (paGeneratedTermCodeEnvelope 1) hcode
  have hcast : provePaZeroEqualsBinaryZero.payloadLength =
      (proveEqualityReflexivityAtTerm paZeroTerm).payloadLength := by
    exact cast_payloadLength paZeroEqualsBinaryZero_formula
      (proveEqualityReflexivityAtTerm paZeroTerm)
  rw [hcast]
  exact hproof

theorem provePaOneEqualsBinaryOne_payloadLength_le :
    provePaOneEqualsBinaryOne.payloadLength <=
      paOneEqualsBinaryOneCostEnvelope 1 := by
  have hcast : provePaOneEqualsBinaryOne.payloadLength =
      proveOneEqualsBinaryOneAlgebra.payloadLength := by
    exact cast_payloadLength paOneEqualsBinaryOne_formula
      proveOneEqualsBinaryOneAlgebra
  rw [hcast]
  exact proveOneEqualsBinaryOneAlgebra_payloadLength_le_incrementLocal 1

def zeroLtBinaryOnePayloadBound : Nat :=
  binaryRelationTransportFullPayloadBound Language.ORing.Rel.lt
      paZeroTerm paOneTerm
      (shortBinaryNumeralTerm 0) (shortBinaryNumeralTerm 1)
      (paPrimitiveCostEnvelope (paGeneratedTermCodeEnvelope 1))
      (paOneEqualsBinaryOneCostEnvelope 1) +
    (32 + 10 * axiomSyntaxBudget .zeroLtOne) + 240 +
    34 * modusPonensSyntaxBudget
      (“!!paZeroTerm < !!paOneTerm” :
        LO.FirstOrder.ArithmeticProposition)
      (“!!(shortBinaryNumeralTerm 0) <
        !!(shortBinaryNumeralTerm 1)” :
        LO.FirstOrder.ArithmeticProposition)

theorem proveZeroLtBinaryOne_payloadLength_le :
    proveZeroLtBinaryOne.payloadLength <=
      zeroLtBinaryOnePayloadBound := by
  have htransport := proveLtTransport_payloadLength_le
    paZeroTerm paOneTerm
    (shortBinaryNumeralTerm 0) (shortBinaryNumeralTerm 1)
    provePaZeroEqualsBinaryZero provePaOneEqualsBinaryOne proveZeroLtOne
  have hmono := binaryRelationTransportFullPayloadBound_mono_lengths
    Language.ORing.Rel.lt paZeroTerm paOneTerm
    (shortBinaryNumeralTerm 0) (shortBinaryNumeralTerm 1)
    provePaZeroEqualsBinaryZero_payloadLength_le
    provePaOneEqualsBinaryOne_payloadLength_le
  have hzeroLt := proveZeroLtOne_payloadLength_le
  unfold proveZeroLtBinaryOne zeroLtBinaryOnePayloadBound
  omega

def castBinaryNumeralLt
    {leftSource rightSource leftTarget rightTarget : Nat}
    (hleft : leftSource = leftTarget)
    (hright : rightSource = rightTarget)
    (proof : CertifiedPAProof
      (“!!(shortBinaryNumeralTerm leftSource) <
        !!(shortBinaryNumeralTerm rightSource)” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(shortBinaryNumeralTerm leftTarget) <
        !!(shortBinaryNumeralTerm rightTarget)” :
        LO.FirstOrder.ArithmeticProposition) := by
  subst leftTarget
  subst rightTarget
  exact proof

theorem castBinaryNumeralLt_payloadLength_eq
    {leftSource rightSource leftTarget rightTarget : Nat}
    (hleft : leftSource = leftTarget)
    (hright : rightSource = rightTarget)
    (proof : CertifiedPAProof
      (“!!(shortBinaryNumeralTerm leftSource) <
        !!(shortBinaryNumeralTerm rightSource)” :
        LO.FirstOrder.ArithmeticProposition)) :
    (castBinaryNumeralLt hleft hright proof).payloadLength =
      proof.payloadLength := by
  subst leftTarget
  subst rightTarget
  rfl

theorem binaryNumeralAddLtAddPayloadBound_mono_relation
    (left right shift : Nat) {relationLength relationBound : Nat}
    (hrelation : relationLength <= relationBound) :
    binaryNumeralAddLtAddPayloadBound left right shift relationLength <=
      binaryNumeralAddLtAddPayloadBound left right shift relationBound := by
  dsimp [binaryNumeralAddLtAddPayloadBound]
  omega

def proveZeroLtBinaryTwo :
    CertifiedPAProof
      (“!!(shortBinaryNumeralTerm 0) <
        !!(shortBinaryNumeralTerm 2)” :
        LO.FirstOrder.ArithmeticProposition) := by
  let oneToTwoRaw :=
    proveBinaryNumeralAddLtAdd 0 1 1 proveZeroLtBinaryOne
  let oneToTwo := castBinaryNumeralLt
    (Nat.zero_add 1) rfl oneToTwoRaw
  exact proveLtTransitivity
    (shortBinaryNumeralTerm 0)
    (shortBinaryNumeralTerm 1)
    (shortBinaryNumeralTerm 2)
    proveZeroLtBinaryOne oneToTwo

def zeroLtBinaryTwoPayloadBound : Nat :=
  let oneToTwoBound :=
    binaryNumeralAddLtAddPayloadBound 0 1 1 zeroLtBinaryOnePayloadBound
  ltTransitivityFullPayloadBound
    (shortBinaryNumeralTerm 0)
    (shortBinaryNumeralTerm 1)
    (shortBinaryNumeralTerm 2)
    zeroLtBinaryOnePayloadBound oneToTwoBound

theorem proveZeroLtBinaryTwo_payloadLength_le :
    proveZeroLtBinaryTwo.payloadLength <=
      zeroLtBinaryTwoPayloadBound := by
  let oneToTwoRaw :=
    proveBinaryNumeralAddLtAdd 0 1 1 proveZeroLtBinaryOne
  let oneToTwo := castBinaryNumeralLt
    (Nat.zero_add 1) rfl oneToTwoRaw
  have honeToTwoRaw := proveBinaryNumeralAddLtAdd_payloadLength_le
    0 1 1 proveZeroLtBinaryOne
  have honeToTwoCast := castBinaryNumeralLt_payloadLength_eq
    (Nat.zero_add 1) rfl oneToTwoRaw
  have honeToTwoMono := binaryNumeralAddLtAddPayloadBound_mono_relation
    0 1 1 proveZeroLtBinaryOne_payloadLength_le
  have honeToTwo : oneToTwo.payloadLength <=
      binaryNumeralAddLtAddPayloadBound 0 1 1
        zeroLtBinaryOnePayloadBound := by
    rw [honeToTwoCast]
    exact honeToTwoRaw.trans honeToTwoMono
  have htrans := proveLtTransitivity_full_payloadLength_le
    (shortBinaryNumeralTerm 0)
    (shortBinaryNumeralTerm 1)
    (shortBinaryNumeralTerm 2)
    proveZeroLtBinaryOne oneToTwo
  have hmono := ltTransitivityFullPayloadBound_mono_lengths
    (shortBinaryNumeralTerm 0)
    (shortBinaryNumeralTerm 1)
    (shortBinaryNumeralTerm 2)
    proveZeroLtBinaryOne_payloadLength_le honeToTwo
  change
    (proveLtTransitivity
      (shortBinaryNumeralTerm 0)
      (shortBinaryNumeralTerm 1)
      (shortBinaryNumeralTerm 2)
      proveZeroLtBinaryOne oneToTwo).payloadLength <= _
  unfold zeroLtBinaryTwoPayloadBound
  exact htrans.trans hmono

theorem binaryZeroLtAsPaZero_formula
    (factor : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (“!!(shortBinaryNumeralTerm 0) < !!factor” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!paZeroTerm < !!factor” :
        LO.FirstOrder.ArithmeticProposition) := by
  have hzero : shortBinaryNumeralTerm 0 = paZeroTerm := by
    simp [shortBinaryNumeralTerm,
      FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero,
      paZeroTerm]
  rw [hzero]

def provePaZeroLtBinaryTwo :
    CertifiedPAProof
      (“!!paZeroTerm < !!(shortBinaryNumeralTerm 2)” :
        LO.FirstOrder.ArithmeticProposition) :=
  CertifiedPAProof.cast
    (binaryZeroLtAsPaZero_formula (shortBinaryNumeralTerm 2))
    proveZeroLtBinaryTwo

theorem provePaZeroLtBinaryTwo_payloadLength_le :
    provePaZeroLtBinaryTwo.payloadLength <=
      zeroLtBinaryTwoPayloadBound := by
  have hcast : provePaZeroLtBinaryTwo.payloadLength =
      proveZeroLtBinaryTwo.payloadLength := by
    exact cast_payloadLength
      (binaryZeroLtAsPaZero_formula (shortBinaryNumeralTerm 2))
      proveZeroLtBinaryTwo
  rw [hcast]
  exact proveZeroLtBinaryTwo_payloadLength_le

theorem mulLtMulAsTerms_formula
    (left right factor : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (“!!left * !!factor < !!right * !!factor” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!(paMulTerm left factor) < !!(paMulTerm right factor)” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [paMulTerm]

def provePositiveBinaryDouble
    (high : Nat)
    (highProof : CertifiedPAProof
      (“!!(shortBinaryNumeralTerm 0) <
        !!(shortBinaryNumeralTerm high)” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(shortBinaryNumeralTerm 0) <
        !!(shortBinaryNumeralTerm (high + high))” :
        LO.FirstOrder.ArithmeticProposition) := by
  let zeroTerm := shortBinaryNumeralTerm 0
  let highTerm := shortBinaryNumeralTerm high
  let twoTerm := shortBinaryNumeralTerm 2
  let leftProduct := paMulTerm zeroTerm twoTerm
  let rightProduct := paMulTerm highTerm twoTerm
  let multipliedRaw := proveMulLtMul zeroTerm highTerm twoTerm
    highProof provePaZeroLtBinaryTwo
  let multiplied : CertifiedPAProof
      (“!!leftProduct < !!rightProduct” :
        LO.FirstOrder.ArithmeticProposition) :=
    CertifiedPAProof.cast
      (mulLtMulAsTerms_formula zeroTerm highTerm twoTerm)
      multipliedRaw
  let normalized := proveLtTransport leftProduct rightProduct
    (shortBinaryNumeralTerm (0 * 2))
    (shortBinaryNumeralTerm (high * 2))
    (proveBinaryNumeralMultiplication 0 2)
    (proveBinaryNumeralMultiplication high 2)
    multiplied
  exact castBinaryNumeralLt (by omega) (by omega) normalized

def positiveBinaryDoublePayloadBound
    (high relationPayloadLength : Nat) : Nat :=
  let zeroTerm := shortBinaryNumeralTerm 0
  let highTerm := shortBinaryNumeralTerm high
  let twoTerm := shortBinaryNumeralTerm 2
  let leftProduct := paMulTerm zeroTerm twoTerm
  let rightProduct := paMulTerm highTerm twoTerm
  let multipliedBound :=
    mulLtMulImplicationFullPayloadBound zeroTerm highTerm twoTerm +
      relationPayloadLength + zeroLtBinaryTwoPayloadBound + 384 +
      11 * conjunctionSyntaxBudget
        (“!!zeroTerm < !!highTerm” :
          LO.FirstOrder.ArithmeticProposition)
        (“!!paZeroTerm < !!twoTerm” :
          LO.FirstOrder.ArithmeticProposition) +
      34 * modusPonensSyntaxBudget
        ((“!!zeroTerm < !!highTerm” :
            LO.FirstOrder.ArithmeticProposition) ⋏
          (“!!paZeroTerm < !!twoTerm” :
            LO.FirstOrder.ArithmeticProposition))
        (“!!zeroTerm * !!twoTerm < !!highTerm * !!twoTerm” :
          LO.FirstOrder.ArithmeticProposition)
  binaryRelationTransportFullPayloadBound Language.ORing.Rel.lt
      leftProduct rightProduct
      (shortBinaryNumeralTerm (0 * 2))
      (shortBinaryNumeralTerm (high * 2))
      (binaryNumeralMultiplicationPayloadPolynomial
        (Nat.size 0 + Nat.size 2))
      (binaryNumeralMultiplicationPayloadPolynomial
        (Nat.size high + Nat.size 2)) +
    multipliedBound + 240 +
    34 * modusPonensSyntaxBudget
      (“!!leftProduct < !!rightProduct” :
        LO.FirstOrder.ArithmeticProposition)
      (“!!(shortBinaryNumeralTerm (0 * 2)) <
        !!(shortBinaryNumeralTerm (high * 2))” :
        LO.FirstOrder.ArithmeticProposition)

theorem positiveBinaryDoublePayloadBound_mono_relation
    (high : Nat) {relationLength relationBound : Nat}
    (hrelation : relationLength <= relationBound) :
    positiveBinaryDoublePayloadBound high relationLength <=
      positiveBinaryDoublePayloadBound high relationBound := by
  dsimp [positiveBinaryDoublePayloadBound]
  omega

theorem provePositiveBinaryDouble_payloadLength_le
    (high : Nat)
    (highProof : CertifiedPAProof
      (“!!(shortBinaryNumeralTerm 0) <
        !!(shortBinaryNumeralTerm high)” :
        LO.FirstOrder.ArithmeticProposition)) :
    (provePositiveBinaryDouble high highProof).payloadLength <=
      positiveBinaryDoublePayloadBound high highProof.payloadLength := by
  let zeroTerm := shortBinaryNumeralTerm 0
  let highTerm := shortBinaryNumeralTerm high
  let twoTerm := shortBinaryNumeralTerm 2
  let leftProduct := paMulTerm zeroTerm twoTerm
  let rightProduct := paMulTerm highTerm twoTerm
  let multipliedRaw := proveMulLtMul zeroTerm highTerm twoTerm
    highProof provePaZeroLtBinaryTwo
  let multiplied : CertifiedPAProof
      (“!!leftProduct < !!rightProduct” :
        LO.FirstOrder.ArithmeticProposition) :=
    CertifiedPAProof.cast
      (mulLtMulAsTerms_formula zeroTerm highTerm twoTerm)
      multipliedRaw
  have himplication := mulLtMulImplication_full_payloadLength_le
    zeroTerm highTerm twoTerm
  have hmulRaw := proveMulLtMul_payloadLength_le
    zeroTerm highTerm twoTerm highProof provePaZeroLtBinaryTwo
  have hmulRawBound : multipliedRaw.payloadLength <=
      (mulLtMulImplication zeroTerm highTerm twoTerm).payloadLength +
        highProof.payloadLength + provePaZeroLtBinaryTwo.payloadLength +
        384 +
        11 * conjunctionSyntaxBudget
          (“!!zeroTerm < !!highTerm” :
            LO.FirstOrder.ArithmeticProposition)
          (“!!paZeroTerm < !!twoTerm” :
            LO.FirstOrder.ArithmeticProposition) +
        34 * modusPonensSyntaxBudget
          ((“!!zeroTerm < !!highTerm” :
              LO.FirstOrder.ArithmeticProposition) ⋏
            (“!!paZeroTerm < !!twoTerm” :
              LO.FirstOrder.ArithmeticProposition))
          (“!!zeroTerm * !!twoTerm < !!highTerm * !!twoTerm” :
            LO.FirstOrder.ArithmeticProposition) := by
    dsimp only [multipliedRaw]
    exact hmulRaw
  have hmulCast : multiplied.payloadLength = multipliedRaw.payloadLength := by
    dsimp only [multiplied]
    exact cast_payloadLength
      (mulLtMulAsTerms_formula zeroTerm highTerm twoTerm) multipliedRaw
  have hmultiplied : multiplied.payloadLength <=
      mulLtMulImplicationFullPayloadBound zeroTerm highTerm twoTerm +
        highProof.payloadLength + zeroLtBinaryTwoPayloadBound + 384 +
        11 * conjunctionSyntaxBudget
          (“!!zeroTerm < !!highTerm” :
            LO.FirstOrder.ArithmeticProposition)
          (“!!paZeroTerm < !!twoTerm” :
            LO.FirstOrder.ArithmeticProposition) +
        34 * modusPonensSyntaxBudget
          ((“!!zeroTerm < !!highTerm” :
              LO.FirstOrder.ArithmeticProposition) ⋏
            (“!!paZeroTerm < !!twoTerm” :
              LO.FirstOrder.ArithmeticProposition))
          (“!!zeroTerm * !!twoTerm < !!highTerm * !!twoTerm” :
            LO.FirstOrder.ArithmeticProposition) := by
    rw [hmulCast]
    have hfactor := provePaZeroLtBinaryTwo_payloadLength_le
    omega
  have hleftMultiplication :=
    proveBinaryNumeralMultiplication_payloadLength_le_polynomial 0 2
  have hrightMultiplication :=
    proveBinaryNumeralMultiplication_payloadLength_le_polynomial high 2
  have htransport := proveLtTransport_payloadLength_le
    leftProduct rightProduct
    (shortBinaryNumeralTerm (0 * 2))
    (shortBinaryNumeralTerm (high * 2))
    (proveBinaryNumeralMultiplication 0 2)
    (proveBinaryNumeralMultiplication high 2)
    multiplied
  have hrelationMono := binaryRelationTransportFullPayloadBound_mono_lengths
    Language.ORing.Rel.lt leftProduct rightProduct
    (shortBinaryNumeralTerm (0 * 2))
    (shortBinaryNumeralTerm (high * 2))
    hleftMultiplication hrightMultiplication
  let normalized := proveLtTransport leftProduct rightProduct
    (shortBinaryNumeralTerm (0 * 2))
    (shortBinaryNumeralTerm (high * 2))
    (proveBinaryNumeralMultiplication 0 2)
    (proveBinaryNumeralMultiplication high 2)
    multiplied
  have hnormalized : normalized.payloadLength <=
      binaryRelationTransportFullPayloadBound Language.ORing.Rel.lt
          leftProduct rightProduct
          (shortBinaryNumeralTerm (0 * 2))
          (shortBinaryNumeralTerm (high * 2))
          (binaryNumeralMultiplicationPayloadPolynomial
            (Nat.size 0 + Nat.size 2))
          (binaryNumeralMultiplicationPayloadPolynomial
            (Nat.size high + Nat.size 2)) +
        (mulLtMulImplicationFullPayloadBound zeroTerm highTerm twoTerm +
          highProof.payloadLength + zeroLtBinaryTwoPayloadBound + 384 +
          11 * conjunctionSyntaxBudget
            (“!!zeroTerm < !!highTerm” :
              LO.FirstOrder.ArithmeticProposition)
            (“!!paZeroTerm < !!twoTerm” :
              LO.FirstOrder.ArithmeticProposition) +
          34 * modusPonensSyntaxBudget
            ((“!!zeroTerm < !!highTerm” :
                LO.FirstOrder.ArithmeticProposition) ⋏
              (“!!paZeroTerm < !!twoTerm” :
                LO.FirstOrder.ArithmeticProposition))
            (“!!zeroTerm * !!twoTerm < !!highTerm * !!twoTerm” :
              LO.FirstOrder.ArithmeticProposition)) + 240 +
        34 * modusPonensSyntaxBudget
          (“!!leftProduct < !!rightProduct” :
            LO.FirstOrder.ArithmeticProposition)
          (“!!(shortBinaryNumeralTerm (0 * 2)) <
            !!(shortBinaryNumeralTerm (high * 2))” :
            LO.FirstOrder.ArithmeticProposition) := by
    dsimp only [normalized]
    omega
  have hcast := castBinaryNumeralLt_payloadLength_eq
    (show 0 * 2 = 0 by omega)
    (show high * 2 = high + high by omega) normalized
  change
    (castBinaryNumeralLt (show 0 * 2 = 0 by omega)
      (show high * 2 = high + high by omega) normalized).payloadLength <= _
  rw [hcast]
  simpa [positiveBinaryDoublePayloadBound, zeroTerm, highTerm,
    twoTerm, leftProduct, rightProduct] using hnormalized

noncomputable def positiveBinaryNumeralPayloadBound : Nat → Nat :=
  Nat.binaryRec'
    0
    (fun bit high _canonical highBound =>
      if high = 0 then
        zeroLtBinaryOnePayloadBound
      else
        let doubleBound :=
          positiveBinaryDoublePayloadBound high highBound
        if bit then
          let doubleToOddBound :=
            binaryNumeralAddLtAddPayloadBound
              0 1 (high + high) zeroLtBinaryOnePayloadBound
          ltTransitivityFullPayloadBound
            (shortBinaryNumeralTerm 0)
            (shortBinaryNumeralTerm (high + high))
            (shortBinaryNumeralTerm (1 + (high + high)))
            doubleBound doubleToOddBound
        else
          doubleBound)

theorem positiveBinaryNumeralPayloadBound_bit
    (bit : Bool) (high : Nat)
    (hcanonical : high = 0 → bit = true) :
    positiveBinaryNumeralPayloadBound (Nat.bit bit high) =
      (if high = 0 then
        zeroLtBinaryOnePayloadBound
      else
        let highBound := positiveBinaryNumeralPayloadBound high
        let doubleBound :=
          positiveBinaryDoublePayloadBound high highBound
        if bit then
          let doubleToOddBound :=
            binaryNumeralAddLtAddPayloadBound
              0 1 (high + high) zeroLtBinaryOnePayloadBound
          ltTransitivityFullPayloadBound
            (shortBinaryNumeralTerm 0)
            (shortBinaryNumeralTerm (high + high))
            (shortBinaryNumeralTerm (1 + (high + high)))
            doubleBound doubleToOddBound
        else
          doubleBound) := by
  unfold positiveBinaryNumeralPayloadBound
  rw [Nat.binaryRec'_eq
    (motive := fun _ => Nat) bit high hcanonical]

structure PositiveBinaryNumeralCompilation (value : Nat) where
  proof : CertifiedPAProof
    (“!!(shortBinaryNumeralTerm 0) <
      !!(shortBinaryNumeralTerm value)” :
      LO.FirstOrder.ArithmeticProposition)
  payload_le : proof.payloadLength <=
    positiveBinaryNumeralPayloadBound value

noncomputable def compilePositiveBinaryNumeral :
    (value : Nat) → 0 < value → PositiveBinaryNumeralCompilation value :=
  Nat.binaryRec'
    (motive := fun value =>
      0 < value → PositiveBinaryNumeralCompilation value)
    (fun hpositive => False.elim (Nat.not_lt_zero 0 hpositive))
    (fun bit high hcanonical recurse _hpositive => by
      by_cases hhigh : high = 0
      · subst high
        have hbit : bit = true := hcanonical rfl
        subst bit
        have hone : 1 = Nat.bit true 0 := by simp [Nat.bit_val]
        let resultProof := castBinaryNumeralLt rfl hone
          proveZeroLtBinaryOne
        refine ⟨resultProof, ?_⟩
        have hcast := castBinaryNumeralLt_payloadLength_eq
          rfl hone proveZeroLtBinaryOne
        rw [hcast]
        rw [positiveBinaryNumeralPayloadBound_bit true 0 (by simp)]
        rw [if_pos rfl]
        exact proveZeroLtBinaryOne_payloadLength_le
      · have hhighPositive : 0 < high := Nat.pos_of_ne_zero hhigh
        let highCompilation := recurse hhighPositive
        let highProof := highCompilation.proof
        let doubleProof := provePositiveBinaryDouble high highProof
        have hdoubleRaw := provePositiveBinaryDouble_payloadLength_le
          high highProof
        have hdoubleMono := positiveBinaryDoublePayloadBound_mono_relation
          high highCompilation.payload_le
        have hdouble : doubleProof.payloadLength <=
            positiveBinaryDoublePayloadBound high
              (positiveBinaryNumeralPayloadBound high) :=
          hdoubleRaw.trans hdoubleMono
        cases bit with
        | false =>
            have hvalue : high + high = Nat.bit false high := by
              simp [Nat.bit_val, Nat.two_mul]
            let resultProof := castBinaryNumeralLt rfl hvalue doubleProof
            refine ⟨resultProof, ?_⟩
            have hcast := castBinaryNumeralLt_payloadLength_eq
              rfl hvalue doubleProof
            rw [hcast]
            rw [positiveBinaryNumeralPayloadBound_bit false high hcanonical]
            rw [if_neg hhigh]
            simp only [Bool.false_eq_true, if_false]
            exact hdouble
        | true =>
            let doubleToOddRaw :=
              proveBinaryNumeralAddLtAdd 0 1 (high + high)
                proveZeroLtBinaryOne
            let doubleToOdd := castBinaryNumeralLt
              (Nat.zero_add (high + high)) rfl doubleToOddRaw
            have hdoubleToOddRaw :=
              proveBinaryNumeralAddLtAdd_payloadLength_le
                0 1 (high + high) proveZeroLtBinaryOne
            have hdoubleToOddCast := castBinaryNumeralLt_payloadLength_eq
              (Nat.zero_add (high + high)) rfl doubleToOddRaw
            have hdoubleToOddMono :=
              binaryNumeralAddLtAddPayloadBound_mono_relation
                0 1 (high + high)
                proveZeroLtBinaryOne_payloadLength_le
            have hdoubleToOdd : doubleToOdd.payloadLength <=
                binaryNumeralAddLtAddPayloadBound
                  0 1 (high + high) zeroLtBinaryOnePayloadBound := by
              rw [hdoubleToOddCast]
              exact hdoubleToOddRaw.trans hdoubleToOddMono
            let oddProof := proveLtTransitivity
              (shortBinaryNumeralTerm 0)
              (shortBinaryNumeralTerm (high + high))
              (shortBinaryNumeralTerm (1 + (high + high)))
              doubleProof doubleToOdd
            have hoddRaw := proveLtTransitivity_full_payloadLength_le
              (shortBinaryNumeralTerm 0)
              (shortBinaryNumeralTerm (high + high))
              (shortBinaryNumeralTerm (1 + (high + high)))
              doubleProof doubleToOdd
            have hoddMono := ltTransitivityFullPayloadBound_mono_lengths
              (shortBinaryNumeralTerm 0)
              (shortBinaryNumeralTerm (high + high))
              (shortBinaryNumeralTerm (1 + (high + high)))
              hdouble hdoubleToOdd
            have hodd : oddProof.payloadLength <=
                ltTransitivityFullPayloadBound
                  (shortBinaryNumeralTerm 0)
                  (shortBinaryNumeralTerm (high + high))
                  (shortBinaryNumeralTerm (1 + (high + high)))
                  (positiveBinaryDoublePayloadBound high
                    (positiveBinaryNumeralPayloadBound high))
                  (binaryNumeralAddLtAddPayloadBound
                    0 1 (high + high) zeroLtBinaryOnePayloadBound) :=
              hoddRaw.trans hoddMono
            have hvalue :
                1 + (high + high) = Nat.bit true high := by
              simp [Nat.bit_val, Nat.two_mul, Nat.add_assoc,
                Nat.add_comm]
            let resultProof := castBinaryNumeralLt rfl hvalue oddProof
            refine ⟨resultProof, ?_⟩
            have hcast := castBinaryNumeralLt_payloadLength_eq
              rfl hvalue oddProof
            rw [hcast]
            rw [positiveBinaryNumeralPayloadBound_bit true high hcanonical]
            rw [if_neg hhigh]
            simp only [if_true]
            exact hodd)

noncomputable def provePositiveBinaryNumeral
    (value : Nat) (hpositive : 0 < value) :
    CertifiedPAProof
      (“!!(shortBinaryNumeralTerm 0) <
        !!(shortBinaryNumeralTerm value)” :
        LO.FirstOrder.ArithmeticProposition) :=
  (compilePositiveBinaryNumeral value hpositive).proof

theorem provePositiveBinaryNumeral_payloadLength_le
    (value : Nat) (hpositive : 0 < value) :
    (provePositiveBinaryNumeral value hpositive).payloadLength <=
      positiveBinaryNumeralPayloadBound value :=
  (compilePositiveBinaryNumeral value hpositive).payload_le

theorem provePositiveBinaryNumeral_verifier_eq_true
    (value : Nat) (hpositive : 0 < value) :
    listedCompactCertifiedPAProofVerifier
      (provePositiveBinaryNumeral value hpositive).code
      (compactFormulaCode
        (“!!(shortBinaryNumeralTerm 0) <
          !!(shortBinaryNumeralTerm value)” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  (provePositiveBinaryNumeral value hpositive).verifier_eq_true

theorem proveZeroLtOne_verifier_eq_true :
    listedCompactCertifiedPAProofVerifier proveZeroLtOne.code
      (compactFormulaCode
        (“!!paZeroTerm < !!paOneTerm” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  proveZeroLtOne.verifier_eq_true

theorem proveLtIrrefl_verifier_eq_true
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    listedCompactCertifiedPAProofVerifier
      (proveLtIrrefl term).code
      (compactFormulaCode
        (∼(“!!term < !!term” :
          LO.FirstOrder.ArithmeticProposition))) = true :=
  (proveLtIrrefl term).verifier_eq_true

theorem proveAddLtAdd_verifier_eq_true
    (left right shift : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (proof : CertifiedPAProof
      (“!!left < !!right” : LO.FirstOrder.ArithmeticProposition)) :
    listedCompactCertifiedPAProofVerifier
      (proveAddLtAdd left right shift proof).code
      (compactFormulaCode
        (“!!left + !!shift < !!right + !!shift” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  (proveAddLtAdd left right shift proof).verifier_eq_true

theorem proveLtTransitivity_verifier_eq_true
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (leftProof : CertifiedPAProof
      (“!!left < !!middle” : LO.FirstOrder.ArithmeticProposition))
    (rightProof : CertifiedPAProof
      (“!!middle < !!right” : LO.FirstOrder.ArithmeticProposition)) :
    listedCompactCertifiedPAProofVerifier
      (proveLtTransitivity left middle right leftProof rightProof).code
      (compactFormulaCode
        (“!!left < !!right” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  (proveLtTransitivity left middle right leftProof rightProof).verifier_eq_true

#print axioms proveZeroLtOne_verifier_eq_true
#print axioms proveLtIrrefl_verifier_eq_true
#print axioms proveLtIrrefl_payloadLength_le
#print axioms proveAddLtAdd_verifier_eq_true
#print axioms proveLtTransitivity_verifier_eq_true
#print axioms provePositiveBinaryNumeral_verifier_eq_true
#print axioms provePositiveBinaryNumeral_payloadLength_le

end FoundationCompactPAQuantitativeOrder
