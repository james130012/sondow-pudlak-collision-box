import integration.FoundationCompactPABinaryNumeralCompiler
import integration.FoundationCompactPAQuantitativeEqualityTransitivity
import integration.FoundationCompactPAQuantitativeFunctionCongruence

/-!
# Certified PA normalization of short binary-numeral addition

The final compiler in this file will recurse on binary digits.  This first
section exposes the exact PA commutative-semiring rewrites used by that
recursion as real derivations with public structural certificates.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABinaryNumeralAddition

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationComputableCompactPAProofEncoder
open FoundationCompactListedCertifiedVerifier
open FoundationCompactCertifiedModusPonens
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralCompiler
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeEqualityTransitivity
open FoundationCompactPAQuantitativeFunctionCongruence

def specializeTwiceWithCasts
    {outerBody middleBody : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    {target : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAProof (∀⁰ outerBody))
    (first second : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstFormula : outerBody/[first] = ∀⁰ middleBody)
    (secondFormula : middleBody/[second] = target) :
    CertifiedPAProof target :=
  cast secondFormula
    (specialize
      (cast firstFormula (specialize proof first)) second)

def specializeThriceWithCasts
    {outerBody middleBody innerBody :
      LO.FirstOrder.ArithmeticSemiformula Nat 1}
    {target : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAProof (∀⁰ outerBody))
    (first second third : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstFormula : outerBody/[first] = ∀⁰ middleBody)
    (secondFormula : middleBody/[second] = ∀⁰ innerBody)
    (thirdFormula : innerBody/[third] = target) :
    CertifiedPAProof target :=
  cast thirdFormula
    (specialize
      (specializeTwiceWithCasts proof first second firstFormula secondFormula)
      third)

theorem specializeTwiceWithCasts_payloadLength_le
    {outerBody middleBody : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    {target : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAProof (∀⁰ outerBody))
    (first second : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstFormula : outerBody/[first] = ∀⁰ middleBody)
    (secondFormula : middleBody/[second] = target) :
    (specializeTwiceWithCasts proof first second firstFormula
      secondFormula).payloadLength <=
        proof.payloadLength + specializationCost outerBody first +
          specializationCost middleBody second := by
  have hfirst := specialize_payloadLength_le_cost proof first
  have hsecond := specialize_payloadLength_le_cost
    (cast firstFormula (specialize proof first)) second
  change
    (cast secondFormula
      (specialize (cast firstFormula (specialize proof first))
        second)).payloadLength <= _
  rw [cast_payloadLength]
  rw [cast_payloadLength] at hsecond
  omega

theorem specializeThriceWithCasts_payloadLength_le
    {outerBody middleBody innerBody :
      LO.FirstOrder.ArithmeticSemiformula Nat 1}
    {target : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAProof (∀⁰ outerBody))
    (first second third : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (firstFormula : outerBody/[first] = ∀⁰ middleBody)
    (secondFormula : middleBody/[second] = ∀⁰ innerBody)
    (thirdFormula : innerBody/[third] = target) :
    (specializeThriceWithCasts proof first second third firstFormula
      secondFormula thirdFormula).payloadLength <=
        proof.payloadLength + specializationCost outerBody first +
          specializationCost middleBody second +
          specializationCost innerBody third := by
  have hfirstTwo := specializeTwiceWithCasts_payloadLength_le
    proof first second firstFormula secondFormula
  have hthird := specialize_payloadLength_le_cost
    (specializeTwiceWithCasts proof first second firstFormula secondFormula)
    third
  change
    (cast thirdFormula
      (specialize
        (specializeTwiceWithCasts proof first second firstFormula
          secondFormula) third)).payloadLength <= _
  rw [cast_payloadLength]
  omega

theorem substQ_bvarOne
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (Rew.subst ![term]).q
        (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2) =
      Rew.bShift term := by
  simpa using
    (Rew.q_bvar_succ (Rew.subst ![term]) (0 : Fin 1))

theorem substQQ_bvarOne
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (Rew.subst ![term]).q.q
        (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 3) =
      (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2) := by
  calc
    (Rew.subst ![term]).q.q
        (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 3) =
        Rew.bShift
          ((Rew.subst ![term]).q
            (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2)) := by
      simpa using
        (Rew.q_bvar_succ ((Rew.subst ![term]).q) (0 : Fin 2))
    _ = (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2) := by simp

theorem substQQ_bvarTwo
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (Rew.subst ![term]).q.q
        (#2 : LO.FirstOrder.ArithmeticSemiterm Nat 3) =
      Rew.bShift (Rew.bShift term) := by
  calc
    (Rew.subst ![term]).q.q
        (#2 : LO.FirstOrder.ArithmeticSemiterm Nat 3) =
        Rew.bShift
          ((Rew.subst ![term]).q
            (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2)) := by
      simpa using
        (Rew.q_bvar_succ ((Rew.subst ![term]).q) (1 : Fin 2))
    _ = Rew.bShift (Rew.bShift term) := by rw [substQ_bvarOne]

/-! ## Addition commutativity -/

def addCommutativityOuterBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰ (#1 + #0 = #0 + #1)”

theorem addCommutativityAxiom_formula :
    (Rewriting.emb PAAxiomCertificate.addComm.sentence :
        LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ addCommutativityOuterBody := by
  simp [addCommutativityOuterBody, PAAxiomCertificate.sentence]

def addCommutativityAxiomProof :
    CertifiedPAProof (∀⁰ addCommutativityOuterBody) :=
  cast addCommutativityAxiom_formula (ofAxiom .addComm)

def addCommutativityInnerBody
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!!(Rew.bShift left) + #0 = #0 + !!(Rew.bShift left)”

theorem addCommutativityAfterFirst_formula
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    addCommutativityOuterBody/[left] =
      ∀⁰ addCommutativityInnerBody left := by
  simp [addCommutativityOuterBody, addCommutativityInnerBody,
    substQ_bvarOne]

theorem addCommutativityFinal_formula
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (addCommutativityInnerBody left)/[right] =
      (“!!left + !!right = !!right + !!left” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [addCommutativityInnerBody]

def proveAddCommutativity
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!left + !!right = !!right + !!left” :
        LO.FirstOrder.ArithmeticProposition) :=
  specializeTwiceWithCasts addCommutativityAxiomProof left right
    (addCommutativityAfterFirst_formula left)
    (addCommutativityFinal_formula left right)

theorem addCommutativityAxiomProof_payloadLength_le :
    addCommutativityAxiomProof.payloadLength <=
      32 + 10 * axiomSyntaxBudget .addComm := by
  calc
    addCommutativityAxiomProof.payloadLength =
        (ofAxiom .addComm).payloadLength := by
      change
        (cast addCommutativityAxiom_formula
          (ofAxiom .addComm)).payloadLength = _
      exact cast_payloadLength _ _
    _ <= _ := ofAxiom_payloadLength_le .addComm

theorem proveAddCommutativity_payloadLength_le
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveAddCommutativity left right).payloadLength <=
      addCommutativityAxiomProof.payloadLength +
        specializationCost addCommutativityOuterBody left +
        specializationCost (addCommutativityInnerBody left) right :=
  specializeTwiceWithCasts_payloadLength_le
    addCommutativityAxiomProof left right
      (addCommutativityAfterFirst_formula left)
      (addCommutativityFinal_formula left right)

/-! ## Addition associativity -/

def addAssociativityOuterBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰ ∀⁰ ((#2 + #1) + #0 = #2 + (#1 + #0))”

theorem addAssociativityAxiom_formula :
    (Rewriting.emb PAAxiomCertificate.addAssoc.sentence :
        LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ addAssociativityOuterBody := by
  simp [addAssociativityOuterBody, PAAxiomCertificate.sentence]

def addAssociativityAxiomProof :
    CertifiedPAProof (∀⁰ addAssociativityOuterBody) :=
  cast addAssociativityAxiom_formula (ofAxiom .addAssoc)

def addAssociativityMiddleBody
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰
    ((!!(Rew.bShift (Rew.bShift left)) + #1) + #0 =
      !!(Rew.bShift (Rew.bShift left)) + (#1 + #0))”

theorem addAssociativityAfterFirst_formula
    (left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    addAssociativityOuterBody/[left] =
      ∀⁰ addAssociativityMiddleBody left := by
  simp [addAssociativityOuterBody, addAssociativityMiddleBody,
    substQQ_bvarOne, substQQ_bvarTwo]

def addAssociativityInnerBody
    (left middle : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “(!!(Rew.bShift left) + !!(Rew.bShift middle)) + #0 =
    !!(Rew.bShift left) + (!!(Rew.bShift middle) + #0)”

theorem addAssociativityAfterSecond_formula
    (left middle : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (addAssociativityMiddleBody left)/[middle] =
      ∀⁰ addAssociativityInnerBody left middle := by
  simp [addAssociativityMiddleBody, addAssociativityInnerBody,
    substQ_bvarOne]

theorem addAssociativityFinal_formula
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (addAssociativityInnerBody left middle)/[right] =
      (“(!!left + !!middle) + !!right =
        !!left + (!!middle + !!right)” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [addAssociativityInnerBody]

def proveAddAssociativity
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“(!!left + !!middle) + !!right =
        !!left + (!!middle + !!right)” :
        LO.FirstOrder.ArithmeticProposition) :=
  specializeThriceWithCasts addAssociativityAxiomProof left middle right
    (addAssociativityAfterFirst_formula left)
    (addAssociativityAfterSecond_formula left middle)
    (addAssociativityFinal_formula left middle right)

theorem addAssociativityAxiomProof_payloadLength_le :
    addAssociativityAxiomProof.payloadLength <=
      32 + 10 * axiomSyntaxBudget .addAssoc := by
  calc
    addAssociativityAxiomProof.payloadLength =
        (ofAxiom .addAssoc).payloadLength := by
      change
        (cast addAssociativityAxiom_formula
          (ofAxiom .addAssoc)).payloadLength = _
      exact cast_payloadLength _ _
    _ <= _ := ofAxiom_payloadLength_le .addAssoc

theorem proveAddAssociativity_payloadLength_le
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveAddAssociativity left middle right).payloadLength <=
      addAssociativityAxiomProof.payloadLength +
        specializationCost addAssociativityOuterBody left +
        specializationCost (addAssociativityMiddleBody left) middle +
        specializationCost (addAssociativityInnerBody left middle) right :=
  specializeThriceWithCasts_payloadLength_le
    addAssociativityAxiomProof left middle right
      (addAssociativityAfterFirst_formula left)
      (addAssociativityAfterSecond_formula left middle)
      (addAssociativityFinal_formula left middle right)

/-! ## Left distributivity -/

def leftDistributivityOuterBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰ ∀⁰ (#2 * (#1 + #0) = #2 * #1 + #2 * #0)”

theorem leftDistributivityAxiom_formula :
    (Rewriting.emb PAAxiomCertificate.distr.sentence :
        LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ leftDistributivityOuterBody := by
  simp [leftDistributivityOuterBody, PAAxiomCertificate.sentence]

def leftDistributivityAxiomProof :
    CertifiedPAProof (∀⁰ leftDistributivityOuterBody) :=
  cast leftDistributivityAxiom_formula (ofAxiom .distr)

def leftDistributivityMiddleBody
    (factor : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰
    (!!(Rew.bShift (Rew.bShift factor)) * (#1 + #0) =
      !!(Rew.bShift (Rew.bShift factor)) * #1 +
        !!(Rew.bShift (Rew.bShift factor)) * #0)”

theorem leftDistributivityAfterFirst_formula
    (factor : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    leftDistributivityOuterBody/[factor] =
      ∀⁰ leftDistributivityMiddleBody factor := by
  simp [leftDistributivityOuterBody, leftDistributivityMiddleBody,
    substQQ_bvarOne, substQQ_bvarTwo]

def leftDistributivityInnerBody
    (factor left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!!(Rew.bShift factor) * (!!(Rew.bShift left) + #0) =
    !!(Rew.bShift factor) * !!(Rew.bShift left) +
      !!(Rew.bShift factor) * #0”

theorem leftDistributivityAfterSecond_formula
    (factor left : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (leftDistributivityMiddleBody factor)/[left] =
      ∀⁰ leftDistributivityInnerBody factor left := by
  simp [leftDistributivityMiddleBody, leftDistributivityInnerBody,
    substQ_bvarOne]

theorem leftDistributivityFinal_formula
    (factor left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (leftDistributivityInnerBody factor left)/[right] =
      (“!!factor * (!!left + !!right) =
        !!factor * !!left + !!factor * !!right” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [leftDistributivityInnerBody]

def proveLeftDistributivity
    (factor left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!factor * (!!left + !!right) =
        !!factor * !!left + !!factor * !!right” :
        LO.FirstOrder.ArithmeticProposition) :=
  specializeThriceWithCasts leftDistributivityAxiomProof factor left right
    (leftDistributivityAfterFirst_formula factor)
    (leftDistributivityAfterSecond_formula factor left)
    (leftDistributivityFinal_formula factor left right)

theorem leftDistributivityAxiomProof_payloadLength_le :
    leftDistributivityAxiomProof.payloadLength <=
      32 + 10 * axiomSyntaxBudget .distr := by
  calc
    leftDistributivityAxiomProof.payloadLength =
        (ofAxiom .distr).payloadLength := by
      change
        (cast leftDistributivityAxiom_formula
          (ofAxiom .distr)).payloadLength = _
      exact cast_payloadLength _ _
    _ <= _ := ofAxiom_payloadLength_le .distr

theorem proveLeftDistributivity_payloadLength_le
    (factor left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveLeftDistributivity factor left right).payloadLength <=
      leftDistributivityAxiomProof.payloadLength +
        specializationCost leftDistributivityOuterBody factor +
        specializationCost (leftDistributivityMiddleBody factor) left +
        specializationCost (leftDistributivityInnerBody factor left) right :=
  specializeThriceWithCasts_payloadLength_le
    leftDistributivityAxiomProof factor left right
      (leftDistributivityAfterFirst_formula factor)
      (leftDistributivityAfterSecond_formula factor left)
      (leftDistributivityFinal_formula factor left right)

/-! ## Derived algebraic rewrites used by the bit recursion -/

def paZeroTerm : LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  arithmeticZeroTerm

def paOneTerm : LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  arithmeticOneTerm

def paAddTerm
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  ‘!!left + !!right’

def paMulTerm
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  ‘!!left * !!right’

theorem addEqualityAsTerm_formula
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (“!!leftFirst + !!leftSecond = !!rightFirst + !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!(paAddTerm leftFirst leftSecond) =
        !!(paAddTerm rightFirst rightSecond)” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [paAddTerm]

theorem addLeftAsTerm_formula
    (left right target : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (“!!left + !!right = !!target” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!(paAddTerm left right) = !!target” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [paAddTerm]

theorem mulEqualityAsTerm_formula
    (leftFirst leftSecond rightFirst rightSecond :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (“!!leftFirst * !!leftSecond = !!rightFirst * !!rightSecond” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!(paMulTerm leftFirst leftSecond) =
        !!(paMulTerm rightFirst rightSecond)” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [paMulTerm]

theorem leftDistributivityReverseAsTerms_formula
    (factor left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (“!!factor * !!left + !!factor * !!right =
      !!factor * (!!left + !!right)” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!(paAddTerm (paMulTerm factor left) (paMulTerm factor right)) =
        !!(paMulTerm factor (paAddTerm left right))” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [paAddTerm, paMulTerm]

theorem addZeroAtPaZero_formula
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    addZeroBody/[term] =
      (“!!(paAddTerm term paZeroTerm) = !!term” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [addZeroBody, paAddTerm, paZeroTerm, arithmeticZeroTerm,
    Semiterm.Operator.operator]
  rw [← Rew.comp_app, Rew.subst_comp_subst]
  congr 2
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
      cases i using Fin.cases with
      | zero =>
          change
            (Rew.subst ![term])
              ((Rew.subst ![])
                (Rew.emb
                  (LO.FirstOrder.Semiterm.func Language.Zero.zero ![]))) =
              LO.FirstOrder.Semiterm.func Language.Zero.zero ![]
          simp
      | succ i => exact Fin.elim0 i

def proveAddZeroAtPaZero
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!(paAddTerm term paZeroTerm) = !!term” :
        LO.FirstOrder.ArithmeticProposition) :=
  cast (addZeroAtPaZero_formula term) (proveAddZero term)

theorem proveAddZeroAtPaZero_payloadLength_le
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveAddZeroAtPaZero term).payloadLength <=
      addZeroAxiomProof.payloadLength + 192 +
        2048 * specializationScale addZeroBody term *
          specializationScale addZeroBody term *
          specializationScale addZeroBody term := by
  calc
    (proveAddZeroAtPaZero term).payloadLength =
        (proveAddZero term).payloadLength := by
      change
        (cast (addZeroAtPaZero_formula term)
          (proveAddZero term)).payloadLength = _
      exact cast_payloadLength _ _
    _ <= _ := proveAddZero_payloadLength_le term

theorem mulZeroAtPaZero_formula
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    mulZeroBody/[term] =
      (“!!(paMulTerm term paZeroTerm) = !!paZeroTerm” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [mulZeroBody, paMulTerm, paZeroTerm, arithmeticZeroTerm,
    Semiterm.Operator.operator]
  constructor
  · rw [← Rew.comp_app, Rew.subst_comp_subst]
    congr 2
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ i =>
        cases i using Fin.cases with
        | zero =>
            change
              (Rew.subst ![term])
                ((Rew.subst ![])
                  (Rew.emb
                    (LO.FirstOrder.Semiterm.func Language.Zero.zero ![]))) =
                LO.FirstOrder.Semiterm.func Language.Zero.zero ![]
            simp
        | succ i => exact Fin.elim0 i
  · change
      (Rew.subst ![term])
          ((Rew.subst ![])
            (Rew.emb
              (LO.FirstOrder.Semiterm.func Language.Zero.zero ![]))) =
        LO.FirstOrder.Semiterm.func Language.Zero.zero ![]
    simp

def proveMulZeroAtPaZero
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!(paMulTerm term paZeroTerm) = !!paZeroTerm” :
        LO.FirstOrder.ArithmeticProposition) :=
  cast (mulZeroAtPaZero_formula term) (proveMulZero term)

theorem mulOneAtPaOne_formula
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    mulOneBody/[term] =
      (“!!(paMulTerm term paOneTerm) = !!term” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [mulOneBody, paMulTerm, paOneTerm, arithmeticOneTerm,
    Semiterm.Operator.operator]
  rw [← Rew.comp_app, Rew.subst_comp_subst]
  congr 2
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
      cases i using Fin.cases with
      | zero =>
          change
            (Rew.subst ![term])
              ((Rew.subst ![])
                (Rew.emb
                  (LO.FirstOrder.Semiterm.func Language.One.one ![]))) =
              LO.FirstOrder.Semiterm.func Language.One.one ![]
          simp
      | succ i => exact Fin.elim0 i

def proveMulOneAtPaOne
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!(paMulTerm term paOneTerm) = !!term” :
        LO.FirstOrder.ArithmeticProposition) :=
  cast (mulOneAtPaOne_formula term) (proveMulOne term)

theorem equalityReflexivityAtTerm_formula
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    equalityReflexivityBody/[term] =
      (“!!term = !!term” : LO.FirstOrder.ArithmeticProposition) := by
  simp [equalityReflexivityBody]

def proveEqualityReflexivityAtTerm
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!term = !!term” : LO.FirstOrder.ArithmeticProposition) :=
  cast (equalityReflexivityAtTerm_formula term)
    (proveEqualityReflexivity term)

abbrev shortBinaryNumeralTerm :=
  FoundationCompactBinaryNumeralTerm.binaryNumeralTerm

theorem paAddOneOne_eq_arithmeticTwoTerm :
    paAddTerm paOneTerm paOneTerm = arithmeticTwoTerm := by
  simp [paAddTerm, paOneTerm, arithmeticOneTerm, arithmeticTwoTerm,
    Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Matrix.fun_eq_vec_two]

theorem paMulTwo_eq_binaryNumeralDoubleTerm
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    paMulTerm arithmeticTwoTerm term = binaryNumeralDoubleTerm term := by
  simp [paMulTerm, binaryNumeralDoubleTerm,
    Semiterm.Operator.operator, Semiterm.Operator.Mul.term_eq,
    Matrix.fun_eq_vec_two]

def binaryOneAlgebraTerm : LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  paAddTerm (paMulTerm arithmeticTwoTerm paZeroTerm) paOneTerm

theorem binaryOneAlgebraTerm_eq_bitTerm :
    binaryOneAlgebraTerm = binaryNumeralBitTerm true paZeroTerm := by
  simp [binaryOneAlgebraTerm, binaryNumeralBitTerm,
    paMulTwo_eq_binaryNumeralDoubleTerm, paAddTerm, paOneTerm,
    arithmeticOneTerm, Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Matrix.fun_eq_vec_two]

def proveZeroAdd
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!paZeroTerm + !!term = !!term” :
        LO.FirstOrder.ArithmeticProposition) :=
  proveEqualityTransitivity
    (paAddTerm paZeroTerm term)
    (paAddTerm term paZeroTerm)
    term
    (proveAddCommutativity paZeroTerm term)
    (proveAddZeroAtPaZero term)

def proveAddAssociativityReverse
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!left + (!!middle + !!right) =
        (!!left + !!middle) + !!right” :
        LO.FirstOrder.ArithmeticProposition) :=
  proveEqualitySymmetry
    (paAddTerm (paAddTerm left middle) right)
    (paAddTerm left (paAddTerm middle right))
    (proveAddAssociativity left middle right)

def proveLeftDistributivityReverse
    (factor left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!factor * !!left + !!factor * !!right =
        !!factor * (!!left + !!right)” :
        LO.FirstOrder.ArithmeticProposition) :=
  proveEqualitySymmetry
    (paMulTerm factor (paAddTerm left right))
    (paAddTerm (paMulTerm factor left) (paMulTerm factor right))
    (proveLeftDistributivity factor left right)

def proveDoubleSum
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!arithmeticTwoTerm * !!left + !!arithmeticTwoTerm * !!right =
        !!arithmeticTwoTerm * (!!left + !!right)” :
        LO.FirstOrder.ArithmeticProposition) :=
  proveLeftDistributivityReverse arithmeticTwoTerm left right

theorem proveZeroAdd_payloadLength_le
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveZeroAdd term).payloadLength <=
      (equalityTransitivityImplication
        (paAddTerm paZeroTerm term)
        (paAddTerm term paZeroTerm) term).payloadLength +
      (proveAddCommutativity paZeroTerm term).payloadLength +
      (proveAddZeroAtPaZero term).payloadLength + 480 +
      34 * equalityTransitivityFirstMPSyntaxBudget
        (paAddTerm paZeroTerm term) (paAddTerm term paZeroTerm) term +
      34 * equalityTransitivitySecondMPSyntaxBudget
        (paAddTerm paZeroTerm term) (paAddTerm term paZeroTerm) term :=
  proveEqualityTransitivity_payloadLength_le
    (paAddTerm paZeroTerm term) (paAddTerm term paZeroTerm) term
      (proveAddCommutativity paZeroTerm term) (proveAddZeroAtPaZero term)

theorem proveAddAssociativityReverse_payloadLength_le
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveAddAssociativityReverse left middle right).payloadLength <=
      (equalitySymmetryImplication
        (paAddTerm (paAddTerm left middle) right)
        (paAddTerm left (paAddTerm middle right))).payloadLength +
      (proveAddAssociativity left middle right).payloadLength + 240 +
      34 * modusPonensSyntaxBudget
        (“(!!left + !!middle) + !!right =
          !!left + (!!middle + !!right)” :
          LO.FirstOrder.ArithmeticProposition)
        (“!!left + (!!middle + !!right) =
          (!!left + !!middle) + !!right” :
          LO.FirstOrder.ArithmeticProposition) :=
  proveEqualitySymmetry_payloadLength_le
    (paAddTerm (paAddTerm left middle) right)
    (paAddTerm left (paAddTerm middle right))
    (proveAddAssociativity left middle right)

theorem proveLeftDistributivityReverse_payloadLength_le
    (factor left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (proveLeftDistributivityReverse factor left right).payloadLength <=
      (equalitySymmetryImplication
        (paMulTerm factor (paAddTerm left right))
        (paAddTerm (paMulTerm factor left) (paMulTerm factor right))).payloadLength +
      (proveLeftDistributivity factor left right).payloadLength + 240 +
      34 * modusPonensSyntaxBudget
        (“!!factor * (!!left + !!right) =
          !!factor * !!left + !!factor * !!right” :
          LO.FirstOrder.ArithmeticProposition)
        (“!!factor * !!left + !!factor * !!right =
          !!factor * (!!left + !!right)” :
          LO.FirstOrder.ArithmeticProposition) :=
  proveEqualitySymmetry_payloadLength_le
    (paMulTerm factor (paAddTerm left right))
    (paAddTerm (paMulTerm factor left) (paMulTerm factor right))
    (proveLeftDistributivity factor left right)

/-! ## The genuine `bn(0) + 1 = bn(1)` carry base case -/

def proveBinaryOneAlgebraEqualsOne :
    CertifiedPAProof
      (“!!binaryOneAlgebraTerm = !!paOneTerm” :
        LO.FirstOrder.ArithmeticProposition) :=
  let doubleZero := paMulTerm arithmeticTwoTerm paZeroTerm
  let zeroPlusOne := paAddTerm paZeroTerm paOneTerm
  let collapseDouble : CertifiedPAProof
      (“!!binaryOneAlgebraTerm = !!zeroPlusOne” :
        LO.FirstOrder.ArithmeticProposition) := by
    let raw := proveAddCongruence doubleZero paOneTerm paZeroTerm paOneTerm
        (proveMulZeroAtPaZero arithmeticTwoTerm)
        (proveEqualityReflexivityAtTerm paOneTerm)
    have hformula := addEqualityAsTerm_formula doubleZero paOneTerm
      paZeroTerm paOneTerm
    simpa [binaryOneAlgebraTerm, doubleZero, zeroPlusOne] using
      (cast hformula raw)
  let collapseZero : CertifiedPAProof
      (“!!zeroPlusOne = !!paOneTerm” :
        LO.FirstOrder.ArithmeticProposition) := by
    let raw := proveZeroAdd paOneTerm
    have hformula := addLeftAsTerm_formula paZeroTerm paOneTerm paOneTerm
    simpa [zeroPlusOne] using (cast hformula raw)
  proveEqualityTransitivity binaryOneAlgebraTerm zeroPlusOne paOneTerm
    collapseDouble collapseZero

def proveOneEqualsBinaryOneAlgebra :
    CertifiedPAProof
      (“!!paOneTerm = !!binaryOneAlgebraTerm” :
        LO.FirstOrder.ArithmeticProposition) :=
  proveEqualitySymmetry binaryOneAlgebraTerm paOneTerm
    proveBinaryOneAlgebraEqualsOne

theorem binaryNumeralTerm_one_formula :
    shortBinaryNumeralTerm 1 = binaryOneAlgebraTerm := by
  change
    FoundationCompactBinaryNumeralTerm.binaryNumeralTerm 1 =
      binaryOneAlgebraTerm
  have hone := FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_bit
    true 0 (by simp)
  rw [show 1 = Nat.bit true 0 by simp [Nat.bit_val], hone,
    FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero]
  exact binaryOneAlgebraTerm_eq_bitTerm.symm

theorem binaryNumeralBitTerm_false_eq_paMul
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryNumeralBitTerm false term =
      paMulTerm arithmeticTwoTerm term := by
  simp [binaryNumeralBitTerm,
    paMulTwo_eq_binaryNumeralDoubleTerm]

theorem binaryNumeralBitTerm_true_eq_paAdd
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryNumeralBitTerm true term =
      paAddTerm (paMulTerm arithmeticTwoTerm term) paOneTerm := by
  simp [binaryNumeralBitTerm, paAddTerm, paOneTerm, arithmeticOneTerm,
    paMulTwo_eq_binaryNumeralDoubleTerm, Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Matrix.fun_eq_vec_two]

theorem shortBinaryNumeralTerm_bit_false
    (high : Nat) (hnonzero : high ≠ 0) :
    shortBinaryNumeralTerm (Nat.bit false high) =
      paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm high) := by
  have hcanonical : high = 0 → false = true := by
    intro hp
    exact (hnonzero hp).elim
  rw [show shortBinaryNumeralTerm (Nat.bit false high) =
      binaryNumeralBitTerm false (shortBinaryNumeralTerm high) from
    FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_bit
      false high hcanonical]
  exact binaryNumeralBitTerm_false_eq_paMul _

theorem shortBinaryNumeralTerm_bit_true
    (high : Nat) :
    shortBinaryNumeralTerm (Nat.bit true high) =
      paAddTerm (paMulTerm arithmeticTwoTerm
        (shortBinaryNumeralTerm high)) paOneTerm := by
  rw [show shortBinaryNumeralTerm (Nat.bit true high) =
      binaryNumeralBitTerm true (shortBinaryNumeralTerm high) from
    FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_bit
      true high (by simp)]
  exact binaryNumeralBitTerm_true_eq_paAdd _

theorem nat_bit_false_add_one
    (high : Nat) :
    Nat.bit false high + 1 = Nat.bit true high := by
  simp [Nat.bit_val]

def binaryNumeralIncrementEvenTerm (high : Nat) :
    LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  paAddTerm
    (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm high))
    paOneTerm

theorem binaryNumeralIncrementEven_formula
    (high : Nat) (hnonzero : high ≠ 0) :
    (“!!(binaryNumeralIncrementEvenTerm high) =
      !!(binaryNumeralIncrementEvenTerm high)” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!(paAddTerm (shortBinaryNumeralTerm (Nat.bit false high))
          paOneTerm) =
        !!(shortBinaryNumeralTerm (Nat.bit false high + 1))” :
        LO.FirstOrder.ArithmeticProposition) := by
  rw [shortBinaryNumeralTerm_bit_false high hnonzero,
    nat_bit_false_add_one,
    shortBinaryNumeralTerm_bit_true]
  rfl

def proveBinaryNumeralIncrementEven
    (high : Nat) (hnonzero : high ≠ 0) :
    CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm (Nat.bit false high))
          paOneTerm) =
        !!(shortBinaryNumeralTerm (Nat.bit false high + 1))” :
        LO.FirstOrder.ArithmeticProposition) :=
  cast (binaryNumeralIncrementEven_formula high hnonzero)
    (proveEqualityReflexivityAtTerm
      (binaryNumeralIncrementEvenTerm high))

theorem nat_bit_true_add_one
    (high : Nat) :
    Nat.bit true high + 1 = Nat.bit false (high + 1) := by
  simp [Nat.bit_val]
  omega

def binaryNumeralIncrementOddSource (high : Nat) :
    LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  paAddTerm
    (paAddTerm
      (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm high))
      paOneTerm)
    paOneTerm

def binaryNumeralIncrementOddAssocMiddle (high : Nat) :
    LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  paAddTerm
    (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm high))
    (paAddTerm paOneTerm paOneTerm)

def binaryNumeralIncrementOddMulMiddle (high : Nat) :
    LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  paAddTerm
    (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm high))
    (paMulTerm arithmeticTwoTerm paOneTerm)

def binaryNumeralIncrementOddFactored (high : Nat) :
    LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  paMulTerm arithmeticTwoTerm
    (paAddTerm (shortBinaryNumeralTerm high) paOneTerm)

def binaryNumeralIncrementOddResult (high : Nat) :
    LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm (high + 1))

theorem onePairToTwoMulOne_formula :
    (“!!arithmeticTwoTerm =
      !!(paMulTerm arithmeticTwoTerm paOneTerm)” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!(paAddTerm paOneTerm paOneTerm) =
        !!(paMulTerm arithmeticTwoTerm paOneTerm)” :
        LO.FirstOrder.ArithmeticProposition) := by
  rw [paAddOneOne_eq_arithmeticTwoTerm]

def proveOnePairToTwoMulOne :
    CertifiedPAProof
      (“!!(paAddTerm paOneTerm paOneTerm) =
        !!(paMulTerm arithmeticTwoTerm paOneTerm)” :
        LO.FirstOrder.ArithmeticProposition) :=
  let reverseMulOne := proveEqualitySymmetry
    (paMulTerm arithmeticTwoTerm paOneTerm) arithmeticTwoTerm
    (proveMulOneAtPaOne arithmeticTwoTerm)
  cast onePairToTwoMulOne_formula reverseMulOne

theorem binaryNumeralIncrementOddAssociation_formula (high : Nat) :
    (“(!!(paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm high)) +
          !!paOneTerm) + !!paOneTerm =
        !!(paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm high)) +
          (!!paOneTerm + !!paOneTerm)” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!(binaryNumeralIncrementOddSource high) =
        !!(binaryNumeralIncrementOddAssocMiddle high)” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [binaryNumeralIncrementOddSource,
    binaryNumeralIncrementOddAssocMiddle, paAddTerm,
    Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Matrix.fun_eq_vec_two]

def proveBinaryNumeralIncrementOddAssociation (high : Nat) :
    CertifiedPAProof
      (“!!(binaryNumeralIncrementOddSource high) =
        !!(binaryNumeralIncrementOddAssocMiddle high)” :
        LO.FirstOrder.ArithmeticProposition) :=
  cast (binaryNumeralIncrementOddAssociation_formula high)
    (proveAddAssociativity
      (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm high))
      paOneTerm paOneTerm)

theorem binaryNumeralIncrementOddReplacePair_formula (high : Nat) :
    (“!!(paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm high)) +
          !!(paAddTerm paOneTerm paOneTerm) =
        !!(paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm high)) +
          !!(paMulTerm arithmeticTwoTerm paOneTerm)” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!(binaryNumeralIncrementOddAssocMiddle high) =
        !!(binaryNumeralIncrementOddMulMiddle high)” :
        LO.FirstOrder.ArithmeticProposition) := by
  let highTerm := shortBinaryNumeralTerm high
  let doubleHigh := paMulTerm arithmeticTwoTerm highTerm
  have hformula := addEqualityAsTerm_formula
    doubleHigh (paAddTerm paOneTerm paOneTerm)
    doubleHigh (paMulTerm arithmeticTwoTerm paOneTerm)
  simpa [binaryNumeralIncrementOddAssocMiddle,
    binaryNumeralIncrementOddMulMiddle, highTerm, doubleHigh] using hformula

def proveBinaryNumeralIncrementOddReplacePair (high : Nat) :
    CertifiedPAProof
      (“!!(binaryNumeralIncrementOddAssocMiddle high) =
        !!(binaryNumeralIncrementOddMulMiddle high)” :
        LO.FirstOrder.ArithmeticProposition) :=
  let doubleHigh :=
    paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm high)
  cast (binaryNumeralIncrementOddReplacePair_formula high)
    (proveAddCongruence
      doubleHigh (paAddTerm paOneTerm paOneTerm)
      doubleHigh (paMulTerm arithmeticTwoTerm paOneTerm)
      (proveEqualityReflexivityAtTerm doubleHigh)
      proveOnePairToTwoMulOne)

theorem binaryNumeralIncrementOddFactor_formula (high : Nat) :
    (“!!arithmeticTwoTerm * !!(shortBinaryNumeralTerm high) +
          !!arithmeticTwoTerm * !!paOneTerm =
        !!arithmeticTwoTerm *
          (!!(shortBinaryNumeralTerm high) + !!paOneTerm)” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!(binaryNumeralIncrementOddMulMiddle high) =
        !!(binaryNumeralIncrementOddFactored high)” :
        LO.FirstOrder.ArithmeticProposition) := by
  let highTerm := shortBinaryNumeralTerm high
  let doubleHigh := paMulTerm arithmeticTwoTerm highTerm
  have hformula := leftDistributivityReverseAsTerms_formula
    arithmeticTwoTerm highTerm paOneTerm
  simpa [binaryNumeralIncrementOddMulMiddle,
    binaryNumeralIncrementOddFactored, highTerm, doubleHigh] using hformula

def proveBinaryNumeralIncrementOddFactor (high : Nat) :
    CertifiedPAProof
      (“!!(binaryNumeralIncrementOddMulMiddle high) =
        !!(binaryNumeralIncrementOddFactored high)” :
        LO.FirstOrder.ArithmeticProposition) :=
  cast (binaryNumeralIncrementOddFactor_formula high)
    (proveLeftDistributivityReverse arithmeticTwoTerm
      (shortBinaryNumeralTerm high) paOneTerm)

theorem binaryNumeralIncrementOddRecurse_formula (high : Nat) :
    (“!!arithmeticTwoTerm *
          !!(paAddTerm (shortBinaryNumeralTerm high) paOneTerm) =
        !!arithmeticTwoTerm * !!(shortBinaryNumeralTerm (high + 1))” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!(binaryNumeralIncrementOddFactored high) =
        !!(binaryNumeralIncrementOddResult high)” :
        LO.FirstOrder.ArithmeticProposition) := by
  let highTerm := shortBinaryNumeralTerm high
  have hformula := mulEqualityAsTerm_formula
    arithmeticTwoTerm (paAddTerm highTerm paOneTerm)
    arithmeticTwoTerm (shortBinaryNumeralTerm (high + 1))
  simpa [binaryNumeralIncrementOddFactored,
    binaryNumeralIncrementOddResult, highTerm] using hformula

def proveBinaryNumeralIncrementOddRecurse
    (high : Nat)
    (incrementHigh : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm high) paOneTerm) =
        !!(shortBinaryNumeralTerm (high + 1))” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(binaryNumeralIncrementOddFactored high) =
        !!(binaryNumeralIncrementOddResult high)” :
        LO.FirstOrder.ArithmeticProposition) :=
  cast (binaryNumeralIncrementOddRecurse_formula high)
    (proveMulCongruence
      arithmeticTwoTerm
      (paAddTerm (shortBinaryNumeralTerm high) paOneTerm)
      arithmeticTwoTerm (shortBinaryNumeralTerm (high + 1))
      (proveEqualityReflexivityAtTerm arithmeticTwoTerm)
      incrementHigh)

def proveBinaryNumeralIncrementOddAlgebra
    (high : Nat)
    (incrementHigh : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm high) paOneTerm) =
        !!(shortBinaryNumeralTerm (high + 1))” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(binaryNumeralIncrementOddSource high) =
        !!(binaryNumeralIncrementOddResult high)” :
        LO.FirstOrder.ArithmeticProposition) :=
  let firstHalf := proveEqualityTransitivity
    (binaryNumeralIncrementOddSource high)
    (binaryNumeralIncrementOddAssocMiddle high)
    (binaryNumeralIncrementOddMulMiddle high)
    (proveBinaryNumeralIncrementOddAssociation high)
    (proveBinaryNumeralIncrementOddReplacePair high)
  let throughFactor := proveEqualityTransitivity
    (binaryNumeralIncrementOddSource high)
    (binaryNumeralIncrementOddMulMiddle high)
    (binaryNumeralIncrementOddFactored high)
    firstHalf (proveBinaryNumeralIncrementOddFactor high)
  proveEqualityTransitivity
    (binaryNumeralIncrementOddSource high)
    (binaryNumeralIncrementOddFactored high)
    (binaryNumeralIncrementOddResult high)
    throughFactor (proveBinaryNumeralIncrementOddRecurse high incrementHigh)

theorem binaryNumeralIncrementOdd_formula
    (high : Nat) :
    (“!!(binaryNumeralIncrementOddSource high) =
      !!(binaryNumeralIncrementOddResult high)” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!(paAddTerm (shortBinaryNumeralTerm (Nat.bit true high))
          paOneTerm) =
        !!(shortBinaryNumeralTerm (Nat.bit true high + 1))” :
        LO.FirstOrder.ArithmeticProposition) := by
  rw [shortBinaryNumeralTerm_bit_true,
    nat_bit_true_add_one,
    shortBinaryNumeralTerm_bit_false (high + 1) (by omega)]
  rfl

def proveBinaryNumeralIncrementOdd
    (high : Nat)
    (incrementHigh : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm high) paOneTerm) =
        !!(shortBinaryNumeralTerm (high + 1))” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm (Nat.bit true high))
          paOneTerm) =
        !!(shortBinaryNumeralTerm (Nat.bit true high + 1))” :
        LO.FirstOrder.ArithmeticProposition) :=
  cast (binaryNumeralIncrementOdd_formula high)
    (proveBinaryNumeralIncrementOddAlgebra high incrementHigh)

def proveBinaryNumeralIncrementZero :
    CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm 0) paOneTerm) =
        !!(shortBinaryNumeralTerm 1)” :
        LO.FirstOrder.ArithmeticProposition) := by
  let zeroPlusOne := paAddTerm paZeroTerm paOneTerm
  let algebraProof : CertifiedPAProof
      (“!!zeroPlusOne = !!binaryOneAlgebraTerm” :
        LO.FirstOrder.ArithmeticProposition) :=
    proveEqualityTransitivity zeroPlusOne paOneTerm binaryOneAlgebraTerm
      (proveZeroAdd paOneTerm) proveOneEqualsBinaryOneAlgebra
  have hformula :
      (“!!zeroPlusOne = !!binaryOneAlgebraTerm” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(paAddTerm (shortBinaryNumeralTerm 0) paOneTerm) =
          !!(shortBinaryNumeralTerm 1)” :
          LO.FirstOrder.ArithmeticProposition) := by
    simp only [shortBinaryNumeralTerm]
    dsimp [zeroPlusOne]
    rw [FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero,
      show FoundationCompactBinaryNumeralTerm.binaryNumeralTerm 1 =
        binaryOneAlgebraTerm from binaryNumeralTerm_one_formula]
    rfl
  exact cast hformula algebraProof

/-- A proof-producing binary carry compiler.  Its recursion follows the actual
binary representation, so the number of recursive calls is `Nat.size value`. -/
noncomputable def proveBinaryNumeralIncrement :
    (value : Nat) →
    CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm value) paOneTerm) =
        !!(shortBinaryNumeralTerm (value + 1))” :
        LO.FirstOrder.ArithmeticProposition) :=
  Nat.binaryRec'
    proveBinaryNumeralIncrementZero
    (fun bit high hcanonical incrementHigh => by
      cases bit with
      | false =>
          have hnonzero : high ≠ 0 := by
            intro hz
            have himpossible := hcanonical hz
            simp at himpossible
          exact proveBinaryNumeralIncrementEven high hnonzero
      | true =>
          exact proveBinaryNumeralIncrementOdd high incrementHigh)

@[simp] theorem proveBinaryNumeralIncrement_zero :
    proveBinaryNumeralIncrement 0 = proveBinaryNumeralIncrementZero := by
  simp [proveBinaryNumeralIncrement]

theorem proveBinaryNumeralIncrement_bit_false
    (high : Nat) (hnonzero : high ≠ 0) :
    proveBinaryNumeralIncrement (Nat.bit false high) =
      proveBinaryNumeralIncrementEven high hnonzero := by
  have hcanonical : high = 0 → false = true := by
    intro hz
    exact (hnonzero hz).elim
  simpa [proveBinaryNumeralIncrement, hnonzero] using
    (Nat.binaryRec'_eq
      (motive := fun value => CertifiedPAProof
        (“!!(paAddTerm (shortBinaryNumeralTerm value) paOneTerm) =
          !!(shortBinaryNumeralTerm (value + 1))” :
          LO.FirstOrder.ArithmeticProposition))
      false high hcanonical)

theorem proveBinaryNumeralIncrement_bit_true (high : Nat) :
    proveBinaryNumeralIncrement (Nat.bit true high) =
      proveBinaryNumeralIncrementOdd high
        (proveBinaryNumeralIncrement high) := by
  simpa [proveBinaryNumeralIncrement] using
    (Nat.binaryRec'_eq
      (motive := fun value => CertifiedPAProof
        (“!!(paAddTerm (shortBinaryNumeralTerm value) paOneTerm) =
          !!(shortBinaryNumeralTerm (value + 1))” :
          LO.FirstOrder.ArithmeticProposition))
      true high (by simp))

theorem proveBinaryNumeralIncrement_verifier_eq_true
    (value : Nat) :
    listedCompactCertifiedPAProofVerifier
      (proveBinaryNumeralIncrement value).code
      (compactFormulaCode
        (“!!(paAddTerm (shortBinaryNumeralTerm value) paOneTerm) =
          !!(shortBinaryNumeralTerm (value + 1))” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  (proveBinaryNumeralIncrement value).verifier_eq_true

/-! ## Binary addition: bases and no-carry bit branches -/

def paBinaryBitTerm
    (bit : Bool) (highTerm : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  if bit then
    paAddTerm (paMulTerm arithmeticTwoTerm highTerm) paOneTerm
  else
    paMulTerm arithmeticTwoTerm highTerm

theorem shortBinaryNumeralTerm_bit_as_pa
    (bit : Bool) (high : Nat)
    (hcanonical : high = 0 → bit = true) :
    shortBinaryNumeralTerm (Nat.bit bit high) =
      paBinaryBitTerm bit (shortBinaryNumeralTerm high) := by
  cases bit with
  | false =>
      have hnonzero : high ≠ 0 := by
        intro hz
        have himpossible := hcanonical hz
        simp at himpossible
      change shortBinaryNumeralTerm (Nat.bit false high) =
        paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm high)
      exact shortBinaryNumeralTerm_bit_false high hnonzero
  | true =>
      change shortBinaryNumeralTerm (Nat.bit true high) =
        paAddTerm (paMulTerm arithmeticTwoTerm
          (shortBinaryNumeralTerm high)) paOneTerm
      exact shortBinaryNumeralTerm_bit_true high

def proveBinaryNumeralAdditionZeroLeft
    (right : Nat) :
    CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm 0)
          (shortBinaryNumeralTerm right)) =
        !!(shortBinaryNumeralTerm (0 + right))” :
        LO.FirstOrder.ArithmeticProposition) := by
  let rightTerm := shortBinaryNumeralTerm right
  let raw := proveZeroAdd rightTerm
  have htermFormula := addLeftAsTerm_formula
    paZeroTerm rightTerm rightTerm
  have hformula :
      (“!!(paAddTerm paZeroTerm rightTerm) = !!rightTerm” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(paAddTerm (shortBinaryNumeralTerm 0)
            (shortBinaryNumeralTerm right)) =
          !!(shortBinaryNumeralTerm (0 + right))” :
          LO.FirstOrder.ArithmeticProposition) := by
    simp [rightTerm, paZeroTerm,
      FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero]
  exact cast hformula (cast htermFormula raw)

def proveBinaryNumeralAdditionZeroRight
    (left : Nat) :
    CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm 0)) =
        !!(shortBinaryNumeralTerm (left + 0))” :
        LO.FirstOrder.ArithmeticProposition) := by
  let leftTerm := shortBinaryNumeralTerm left
  let raw := proveAddZeroAtPaZero leftTerm
  have hformula :
      (“!!(paAddTerm leftTerm paZeroTerm) = !!leftTerm” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(paAddTerm (shortBinaryNumeralTerm left)
            (shortBinaryNumeralTerm 0)) =
          !!(shortBinaryNumeralTerm (left + 0))” :
          LO.FirstOrder.ArithmeticProposition) := by
    simp [leftTerm, paZeroTerm,
      FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero]
  exact cast hformula raw

def binaryAdditionHighSumTerm (leftHigh rightHigh : Nat) :
    LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  shortBinaryNumeralTerm (leftHigh + rightHigh)

def proveBinaryAdditionEvenEvenAlgebra
    (leftHigh rightHigh : Nat)
    (highProof : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm leftHigh)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(binaryAdditionHighSumTerm leftHigh rightHigh)” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(paAddTerm
          (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm leftHigh))
          (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm rightHigh))) =
        !!(paMulTerm arithmeticTwoTerm
          (binaryAdditionHighSumTerm leftHigh rightHigh))” :
        LO.FirstOrder.ArithmeticProposition) := by
  let leftTerm := shortBinaryNumeralTerm leftHigh
  let rightTerm := shortBinaryNumeralTerm rightHigh
  let highAdd := paAddTerm leftTerm rightTerm
  let doubledHighAdd := paMulTerm arithmeticTwoTerm highAdd
  let distributed := paAddTerm
    (paMulTerm arithmeticTwoTerm leftTerm)
    (paMulTerm arithmeticTwoTerm rightTerm)
  let distributionRaw := proveDoubleSum leftTerm rightTerm
  let distribution : CertifiedPAProof
      (“!!distributed = !!doubledHighAdd” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := leftDistributivityReverseAsTerms_formula
      arithmeticTwoTerm leftTerm rightTerm
    simpa [distributed, doubledHighAdd, highAdd] using
      (cast hformula distributionRaw)
  let recurseRaw := proveMulCongruence
    arithmeticTwoTerm highAdd arithmeticTwoTerm
    (binaryAdditionHighSumTerm leftHigh rightHigh)
    (proveEqualityReflexivityAtTerm arithmeticTwoTerm) highProof
  let recurse : CertifiedPAProof
      (“!!doubledHighAdd =
        !!(paMulTerm arithmeticTwoTerm
          (binaryAdditionHighSumTerm leftHigh rightHigh))” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := mulEqualityAsTerm_formula
      arithmeticTwoTerm highAdd arithmeticTwoTerm
      (binaryAdditionHighSumTerm leftHigh rightHigh)
    simpa [doubledHighAdd] using (cast hformula recurseRaw)
  exact proveEqualityTransitivity distributed doubledHighAdd
    (paMulTerm arithmeticTwoTerm
      (binaryAdditionHighSumTerm leftHigh rightHigh))
    distribution recurse

theorem nat_bit_false_add_bit_false
    (leftHigh rightHigh : Nat) :
    Nat.bit false leftHigh + Nat.bit false rightHigh =
      Nat.bit false (leftHigh + rightHigh) := by
  simp [Nat.bit_val, Nat.mul_add]

def proveBinaryNumeralAdditionEvenEven
    (leftHigh rightHigh : Nat)
    (hleft : leftHigh ≠ 0) (hright : rightHigh ≠ 0)
    (highProof : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm leftHigh)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(binaryAdditionHighSumTerm leftHigh rightHigh)” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(paAddTerm
          (shortBinaryNumeralTerm (Nat.bit false leftHigh))
          (shortBinaryNumeralTerm (Nat.bit false rightHigh))) =
        !!(shortBinaryNumeralTerm
          (Nat.bit false leftHigh + Nat.bit false rightHigh))” :
        LO.FirstOrder.ArithmeticProposition) := by
  let algebra := proveBinaryAdditionEvenEvenAlgebra
    leftHigh rightHigh highProof
  have hsum : leftHigh + rightHigh ≠ 0 := by omega
  have hformula :
      (“!!(paAddTerm
          (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm leftHigh))
          (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm rightHigh))) =
        !!(paMulTerm arithmeticTwoTerm
          (binaryAdditionHighSumTerm leftHigh rightHigh))” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(paAddTerm
            (shortBinaryNumeralTerm (Nat.bit false leftHigh))
            (shortBinaryNumeralTerm (Nat.bit false rightHigh))) =
          !!(shortBinaryNumeralTerm
            (Nat.bit false leftHigh + Nat.bit false rightHigh))” :
          LO.FirstOrder.ArithmeticProposition) := by
    rw [shortBinaryNumeralTerm_bit_false leftHigh hleft,
      shortBinaryNumeralTerm_bit_false rightHigh hright,
      nat_bit_false_add_bit_false,
      shortBinaryNumeralTerm_bit_false (leftHigh + rightHigh) hsum]
    rfl
  exact cast hformula algebra

def proveBinaryAdditionEvenOddAlgebra
    (leftHigh rightHigh : Nat)
    (highProof : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm leftHigh)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(binaryAdditionHighSumTerm leftHigh rightHigh)” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(paAddTerm
          (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm leftHigh))
          (paAddTerm
            (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm rightHigh))
            paOneTerm)) =
        !!(paAddTerm
          (paMulTerm arithmeticTwoTerm
            (binaryAdditionHighSumTerm leftHigh rightHigh))
          paOneTerm)” :
        LO.FirstOrder.ArithmeticProposition) := by
  let leftTerm := shortBinaryNumeralTerm leftHigh
  let rightTerm := shortBinaryNumeralTerm rightHigh
  let doubleLeft := paMulTerm arithmeticTwoTerm leftTerm
  let doubleRight := paMulTerm arithmeticTwoTerm rightTerm
  let source := paAddTerm doubleLeft (paAddTerm doubleRight paOneTerm)
  let grouped := paAddTerm (paAddTerm doubleLeft doubleRight) paOneTerm
  let highAdd := paAddTerm leftTerm rightTerm
  let doubledHighAdd := paMulTerm arithmeticTwoTerm highAdd
  let distributed := paAddTerm doubledHighAdd paOneTerm
  let result := paAddTerm
    (paMulTerm arithmeticTwoTerm
      (binaryAdditionHighSumTerm leftHigh rightHigh)) paOneTerm
  let groupingRaw := proveAddAssociativityReverse
    doubleLeft doubleRight paOneTerm
  let grouping : CertifiedPAProof
      (“!!source = !!grouped” : LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      doubleLeft (paAddTerm doubleRight paOneTerm)
      (paAddTerm doubleLeft doubleRight) paOneTerm
    simpa [source, grouped] using (cast hformula groupingRaw)
  let doubleRaw := proveDoubleSum leftTerm rightTerm
  let doubleAsTerms : CertifiedPAProof
      (“!!(paAddTerm doubleLeft doubleRight) = !!doubledHighAdd” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := leftDistributivityReverseAsTerms_formula
      arithmeticTwoTerm leftTerm rightTerm
    simpa [doubleLeft, doubleRight, doubledHighAdd, highAdd] using
      (cast hformula doubleRaw)
  let distributeRaw := proveAddCongruence
    (paAddTerm doubleLeft doubleRight) paOneTerm
    doubledHighAdd paOneTerm doubleAsTerms
    (proveEqualityReflexivityAtTerm paOneTerm)
  let distribute : CertifiedPAProof
      (“!!grouped = !!distributed” : LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      (paAddTerm doubleLeft doubleRight) paOneTerm
      doubledHighAdd paOneTerm
    simpa [grouped, distributed] using (cast hformula distributeRaw)
  let recurseMulRaw := proveMulCongruence
    arithmeticTwoTerm highAdd arithmeticTwoTerm
    (binaryAdditionHighSumTerm leftHigh rightHigh)
    (proveEqualityReflexivityAtTerm arithmeticTwoTerm) highProof
  let recurseMul : CertifiedPAProof
      (“!!doubledHighAdd =
        !!(paMulTerm arithmeticTwoTerm
          (binaryAdditionHighSumTerm leftHigh rightHigh))” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := mulEqualityAsTerm_formula
      arithmeticTwoTerm highAdd arithmeticTwoTerm
      (binaryAdditionHighSumTerm leftHigh rightHigh)
    simpa [doubledHighAdd] using (cast hformula recurseMulRaw)
  let recurseRaw := proveAddCongruence
    doubledHighAdd paOneTerm
    (paMulTerm arithmeticTwoTerm
      (binaryAdditionHighSumTerm leftHigh rightHigh)) paOneTerm
    recurseMul (proveEqualityReflexivityAtTerm paOneTerm)
  let recurse : CertifiedPAProof
      (“!!distributed = !!result” : LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      doubledHighAdd paOneTerm
      (paMulTerm arithmeticTwoTerm
        (binaryAdditionHighSumTerm leftHigh rightHigh)) paOneTerm
    simpa [distributed, result] using (cast hformula recurseRaw)
  let firstHalf := proveEqualityTransitivity source grouped distributed
    grouping distribute
  exact proveEqualityTransitivity source distributed result firstHalf recurse

theorem nat_bit_false_add_bit_true
    (leftHigh rightHigh : Nat) :
    Nat.bit false leftHigh + Nat.bit true rightHigh =
      Nat.bit true (leftHigh + rightHigh) := by
  simp [Nat.bit_val, Nat.mul_add]
  omega

def proveBinaryNumeralAdditionEvenOdd
    (leftHigh rightHigh : Nat) (hleft : leftHigh ≠ 0)
    (highProof : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm leftHigh)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(binaryAdditionHighSumTerm leftHigh rightHigh)” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(paAddTerm
          (shortBinaryNumeralTerm (Nat.bit false leftHigh))
          (shortBinaryNumeralTerm (Nat.bit true rightHigh))) =
        !!(shortBinaryNumeralTerm
          (Nat.bit false leftHigh + Nat.bit true rightHigh))” :
        LO.FirstOrder.ArithmeticProposition) := by
  let algebra := proveBinaryAdditionEvenOddAlgebra
    leftHigh rightHigh highProof
  have hformula :
      (“!!(paAddTerm
          (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm leftHigh))
          (paAddTerm
            (paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm rightHigh))
            paOneTerm)) =
        !!(paAddTerm
          (paMulTerm arithmeticTwoTerm
            (binaryAdditionHighSumTerm leftHigh rightHigh))
          paOneTerm)” : LO.FirstOrder.ArithmeticProposition) =
        (“!!(paAddTerm
            (shortBinaryNumeralTerm (Nat.bit false leftHigh))
            (shortBinaryNumeralTerm (Nat.bit true rightHigh))) =
          !!(shortBinaryNumeralTerm
            (Nat.bit false leftHigh + Nat.bit true rightHigh))” :
          LO.FirstOrder.ArithmeticProposition) := by
    rw [shortBinaryNumeralTerm_bit_false leftHigh hleft,
      shortBinaryNumeralTerm_bit_true,
      nat_bit_false_add_bit_true,
      shortBinaryNumeralTerm_bit_true]
    rfl
  exact cast hformula algebra

def proveSwappedBinaryHighAddition
    (leftHigh rightHigh : Nat)
    (highProof : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm leftHigh)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(binaryAdditionHighSumTerm leftHigh rightHigh)” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm rightHigh)
          (shortBinaryNumeralTerm leftHigh)) =
        !!(binaryAdditionHighSumTerm rightHigh leftHigh)” :
        LO.FirstOrder.ArithmeticProposition) := by
  let leftTerm := shortBinaryNumeralTerm leftHigh
  let rightTerm := shortBinaryNumeralTerm rightHigh
  let commRaw := proveAddCommutativity rightTerm leftTerm
  let comm : CertifiedPAProof
      (“!!(paAddTerm rightTerm leftTerm) =
        !!(paAddTerm leftTerm rightTerm)” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      rightTerm leftTerm leftTerm rightTerm
    exact cast hformula commRaw
  let throughOriginal := proveEqualityTransitivity
    (paAddTerm rightTerm leftTerm)
    (paAddTerm leftTerm rightTerm)
    (binaryAdditionHighSumTerm leftHigh rightHigh)
    comm highProof
  have hformula :
      (“!!(paAddTerm rightTerm leftTerm) =
        !!(binaryAdditionHighSumTerm leftHigh rightHigh)” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(paAddTerm (shortBinaryNumeralTerm rightHigh)
            (shortBinaryNumeralTerm leftHigh)) =
          !!(binaryAdditionHighSumTerm rightHigh leftHigh)” :
          LO.FirstOrder.ArithmeticProposition) := by
    simp [rightTerm, leftTerm, binaryAdditionHighSumTerm, Nat.add_comm]
  exact cast hformula throughOriginal

def proveBinaryNumeralAdditionOddEven
    (leftHigh rightHigh : Nat) (hright : rightHigh ≠ 0)
    (highProof : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm leftHigh)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(binaryAdditionHighSumTerm leftHigh rightHigh)” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(paAddTerm
          (shortBinaryNumeralTerm (Nat.bit true leftHigh))
          (shortBinaryNumeralTerm (Nat.bit false rightHigh))) =
        !!(shortBinaryNumeralTerm
          (Nat.bit true leftHigh + Nat.bit false rightHigh))” :
        LO.FirstOrder.ArithmeticProposition) := by
  let oddTerm := shortBinaryNumeralTerm (Nat.bit true leftHigh)
  let evenTerm := shortBinaryNumeralTerm (Nat.bit false rightHigh)
  let commRaw := proveAddCommutativity oddTerm evenTerm
  let comm : CertifiedPAProof
      (“!!(paAddTerm oddTerm evenTerm) =
        !!(paAddTerm evenTerm oddTerm)” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      oddTerm evenTerm evenTerm oddTerm
    exact cast hformula commRaw
  let swappedHigh := proveSwappedBinaryHighAddition
    leftHigh rightHigh highProof
  let swappedResult := proveBinaryNumeralAdditionEvenOdd
    rightHigh leftHigh hright swappedHigh
  let throughSwap := proveEqualityTransitivity
    (paAddTerm oddTerm evenTerm)
    (paAddTerm evenTerm oddTerm)
    (shortBinaryNumeralTerm
      (Nat.bit false rightHigh + Nat.bit true leftHigh))
    comm swappedResult
  have hformula :
      (“!!(paAddTerm oddTerm evenTerm) =
        !!(shortBinaryNumeralTerm
          (Nat.bit false rightHigh + Nat.bit true leftHigh))” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(paAddTerm
            (shortBinaryNumeralTerm (Nat.bit true leftHigh))
            (shortBinaryNumeralTerm (Nat.bit false rightHigh))) =
          !!(shortBinaryNumeralTerm
            (Nat.bit true leftHigh + Nat.bit false rightHigh))” :
          LO.FirstOrder.ArithmeticProposition) := by
    simp [oddTerm, evenTerm, Nat.add_comm]
  exact cast hformula throughSwap

def oddOddIntermediateValue (leftHigh rightHigh : Nat) : Nat :=
  Nat.bit true leftHigh + Nat.bit false rightHigh

theorem nat_bit_true_add_bit_true
    (leftHigh rightHigh : Nat) :
    Nat.bit true leftHigh + Nat.bit true rightHigh =
      oddOddIntermediateValue leftHigh rightHigh + 1 := by
  simp [oddOddIntermediateValue, Nat.bit_val]
  omega

def proveBinaryNumeralAdditionOddOddNonzero
    (leftHigh rightHigh : Nat) (hright : rightHigh ≠ 0)
    (highProof : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm leftHigh)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(binaryAdditionHighSumTerm leftHigh rightHigh)” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(paAddTerm
          (shortBinaryNumeralTerm (Nat.bit true leftHigh))
          (shortBinaryNumeralTerm (Nat.bit true rightHigh))) =
        !!(shortBinaryNumeralTerm
          (Nat.bit true leftHigh + Nat.bit true rightHigh))” :
        LO.FirstOrder.ArithmeticProposition) := by
  let oddLeft := shortBinaryNumeralTerm (Nat.bit true leftHigh)
  let doubleRight :=
    paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm rightHigh)
  let oddRight := paAddTerm doubleRight paOneTerm
  let source := paAddTerm oddLeft oddRight
  let grouped := paAddTerm (paAddTerm oddLeft doubleRight) paOneTerm
  let intermediate := oddOddIntermediateValue leftHigh rightHigh
  let normalizedGrouped := paAddTerm
    (shortBinaryNumeralTerm intermediate) paOneTerm
  let associationRaw := proveAddAssociativityReverse
    oddLeft doubleRight paOneTerm
  let association : CertifiedPAProof
      (“!!source = !!grouped” : LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      oddLeft (paAddTerm doubleRight paOneTerm)
      (paAddTerm oddLeft doubleRight) paOneTerm
    simpa [source, grouped, oddRight] using (cast hformula associationRaw)
  let oddEven := proveBinaryNumeralAdditionOddEven
    leftHigh rightHigh hright highProof
  let normalizeInner : CertifiedPAProof
      (“!!(paAddTerm oddLeft doubleRight) =
        !!(shortBinaryNumeralTerm intermediate)” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula :
        (“!!(paAddTerm
            (shortBinaryNumeralTerm (Nat.bit true leftHigh))
            (shortBinaryNumeralTerm (Nat.bit false rightHigh))) =
          !!(shortBinaryNumeralTerm
            (Nat.bit true leftHigh + Nat.bit false rightHigh))” :
            LO.FirstOrder.ArithmeticProposition) =
          (“!!(paAddTerm oddLeft doubleRight) =
            !!(shortBinaryNumeralTerm intermediate)” :
            LO.FirstOrder.ArithmeticProposition) := by
      rw [shortBinaryNumeralTerm_bit_false rightHigh hright]
      rfl
    exact cast hformula oddEven
  let liftRaw := proveAddCongruence
    (paAddTerm oddLeft doubleRight) paOneTerm
    (shortBinaryNumeralTerm intermediate) paOneTerm
    normalizeInner (proveEqualityReflexivityAtTerm paOneTerm)
  let lift : CertifiedPAProof
      (“!!grouped = !!normalizedGrouped” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      (paAddTerm oddLeft doubleRight) paOneTerm
      (shortBinaryNumeralTerm intermediate) paOneTerm
    simpa [grouped, normalizedGrouped] using (cast hformula liftRaw)
  let increment := proveBinaryNumeralIncrement intermediate
  let throughGrouping := proveEqualityTransitivity
    source grouped normalizedGrouped association lift
  let throughIncrement := proveEqualityTransitivity
    source normalizedGrouped (shortBinaryNumeralTerm (intermediate + 1))
    throughGrouping increment
  have hformula :
      (“!!source = !!(shortBinaryNumeralTerm (intermediate + 1))” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(paAddTerm
            (shortBinaryNumeralTerm (Nat.bit true leftHigh))
            (shortBinaryNumeralTerm (Nat.bit true rightHigh))) =
          !!(shortBinaryNumeralTerm
            (Nat.bit true leftHigh + Nat.bit true rightHigh))” :
          LO.FirstOrder.ArithmeticProposition) := by
    dsimp [source, oddRight, doubleRight, oddLeft, intermediate]
    have hrightTerm :
        shortBinaryNumeralTerm (2 * rightHigh + 1) =
          paAddTerm
            (paMulTerm arithmeticTwoTerm
              (shortBinaryNumeralTerm rightHigh)) paOneTerm := by
      simpa [Nat.bit_val] using shortBinaryNumeralTerm_bit_true rightHigh
    have hsum :
        (2 * leftHigh + 1) + (2 * rightHigh + 1) =
          oddOddIntermediateValue leftHigh rightHigh + 1 := by
      simpa [Nat.bit_val] using
        nat_bit_true_add_bit_true leftHigh rightHigh
    rw [hrightTerm, hsum]
  exact cast hformula throughIncrement

def proveBinaryNumeralAdditionOddOddZero
    (leftHigh : Nat) :
    CertifiedPAProof
      (“!!(paAddTerm
          (shortBinaryNumeralTerm (Nat.bit true leftHigh))
          (shortBinaryNumeralTerm (Nat.bit true 0))) =
        !!(shortBinaryNumeralTerm
          (Nat.bit true leftHigh + Nat.bit true 0))” :
        LO.FirstOrder.ArithmeticProposition) := by
  let oddLeft := shortBinaryNumeralTerm (Nat.bit true leftHigh)
  let doubleZero :=
    paMulTerm arithmeticTwoTerm (shortBinaryNumeralTerm 0)
  let oddRight := paAddTerm doubleZero paOneTerm
  let source := paAddTerm oddLeft oddRight
  let grouped := paAddTerm (paAddTerm oddLeft doubleZero) paOneTerm
  let collapsed := paAddTerm oddLeft paOneTerm
  let associationRaw := proveAddAssociativityReverse
    oddLeft doubleZero paOneTerm
  let association : CertifiedPAProof
      (“!!source = !!grouped” : LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      oddLeft (paAddTerm doubleZero paOneTerm)
      (paAddTerm oddLeft doubleZero) paOneTerm
    simpa [source, grouped, oddRight] using (cast hformula associationRaw)
  let collapseDouble : CertifiedPAProof
      (“!!doubleZero = !!paZeroTerm” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula :
        (“!!(paMulTerm arithmeticTwoTerm paZeroTerm) = !!paZeroTerm” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!doubleZero = !!paZeroTerm” :
          LO.FirstOrder.ArithmeticProposition) := by
      simp [doubleZero, paZeroTerm,
        FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero]
    exact cast hformula (proveMulZeroAtPaZero arithmeticTwoTerm)
  let collapseInnerRaw := proveAddCongruence
    oddLeft doubleZero oddLeft paZeroTerm
    (proveEqualityReflexivityAtTerm oddLeft) collapseDouble
  let collapseInnerToZero : CertifiedPAProof
      (“!!(paAddTerm oddLeft doubleZero) =
        !!(paAddTerm oddLeft paZeroTerm)” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      oddLeft doubleZero oddLeft paZeroTerm
    exact cast hformula collapseInnerRaw
  let collapseInner := proveEqualityTransitivity
    (paAddTerm oddLeft doubleZero)
    (paAddTerm oddLeft paZeroTerm)
    oddLeft collapseInnerToZero (proveAddZeroAtPaZero oddLeft)
  let liftRaw := proveAddCongruence
    (paAddTerm oddLeft doubleZero) paOneTerm
    oddLeft paOneTerm collapseInner
    (proveEqualityReflexivityAtTerm paOneTerm)
  let lift : CertifiedPAProof
      (“!!grouped = !!collapsed” :
        LO.FirstOrder.ArithmeticProposition) := by
    have hformula := addEqualityAsTerm_formula
      (paAddTerm oddLeft doubleZero) paOneTerm oddLeft paOneTerm
    simpa [grouped, collapsed] using (cast hformula liftRaw)
  let increment := proveBinaryNumeralIncrement (Nat.bit true leftHigh)
  let throughGrouping := proveEqualityTransitivity
    source grouped collapsed association lift
  let throughIncrement := proveEqualityTransitivity
    source collapsed
    (shortBinaryNumeralTerm (Nat.bit true leftHigh + 1))
    throughGrouping increment
  have hformula :
      (“!!source =
        !!(shortBinaryNumeralTerm (Nat.bit true leftHigh + 1))” :
          LO.FirstOrder.ArithmeticProposition) =
        (“!!(paAddTerm
            (shortBinaryNumeralTerm (Nat.bit true leftHigh))
            (shortBinaryNumeralTerm (Nat.bit true 0))) =
          !!(shortBinaryNumeralTerm
            (Nat.bit true leftHigh + Nat.bit true 0))” :
          LO.FirstOrder.ArithmeticProposition) := by
    dsimp [source, oddRight, doubleZero, oddLeft]
    have hrightTerm :
        shortBinaryNumeralTerm 1 =
          paAddTerm
            (paMulTerm arithmeticTwoTerm
              (shortBinaryNumeralTerm 0)) paOneTerm := by
      simpa [Nat.bit_val] using shortBinaryNumeralTerm_bit_true 0
    rw [hrightTerm]
  exact cast hformula throughIncrement

def proveBinaryNumeralAdditionOddOdd
    (leftHigh rightHigh : Nat)
    (highProof : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm leftHigh)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(binaryAdditionHighSumTerm leftHigh rightHigh)” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(paAddTerm
          (shortBinaryNumeralTerm (Nat.bit true leftHigh))
          (shortBinaryNumeralTerm (Nat.bit true rightHigh))) =
        !!(shortBinaryNumeralTerm
          (Nat.bit true leftHigh + Nat.bit true rightHigh))” :
        LO.FirstOrder.ArithmeticProposition) := by
  by_cases hright : rightHigh = 0
  · subst rightHigh
    exact proveBinaryNumeralAdditionOddOddZero leftHigh
  · exact proveBinaryNumeralAdditionOddOddNonzero
      leftHigh rightHigh hright highProof

def proveBinaryNumeralAdditionBitStep
    (leftBit rightBit : Bool) (leftHigh rightHigh : Nat)
    (hleftCanonical : leftHigh = 0 → leftBit = true)
    (hrightCanonical : rightHigh = 0 → rightBit = true)
    (highProof : CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm leftHigh)
          (shortBinaryNumeralTerm rightHigh)) =
        !!(binaryAdditionHighSumTerm leftHigh rightHigh)” :
        LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAProof
      (“!!(paAddTerm
          (shortBinaryNumeralTerm (Nat.bit leftBit leftHigh))
          (shortBinaryNumeralTerm (Nat.bit rightBit rightHigh))) =
        !!(shortBinaryNumeralTerm
          (Nat.bit leftBit leftHigh + Nat.bit rightBit rightHigh))” :
        LO.FirstOrder.ArithmeticProposition) := by
  cases leftBit with
  | false =>
      have hleft : leftHigh ≠ 0 := by
        intro hz
        have himpossible := hleftCanonical hz
        simp at himpossible
      cases rightBit with
      | false =>
          have hright : rightHigh ≠ 0 := by
            intro hz
            have himpossible := hrightCanonical hz
            simp at himpossible
          exact proveBinaryNumeralAdditionEvenEven
            leftHigh rightHigh hleft hright highProof
      | true =>
          exact proveBinaryNumeralAdditionEvenOdd
            leftHigh rightHigh hleft highProof
  | true =>
      cases rightBit with
      | false =>
          have hright : rightHigh ≠ 0 := by
            intro hz
            have himpossible := hrightCanonical hz
            simp at himpossible
          exact proveBinaryNumeralAdditionOddEven
            leftHigh rightHigh hright highProof
      | true =>
          exact proveBinaryNumeralAdditionOddOdd
            leftHigh rightHigh highProof

/-- The complete proof-producing normalizer for addition of two short binary
numerals.  The proof recursion follows the binary height of the left input;
the nested recursion only exposes the current right-hand bit. -/
noncomputable def proveBinaryNumeralAddition :
    (left right : Nat) →
    CertifiedPAProof
      (“!!(paAddTerm (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm right)) =
        !!(shortBinaryNumeralTerm (left + right))” :
        LO.FirstOrder.ArithmeticProposition) :=
  Nat.binaryRec'
    (motive := fun left => (right : Nat) →
      CertifiedPAProof
        (“!!(paAddTerm (shortBinaryNumeralTerm left)
            (shortBinaryNumeralTerm right)) =
          !!(shortBinaryNumeralTerm (left + right))” :
          LO.FirstOrder.ArithmeticProposition))
    proveBinaryNumeralAdditionZeroLeft
    (fun leftBit leftHigh hleftCanonical addHigh right =>
      Nat.binaryRec'
        (motive := fun right =>
          CertifiedPAProof
            (“!!(paAddTerm
                (shortBinaryNumeralTerm (Nat.bit leftBit leftHigh))
                (shortBinaryNumeralTerm right)) =
              !!(shortBinaryNumeralTerm
                (Nat.bit leftBit leftHigh + right))” :
              LO.FirstOrder.ArithmeticProposition))
        (proveBinaryNumeralAdditionZeroRight
          (Nat.bit leftBit leftHigh))
        (fun rightBit rightHigh hrightCanonical _rightProof =>
          proveBinaryNumeralAdditionBitStep
            leftBit rightBit leftHigh rightHigh
            hleftCanonical hrightCanonical (addHigh rightHigh))
        right)

@[simp] theorem proveBinaryNumeralAddition_zero_left (right : Nat) :
    proveBinaryNumeralAddition 0 right =
      proveBinaryNumeralAdditionZeroLeft right := by
  simp [proveBinaryNumeralAddition]

theorem proveBinaryNumeralAddition_bit_zero
    (leftBit : Bool) (leftHigh : Nat)
    (hleftCanonical : leftHigh = 0 → leftBit = true) :
    proveBinaryNumeralAddition (Nat.bit leftBit leftHigh) 0 =
      proveBinaryNumeralAdditionZeroRight
        (Nat.bit leftBit leftHigh) := by
  unfold proveBinaryNumeralAddition
  rw [Nat.binaryRec'_eq
    (motive := fun left => (right : Nat) →
      CertifiedPAProof
        (“!!(paAddTerm (shortBinaryNumeralTerm left)
            (shortBinaryNumeralTerm right)) =
          !!(shortBinaryNumeralTerm (left + right))” :
          LO.FirstOrder.ArithmeticProposition))
    leftBit leftHigh hleftCanonical]
  rfl

theorem proveBinaryNumeralAddition_bit_bit
    (leftBit rightBit : Bool) (leftHigh rightHigh : Nat)
    (hleftCanonical : leftHigh = 0 → leftBit = true)
    (hrightCanonical : rightHigh = 0 → rightBit = true) :
    proveBinaryNumeralAddition
        (Nat.bit leftBit leftHigh) (Nat.bit rightBit rightHigh) =
      proveBinaryNumeralAdditionBitStep
        leftBit rightBit leftHigh rightHigh
        hleftCanonical hrightCanonical
        (proveBinaryNumeralAddition leftHigh rightHigh) := by
  unfold proveBinaryNumeralAddition
  rw [Nat.binaryRec'_eq
    (motive := fun left => (right : Nat) →
      CertifiedPAProof
        (“!!(paAddTerm (shortBinaryNumeralTerm left)
            (shortBinaryNumeralTerm right)) =
          !!(shortBinaryNumeralTerm (left + right))” :
          LO.FirstOrder.ArithmeticProposition))
    leftBit leftHigh hleftCanonical]
  rw [Nat.binaryRec'_eq
    (motive := fun right =>
      CertifiedPAProof
        (“!!(paAddTerm
            (shortBinaryNumeralTerm (Nat.bit leftBit leftHigh))
            (shortBinaryNumeralTerm right)) =
          !!(shortBinaryNumeralTerm
            (Nat.bit leftBit leftHigh + right))” :
          LO.FirstOrder.ArithmeticProposition))
    rightBit rightHigh hrightCanonical]

theorem proveBinaryNumeralAddition_verifier_eq_true
    (left right : Nat) :
    listedCompactCertifiedPAProofVerifier
      (proveBinaryNumeralAddition left right).code
      (compactFormulaCode
        (“!!(paAddTerm (shortBinaryNumeralTerm left)
            (shortBinaryNumeralTerm right)) =
          !!(shortBinaryNumeralTerm (left + right))” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  (proveBinaryNumeralAddition left right).verifier_eq_true

theorem proveAddCommutativity_verifier_eq_true
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    listedCompactCertifiedPAProofVerifier
      (proveAddCommutativity left right).code
      (compactFormulaCode
        (“!!left + !!right = !!right + !!left” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  (proveAddCommutativity left right).verifier_eq_true

theorem proveAddAssociativity_verifier_eq_true
    (left middle right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    listedCompactCertifiedPAProofVerifier
      (proveAddAssociativity left middle right).code
      (compactFormulaCode
        (“(!!left + !!middle) + !!right =
          !!left + (!!middle + !!right)” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  (proveAddAssociativity left middle right).verifier_eq_true

theorem proveLeftDistributivity_verifier_eq_true
    (factor left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    listedCompactCertifiedPAProofVerifier
      (proveLeftDistributivity factor left right).code
      (compactFormulaCode
        (“!!factor * (!!left + !!right) =
          !!factor * !!left + !!factor * !!right” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  (proveLeftDistributivity factor left right).verifier_eq_true

#print axioms proveAddCommutativity_verifier_eq_true
#print axioms proveAddAssociativity_verifier_eq_true
#print axioms proveLeftDistributivity_verifier_eq_true
#print axioms proveAddCommutativity_payloadLength_le
#print axioms proveAddAssociativity_payloadLength_le
#print axioms proveLeftDistributivity_payloadLength_le
#print axioms proveZeroAdd
#print axioms proveDoubleSum
#print axioms proveZeroAdd_payloadLength_le
#print axioms proveLeftDistributivityReverse_payloadLength_le
#print axioms proveBinaryNumeralIncrementZero
#print axioms proveBinaryNumeralIncrementEven
#print axioms proveBinaryNumeralIncrementOdd
#print axioms proveBinaryNumeralIncrement_verifier_eq_true
#print axioms proveBinaryNumeralAdditionBitStep
#print axioms proveBinaryNumeralAddition_verifier_eq_true

end FoundationCompactPABinaryNumeralAddition
