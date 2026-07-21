import integration.FoundationCompactPAExponentialRuleCompiler
import integration.FoundationCompactPAExponentialShortNumeralCompiler
import integration.FoundationCompactPABinaryNumeralAddition
import integration.FoundationCompactPAClosedAtomicCompiler
import Foundation.FirstOrder.Arithmetic.Exponential.Log

/-!
# Fixed PA rules for binary-length proofs

The direct proof predicate repeatedly uses Foundation's `lengthDef` at large
closed numerals.  This module fixes genuine PA proofs of the zero, even, and
odd binary-recursion rules.  Later modules specialize these fixed proofs along
the actual input bits; no proof-existence or proof-length premise is accepted.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABinaryLengthRuleCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAExponentialRuleCompiler
open FoundationCompactPAExponentialShortNumeralCompiler
open FoundationCompactPAClosedAtomicCompiler
open FoundationCompactPAClosedAtomicCompiler.ClosedPATerm

def binaryLengthZeroSentence : LO.FirstOrder.ArithmeticSentence :=
  “!lengthDef 0 0”

theorem models_binaryLengthZeroSentence
    (M : Type*) [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* PA] :
    M↓[ℒₒᵣ] ⊧ binaryLengthZeroSentence := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ :=
    ModelsTheory.of_provably_subtheory M 𝗜𝚺₀ PA inferInstance
  rw [models_iff]
  simp [binaryLengthZeroSentence]

theorem binaryLengthZeroSentence_provable :
    PA ⊢ binaryLengthZeroSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} PA
    binaryLengthZeroSentence
  intro M _ _
  exact models_binaryLengthZeroSentence M

noncomputable def binaryLengthZeroCertifiedProof :
    CertifiedPAProof
      (Rewriting.emb binaryLengthZeroSentence :
        LO.FirstOrder.ArithmeticProposition) :=
  certifiedProofOfProvable binaryLengthZeroSentence_provable

def binaryLengthEvenSentence : LO.FirstOrder.ArithmeticSentence :=
  “∀ size value,
    0 < value →
    !lengthDef size value →
    !lengthDef (size + 1) (2 * value)”

theorem models_binaryLengthEvenSentence
    (M : Type*) [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* PA] :
    M↓[ℒₒᵣ] ⊧ binaryLengthEvenSentence := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ :=
    ModelsTheory.of_provably_subtheory M 𝗜𝚺₀ PA inferInstance
  rw [models_iff]
  simp only [binaryLengthEvenSentence, Semiformula.eval_all,
    LO.LogicalConnective.HomClass.map_imply]
  intro size value hpositive hlength
  have hsize : size = ‖value‖ := by
    simpa using hlength
  have hstep := LO.FirstOrder.Arithmetic.length_two_mul_of_pos hpositive
  simpa [hsize] using hstep.symm

theorem binaryLengthEvenSentence_provable :
    PA ⊢ binaryLengthEvenSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} PA
    binaryLengthEvenSentence
  intro M _ _
  exact models_binaryLengthEvenSentence M

noncomputable def binaryLengthEvenCertifiedProof :
    CertifiedPAProof
      (Rewriting.emb binaryLengthEvenSentence :
        LO.FirstOrder.ArithmeticProposition) :=
  certifiedProofOfProvable binaryLengthEvenSentence_provable

def binaryLengthOddSentence : LO.FirstOrder.ArithmeticSentence :=
  “∀ size value,
    !lengthDef size value →
    !lengthDef (size + 1) (2 * value + 1)”

theorem models_binaryLengthOddSentence
    (M : Type*) [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* PA] :
    M↓[ℒₒᵣ] ⊧ binaryLengthOddSentence := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ :=
    ModelsTheory.of_provably_subtheory M 𝗜𝚺₀ PA inferInstance
  rw [models_iff]
  simp only [binaryLengthOddSentence, Semiformula.eval_all,
    LO.LogicalConnective.HomClass.map_imply]
  intro size value hlength
  have hsize : size = ‖value‖ := by
    simpa using hlength
  have hstep :=
    LO.FirstOrder.Arithmetic.length_two_mul_add_one value
  simpa [hsize] using hstep.symm

theorem binaryLengthOddSentence_provable :
    PA ⊢ binaryLengthOddSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} PA
    binaryLengthOddSentence
  intro M _ _
  exact models_binaryLengthOddSentence M

noncomputable def binaryLengthOddCertifiedProof :
    CertifiedPAProof
      (Rewriting.emb binaryLengthOddSentence :
        LO.FirstOrder.ArithmeticProposition) :=
  certifiedProofOfProvable binaryLengthOddSentence_provable

theorem subst_lengthDef_instance
    {sourceArity targetArity : Nat}
    (values : Fin sourceArity →
      LO.FirstOrder.ArithmeticSemiterm Nat targetArity)
    (first second :
      LO.FirstOrder.ArithmeticSemiterm Nat sourceArity) :
    Rewriting.app (Rew.subst values)
        ((Rewriting.emb lengthDef.val :
          LO.FirstOrder.ArithmeticSemiformula Nat 2)/[first, second]) =
      (Rewriting.emb lengthDef.val :
        LO.FirstOrder.ArithmeticSemiformula Nat 2)/[
          Rew.subst values first, Rew.subst values second] := by
  rw [← TransitiveRewriting.comp_app, Rew.subst_comp_subst]
  congr 2
  congr 1
  funext index
  cases index using Fin.cases with
  | zero => rfl
  | succ index =>
      cases index using Fin.cases with
      | zero => rfl
      | succ index => exact Fin.elim0 index

theorem q_subst_lengthDef_instance
    {sourceArity targetArity : Nat}
    (values : Fin sourceArity →
      LO.FirstOrder.ArithmeticSemiterm Nat targetArity)
    (first second :
      LO.FirstOrder.ArithmeticSemiterm Nat (sourceArity + 1)) :
    Rewriting.app (Rew.subst values).q
        ((Rewriting.emb lengthDef.val :
          LO.FirstOrder.ArithmeticSemiformula Nat 2)/[first, second]) =
      (Rewriting.emb lengthDef.val :
        LO.FirstOrder.ArithmeticSemiformula Nat 2)/[
          (Rew.subst values).q first,
          (Rew.subst values).q second] := by
  rw [Rew.q_subst]
  exact subst_lengthDef_instance
    (#0 :> Rew.bShift ∘ values) first second

theorem lengthDef_instance_congr
    {arity : Nat}
    {first second first' second' :
      LO.FirstOrder.ArithmeticSemiterm Nat arity}
    (hfirst : first = first')
    (hsecond : second = second') :
    ((Rewriting.emb lengthDef.val :
        LO.FirstOrder.ArithmeticSemiformula Nat 2)/[first, second]) =
      (Rewriting.emb lengthDef.val :
        LO.FirstOrder.ArithmeticSemiformula Nat 2)/[first', second'] := by
  rw [hfirst, hsecond]

def binaryLengthEvenOuterBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰
    0 < #0 →
    !lengthDef #1 #0 →
    !lengthDef (#1 + 1) (2 * #0)”

theorem binaryLengthEvenSentence_emb_formula :
    (Rewriting.emb binaryLengthEvenSentence :
      LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ binaryLengthEvenOuterBody := by
  simp [binaryLengthEvenSentence, binaryLengthEvenOuterBody]
  constructor <;>
    rw [Rewriting.emb_subst_eq_subst_emb] <;>
    congr 1 <;>
    funext index <;>
    cases index using Fin.cases <;>
    simp

noncomputable def binaryLengthEvenUniversalProof :
    CertifiedPAProof (∀⁰ binaryLengthEvenOuterBody) :=
  CertifiedPAProof.cast binaryLengthEvenSentence_emb_formula
    binaryLengthEvenCertifiedProof

def binaryLengthEvenInnerBody
    (size : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “0 < #0 →
    !lengthDef !!(Rew.bShift size) #0 →
    !lengthDef (!!(Rew.bShift size) + 1) (2 * #0)”

theorem binaryLengthEvenAfterFirst_formula
    (size : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryLengthEvenOuterBody/[size] =
      ∀⁰ binaryLengthEvenInnerBody size := by
  simp [binaryLengthEvenOuterBody, binaryLengthEvenInnerBody,
    substQ_bvarOne]
  constructor
  · rw [q_subst_lengthDef_instance]
    apply lengthDef_instance_congr <;> simp [substQ_bvarOne]
  · rw [q_subst_lengthDef_instance]
    apply lengthDef_instance_congr <;> simp [substQ_bvarOne]

theorem binaryLengthEvenFinal_formula
    (size value : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryLengthEvenInnerBody size)/[value] =
      (“0 < !!value →
        !lengthDef !!size !!value →
        !lengthDef (!!size + 1) (2 * !!value)” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [binaryLengthEvenInnerBody]
  constructor
  · rw [subst_lengthDef_instance]
    apply lengthDef_instance_congr <;> simp
  · rw [subst_lengthDef_instance]
    apply lengthDef_instance_congr <;> simp

noncomputable def binaryLengthEvenImplication
    (size value : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“0 < !!value →
        !lengthDef !!size !!value →
        !lengthDef (!!size + 1) (2 * !!value)” :
        LO.FirstOrder.ArithmeticProposition) :=
  specializeTwiceWithCasts binaryLengthEvenUniversalProof size value
    (binaryLengthEvenAfterFirst_formula size)
    (binaryLengthEvenFinal_formula size value)

def binaryLengthOddOuterBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰
    !lengthDef #1 #0 →
    !lengthDef (#1 + 1) (2 * #0 + 1)”

theorem binaryLengthOddSentence_emb_formula :
    (Rewriting.emb binaryLengthOddSentence :
      LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ binaryLengthOddOuterBody := by
  simp [binaryLengthOddSentence, binaryLengthOddOuterBody]
  constructor <;>
    rw [Rewriting.emb_subst_eq_subst_emb] <;>
    congr 1 <;>
    funext index <;>
    cases index using Fin.cases <;>
    simp

noncomputable def binaryLengthOddUniversalProof :
    CertifiedPAProof (∀⁰ binaryLengthOddOuterBody) :=
  CertifiedPAProof.cast binaryLengthOddSentence_emb_formula
    binaryLengthOddCertifiedProof

def binaryLengthOddInnerBody
    (size : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!lengthDef !!(Rew.bShift size) #0 →
    !lengthDef (!!(Rew.bShift size) + 1) (2 * #0 + 1)”

theorem binaryLengthOddAfterFirst_formula
    (size : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryLengthOddOuterBody/[size] =
      ∀⁰ binaryLengthOddInnerBody size := by
  simp [binaryLengthOddOuterBody, binaryLengthOddInnerBody,
    substQ_bvarOne]
  constructor
  · rw [q_subst_lengthDef_instance]
    apply lengthDef_instance_congr <;> simp [substQ_bvarOne]
  · rw [q_subst_lengthDef_instance]
    apply lengthDef_instance_congr <;> simp [substQ_bvarOne]

theorem binaryLengthOddFinal_formula
    (size value : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryLengthOddInnerBody size)/[value] =
      (“!lengthDef !!size !!value →
        !lengthDef (!!size + 1) (2 * !!value + 1)” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [binaryLengthOddInnerBody]
  constructor
  · rw [subst_lengthDef_instance]
    apply lengthDef_instance_congr <;> simp
  · rw [subst_lengthDef_instance]
    apply lengthDef_instance_congr <;> simp

noncomputable def binaryLengthOddImplication
    (size value : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!lengthDef !!size !!value →
        !lengthDef (!!size + 1) (2 * !!value + 1)” :
        LO.FirstOrder.ArithmeticProposition) :=
  specializeTwiceWithCasts binaryLengthOddUniversalProof size value
    (binaryLengthOddAfterFirst_formula size)
    (binaryLengthOddFinal_formula size value)

def binaryLengthRecursiveFormula
    (value : Nat) : LO.FirstOrder.ArithmeticProposition :=
  “!lengthDef
      !!(exponentialExponentTerm (Nat.size value))
      !!(shortBinaryNumeralTerm value)”

theorem binaryLengthZeroCertifiedProof_formula :
    (Rewriting.emb binaryLengthZeroSentence :
      LO.FirstOrder.ArithmeticProposition) =
      binaryLengthRecursiveFormula 0 := by
  simp only [binaryLengthZeroSentence, binaryLengthRecursiveFormula,
    exponentialExponentTerm, Nat.size_zero]
  rw [Rewriting.emb_subst_eq_subst_emb]
  congr 1
  funext index
  cases index using Fin.cases with
  | zero => rfl
  | succ index =>
      cases index using Fin.cases with
      | zero =>
          simp [shortBinaryNumeralTerm,
            FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero,
            embeddedClosedNumeralZero_eq_paZeroTerm, paZeroTerm,
            arithmeticZeroTerm, Semiterm.Operator.operator,
            Semiterm.Operator.numeral_zero,
            Semiterm.Operator.Zero.term_eq]
      | succ index => exact Fin.elim0 index

noncomputable def binaryLengthZeroRecursiveProof :
    CertifiedPAProof (binaryLengthRecursiveFormula 0) :=
  CertifiedPAProof.cast binaryLengthZeroCertifiedProof_formula
    binaryLengthZeroCertifiedProof

noncomputable def binaryLengthPositivityProof
    (value : Nat) (hpositive : 0 < value) :
    CertifiedPAProof
      (“0 < !!(shortBinaryNumeralTerm value)” :
        LO.FirstOrder.ArithmeticProposition) := by
  let positivityRaw :=
    FoundationCompactPAClosedAtomicCompiler.ClosedPATerm.provePositiveLessThan
      (.numeral 0) (.numeral value) hpositive
  have hformula :
      (“!!((.numeral 0 :
          FoundationCompactPAClosedAtomicCompiler.ClosedPATerm).term) <
        !!((.numeral value :
          FoundationCompactPAClosedAtomicCompiler.ClosedPATerm).term)” :
        LO.FirstOrder.ArithmeticProposition) =
        (“0 < !!(shortBinaryNumeralTerm value)” :
          LO.FirstOrder.ArithmeticProposition) := by
    simp [FoundationCompactPAClosedAtomicCompiler.ClosedPATerm.term,
      shortBinaryNumeralTerm,
      FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero,
      arithmeticZeroTerm, Semiterm.Operator.operator,
      Semiterm.Operator.numeral_zero,
      Semiterm.Operator.Zero.term_eq]
  exact CertifiedPAProof.cast hformula positivityRaw

noncomputable def binaryLengthBitStep
    (bit : Bool) (value : Nat)
    (hcanonical : value = 0 → bit = true)
    (previous : CertifiedPAProof (binaryLengthRecursiveFormula value)) :
    CertifiedPAProof
      (binaryLengthRecursiveFormula (Nat.bit bit value)) := by
  have hnonzero : Nat.bit bit value ≠ 0 :=
    Nat.bit_ne_zero_iff.mpr hcanonical
  have hsize :
      Nat.size (Nat.bit bit value) = Nat.size value + 1 :=
    Nat.size_bit hnonzero
  let sizeTerm := exponentialExponentTerm (Nat.size value)
  let valueTerm := shortBinaryNumeralTerm value
  cases bit with
  | false =>
      have hvalueNonzero : value ≠ 0 := by
        intro hzero
        have himpossible := hcanonical hzero
        simp at himpossible
      have hpositive : 0 < value :=
        Nat.pos_of_ne_zero hvalueNonzero
      let positivity : CertifiedPAProof
          (“0 < !!valueTerm” :
            LO.FirstOrder.ArithmeticProposition) := by
        exact binaryLengthPositivityProof value hpositive
      let afterPositive :=
        CertifiedPAProof.modusPonens
          (binaryLengthEvenImplication sizeTerm valueTerm)
          positivity
      let result :=
        CertifiedPAProof.modusPonens afterPositive previous
      have hsizeTerm :
          (‘(!!sizeTerm + 1)’ :
            LO.FirstOrder.ArithmeticSemiterm Nat 0) =
            exponentialExponentTerm
              (Nat.size (Nat.bit false value)) := by
        rw [hsize, exponentialExponentTerm]
      have hvalueTerm :
          (‘(2 * !!valueTerm)’ :
            LO.FirstOrder.ArithmeticSemiterm Nat 0) =
            shortBinaryNumeralTerm (Nat.bit false value) := by
        have hformula :
            (‘(2 * !!valueTerm)’ :
              LO.FirstOrder.ArithmeticSemiterm Nat 0) =
              paMulTerm
                (Rew.emb (closedNumeralTerm 2)) valueTerm := by
          simp [paMulTerm, closedNumeralTerm]
        calc
          (‘(2 * !!valueTerm)’ :
              LO.FirstOrder.ArithmeticSemiterm Nat 0) =
              paMulTerm
                (Rew.emb (closedNumeralTerm 2)) valueTerm := hformula
          _ = paMulTerm arithmeticTwoTerm valueTerm := by
            rw [embeddedClosedNumeralTwo_eq_arithmeticTwoTerm]
          _ = shortBinaryNumeralTerm (Nat.bit false value) :=
            (shortBinaryNumeralTerm_bit_false
              value hvalueNonzero).symm
      have hformula :
          (“!lengthDef (!!sizeTerm + 1) (2 * !!valueTerm)” :
            LO.FirstOrder.ArithmeticProposition) =
            binaryLengthRecursiveFormula (Nat.bit false value) := by
        unfold binaryLengthRecursiveFormula
        exact lengthDef_instance_congr hsizeTerm hvalueTerm
      exact CertifiedPAProof.cast hformula result
  | true =>
      let result :=
        CertifiedPAProof.modusPonens
          (binaryLengthOddImplication sizeTerm valueTerm)
          previous
      have hsizeTerm :
          (‘(!!sizeTerm + 1)’ :
            LO.FirstOrder.ArithmeticSemiterm Nat 0) =
            exponentialExponentTerm
              (Nat.size (Nat.bit true value)) := by
        rw [hsize, exponentialExponentTerm]
      have hvalueTerm :
          (‘(2 * !!valueTerm + 1)’ :
            LO.FirstOrder.ArithmeticSemiterm Nat 0) =
            shortBinaryNumeralTerm (Nat.bit true value) := by
        have hformula :
            (‘(2 * !!valueTerm + 1)’ :
              LO.FirstOrder.ArithmeticSemiterm Nat 0) =
              paAddTerm
                (paMulTerm
                  (Rew.emb (closedNumeralTerm 2)) valueTerm)
                (Rew.emb (closedNumeralTerm 1)) := by
          simp [paMulTerm, paAddTerm, closedNumeralTerm]
        calc
          (‘(2 * !!valueTerm + 1)’ :
              LO.FirstOrder.ArithmeticSemiterm Nat 0) =
              paAddTerm
                (paMulTerm
                  (Rew.emb (closedNumeralTerm 2)) valueTerm)
                (Rew.emb (closedNumeralTerm 1)) := hformula
          _ = paAddTerm
                (paMulTerm arithmeticTwoTerm valueTerm)
                paOneTerm := by
            rw [embeddedClosedNumeralTwo_eq_arithmeticTwoTerm,
              embeddedClosedNumeralOne_eq_paOneTerm]
          _ = shortBinaryNumeralTerm (Nat.bit true value) :=
            (shortBinaryNumeralTerm_bit_true value).symm
      have hformula :
          (“!lengthDef
              (!!sizeTerm + 1) (2 * !!valueTerm + 1)” :
            LO.FirstOrder.ArithmeticProposition) =
            binaryLengthRecursiveFormula (Nat.bit true value) := by
        unfold binaryLengthRecursiveFormula
        exact lengthDef_instance_congr hsizeTerm hvalueTerm
      exact CertifiedPAProof.cast hformula result

noncomputable def proveBinaryLengthAtRecursiveSize :
    (value : Nat) →
    CertifiedPAProof (binaryLengthRecursiveFormula value) :=
  Nat.binaryRec' binaryLengthZeroRecursiveProof binaryLengthBitStep

@[simp] theorem proveBinaryLengthAtRecursiveSize_zero :
    proveBinaryLengthAtRecursiveSize 0 =
      binaryLengthZeroRecursiveProof := by
  simp [proveBinaryLengthAtRecursiveSize]

theorem proveBinaryLengthAtRecursiveSize_bit
    (bit : Bool) (value : Nat)
    (hcanonical : value = 0 → bit = true) :
    proveBinaryLengthAtRecursiveSize (Nat.bit bit value) =
      binaryLengthBitStep bit value hcanonical
        (proveBinaryLengthAtRecursiveSize value) := by
  unfold proveBinaryLengthAtRecursiveSize
  rw [Nat.binaryRec'_eq
    (motive := fun value =>
      CertifiedPAProof (binaryLengthRecursiveFormula value))
    bit value hcanonical]

theorem proveBinaryLengthAtRecursiveSize_verifier_eq_true
    (value : Nat) :
    listedCompactCertifiedPAProofVerifier
        (proveBinaryLengthAtRecursiveSize value).code
        (compactFormulaCode
          (binaryLengthRecursiveFormula value)) = true :=
  (proveBinaryLengthAtRecursiveSize value).verifier_eq_true

def binaryLengthSizeTransportSentence :
    LO.FirstOrder.ArithmeticSentence :=
  “∀ leftSize rightSize value,
    leftSize = rightSize →
    (!lengthDef leftSize value →
      !lengthDef rightSize value)”

theorem models_binaryLengthSizeTransportSentence
    (M : Type*) [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* PA] :
    M↓[ℒₒᵣ] ⊧ binaryLengthSizeTransportSentence := by
  rw [models_iff]
  simp only [binaryLengthSizeTransportSentence,
    Semiformula.eval_all, LO.LogicalConnective.HomClass.map_imply]
  intro leftSize rightSize value hsize
  have hsize' : leftSize = rightSize := by
    simpa using hsize
  clear hsize
  subst rightSize
  exact fun hlength => by simpa using hlength

theorem binaryLengthSizeTransportSentence_provable :
    PA ⊢ binaryLengthSizeTransportSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} PA
    binaryLengthSizeTransportSentence
  intro M _ _
  exact models_binaryLengthSizeTransportSentence M

noncomputable def binaryLengthSizeTransportCertifiedProof :
    CertifiedPAProof
      (Rewriting.emb binaryLengthSizeTransportSentence :
        LO.FirstOrder.ArithmeticProposition) :=
  certifiedProofOfProvable
    binaryLengthSizeTransportSentence_provable

def binaryLengthSizeTransportOuterBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰ ∀⁰
    (#2 = #1 →
      (!lengthDef #2 #0 → !lengthDef #1 #0))”

theorem binaryLengthSizeTransportSentence_emb_formula :
    (Rewriting.emb binaryLengthSizeTransportSentence :
      LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ binaryLengthSizeTransportOuterBody := by
  simp [binaryLengthSizeTransportSentence,
    binaryLengthSizeTransportOuterBody]
  constructor
  · rw [Rewriting.emb_subst_eq_subst_emb]
    congr 1
    funext index
    cases index using Fin.cases with
    | zero => rfl
    | succ index =>
        cases index using Fin.cases with
        | zero => rfl
        | succ index => exact Fin.elim0 index
  · rw [Rewriting.emb_subst_eq_subst_emb]
    congr 1
    funext index
    cases index using Fin.cases with
    | zero => rfl
    | succ index =>
        cases index using Fin.cases with
        | zero => rfl
        | succ index => exact Fin.elim0 index

noncomputable def binaryLengthSizeTransportUniversalProof :
    CertifiedPAProof (∀⁰ binaryLengthSizeTransportOuterBody) :=
  CertifiedPAProof.cast
    binaryLengthSizeTransportSentence_emb_formula
    binaryLengthSizeTransportCertifiedProof

def binaryLengthSizeTransportMiddleBody
    (leftSize : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰
    (!!(Rew.bShift (Rew.bShift leftSize)) = #1 →
      (!lengthDef !!(Rew.bShift (Rew.bShift leftSize)) #0 →
        !lengthDef #1 #0))”

theorem binaryLengthSizeTransportAfterFirst_formula
    (leftSize : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryLengthSizeTransportOuterBody/[leftSize] =
      ∀⁰ binaryLengthSizeTransportMiddleBody leftSize := by
  simp [binaryLengthSizeTransportOuterBody,
    binaryLengthSizeTransportMiddleBody,
    substQQ_bvarOne, substQQ_bvarTwo]
  constructor
  · rw [Rew.q_subst, Rew.q_subst, subst_lengthDef_instance]
    apply lengthDef_instance_congr <;>
      simp [Rew.comp_app, substQQ_bvarOne, substQQ_bvarTwo]
  · rw [Rew.q_subst, Rew.q_subst, subst_lengthDef_instance]
    apply lengthDef_instance_congr <;>
      simp [Rew.comp_app, substQQ_bvarOne, substQQ_bvarTwo]

def binaryLengthSizeTransportInnerBody
    (leftSize rightSize :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!!(Rew.bShift leftSize) = !!(Rew.bShift rightSize) →
    (!lengthDef !!(Rew.bShift leftSize) #0 →
      !lengthDef !!(Rew.bShift rightSize) #0)”

theorem binaryLengthSizeTransportAfterSecond_formula
    (leftSize rightSize :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryLengthSizeTransportMiddleBody leftSize)/[rightSize] =
      ∀⁰ binaryLengthSizeTransportInnerBody leftSize rightSize := by
  have hleft :
      (Rew.subst ![rightSize]).q
          (Rew.bShift (Rew.bShift leftSize)) =
        Rew.bShift leftSize := by
    simp
  simp [binaryLengthSizeTransportMiddleBody,
    binaryLengthSizeTransportInnerBody, substQ_bvarOne, hleft]
  constructor
  · rw [q_subst_lengthDef_instance]
    apply lengthDef_instance_congr <;> simp [substQ_bvarOne, hleft]
  · rw [q_subst_lengthDef_instance]
    apply lengthDef_instance_congr <;> simp [substQ_bvarOne, hleft]

theorem binaryLengthSizeTransportFinal_formula
    (leftSize rightSize value :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryLengthSizeTransportInnerBody
      leftSize rightSize)/[value] =
      (“!!leftSize = !!rightSize →
        (!lengthDef !!leftSize !!value →
          !lengthDef !!rightSize !!value)” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [binaryLengthSizeTransportInnerBody]
  constructor
  · rw [subst_lengthDef_instance]
    apply lengthDef_instance_congr <;> simp
  · rw [subst_lengthDef_instance]
    apply lengthDef_instance_congr <;> simp

noncomputable def binaryLengthSizeTransportImplication
    (leftSize rightSize value :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!leftSize = !!rightSize →
        (!lengthDef !!leftSize !!value →
          !lengthDef !!rightSize !!value)” :
        LO.FirstOrder.ArithmeticProposition) :=
  specializeThriceWithCasts
    binaryLengthSizeTransportUniversalProof
    leftSize rightSize value
    (binaryLengthSizeTransportAfterFirst_formula leftSize)
    (binaryLengthSizeTransportAfterSecond_formula
      leftSize rightSize)
    (binaryLengthSizeTransportFinal_formula
      leftSize rightSize value)

def binaryLengthShortNumeralFormula
    (value : Nat) : LO.FirstOrder.ArithmeticProposition :=
  “!lengthDef
      !!(shortBinaryNumeralTerm (Nat.size value))
      !!(shortBinaryNumeralTerm value)”

noncomputable def proveBinaryLengthAtShortNumerals
    (value : Nat) :
    CertifiedPAProof (binaryLengthShortNumeralFormula value) := by
  let recursiveSize := exponentialExponentTerm (Nat.size value)
  let shortSize := shortBinaryNumeralTerm (Nat.size value)
  let valueTerm := shortBinaryNumeralTerm value
  let transportAfterEquality :=
    CertifiedPAProof.modusPonens
      (binaryLengthSizeTransportImplication
        recursiveSize shortSize valueTerm)
      (exponentialExponentRecursiveToShortProof
        (Nat.size value))
  let result :=
    CertifiedPAProof.modusPonens transportAfterEquality
      (proveBinaryLengthAtRecursiveSize value)
  exact result

theorem proveBinaryLengthAtShortNumerals_verifier_eq_true
    (value : Nat) :
    listedCompactCertifiedPAProofVerifier
        (proveBinaryLengthAtShortNumerals value).code
        (compactFormulaCode
          (binaryLengthShortNumeralFormula value)) = true :=
  (proveBinaryLengthAtShortNumerals value).verifier_eq_true

#print axioms models_binaryLengthZeroSentence
#print axioms binaryLengthZeroCertifiedProof
#print axioms models_binaryLengthEvenSentence
#print axioms binaryLengthEvenCertifiedProof
#print axioms models_binaryLengthOddSentence
#print axioms binaryLengthOddCertifiedProof
#print axioms binaryLengthEvenImplication
#print axioms binaryLengthOddImplication
#print axioms proveBinaryLengthAtRecursiveSize
#print axioms proveBinaryLengthAtRecursiveSize_verifier_eq_true
#print axioms binaryLengthSizeTransportImplication
#print axioms proveBinaryLengthAtShortNumerals
#print axioms proveBinaryLengthAtShortNumerals_verifier_eq_true

end FoundationCompactPABinaryLengthRuleCompiler
