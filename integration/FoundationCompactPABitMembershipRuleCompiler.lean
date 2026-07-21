import integration.FoundationCompactPABinaryLengthRuleCompiler
import integration.FoundationCompactPABinaryNumeralAddition
import Foundation.FirstOrder.Arithmetic.Exponential.Bit

/-!
# Fixed PA rules for binary membership proofs

Foundation's arithmetic membership atom `index ∈ value` is represented by
`bitDef index value`.  Expanding that bounded definition at a large closed
value would enumerate a numeric interval.  This module instead specializes
fixed PA proofs of the binary recursion rules and follows only the relevant
bits of the represented value.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABitMembershipRuleCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAExponentialRuleCompiler
open FoundationCompactPAExponentialShortNumeralCompiler

/-! ## Formula coordinates -/

def binaryBitZeroTerm {boundArity : Nat} :
    LO.FirstOrder.ArithmeticSemiterm Nat boundArity :=
  ‘0’

def binaryBitAtomAtTerms {boundArity : Nat}
    (index value :
      LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
    LO.FirstOrder.ArithmeticSemiformula Nat boundArity :=
  “!bitDef !!index !!value”

def binaryBitLiteralAtTerms {boundArity : Nat}
    (expected : Bool)
    (index value :
      LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
    LO.FirstOrder.ArithmeticSemiformula Nat boundArity :=
  if expected then
    binaryBitAtomAtTerms index value
  else
    ∼binaryBitAtomAtTerms index value

def binaryBitValueStepTerm {boundArity : Nat}
    (valueBit : Bool)
    (value : LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
    LO.FirstOrder.ArithmeticSemiterm Nat boundArity :=
  if valueBit then ‘(2 * !!value + 1)’ else ‘(2 * !!value)’

def binaryBitIncrementEquality {boundArity : Nat}
    (index nextIndex :
      LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
    LO.FirstOrder.ArithmeticSemiformula Nat boundArity :=
  “!!index + 1 = !!nextIndex”

def binaryBitStepFormula {boundArity : Nat}
    (valueBit expected : Bool)
    (index nextIndex value :
      LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
    LO.FirstOrder.ArithmeticSemiformula Nat boundArity :=
  binaryBitIncrementEquality index nextIndex 🡒
    (binaryBitLiteralAtTerms expected index value 🡒
      binaryBitLiteralAtTerms expected nextIndex
        (binaryBitValueStepTerm valueBit value))

def binaryBitShortLiteralFormula
    (expected : Bool) (index value : Nat) :
    LO.FirstOrder.ArithmeticProposition :=
  binaryBitLiteralAtTerms expected
    (shortBinaryNumeralTerm index)
    (shortBinaryNumeralTerm value)

theorem binaryBitLiteralAtTerms_congr
    (expected : Bool)
    {index index' value value' :
      LO.FirstOrder.ArithmeticSemiterm Nat 0}
    (hindex : index = index')
    (hvalue : value = value') :
    binaryBitLiteralAtTerms expected index value =
      binaryBitLiteralAtTerms expected index' value' := by
  subst index'
  subst value'
  rfl

/-! ## Fixed PA recursion rules -/

def binaryBitZeroValueNegativeSentence :
    LO.FirstOrder.ArithmeticSentence :=
  “∀ index, ¬!bitDef index 0”

def binaryBitLowSentence (valueBit : Bool) :
    LO.FirstOrder.ArithmeticSentence :=
  match valueBit with
  | false => “∀ value, ¬!bitDef 0 (2 * value)”
  | true => “∀ value, !bitDef 0 (2 * value + 1)”

def binaryBitStepSentence (valueBit expected : Bool) :
    LO.FirstOrder.ArithmeticSentence :=
  match valueBit, expected with
  | false, false =>
      “∀ index nextIndex value,
        index + 1 = nextIndex →
        ¬!bitDef index value →
        ¬!bitDef nextIndex (2 * value)”
  | false, true =>
      “∀ index nextIndex value,
        index + 1 = nextIndex →
        !bitDef index value →
        !bitDef nextIndex (2 * value)”
  | true, false =>
      “∀ index nextIndex value,
        index + 1 = nextIndex →
        ¬!bitDef index value →
        ¬!bitDef nextIndex (2 * value + 1)”
  | true, true =>
      “∀ index nextIndex value,
        index + 1 = nextIndex →
        !bitDef index value →
        !bitDef nextIndex (2 * value + 1)”

theorem models_binaryBitZeroValueNegativeSentence
    (M : Type*) [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* PA] :
    M↓[ℒₒᵣ] ⊧ binaryBitZeroValueNegativeSentence := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
    ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ PA inferInstance
  rw [models_iff]
  simp [binaryBitZeroValueNegativeSentence, bitDef]

theorem models_binaryBitLowSentence
    (valueBit : Bool)
    (M : Type*) [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* PA] :
    M↓[ℒₒᵣ] ⊧ binaryBitLowSentence valueBit := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
    ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ PA inferInstance
  cases valueBit with
  | false =>
      rw [models_iff]
      simp [binaryBitLowSentence, bitDef, LenBit]
  | true =>
      rw [models_iff]
      simp [binaryBitLowSentence, bitDef, LenBit,
        ← mod_eq_zero_iff_dvd]

theorem models_binaryBitStepSentence
    (valueBit expected : Bool)
    (M : Type*) [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* PA] :
    M↓[ℒₒᵣ] ⊧ binaryBitStepSentence valueBit expected := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
    ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ PA inferInstance
  cases valueBit with
  | false =>
      cases expected with
      | false =>
          rw [models_iff]
          simp only [binaryBitStepSentence, Semiformula.eval_all,
            LO.LogicalConnective.HomClass.map_imply]
          intro index nextIndex value hnext hbit
          simp [bitDef] at hnext hbit ⊢
          subst nextIndex
          intro _ hsuccessor
          have hsuccessorMem : index + 1 ∈ 2 * value := hsuccessor
          have hprevious : index ∈ value :=
            (LO.FirstOrder.Arithmetic.succ_mem_two_mul_iff
              (i := index) (a := value)).mp hsuccessorMem
          exact hbit
            (LO.FirstOrder.Arithmetic.exp_le_of_mem hprevious)
            hprevious
      | true =>
          rw [models_iff]
          simp only [binaryBitStepSentence, Semiformula.eval_all,
            LO.LogicalConnective.HomClass.map_imply]
          intro index nextIndex value hnext hbit
          simp [bitDef] at hnext hbit ⊢
          subst nextIndex
          have hprevious : index ∈ value := hbit.2
          have hsuccessor : index + 1 ∈ 2 * value :=
            (LO.FirstOrder.Arithmetic.succ_mem_two_mul_iff
              (i := index) (a := value)).mpr hprevious
          exact ⟨LO.FirstOrder.Arithmetic.exp_le_of_mem hsuccessor,
            hsuccessor⟩
  | true =>
      cases expected with
      | false =>
          rw [models_iff]
          simp only [binaryBitStepSentence, Semiformula.eval_all,
            LO.LogicalConnective.HomClass.map_imply]
          intro index nextIndex value hnext hbit
          simp [bitDef] at hnext hbit ⊢
          subst nextIndex
          intro _ hsuccessor
          have hsuccessorMem : index + 1 ∈ 2 * value + 1 :=
            hsuccessor
          have hprevious : index ∈ value :=
            (LO.FirstOrder.Arithmetic.succ_mem_two_mul_succ_iff
              (i := index) (a := value)).mp hsuccessorMem
          exact hbit
            (LO.FirstOrder.Arithmetic.exp_le_of_mem hprevious)
            hprevious
      | true =>
          rw [models_iff]
          simp only [binaryBitStepSentence, Semiformula.eval_all,
            LO.LogicalConnective.HomClass.map_imply]
          intro index nextIndex value hnext hbit
          simp [bitDef] at hnext hbit ⊢
          subst nextIndex
          have hprevious : index ∈ value := hbit.2
          have hsuccessor : index + 1 ∈ 2 * value + 1 :=
            (LO.FirstOrder.Arithmetic.succ_mem_two_mul_succ_iff
              (i := index) (a := value)).mpr hprevious
          exact ⟨LO.FirstOrder.Arithmetic.exp_le_of_mem hsuccessor,
            hsuccessor⟩

theorem binaryBitZeroValueNegativeSentence_provable :
    PA ⊢ binaryBitZeroValueNegativeSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} PA
    binaryBitZeroValueNegativeSentence
  intro M _ _
  exact models_binaryBitZeroValueNegativeSentence M

theorem binaryBitLowSentence_provable (valueBit : Bool) :
    PA ⊢ binaryBitLowSentence valueBit := by
  apply LO.FirstOrder.Arithmetic.complete.{0} PA
    (binaryBitLowSentence valueBit)
  intro M _ _
  exact models_binaryBitLowSentence valueBit M

theorem binaryBitStepSentence_provable
    (valueBit expected : Bool) :
    PA ⊢ binaryBitStepSentence valueBit expected := by
  apply LO.FirstOrder.Arithmetic.complete.{0} PA
    (binaryBitStepSentence valueBit expected)
  intro M _ _
  exact models_binaryBitStepSentence valueBit expected M

noncomputable def binaryBitZeroValueNegativeCertifiedProof :
    CertifiedPAProof
      (Rewriting.emb binaryBitZeroValueNegativeSentence :
        LO.FirstOrder.ArithmeticProposition) :=
  certifiedProofOfProvable
    binaryBitZeroValueNegativeSentence_provable

noncomputable def binaryBitLowCertifiedProof (valueBit : Bool) :
    CertifiedPAProof
      (Rewriting.emb (binaryBitLowSentence valueBit) :
        LO.FirstOrder.ArithmeticProposition) :=
  certifiedProofOfProvable
    (binaryBitLowSentence_provable valueBit)

noncomputable def binaryBitStepCertifiedProof
    (valueBit expected : Bool) :
    CertifiedPAProof
      (Rewriting.emb (binaryBitStepSentence valueBit expected) :
        LO.FirstOrder.ArithmeticProposition) :=
  certifiedProofOfProvable
    (binaryBitStepSentence_provable valueBit expected)

/-! ## Substitution and specialization -/

theorem subst_bitDef_instance
    {sourceArity targetArity : Nat}
    (values : Fin sourceArity →
      LO.FirstOrder.ArithmeticSemiterm Nat targetArity)
    (first second :
      LO.FirstOrder.ArithmeticSemiterm Nat sourceArity) :
    Rewriting.app (Rew.subst values)
        ((Rewriting.emb bitDef.val :
          LO.FirstOrder.ArithmeticSemiformula Nat 2)/[first, second]) =
      (Rewriting.emb bitDef.val :
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

theorem q_subst_bitDef_instance
    {sourceArity targetArity : Nat}
    (values : Fin sourceArity →
      LO.FirstOrder.ArithmeticSemiterm Nat targetArity)
    (first second :
      LO.FirstOrder.ArithmeticSemiterm Nat (sourceArity + 1)) :
    Rewriting.app (Rew.subst values).q
        ((Rewriting.emb bitDef.val :
          LO.FirstOrder.ArithmeticSemiformula Nat 2)/[first, second]) =
      (Rewriting.emb bitDef.val :
        LO.FirstOrder.ArithmeticSemiformula Nat 2)/[
          (Rew.subst values).q first,
          (Rew.subst values).q second] := by
  rw [Rew.q_subst]
  exact subst_bitDef_instance
    (#0 :> Rew.bShift ∘ values) first second

def binaryBitZeroValueNegativeBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  binaryBitLiteralAtTerms false #0 binaryBitZeroTerm

theorem binaryBitZeroValueNegativeSentence_emb_formula :
    (Rewriting.emb binaryBitZeroValueNegativeSentence :
      LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ binaryBitZeroValueNegativeBody := by
  simp [binaryBitZeroValueNegativeSentence,
    binaryBitZeroValueNegativeBody, binaryBitLiteralAtTerms,
    binaryBitAtomAtTerms, binaryBitZeroTerm]
  rw [Rewriting.emb_subst_eq_subst_emb]
  congr 1
  funext index
  cases index using Fin.cases <;> simp [binaryBitZeroTerm]

noncomputable def binaryBitZeroValueNegativeUniversalProof :
    CertifiedPAProof (∀⁰ binaryBitZeroValueNegativeBody) :=
  CertifiedPAProof.cast
    binaryBitZeroValueNegativeSentence_emb_formula
    binaryBitZeroValueNegativeCertifiedProof

theorem binaryBitZeroValueNegativeFinal_formula
    (index : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryBitZeroValueNegativeBody/[index] =
      binaryBitLiteralAtTerms false index binaryBitZeroTerm := by
  simp [binaryBitZeroValueNegativeBody,
    binaryBitLiteralAtTerms, binaryBitAtomAtTerms,
    binaryBitZeroTerm]
  rw [subst_bitDef_instance]
  simp [binaryBitZeroTerm]

noncomputable def binaryBitZeroValueNegativeProof
    (index : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (binaryBitLiteralAtTerms false index binaryBitZeroTerm) :=
  CertifiedPAProof.cast
    (binaryBitZeroValueNegativeFinal_formula index)
    (CertifiedPAProof.specialize
      binaryBitZeroValueNegativeUniversalProof index)

def binaryBitLowBody (valueBit : Bool) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  binaryBitLiteralAtTerms valueBit binaryBitZeroTerm
    (binaryBitValueStepTerm valueBit #0)

theorem binaryBitLowSentence_emb_formula (valueBit : Bool) :
    (Rewriting.emb (binaryBitLowSentence valueBit) :
      LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ binaryBitLowBody valueBit := by
  cases valueBit <;>
    simp [binaryBitLowSentence, binaryBitLowBody,
      binaryBitLiteralAtTerms, binaryBitAtomAtTerms,
      binaryBitValueStepTerm, binaryBitZeroTerm]
  all_goals
    rw [Rewriting.emb_subst_eq_subst_emb]
    congr 1
    funext index
    cases index using Fin.cases <;> simp [binaryBitZeroTerm]

noncomputable def binaryBitLowUniversalProof (valueBit : Bool) :
    CertifiedPAProof (∀⁰ binaryBitLowBody valueBit) :=
  CertifiedPAProof.cast
    (binaryBitLowSentence_emb_formula valueBit)
    (binaryBitLowCertifiedProof valueBit)

theorem binaryBitLowFinal_formula
    (valueBit : Bool)
    (value : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryBitLowBody valueBit)/[value] =
      binaryBitLiteralAtTerms valueBit binaryBitZeroTerm
        (binaryBitValueStepTerm valueBit value) := by
  cases valueBit with
  | false =>
      simp [binaryBitLowBody, binaryBitLiteralAtTerms,
        binaryBitAtomAtTerms, binaryBitValueStepTerm,
        binaryBitZeroTerm]
      rw [subst_bitDef_instance]
      simp [binaryBitZeroTerm]
  | true =>
      simp [binaryBitLowBody, binaryBitLiteralAtTerms,
        binaryBitAtomAtTerms, binaryBitValueStepTerm,
        binaryBitZeroTerm]
      simpa [binaryBitZeroTerm, binaryBitValueStepTerm] using
        (subst_bitDef_instance ![value]
          (binaryBitZeroTerm :
            LO.FirstOrder.ArithmeticSemiterm Nat 1)
          (binaryBitValueStepTerm true
            (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)))

noncomputable def binaryBitLowProof
    (valueBit : Bool)
    (value : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (binaryBitLiteralAtTerms valueBit binaryBitZeroTerm
        (binaryBitValueStepTerm valueBit value)) :=
  CertifiedPAProof.cast
    (binaryBitLowFinal_formula valueBit value)
    (CertifiedPAProof.specialize
      (binaryBitLowUniversalProof valueBit) value)

def binaryBitStepOuterBody (valueBit expected : Bool) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  ∀⁰ ∀⁰ binaryBitStepFormula valueBit expected #2 #1 #0

theorem binaryBitStepSentence_emb_formula
    (valueBit expected : Bool) :
    (Rewriting.emb (binaryBitStepSentence valueBit expected) :
      LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ binaryBitStepOuterBody valueBit expected := by
  cases valueBit <;> cases expected <;>
    simp [binaryBitStepSentence, binaryBitStepOuterBody,
      binaryBitStepFormula, binaryBitIncrementEquality,
      binaryBitLiteralAtTerms, binaryBitAtomAtTerms,
      binaryBitValueStepTerm]
  all_goals
    constructor <;>
      rw [Rewriting.emb_subst_eq_subst_emb] <;>
      congr 1 <;> funext index <;>
      cases index using Fin.cases <;> simp

noncomputable def binaryBitStepUniversalProof
    (valueBit expected : Bool) :
    CertifiedPAProof
      (∀⁰ binaryBitStepOuterBody valueBit expected) :=
  CertifiedPAProof.cast
    (binaryBitStepSentence_emb_formula valueBit expected)
    (binaryBitStepCertifiedProof valueBit expected)

def binaryBitStepMiddleBody
    (valueBit expected : Bool)
    (index : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  ∀⁰ binaryBitStepFormula valueBit expected
    (Rew.bShift (Rew.bShift index)) #1 #0

theorem binaryBitStepAfterFirst_formula
    (valueBit expected : Bool)
    (index : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryBitStepOuterBody valueBit expected)/[index] =
      ∀⁰ binaryBitStepMiddleBody valueBit expected index := by
  cases valueBit <;> cases expected <;>
    simp [binaryBitStepOuterBody, binaryBitStepMiddleBody,
      binaryBitStepFormula, binaryBitIncrementEquality,
      binaryBitLiteralAtTerms, binaryBitAtomAtTerms,
      binaryBitValueStepTerm]
  all_goals
    simp [Rew.q_subst, subst_bitDef_instance,
      substQQ_bvarOne, substQQ_bvarTwo]

def binaryBitStepInnerBody
    (valueBit expected : Bool)
    (index nextIndex :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  binaryBitStepFormula valueBit expected
    (Rew.bShift index) (Rew.bShift nextIndex) #0

theorem binaryBitStepAfterSecond_formula
    (valueBit expected : Bool)
    (index nextIndex :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryBitStepMiddleBody valueBit expected index)/[nextIndex] =
      ∀⁰ binaryBitStepInnerBody valueBit expected
        index nextIndex := by
  cases valueBit <;> cases expected <;>
    simp [binaryBitStepMiddleBody, binaryBitStepInnerBody,
      binaryBitStepFormula, binaryBitIncrementEquality,
      binaryBitLiteralAtTerms, binaryBitAtomAtTerms,
      binaryBitValueStepTerm, substQ_bvarOne]
  all_goals
    constructor <;> rw [q_subst_bitDef_instance] <;>
      simp [substQ_bvarOne]

theorem binaryBitStepFinal_formula
    (valueBit expected : Bool)
    (index nextIndex value :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryBitStepInnerBody valueBit expected
      index nextIndex)/[value] =
      binaryBitStepFormula valueBit expected
        index nextIndex value := by
  cases valueBit <;> cases expected <;>
    simp [binaryBitStepInnerBody, binaryBitStepFormula,
      binaryBitIncrementEquality, binaryBitLiteralAtTerms,
      binaryBitAtomAtTerms, binaryBitValueStepTerm]
  all_goals
    constructor <;> rw [subst_bitDef_instance] <;> simp

noncomputable def binaryBitStepImplication
    (valueBit expected : Bool)
    (index nextIndex value :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (binaryBitStepFormula valueBit expected
        index nextIndex value) :=
  specializeThriceWithCasts
    (binaryBitStepUniversalProof valueBit expected)
    index nextIndex value
    (binaryBitStepAfterFirst_formula valueBit expected index)
    (binaryBitStepAfterSecond_formula
      valueBit expected index nextIndex)
    (binaryBitStepFinal_formula
      valueBit expected index nextIndex value)

/-! ## Closed short-binary compiler -/

theorem binaryBitZeroTerm_eq_shortBinaryNumeralTerm_zero :
    (binaryBitZeroTerm :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) =
      shortBinaryNumeralTerm 0 := by
  simp [binaryBitZeroTerm, shortBinaryNumeralTerm,
    FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero,
    embeddedClosedNumeralZero_eq_paZeroTerm, paZeroTerm,
    arithmeticZeroTerm, Semiterm.Operator.operator,
    Semiterm.Operator.numeral_zero,
    Semiterm.Operator.Zero.term_eq]

theorem binaryBitValueStepTerm_eq_shortBinaryNumeralTerm
    (valueBit : Bool) (high : Nat)
    (hcanonical : high = 0 → valueBit = true) :
    binaryBitValueStepTerm valueBit
        (shortBinaryNumeralTerm high) =
      shortBinaryNumeralTerm (Nat.bit valueBit high) := by
  let highTerm := shortBinaryNumeralTerm high
  cases valueBit with
  | false =>
      have hnonzero : high ≠ 0 := by
        intro hzero
        have himpossible := hcanonical hzero
        simp at himpossible
      have hformula :
          (‘(2 * !!highTerm)’ :
            LO.FirstOrder.ArithmeticSemiterm Nat 0) =
            paMulTerm (Rew.emb (closedNumeralTerm 2)) highTerm := by
        simp [paMulTerm, closedNumeralTerm]
      calc
        binaryBitValueStepTerm false highTerm =
            (‘(2 * !!highTerm)’ :
              LO.FirstOrder.ArithmeticSemiterm Nat 0) := rfl
        _ = paMulTerm (Rew.emb (closedNumeralTerm 2)) highTerm :=
          hformula
        _ = paMulTerm arithmeticTwoTerm highTerm := by
          rw [embeddedClosedNumeralTwo_eq_arithmeticTwoTerm]
        _ = shortBinaryNumeralTerm (Nat.bit false high) :=
          (shortBinaryNumeralTerm_bit_false high hnonzero).symm
  | true =>
      have hformula :
          (‘(2 * !!highTerm + 1)’ :
            LO.FirstOrder.ArithmeticSemiterm Nat 0) =
            paAddTerm
              (paMulTerm (Rew.emb (closedNumeralTerm 2)) highTerm)
              (Rew.emb (closedNumeralTerm 1)) := by
        simp [paMulTerm, paAddTerm, closedNumeralTerm]
      calc
        binaryBitValueStepTerm true highTerm =
            (‘(2 * !!highTerm + 1)’ :
              LO.FirstOrder.ArithmeticSemiterm Nat 0) := rfl
        _ = paAddTerm
              (paMulTerm (Rew.emb (closedNumeralTerm 2)) highTerm)
              (Rew.emb (closedNumeralTerm 1)) := hformula
        _ = paAddTerm
              (paMulTerm arithmeticTwoTerm highTerm) paOneTerm := by
          rw [embeddedClosedNumeralTwo_eq_arithmeticTwoTerm,
            embeddedClosedNumeralOne_eq_paOneTerm]
        _ = shortBinaryNumeralTerm (Nat.bit true high) :=
          (shortBinaryNumeralTerm_bit_true high).symm

noncomputable def binaryBitZeroValueNegativeProofAtShortIndex
    (index : Nat) :
    CertifiedPAProof
      (binaryBitShortLiteralFormula false index 0) := by
  let raw := binaryBitZeroValueNegativeProof
    (shortBinaryNumeralTerm index)
  have hformula :
      binaryBitLiteralAtTerms false
          (shortBinaryNumeralTerm index) binaryBitZeroTerm =
        binaryBitShortLiteralFormula false index 0 := by
    unfold binaryBitShortLiteralFormula
    exact binaryBitLiteralAtTerms_congr false rfl
      binaryBitZeroTerm_eq_shortBinaryNumeralTerm_zero
  exact CertifiedPAProof.cast hformula raw

noncomputable def binaryBitLowProofAtShortNumerals
    (valueBit : Bool) (high : Nat)
    (hcanonical : high = 0 → valueBit = true) :
    CertifiedPAProof
      (binaryBitShortLiteralFormula valueBit 0
        (Nat.bit valueBit high)) := by
  let raw := binaryBitLowProof valueBit
    (shortBinaryNumeralTerm high)
  have hformula :
      binaryBitLiteralAtTerms valueBit binaryBitZeroTerm
          (binaryBitValueStepTerm valueBit
            (shortBinaryNumeralTerm high)) =
        binaryBitShortLiteralFormula valueBit 0
          (Nat.bit valueBit high) := by
    unfold binaryBitShortLiteralFormula
    exact binaryBitLiteralAtTerms_congr valueBit
      binaryBitZeroTerm_eq_shortBinaryNumeralTerm_zero
      (binaryBitValueStepTerm_eq_shortBinaryNumeralTerm
        valueBit high hcanonical)
  exact CertifiedPAProof.cast hformula raw

theorem binaryBitIncrementEquality_short_formula (index : Nat) :
    (“!!(paAddTerm (shortBinaryNumeralTerm index) paOneTerm) =
        !!(shortBinaryNumeralTerm (index + 1))” :
      LO.FirstOrder.ArithmeticProposition) =
      binaryBitIncrementEquality
        (shortBinaryNumeralTerm index)
        (shortBinaryNumeralTerm (index + 1)) := by
  simp [binaryBitIncrementEquality, paAddTerm, paOneTerm,
    arithmeticOneTerm, Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq,
    Semiterm.Operator.numeral_one,
    Semiterm.Operator.One.term_eq, Matrix.fun_eq_vec_two]

noncomputable def binaryBitIncrementProof (index : Nat) :
    CertifiedPAProof
      (binaryBitIncrementEquality
        (shortBinaryNumeralTerm index)
        (shortBinaryNumeralTerm (index + 1))) :=
  CertifiedPAProof.cast
    (binaryBitIncrementEquality_short_formula index)
    (proveBinaryNumeralIncrement index)

noncomputable def binaryBitStepProofAtShortNumerals
    (valueBit expected : Bool)
    (index high : Nat)
    (hcanonical : high = 0 → valueBit = true)
    (previous : CertifiedPAProof
      (binaryBitShortLiteralFormula expected index high)) :
    CertifiedPAProof
      (binaryBitShortLiteralFormula expected (index + 1)
        (Nat.bit valueBit high)) := by
  let indexTerm := shortBinaryNumeralTerm index
  let nextIndexTerm := shortBinaryNumeralTerm (index + 1)
  let highTerm := shortBinaryNumeralTerm high
  let afterIncrement := CertifiedPAProof.modusPonens
    (binaryBitStepImplication valueBit expected
      indexTerm nextIndexTerm highTerm)
    (binaryBitIncrementProof index)
  let raw := CertifiedPAProof.modusPonens afterIncrement previous
  have hformula :
      binaryBitLiteralAtTerms expected nextIndexTerm
          (binaryBitValueStepTerm valueBit highTerm) =
        binaryBitShortLiteralFormula expected (index + 1)
          (Nat.bit valueBit high) := by
    unfold binaryBitShortLiteralFormula
    exact binaryBitLiteralAtTerms_congr expected rfl
      (binaryBitValueStepTerm_eq_shortBinaryNumeralTerm
        valueBit high hcanonical)
  exact CertifiedPAProof.cast hformula raw

noncomputable def proveBinaryBitLiteralAtShortNumerals :
    (value : Nat) → (index : Nat) →
    CertifiedPAProof
      (binaryBitShortLiteralFormula
        (value.testBit index) index value) :=
  Nat.binaryRec'
    (fun index => by
      simpa using binaryBitZeroValueNegativeProofAtShortIndex index)
    (fun valueBit high hcanonical previous index => by
      cases index with
      | zero =>
          simpa [Nat.testBit_bit_zero] using
            binaryBitLowProofAtShortNumerals
              valueBit high hcanonical
      | succ index =>
          simpa [Nat.testBit_bit_succ] using
            binaryBitStepProofAtShortNumerals
              valueBit (high.testBit index) index high hcanonical
              (previous index))

theorem proveBinaryBitLiteralAtShortNumerals_verifier_eq_true
    (index value : Nat) :
    listedCompactCertifiedPAProofVerifier
        (proveBinaryBitLiteralAtShortNumerals value index).code
        (compactFormulaCode
          (binaryBitShortLiteralFormula
            (value.testBit index) index value)) = true :=
  (proveBinaryBitLiteralAtShortNumerals value index).verifier_eq_true

#print axioms binaryBitStepSentence_provable
#print axioms binaryBitStepImplication
#print axioms proveBinaryBitLiteralAtShortNumerals
#print axioms proveBinaryBitLiteralAtShortNumerals_verifier_eq_true

end FoundationCompactPABitMembershipRuleCompiler
