import integration.FoundationCompactPABitMembershipRuleCompiler
import integration.FoundationCompactPAExponentialRuleCompiler

/-!
# Certified positive bit-membership transport under argument equalities

These fixed PA theorems transport positive `bitDef` facts across equality in
either argument.  Negative transport can reuse the reverse positive
implication with contextual modus tollens, so no separate negative sentences
are introduced here.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABitMembershipArgumentTransport

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExponentialRuleCompiler
open FoundationCompactPABitMembershipRuleCompiler

/-! ## Index transport -/

def binaryBitIndexTransportSentence :
    LO.FirstOrder.ArithmeticSentence :=
  “∀ leftIndex rightIndex value,
    leftIndex = rightIndex →
    (!bitDef leftIndex value →
      !bitDef rightIndex value)”

theorem models_binaryBitIndexTransportSentence
    (M : Type*) [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* PA] :
    M↓[ℒₒᵣ] ⊧ binaryBitIndexTransportSentence := by
  rw [models_iff]
  simp only [binaryBitIndexTransportSentence,
    Semiformula.eval_all, LO.LogicalConnective.HomClass.map_imply]
  intro leftIndex rightIndex value hindex
  have hindex' : leftIndex = rightIndex := by
    simpa using hindex
  clear hindex
  subst rightIndex
  exact fun hbit => by simpa using hbit

theorem binaryBitIndexTransportSentence_provable :
    PA ⊢ binaryBitIndexTransportSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} PA
    binaryBitIndexTransportSentence
  intro M _ _
  exact models_binaryBitIndexTransportSentence M

noncomputable def binaryBitIndexTransportCertifiedProof :
    CertifiedPAProof
      (Rewriting.emb binaryBitIndexTransportSentence :
        LO.FirstOrder.ArithmeticProposition) :=
  certifiedProofOfProvable
    binaryBitIndexTransportSentence_provable

theorem binaryBitIndexTransportCertifiedProof_verifier_eq_true :
    listedCompactCertifiedPAProofVerifier
        binaryBitIndexTransportCertifiedProof.code
        (compactFormulaCode
          (Rewriting.emb binaryBitIndexTransportSentence :
            LO.FirstOrder.ArithmeticProposition)) = true :=
  binaryBitIndexTransportCertifiedProof.verifier_eq_true

def binaryBitIndexTransportOuterBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰ ∀⁰
    (#2 = #1 →
      (!bitDef #2 #0 → !bitDef #1 #0))”

theorem binaryBitIndexTransportSentence_emb_formula :
    (Rewriting.emb binaryBitIndexTransportSentence :
      LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ binaryBitIndexTransportOuterBody := by
  simp [binaryBitIndexTransportSentence,
    binaryBitIndexTransportOuterBody]
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

noncomputable def binaryBitIndexTransportUniversalProof :
    CertifiedPAProof (∀⁰ binaryBitIndexTransportOuterBody) :=
  CertifiedPAProof.cast
    binaryBitIndexTransportSentence_emb_formula
    binaryBitIndexTransportCertifiedProof

def binaryBitIndexTransportMiddleBody
    (leftIndex : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰
    (!!(Rew.bShift (Rew.bShift leftIndex)) = #1 →
      (!bitDef !!(Rew.bShift (Rew.bShift leftIndex)) #0 →
        !bitDef #1 #0))”

theorem binaryBitIndexTransportAfterFirst_formula
    (leftIndex : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryBitIndexTransportOuterBody/[leftIndex] =
      ∀⁰ binaryBitIndexTransportMiddleBody leftIndex := by
  simp [binaryBitIndexTransportOuterBody,
    binaryBitIndexTransportMiddleBody,
    substQQ_bvarOne, substQQ_bvarTwo]
  constructor <;>
    rw [Rew.q_subst, Rew.q_subst, subst_bitDef_instance] <;>
    congr 1 <;>
    funext index <;>
    cases index using Fin.cases <;>
    simp [Rew.comp_app, substQQ_bvarOne, substQQ_bvarTwo]

def binaryBitIndexTransportInnerBody
    (leftIndex rightIndex :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!!(Rew.bShift leftIndex) = !!(Rew.bShift rightIndex) →
    (!bitDef !!(Rew.bShift leftIndex) #0 →
      !bitDef !!(Rew.bShift rightIndex) #0)”

theorem binaryBitIndexTransportAfterSecond_formula
    (leftIndex rightIndex :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryBitIndexTransportMiddleBody leftIndex)/[rightIndex] =
      ∀⁰ binaryBitIndexTransportInnerBody
        leftIndex rightIndex := by
  have hleft :
      (Rew.subst ![rightIndex]).q
          (Rew.bShift (Rew.bShift leftIndex)) =
        Rew.bShift leftIndex := by
    simp
  simp [binaryBitIndexTransportMiddleBody,
    binaryBitIndexTransportInnerBody, substQ_bvarOne, hleft]
  constructor <;>
    rw [q_subst_bitDef_instance] <;>
    simp [substQ_bvarOne, hleft]

theorem binaryBitIndexTransportFinal_formula
    (leftIndex rightIndex value :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryBitIndexTransportInnerBody
      leftIndex rightIndex)/[value] =
      (“!!leftIndex = !!rightIndex →
        (!bitDef !!leftIndex !!value →
          !bitDef !!rightIndex !!value)” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [binaryBitIndexTransportInnerBody]
  constructor <;>
    rw [subst_bitDef_instance] <;>
    simp

noncomputable def binaryBitIndexTransportImplication
    (leftIndex rightIndex value :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!leftIndex = !!rightIndex →
        (!bitDef !!leftIndex !!value →
          !bitDef !!rightIndex !!value)” :
        LO.FirstOrder.ArithmeticProposition) :=
  specializeThriceWithCasts
    binaryBitIndexTransportUniversalProof
    leftIndex rightIndex value
    (binaryBitIndexTransportAfterFirst_formula leftIndex)
    (binaryBitIndexTransportAfterSecond_formula
      leftIndex rightIndex)
    (binaryBitIndexTransportFinal_formula
      leftIndex rightIndex value)

theorem binaryBitIndexTransportImplication_verifier_eq_true
    (leftIndex rightIndex value :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    listedCompactCertifiedPAProofVerifier
        (binaryBitIndexTransportImplication
          leftIndex rightIndex value).code
        (compactFormulaCode
          (“!!leftIndex = !!rightIndex →
            (!bitDef !!leftIndex !!value →
              !bitDef !!rightIndex !!value)” :
            LO.FirstOrder.ArithmeticProposition)) = true :=
  (binaryBitIndexTransportImplication
    leftIndex rightIndex value).verifier_eq_true

/-! ## Value transport -/

def binaryBitValueTransportSentence :
    LO.FirstOrder.ArithmeticSentence :=
  “∀ index leftValue rightValue,
    leftValue = rightValue →
    (!bitDef index leftValue →
      !bitDef index rightValue)”

theorem models_binaryBitValueTransportSentence
    (M : Type*) [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* PA] :
    M↓[ℒₒᵣ] ⊧ binaryBitValueTransportSentence := by
  rw [models_iff]
  simp only [binaryBitValueTransportSentence,
    Semiformula.eval_all, LO.LogicalConnective.HomClass.map_imply]
  intro index leftValue rightValue hvalue
  have hvalue' : leftValue = rightValue := by
    simpa using hvalue
  clear hvalue
  subst rightValue
  exact fun hbit => by simpa using hbit

theorem binaryBitValueTransportSentence_provable :
    PA ⊢ binaryBitValueTransportSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} PA
    binaryBitValueTransportSentence
  intro M _ _
  exact models_binaryBitValueTransportSentence M

noncomputable def binaryBitValueTransportCertifiedProof :
    CertifiedPAProof
      (Rewriting.emb binaryBitValueTransportSentence :
        LO.FirstOrder.ArithmeticProposition) :=
  certifiedProofOfProvable
    binaryBitValueTransportSentence_provable

theorem binaryBitValueTransportCertifiedProof_verifier_eq_true :
    listedCompactCertifiedPAProofVerifier
        binaryBitValueTransportCertifiedProof.code
        (compactFormulaCode
          (Rewriting.emb binaryBitValueTransportSentence :
            LO.FirstOrder.ArithmeticProposition)) = true :=
  binaryBitValueTransportCertifiedProof.verifier_eq_true

def binaryBitValueTransportOuterBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰ ∀⁰
    (#1 = #0 →
      (!bitDef #2 #1 → !bitDef #2 #0))”

theorem binaryBitValueTransportSentence_emb_formula :
    (Rewriting.emb binaryBitValueTransportSentence :
      LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ binaryBitValueTransportOuterBody := by
  simp [binaryBitValueTransportSentence,
    binaryBitValueTransportOuterBody]
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

noncomputable def binaryBitValueTransportUniversalProof :
    CertifiedPAProof (∀⁰ binaryBitValueTransportOuterBody) :=
  CertifiedPAProof.cast
    binaryBitValueTransportSentence_emb_formula
    binaryBitValueTransportCertifiedProof

def binaryBitValueTransportMiddleBody
    (index : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰
    (#1 = #0 →
      (!bitDef !!(Rew.bShift (Rew.bShift index)) #1 →
        !bitDef !!(Rew.bShift (Rew.bShift index)) #0))”

theorem binaryBitValueTransportAfterFirst_formula
    (index : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryBitValueTransportOuterBody/[index] =
      ∀⁰ binaryBitValueTransportMiddleBody index := by
  simp [binaryBitValueTransportOuterBody,
    binaryBitValueTransportMiddleBody,
    substQQ_bvarOne, substQQ_bvarTwo]
  constructor <;>
    rw [Rew.q_subst, Rew.q_subst, subst_bitDef_instance] <;>
    simp [substQQ_bvarOne, substQQ_bvarTwo]

def binaryBitValueTransportInnerBody
    (index leftValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!!(Rew.bShift leftValue) = #0 →
    (!bitDef !!(Rew.bShift index) !!(Rew.bShift leftValue) →
      !bitDef !!(Rew.bShift index) #0)”

theorem binaryBitValueTransportAfterSecond_formula
    (index leftValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryBitValueTransportMiddleBody index)/[leftValue] =
      ∀⁰ binaryBitValueTransportInnerBody
        index leftValue := by
  have hindex :
      (Rew.subst ![leftValue]).q
          (Rew.bShift (Rew.bShift index)) =
        Rew.bShift index := by
    simp
  simp [binaryBitValueTransportMiddleBody,
    binaryBitValueTransportInnerBody, substQ_bvarOne, hindex]
  constructor <;>
    rw [q_subst_bitDef_instance] <;>
    simp [substQ_bvarOne, hindex]

theorem binaryBitValueTransportFinal_formula
    (index leftValue rightValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryBitValueTransportInnerBody
      index leftValue)/[rightValue] =
      (“!!leftValue = !!rightValue →
        (!bitDef !!index !!leftValue →
          !bitDef !!index !!rightValue)” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [binaryBitValueTransportInnerBody]
  constructor <;>
    rw [subst_bitDef_instance] <;>
    simp

noncomputable def binaryBitValueTransportImplication
    (index leftValue rightValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!leftValue = !!rightValue →
        (!bitDef !!index !!leftValue →
          !bitDef !!index !!rightValue)” :
        LO.FirstOrder.ArithmeticProposition) :=
  specializeThriceWithCasts
    binaryBitValueTransportUniversalProof
    index leftValue rightValue
    (binaryBitValueTransportAfterFirst_formula index)
    (binaryBitValueTransportAfterSecond_formula
      index leftValue)
    (binaryBitValueTransportFinal_formula
      index leftValue rightValue)

theorem binaryBitValueTransportImplication_verifier_eq_true
    (index leftValue rightValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    listedCompactCertifiedPAProofVerifier
        (binaryBitValueTransportImplication
          index leftValue rightValue).code
        (compactFormulaCode
          (“!!leftValue = !!rightValue →
            (!bitDef !!index !!leftValue →
              !bitDef !!index !!rightValue)” :
            LO.FirstOrder.ArithmeticProposition)) = true :=
  (binaryBitValueTransportImplication
    index leftValue rightValue).verifier_eq_true

#print axioms models_binaryBitIndexTransportSentence
#print axioms binaryBitIndexTransportSentence_provable
#print axioms binaryBitIndexTransportCertifiedProof
#print axioms binaryBitIndexTransportCertifiedProof_verifier_eq_true
#print axioms binaryBitIndexTransportImplication
#print axioms binaryBitIndexTransportImplication_verifier_eq_true
#print axioms models_binaryBitValueTransportSentence
#print axioms binaryBitValueTransportSentence_provable
#print axioms binaryBitValueTransportCertifiedProof
#print axioms binaryBitValueTransportCertifiedProof_verifier_eq_true
#print axioms binaryBitValueTransportImplication
#print axioms binaryBitValueTransportImplication_verifier_eq_true

end FoundationCompactPABitMembershipArgumentTransport
