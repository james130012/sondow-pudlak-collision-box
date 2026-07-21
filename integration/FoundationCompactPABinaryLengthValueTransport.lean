import integration.FoundationCompactPABinaryLengthRuleCompiler

/-!
# Fixed PA transport for the value argument of binary length

Foundation's `lengthDef` represents the graph of `compactNatSize`.  This
module fixes a genuine PA proof that the graph is preserved when its value
argument is replaced by an equal closed term.  The fixed three-universal
proof is then specialized, with explicit formula casts, to arbitrary closed
arithmetic terms.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABinaryLengthValueTransport

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExponentialRuleCompiler
open FoundationCompactPABinaryLengthRuleCompiler

def binaryLengthValueTransportSentence :
    LO.FirstOrder.ArithmeticSentence :=
  “∀ size leftValue rightValue,
    leftValue = rightValue →
    (!lengthDef size leftValue →
      !lengthDef size rightValue)”

theorem models_binaryLengthValueTransportSentence
    (M : Type*) [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* PA] :
    M↓[ℒₒᵣ] ⊧ binaryLengthValueTransportSentence := by
  rw [models_iff]
  simp only [binaryLengthValueTransportSentence,
    Semiformula.eval_all, LO.LogicalConnective.HomClass.map_imply]
  intro size leftValue rightValue hvalue
  have hvalue' : leftValue = rightValue := by
    simpa using hvalue
  clear hvalue
  subst rightValue
  exact fun hlength => by simpa using hlength

theorem binaryLengthValueTransportSentence_provable :
    PA ⊢ binaryLengthValueTransportSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} PA
    binaryLengthValueTransportSentence
  intro M _ _
  exact models_binaryLengthValueTransportSentence M

noncomputable def binaryLengthValueTransportCertifiedProof :
    CertifiedPAProof
      (Rewriting.emb binaryLengthValueTransportSentence :
        LO.FirstOrder.ArithmeticProposition) :=
  certifiedProofOfProvable
    binaryLengthValueTransportSentence_provable

def binaryLengthValueTransportOuterBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰ ∀⁰
    (#1 = #0 →
      (!lengthDef #2 #1 → !lengthDef #2 #0))”

theorem binaryLengthValueTransportSentence_emb_formula :
    (Rewriting.emb binaryLengthValueTransportSentence :
      LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ binaryLengthValueTransportOuterBody := by
  simp [binaryLengthValueTransportSentence,
    binaryLengthValueTransportOuterBody]
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

noncomputable def binaryLengthValueTransportUniversalProof :
    CertifiedPAProof (∀⁰ binaryLengthValueTransportOuterBody) :=
  CertifiedPAProof.cast
    binaryLengthValueTransportSentence_emb_formula
    binaryLengthValueTransportCertifiedProof

def binaryLengthValueTransportMiddleBody
    (size : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰
    (#1 = #0 →
      (!lengthDef !!(Rew.bShift (Rew.bShift size)) #1 →
        !lengthDef !!(Rew.bShift (Rew.bShift size)) #0))”

theorem binaryLengthValueTransportAfterFirst_formula
    (size : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryLengthValueTransportOuterBody/[size] =
      ∀⁰ binaryLengthValueTransportMiddleBody size := by
  simp [binaryLengthValueTransportOuterBody,
    binaryLengthValueTransportMiddleBody,
    substQQ_bvarOne, substQQ_bvarTwo]
  constructor
  · rw [Rew.q_subst, Rew.q_subst, subst_lengthDef_instance]
    apply lengthDef_instance_congr <;>
      simp [Rew.comp_app, substQQ_bvarOne, substQQ_bvarTwo]
  · rw [Rew.q_subst, Rew.q_subst, subst_lengthDef_instance]
    apply lengthDef_instance_congr <;>
      simp [Rew.comp_app, substQQ_bvarOne, substQQ_bvarTwo]

def binaryLengthValueTransportInnerBody
    (size leftValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!!(Rew.bShift leftValue) = #0 →
    (!lengthDef !!(Rew.bShift size) !!(Rew.bShift leftValue) →
      !lengthDef !!(Rew.bShift size) #0)”

theorem binaryLengthValueTransportAfterSecond_formula
    (size leftValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryLengthValueTransportMiddleBody size)/[leftValue] =
      ∀⁰ binaryLengthValueTransportInnerBody size leftValue := by
  have hsize :
      (Rew.subst ![leftValue]).q
          (Rew.bShift (Rew.bShift size)) =
        Rew.bShift size := by
    simp
  simp [binaryLengthValueTransportMiddleBody,
    binaryLengthValueTransportInnerBody, substQ_bvarOne, hsize]
  constructor
  · rw [q_subst_lengthDef_instance]
    apply lengthDef_instance_congr <;>
      simp [substQ_bvarOne, hsize]
  · rw [q_subst_lengthDef_instance]
    apply lengthDef_instance_congr <;>
      simp [substQ_bvarOne, hsize]

theorem binaryLengthValueTransportFinal_formula
    (size leftValue rightValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryLengthValueTransportInnerBody
      size leftValue)/[rightValue] =
      (“!!leftValue = !!rightValue →
        (!lengthDef !!size !!leftValue →
          !lengthDef !!size !!rightValue)” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [binaryLengthValueTransportInnerBody]
  constructor
  · rw [subst_lengthDef_instance]
    apply lengthDef_instance_congr <;> simp
  · rw [subst_lengthDef_instance]
    apply lengthDef_instance_congr <;> simp

noncomputable def binaryLengthValueTransportImplication
    (size leftValue rightValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!leftValue = !!rightValue →
        (!lengthDef !!size !!leftValue →
          !lengthDef !!size !!rightValue)” :
        LO.FirstOrder.ArithmeticProposition) :=
  specializeThriceWithCasts
    binaryLengthValueTransportUniversalProof
    size leftValue rightValue
    (binaryLengthValueTransportAfterFirst_formula size)
    (binaryLengthValueTransportAfterSecond_formula size leftValue)
    (binaryLengthValueTransportFinal_formula
      size leftValue rightValue)

theorem binaryLengthValueTransportCertifiedProof_verifier_eq_true :
    listedCompactCertifiedPAProofVerifier
        binaryLengthValueTransportCertifiedProof.code
        (compactFormulaCode
          (Rewriting.emb binaryLengthValueTransportSentence :
            LO.FirstOrder.ArithmeticProposition)) = true :=
  binaryLengthValueTransportCertifiedProof.verifier_eq_true

theorem binaryLengthValueTransportImplication_verifier_eq_true
    (size leftValue rightValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    listedCompactCertifiedPAProofVerifier
        (binaryLengthValueTransportImplication
          size leftValue rightValue).code
        (compactFormulaCode
          (“!!leftValue = !!rightValue →
            (!lengthDef !!size !!leftValue →
              !lengthDef !!size !!rightValue)” :
            LO.FirstOrder.ArithmeticProposition)) = true :=
  (binaryLengthValueTransportImplication
    size leftValue rightValue).verifier_eq_true

#print axioms models_binaryLengthValueTransportSentence
#print axioms binaryLengthValueTransportSentence_provable
#print axioms binaryLengthValueTransportCertifiedProof
#print axioms binaryLengthValueTransportImplication
#print axioms binaryLengthValueTransportCertifiedProof_verifier_eq_true
#print axioms binaryLengthValueTransportImplication_verifier_eq_true

end FoundationCompactPABinaryLengthValueTransport
