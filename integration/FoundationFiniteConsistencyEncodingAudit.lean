import Foundation.FirstOrder.Incompleteness.RestrictedProvability
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
import Mathlib.Data.Nat.Size

/-!
# Foundation finite-consistency encoding audit

This file checks whether the raw-code bit-length lower bound is already forced
by the unary numeral occurring in the conclusion formula.  Such a bound would
be an encoding-size fact, not the Pudlak proof-complexity theorem.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationFiniteConsistencyEncodingAudit

open Encodable

abbrev PA : LO.FirstOrder.ArithmeticTheory :=
  LO.FirstOrder.Arithmetic.Peano

noncomputable def finiteConsistencySentence (e : Nat) :
    LO.FirstOrder.ArithmeticSentence :=
  ∼(LO.FirstOrder.Theory.restrictedProvabilityPred
      (T := PA) e (⊥ : LO.FirstOrder.ArithmeticSentence))

/-- Maximum term depth occurring in a first-order formula.  Unlike Foundation's
logical `Semiformula.complexity`, this measure includes terms in atomic
formulas. -/
def formulaTermDepth {L : Language} {xi : Type*} :
    {n : Nat} → Semiformula L xi n → Nat
  | _, ⊤ => 0
  | _, ⊥ => 0
  | _, Semiformula.rel _ v =>
      Finset.sup Finset.univ (fun i => (v i).complexity)
  | _, Semiformula.nrel _ v =>
      Finset.sup Finset.univ (fun i => (v i).complexity)
  | _, phi ⋏ psi => max (formulaTermDepth phi) (formulaTermDepth psi)
  | _, phi ⋎ psi => max (formulaTermDepth phi) (formulaTermDepth psi)
  | _, ∀⁰ phi => formulaTermDepth phi
  | _, ∃⁰ phi => formulaTermDepth phi

@[simp] theorem formulaTermDepth_top {L : Language} {xi : Type*} {n : Nat} :
    formulaTermDepth (⊤ : Semiformula L xi n) = 0 := rfl

@[simp] theorem formulaTermDepth_bot {L : Language} {xi : Type*} {n : Nat} :
    formulaTermDepth (⊥ : Semiformula L xi n) = 0 := rfl

@[simp] theorem formulaTermDepth_rel
    {L : Language} {xi : Type*} {n k : Nat}
    (r : L.Rel k) (v : Fin k → Semiterm L xi n) :
    formulaTermDepth (Semiformula.rel r v) =
      Finset.sup Finset.univ (fun i => (v i).complexity) := rfl

@[simp] theorem formulaTermDepth_nrel
    {L : Language} {xi : Type*} {n k : Nat}
    (r : L.Rel k) (v : Fin k → Semiterm L xi n) :
    formulaTermDepth (Semiformula.nrel r v) =
      Finset.sup Finset.univ (fun i => (v i).complexity) := rfl

@[simp] theorem formulaTermDepth_eq
    {xi : Type*} {n : Nat}
    (t u : LO.FirstOrder.ArithmeticSemiterm xi n) :
    formulaTermDepth
        (“!!t = !!u” : LO.FirstOrder.ArithmeticSemiformula xi n) =
      max t.complexity u.complexity := by
  simp [Semiformula.Operator.operator,
    Semiformula.Operator.Eq.sentence_eq,
    Matrix.fun_eq_vec_two]
  simp [show (Finset.univ : Finset (Fin 2)) = {0, 1} from by
    ext i
    cases i using Fin.cases <;> simp]

@[simp] theorem formulaTermDepth_and
    {L : Language} {xi : Type*} {n : Nat}
    (phi psi : Semiformula L xi n) :
    formulaTermDepth (phi ⋏ psi) =
      max (formulaTermDepth phi) (formulaTermDepth psi) := rfl

@[simp] theorem formulaTermDepth_or
    {L : Language} {xi : Type*} {n : Nat}
    (phi psi : Semiformula L xi n) :
    formulaTermDepth (phi ⋎ psi) =
      max (formulaTermDepth phi) (formulaTermDepth psi) := rfl

@[simp] theorem formulaTermDepth_all
    {L : Language} {xi : Type*} {n : Nat}
    (phi : Semiformula L xi (n + 1)) :
    formulaTermDepth (∀⁰ phi) = formulaTermDepth phi := rfl

@[simp] theorem formulaTermDepth_exs
    {L : Language} {xi : Type*} {n : Nat}
    (phi : Semiformula L xi (n + 1)) :
    formulaTermDepth (∃⁰ phi) = formulaTermDepth phi := rfl

@[simp] theorem formulaTermDepth_neg
    {L : Language} {xi : Type*} {n : Nat}
    (phi : Semiformula L xi n) :
    formulaTermDepth (∼phi) = formulaTermDepth phi := by
  induction phi using Semiformula.rec' <;>
    simp [formulaTermDepth, *]

@[simp] theorem formulaTermDepth_imp
    {L : Language} {xi : Type*} {n : Nat}
    (phi psi : Semiformula L xi n) :
    formulaTermDepth (phi 🡒 psi) =
      max (formulaTermDepth phi) (formulaTermDepth psi) := by
  simp [Semiformula.imp_eq]

/-- The input term substituted into the exponent graph occurs in its first
atomic equality, so its term depth survives the graph formula. -/
theorem termDepth_le_expDef_subst
    (t : LO.FirstOrder.ArithmeticSemiterm Empty 1) :
    t.complexity ≤
      formulaTermDepth
        (LO.FirstOrder.Arithmetic.expDef.val/[#0, t]) := by
  simp [LO.FirstOrder.Arithmetic.expDef,
    LO.FirstOrder.Arithmetic.exponentialDef,
    formulaTermDepth]

def numeralTerm (e : Nat) :
    LO.FirstOrder.ArithmeticSemiterm Empty 1 :=
  Semiterm.Operator.operator
    (Semiterm.Operator.numeral ℒₒᵣ e) ![]

/-- Foundation's object-language numeral is unary: after the exceptional
cases `0` and `1`, each successor adds one nested addition node. -/
theorem parameter_le_numeralTerm_complexity (e : Nat) :
    e ≤ (numeralTerm e).complexity := by
  induction e with
  | zero => simp [numeralTerm]
  | succ e ih =>
      by_cases he : e = 0
      · subst e
        simp [numeralTerm, Semiterm.Operator.numeral]
      · have hsucc :
            (numeralTerm (e + 1)).complexity =
              max (numeralTerm e).complexity 1 + 1 := by
          simp [numeralTerm,
            Semiterm.Operator.numeral_succ he,
            Semiterm.Operator.operator_comp,
            Matrix.fun_eq_vec_two]
        rw [hsucc]
        exact Nat.add_le_add_right
          (ih.trans (Nat.le_max_left _ _)) 1

/-- Every immediate subterm code is strictly smaller than the enclosing
function-application code in Foundation's concrete encoding. -/
theorem encode_term_lt_encode_func
    {n k : Nat}
    (f : LO.FirstOrder.Language.ORing.Func k)
    (v : Fin k → LO.FirstOrder.ArithmeticSemiterm Empty n)
    (i : Fin k) :
    encode (v i) < encode (Semiterm.func f v) := by
  change Semiterm.toNat (v i) <
    Semiterm.toNat (Semiterm.func f v)
  rw [Semiterm.toNat_func]
  calc
    Semiterm.toNat (v i) <
        Matrix.vecToNat (fun j ↦ Semiterm.toNat (v j)) :=
      Nat.lt_of_eq_natToVec
        (Nat.natToVec_vecToNat
          (fun j ↦ Semiterm.toNat (v j))) i
    _ ≤ Nat.pair (encode f)
        (Matrix.vecToNat (fun j ↦ Semiterm.toNat (v j))) :=
      Nat.right_le_pair _ _
    _ ≤ Nat.pair k (Nat.pair (encode f)
        (Matrix.vecToNat (fun j ↦ Semiterm.toNat (v j)))) :=
      Nat.right_le_pair _ _
    _ ≤ Nat.pair 2 (Nat.pair k (Nat.pair (encode f)
        (Matrix.vecToNat (fun j ↦ Semiterm.toNat (v j))))) :=
      Nat.right_le_pair _ _
    _ < Nat.pair 2 (Nat.pair k (Nat.pair (encode f)
        (Matrix.vecToNat (fun j ↦ Semiterm.toNat (v j))))) + 1 :=
      Nat.lt_succ_self _

/-- Term depth is bounded by Foundation's concrete Gödel code. -/
theorem termComplexity_le_encode
    {n : Nat}
    (t : LO.FirstOrder.ArithmeticSemiterm Empty n) :
    t.complexity ≤ encode t := by
  induction t with
  | bvar x =>
      simp [Semiterm.encode_eq_toNat, Semiterm.toNat]
  | fvar x =>
      exact Empty.elim x
  | func f v ih =>
      rw [Semiterm.complexity_func, Nat.add_one_le_iff]
      apply (Finset.sup_lt_iff (by
        simp [Semiterm.encode_eq_toNat, Semiterm.toNat_func])).2
      intro i hi
      exact (ih i).trans_lt (encode_term_lt_encode_func f v i)

theorem vecEntry_lt_atomCode
    {k : Nat}
    (tag relationCode : Nat)
    (w : Fin k → Nat)
    (i : Fin k) :
    w i < Nat.pair tag
      (Nat.pair k (Nat.pair relationCode (Matrix.vecToNat w))) + 1 := by
  calc
    w i < Matrix.vecToNat w :=
      Nat.lt_of_eq_natToVec (Nat.natToVec_vecToNat w) i
    _ ≤ Nat.pair relationCode (Matrix.vecToNat w) :=
      Nat.right_le_pair _ _
    _ ≤ Nat.pair k
        (Nat.pair relationCode (Matrix.vecToNat w)) :=
      Nat.right_le_pair _ _
    _ ≤ Nat.pair tag
        (Nat.pair k (Nat.pair relationCode (Matrix.vecToNat w))) :=
      Nat.right_le_pair _ _
    _ < Nat.pair tag
        (Nat.pair k (Nat.pair relationCode (Matrix.vecToNat w))) + 1 :=
      Nat.lt_succ_self _

theorem encode_term_lt_encode_rel
    {n k : Nat}
    (R : LO.FirstOrder.Language.ORing.Rel k)
    (v : Fin k → LO.FirstOrder.ArithmeticSemiterm Empty n)
    (i : Fin k) :
    encode (v i) < encode (Semiformula.rel R v) := by
  change Semiterm.toNat (v i) <
    Nat.pair 0 (Nat.pair k (Nat.pair (encode R)
      (Matrix.vecToNat (fun j ↦ Semiterm.toNat (v j))))) + 1
  exact vecEntry_lt_atomCode 0 (encode R)
    (fun j ↦ Semiterm.toNat (v j)) i

theorem encode_term_lt_encode_nrel
    {n k : Nat}
    (R : LO.FirstOrder.Language.ORing.Rel k)
    (v : Fin k → LO.FirstOrder.ArithmeticSemiterm Empty n)
    (i : Fin k) :
    encode (v i) < encode (Semiformula.nrel R v) := by
  change Semiterm.toNat (v i) <
    Nat.pair 1 (Nat.pair k (Nat.pair (encode R)
      (Matrix.vecToNat (fun j ↦ Semiterm.toNat (v j))))) + 1
  exact vecEntry_lt_atomCode 1 (encode R)
    (fun j ↦ Semiterm.toNat (v j)) i

theorem left_lt_binaryCode (tag a b : Nat) :
    a < Nat.pair tag (Nat.pair a b) + 1 := by
  exact lt_of_le_of_lt
    ((Nat.left_le_pair a b).trans
      (Nat.right_le_pair tag (Nat.pair a b)))
    (Nat.lt_succ_self _)

theorem right_lt_binaryCode (tag a b : Nat) :
    b < Nat.pair tag (Nat.pair a b) + 1 := by
  exact lt_of_le_of_lt
    ((Nat.right_le_pair a b).trans
      (Nat.right_le_pair tag (Nat.pair a b)))
    (Nat.lt_succ_self _)

theorem value_lt_unaryCode (tag a : Nat) :
    a < Nat.pair tag a + 1 := by
  exact lt_of_le_of_lt (Nat.right_le_pair tag a) (Nat.lt_succ_self _)

/-- Formula term depth is strictly below Foundation's concrete formula
Gödel code. -/
theorem formulaTermDepth_lt_encode
    {n : Nat}
    (phi : LO.FirstOrder.ArithmeticSemiformula Empty n) :
    formulaTermDepth phi < encode phi := by
  induction phi using Semiformula.rec' with
  | hverum =>
      simp [formulaTermDepth, Semiformula.encode_eq_toNat,
        Semiformula.toNat]
  | hfalsum =>
      simp [formulaTermDepth, Semiformula.encode_eq_toNat,
        Semiformula.toNat]
  | hrel R v =>
      rw [formulaTermDepth_rel]
      apply (Finset.sup_lt_iff (by
        simp [Semiformula.encode_eq_toNat,
          Semiformula.toNat])).2
      intro i hi
      exact (termComplexity_le_encode (v i)).trans_lt
        (encode_term_lt_encode_rel R v i)
  | hnrel R v =>
      rw [formulaTermDepth_nrel]
      apply (Finset.sup_lt_iff (by
        simp [Semiformula.encode_eq_toNat,
          Semiformula.toNat])).2
      intro i hi
      exact (termComplexity_le_encode (v i)).trans_lt
        (encode_term_lt_encode_nrel R v i)
  | hand phi psi ihPhi ihPsi =>
      rw [formulaTermDepth_and]
      apply max_lt
      · exact ihPhi.trans
          (by
            change Semiformula.toNat phi <
              Nat.pair 4
                (Nat.pair (Semiformula.toNat phi)
                  (Semiformula.toNat psi)) + 1
            exact left_lt_binaryCode 4 _ _)
      · exact ihPsi.trans
          (by
            change Semiformula.toNat psi <
              Nat.pair 4
                (Nat.pair (Semiformula.toNat phi)
                  (Semiformula.toNat psi)) + 1
            exact right_lt_binaryCode 4 _ _)
  | hor phi psi ihPhi ihPsi =>
      rw [formulaTermDepth_or]
      apply max_lt
      · exact ihPhi.trans
          (by
            change Semiformula.toNat phi <
              Nat.pair 5
                (Nat.pair (Semiformula.toNat phi)
                  (Semiformula.toNat psi)) + 1
            exact left_lt_binaryCode 5 _ _)
      · exact ihPsi.trans
          (by
            change Semiformula.toNat psi <
              Nat.pair 5
                (Nat.pair (Semiformula.toNat phi)
                  (Semiformula.toNat psi)) + 1
            exact right_lt_binaryCode 5 _ _)
  | hall phi ih =>
      rw [formulaTermDepth_all]
      exact ih.trans (by
        change Semiformula.toNat phi <
          Nat.pair 6 (Semiformula.toNat phi) + 1
        exact value_lt_unaryCode 6 _)
  | hexs phi ih =>
      rw [formulaTermDepth_exs]
      exact ih.trans (by
        change Semiformula.toNat phi <
          Nat.pair 7 (Semiformula.toNat phi) + 1
        exact value_lt_unaryCode 7 _)

/-- The concrete sentence has the expected outer shape: negation of a
universal implication whose antecedent is the exponent graph at `e`. -/
theorem finiteConsistencySentence_shape (e : Nat) :
    ∃ alpha psi : LO.FirstOrder.ArithmeticSemiformula Empty 1,
      finiteConsistencySentence e = ∼(∀⁰ (alpha 🡒 psi)) ∧
      e ≤ formulaTermDepth alpha := by
  simp [finiteConsistencySentence,
    LO.FirstOrder.Theory.restrictedProvabilityPred,
    LO.FirstOrder.Theory.restrictedProvable,
    formulaTermDepth,
    LO.FirstOrder.Arithmetic.expDef,
    LO.FirstOrder.Arithmetic.exponentialDef]
  exact Or.inl (by
    simpa only [numeralTerm] using
      parameter_le_numeralTerm_complexity e)

/-- Probe target: the unary numeral parameter should occur at term depth at
least `e` in the concrete finite-consistency sentence. -/
theorem parameter_le_formulaTermDepth (e : Nat) :
    e ≤ formulaTermDepth (finiteConsistencySentence e) := by
  obtain ⟨alpha, psi, hshape, hdepth⟩ :=
    finiteConsistencySentence_shape e
  rw [hshape, formulaTermDepth_neg, formulaTermDepth_all,
    formulaTermDepth_imp]
  exact hdepth.trans (Nat.le_max_left _ _)

/-- The raw numeric formula code already dominates the cutoff parameter. -/
theorem parameter_lt_encode_finiteConsistencySentence (e : Nat) :
    e < encode (finiteConsistencySentence e) :=
  (parameter_le_formulaTermDepth e).trans_lt
    (formulaTermDepth_lt_encode (finiteConsistencySentence e))

/-- The same fact in the exact quoted-code coordinate used by Foundation's
proof checker. -/
theorem parameter_lt_conclusionCode (e : Nat) :
    e < (⌜finiteConsistencySentence e⌝ : Nat) := by
  simpa [LO.FirstOrder.Sentence.quote_eq_encode] using
    parameter_lt_encode_finiteConsistencySentence e

def ChecksAtBitCutoff (d e : Nat) : Prop :=
  LO.FirstOrder.Arithmetic.Bootstrapping.Proof
    PA d (⌜finiteConsistencySentence e⌝ : Nat)

/-- Foundation stores the concluding singleton sequent inside every raw proof
code, so the proof-code bit length exceeds the numeric conclusion code. -/
theorem conclusionCode_lt_bitSize_of_proof
    {d phi : Nat}
    (hproof :
      LO.FirstOrder.Arithmetic.Bootstrapping.Proof PA d phi) :
    phi < Nat.size d := by
  rw [Nat.lt_size]
  have hsingleton : (2 ^ phi : Nat) = ({phi} : Nat) := by
    rw [LO.FirstOrder.Arithmetic.singleton_def]
    exact (LO.FirstOrder.Arithmetic.exp_nat (n := phi)).symm
  have hfstLe : LO.FirstOrder.Arithmetic.fstIdx d ≤ d := by
    have hfoundation := LO.FirstOrder.Arithmetic.fstIdx_le_self d
    rw [LO.FirstOrder.Arithmetic.le_def] at hfoundation
    rcases hfoundation with hEq | hLt
    · exact hEq.le
    · exact Nat.le_of_lt hLt
  calc
    2 ^ phi = ({phi} : Nat) := hsingleton
    _ = LO.FirstOrder.Arithmetic.fstIdx d := hproof.1.symm
    _ ≤ d := hfstLe

/-- Diagnostic theorem: the apparent degree-one proof lower bound follows
solely from the concrete encodings, before any Buss-Pudlak argument. -/
theorem encodingArtifact_bitSize_lower
    {d e : Nat}
    (hcheck : ChecksAtBitCutoff d e) :
    e < Nat.size d :=
  (parameter_lt_conclusionCode e).trans
    (conclusionCode_lt_bitSize_of_proof hcheck)

theorem encodingArtifact_eventual_powerLower :
    ∀ᶠ e in Filter.atTop,
      ∀ d : Nat, ChecksAtBitCutoff d e →
        e < (Nat.size d) ^ 1 := by
  exact Filter.Eventually.of_forall fun e d hcheck ↦ by
    simpa using encodingArtifact_bitSize_lower hcheck

theorem exists_encodingArtifact_powerLower :
    ∃ degree : Nat,
      0 < degree ∧
      ∀ᶠ e in Filter.atTop,
        ∀ d : Nat, ChecksAtBitCutoff d e →
          e < (Nat.size d) ^ degree :=
  ⟨1, by simp, encodingArtifact_eventual_powerLower⟩

#check parameter_le_formulaTermDepth
#print axioms parameter_le_formulaTermDepth

#check parameter_lt_conclusionCode
#print axioms parameter_lt_conclusionCode

#check exists_encodingArtifact_powerLower
#print axioms exists_encodingArtifact_powerLower

end FoundationFiniteConsistencyEncodingAudit
