import Foundation.FirstOrder.Incompleteness.RestrictedProvability
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Size

/-!
# Succinct finite-consistency target

This file replaces Foundation's unary cutoff numeral by an explicit short term
for `2^(amplification * n)`.  The first target is exact standard-model
calibration; no proof-length lower bound is assumed here.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationSuccinctFiniteConsistencyTarget

abbrev PA : LO.FirstOrder.ArithmeticTheory :=
  LO.FirstOrder.Arithmetic.Peano

def closedNumeralTerm (k : Nat) :
    LO.FirstOrder.ArithmeticSemiterm Empty 0 :=
  Semiterm.Operator.operator
    (Semiterm.Operator.numeral ℒₒᵣ k) ![]

/-- A linear-depth term for `2^m`; unlike the built-in numeral for `2^m`, it
does not contain `2^m` unary successor/addition nodes. -/
def powTwoTerm : Nat → LO.FirstOrder.ArithmeticSemiterm Empty 0
  | 0 => closedNumeralTerm 1
  | m + 1 =>
      Semiterm.Operator.Mul.mul.operator
        ![closedNumeralTerm 2, powTwoTerm m]

@[simp] theorem val_closedNumeralTerm (k : Nat) :
    (closedNumeralTerm k).val ![] Empty.elim = k := by
  simp [closedNumeralTerm]

@[simp] theorem val_powTwoTerm (m : Nat) :
    (powTwoTerm m).val ![] Empty.elim = 2 ^ m := by
  induction m with
  | zero => simp [powTwoTerm]
  | succ m ih =>
      simp [powTwoTerm, ih, pow_succ, Nat.mul_comm]

@[simp] theorem complexity_closedNumeralTerm_one :
    (closedNumeralTerm 1).complexity = 1 := by
  simp [closedNumeralTerm, Semiterm.Operator.numeral_one]

@[simp] theorem complexity_closedNumeralTerm_two :
    (closedNumeralTerm 2).complexity = 2 := by
  simp [closedNumeralTerm, Semiterm.Operator.numeral]

theorem powTwoTerm_complexity_le (m : Nat) :
    (powTwoTerm m).complexity ≤ m + 2 := by
  induction m with
  | zero => simp [powTwoTerm]
  | succ m ih =>
      rw [powTwoTerm, Semiterm.complexity_mul,
        complexity_closedNumeralTerm_two]
      have hmax : max 2 (powTwoTerm m).complexity ≤ m + 2 :=
        max_le (by omega) ih
      omega

def bottomCodeTerm : LO.FirstOrder.ArithmeticSemiterm Empty 0 :=
  (⌜(⊥ : LO.FirstOrder.ArithmeticSentence)⌝ :
    LO.FirstOrder.ArithmeticSemiterm Empty 0)

@[simp] theorem val_bottomSubst_q_bvar_one (x : Nat) :
    ((((Rew.subst ![bottomCodeTerm]).q)
        (#1 : LO.FirstOrder.ArithmeticSemiterm Empty 2)).val
      ![x] Empty.elim) =
      (⌜(⊥ : LO.FirstOrder.ArithmeticSentence)⌝ : Nat) := by
  have hterm :
      ((Rew.subst ![bottomCodeTerm]).q)
          (#1 : LO.FirstOrder.ArithmeticSemiterm Empty 2) =
        Rew.bShift bottomCodeTerm := by
    simpa using
      (Rew.q_bvar_succ
        (Rew.subst ![bottomCodeTerm]) (0 : Fin 1))
  rw [hterm]
  simp [bottomCodeTerm]

/-- Foundation's restricted provability formula with an explicit closed term
as the exponent parameter. -/
noncomputable def restrictedProvableAtTerm
    (t : LO.FirstOrder.ArithmeticSemiterm Empty 0) :
    HierarchySymbol.piOne.Semisentence 1 :=
  .mkPi “phi. ∀ E,
    !expDef E
      !!(Rew.bShift (Rew.bShift t)) →
    ∃ d < E, !(Bootstrapping.proof PA).pi d phi”

noncomputable def succinctFiniteConsistencySentence
    (amplification n : Nat) : LO.FirstOrder.ArithmeticSentence :=
  ∼(restrictedProvableAtTerm
      (powTwoTerm (amplification * n))).val/[
        ⌜(⊥ : LO.FirstOrder.ArithmeticSentence)⌝]

/-- Exact intended standard-model meaning of the succinct sentence. -/
theorem models_succinctFiniteConsistencySentence_iff
    (amplification n : Nat) :
    Nat↓[ℒₒᵣ] ⊧ succinctFiniteConsistencySentence amplification n ↔
      ∀ d : Nat, Nat.size d ≤ 2 ^ (amplification * n) →
        ¬ LO.FirstOrder.Arithmetic.Bootstrapping.Proof
          PA d (⌜(⊥ : LO.FirstOrder.ArithmeticSentence)⌝ : Nat) := by
  have hcode (x : Nat) :
      ((((Rew.subst
          ![(⌜(⊥ : LO.FirstOrder.ArithmeticSentence)⌝ :
            LO.FirstOrder.ArithmeticSemiterm Empty 0)]).q)
          (#1 : LO.FirstOrder.ArithmeticSemiterm Empty 2)).val
        ![x] Empty.elim) =
        (⌜(⊥ : LO.FirstOrder.ArithmeticSentence)⌝ : Nat) := by
    simpa only [bottomCodeTerm] using
      val_bottomSubst_q_bvar_one x
  simp [succinctFiniteConsistencySentence,
    restrictedProvableAtTerm,
    models_iff,
    Nat.size_le,
    Semiformula.eval_rew,
    Rew.subst_bvar,
    Semiterm.val_bShift',
    Matrix.empty_eq,
    Function.comp_def]
  simp only [hcode]

theorem no_standard_proof_falsum (d : Nat) :
    ¬ LO.FirstOrder.Arithmetic.Bootstrapping.Proof
      PA d (⌜(⊥ : LO.FirstOrder.ArithmeticSentence)⌝ : Nat) := by
  intro hd
  have hprov : PA ⊢ (⊥ : LO.FirstOrder.ArithmeticSentence) :=
    LO.FirstOrder.Arithmetic.Bootstrapping.provable_of_standard_proof
      (T := PA) (V := Nat) (n := d) (by simpa using hd)
  exact LO.Entailment.Consistent.not_bot (𝓢 := PA) inferInstance hprov

theorem models_succinctFiniteConsistencySentence
    (amplification n : Nat) :
    Nat↓[ℒₒᵣ] ⊧ succinctFiniteConsistencySentence amplification n := by
  rw [models_succinctFiniteConsistencySentence_iff]
  intro d hd
  exact no_standard_proof_falsum d

theorem succinctFiniteConsistencySentence_sigmaOne
    (amplification n : Nat) :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 1
      (succinctFiniteConsistencySentence amplification n) := by
  simp [succinctFiniteConsistencySentence,
    restrictedProvableAtTerm]

theorem provable_succinctFiniteConsistencySentence
    (amplification n : Nat) :
    PA ⊢ succinctFiniteConsistencySentence amplification n :=
  LO.FirstOrder.Arithmetic.sigma_one_completeness
    (T := PA)
    (succinctFiniteConsistencySentence_sigmaOne amplification n)
    (models_succinctFiniteConsistencySentence amplification n)

noncomputable def succinctFiniteConsistencyProof
    (amplification n : Nat) :
    PA ⊢! succinctFiniteConsistencySentence amplification n :=
  Classical.choice
    (provable_succinctFiniteConsistencySentence amplification n)

def Checks (amplification d n : Nat) : Prop :=
  LO.FirstOrder.Arithmetic.Bootstrapping.Proof
    PA d (⌜succinctFiniteConsistencySentence amplification n⌝ : Nat)

theorem checks_complete (amplification n : Nat) :
    ∃ d : Nat, Checks amplification d n := by
  refine ⟨⌜succinctFiniteConsistencyProof amplification n⌝, ?_⟩
  exact LO.FirstOrder.proof_of_quote_proof
    (succinctFiniteConsistencyProof amplification n)

/-- Number of symbols in a first-order term tree. -/
def termSymbolCount {L : Language} {xi : Type*} {n : Nat} :
    Semiterm L xi n → Nat
  | #_ => 1
  | &_ => 1
  | Semiterm.func _ v =>
      1 + Finset.univ.sum (fun i ↦ termSymbolCount (v i))

@[simp] theorem termSymbolCount_closedNumeralTerm_one :
    termSymbolCount (closedNumeralTerm 1) = 1 := by
  simp [closedNumeralTerm, Semiterm.Operator.numeral_one,
    Semiterm.Operator.operator, Semiterm.Operator.One.term_eq,
    termSymbolCount, Rew.func]

@[simp] theorem termSymbolCount_closedNumeralTerm_two :
    termSymbolCount (closedNumeralTerm 2) = 3 := by
  simp [closedNumeralTerm, Semiterm.Operator.numeral,
    Semiterm.Operator.foldr, Semiterm.Operator.comp,
    Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    termSymbolCount, Rew.func]
  simp [Semiterm.Operator.One.term_eq, termSymbolCount]

@[simp] theorem termSymbolCount_mul
    {xi : Type*} {n : Nat}
    (t u : LO.FirstOrder.ArithmeticSemiterm xi n) :
    termSymbolCount
        (Semiterm.Operator.Mul.mul.operator ![t, u]) =
      1 + termSymbolCount t + termSymbolCount u := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Mul.term_eq,
    termSymbolCount, Rew.func,
    show (Finset.univ : Finset (Fin 2)) = {0, 1} from by
    ext i
    cases i using Fin.cases <;> simp]
  omega

theorem powTwoTerm_symbolCount (m : Nat) :
    termSymbolCount (powTwoTerm m) = 4 * m + 1 := by
  induction m with
  | zero => simp [powTwoTerm]
  | succ m ih =>
      simp [powTwoTerm, ih]
      omega

/-- Number of symbols in a first-order formula tree, including all terms in
atomic formulas. -/
def formulaSymbolCount {L : Language} {xi : Type*} :
    {n : Nat} → Semiformula L xi n → Nat
  | _, Semiformula.rel _ v =>
      1 + Finset.univ.sum (fun i ↦ termSymbolCount (v i))
  | _, Semiformula.nrel _ v =>
      1 + Finset.univ.sum (fun i ↦ termSymbolCount (v i))
  | _, ⊤ => 1
  | _, ⊥ => 1
  | _, phi ⋏ psi =>
      1 + formulaSymbolCount phi + formulaSymbolCount psi
  | _, phi ⋎ psi =>
      1 + formulaSymbolCount phi + formulaSymbolCount psi
  | _, ∀⁰ phi => 1 + formulaSymbolCount phi
  | _, ∃⁰ phi => 1 + formulaSymbolCount phi

def sequentSymbolCount {L : Language}
    (Gamma : Finset (LO.FirstOrder.Proposition L)) : Nat :=
  Gamma.sum (fun phi ↦ formulaSymbolCount phi)

/-- Structural length of a real `Derivation2`: every inference contributes
its displayed conclusion sequent; existential introduction also contributes
its witness term. -/
def derivationSymbolLength
    {L : Language} [L.DecidableEq] {T : LO.FirstOrder.Theory L} :
    {Gamma : Finset (LO.FirstOrder.Proposition L)} →
      LO.FirstOrder.Derivation2 T Gamma → Nat
  | _, .closed Gamma _ _ _ => 1 + sequentSymbolCount Gamma
  | Gamma, .axm _ _ _ => 1 + sequentSymbolCount Gamma
  | Gamma, .verum _ => 1 + sequentSymbolCount Gamma
  | Gamma, .and _ dp dq =>
      1 + sequentSymbolCount Gamma +
        derivationSymbolLength dp + derivationSymbolLength dq
  | Gamma, .or _ dp =>
      1 + sequentSymbolCount Gamma + derivationSymbolLength dp
  | Gamma, .all _ dp =>
      1 + sequentSymbolCount Gamma + derivationSymbolLength dp
  | Gamma, .exs _ t dp =>
      1 + sequentSymbolCount Gamma + termSymbolCount t +
        derivationSymbolLength dp
  | Gamma, .wk dp _ =>
      1 + sequentSymbolCount Gamma + derivationSymbolLength dp
  | _, .shift (Γ := Delta) dp =>
      1 + sequentSymbolCount (Delta.image Rewriting.shift) +
        derivationSymbolLength dp
  | Gamma, .cut dp dn =>
      1 + sequentSymbolCount Gamma +
        derivationSymbolLength dp + derivationSymbolLength dn

/-- A checker-accepted raw code always yields a real derivation of exactly the
same succinct sentence.  No length comparison is asserted here. -/
theorem checks_to_real_derivation
    {amplification d n : Nat}
    (hcheck : Checks amplification d n) :
    Nonempty
      (PA ⊢!₂!
        (succinctFiniteConsistencySentence amplification n :
          LO.FirstOrder.ArithmeticProposition)) := by
  apply (LO.FirstOrder.provable_iff_derivable2
    (T := PA)).mp
  exact LO.FirstOrder.Arithmetic.Bootstrapping.provable_of_standard_proof
    (T := PA) (V := Nat) (n := d) (by simpa [Checks] using hcheck)

theorem structuralProofLength_exists (amplification n : Nat) :
    ∃ k : Nat,
      ∃ b :
        PA ⊢!₂!
          (succinctFiniteConsistencySentence amplification n :
            LO.FirstOrder.ArithmeticProposition),
        derivationSymbolLength b = k := by
  have hproof :
      Nonempty
        (PA ⊢!₂!
          (succinctFiniteConsistencySentence amplification n :
            LO.FirstOrder.ArithmeticProposition)) :=
    (LO.FirstOrder.provable_iff_derivable2 (T := PA)).mp
      (provable_succinctFiniteConsistencySentence amplification n)
  rcases hproof with ⟨b⟩
  exact ⟨derivationSymbolLength b, b, rfl⟩

noncomputable def minStructuralProofLength
    (amplification n : Nat) : Nat :=
  by
    classical
    exact Nat.find (structuralProofLength_exists amplification n)

theorem minStructuralProofLength_spec (amplification n : Nat) :
    ∃ b :
      PA ⊢!₂!
        (succinctFiniteConsistencySentence amplification n :
          LO.FirstOrder.ArithmeticProposition),
      derivationSymbolLength b =
        minStructuralProofLength amplification n := by
  classical
  exact Nat.find_spec (structuralProofLength_exists amplification n)

theorem minStructuralProofLength_le
    (amplification n : Nat)
    (b :
      PA ⊢!₂!
        (succinctFiniteConsistencySentence amplification n :
          LO.FirstOrder.ArithmeticProposition)) :
    minStructuralProofLength amplification n ≤
      derivationSymbolLength b := by
  classical
  exact Nat.find_min'
    (structuralProofLength_exists amplification n)
    ⟨b, rfl⟩

/-! ## Explicit binary serialization -/

/-- Prefix code for a natural number.  Data bits are escaped as `10`/`11`
and the code is terminated by `00`. -/
def binaryNatCode (n : Nat) : List Bool :=
  n.bits.flatMap (fun bit ↦ [true, bit]) ++ [false, false]

/-- Decoder for one `binaryNatCode` prefix, returning the unconsumed suffix. -/
def decodeBinaryNat : List Bool → Option (Nat × List Bool)
  | false :: false :: rest => some (0, rest)
  | true :: bit :: rest => do
      let (n, suffix) ← decodeBinaryNat rest
      pure (Nat.bit bit n, suffix)
  | _ => none

@[simp] theorem decodeBinaryNat_binaryNatCode_append
    (n : Nat) (suffix : List Bool) :
    decodeBinaryNat (binaryNatCode n ++ suffix) =
      some (n, suffix) := by
  induction n using Nat.binaryRec' with
  | zero => simp [binaryNatCode, decodeBinaryNat]
  | bit bit n hn ih =>
      have ih' :
          decodeBinaryNat
              (n.bits.flatMap (fun bit ↦ [true, bit]) ++
                false :: false :: suffix) =
            some (n, suffix) := by
        simpa [binaryNatCode, List.append_assoc] using ih
      simp [binaryNatCode, Nat.bits_append_bit n bit hn,
        decodeBinaryNat, ih']

/-- Encode an arbitrary finite bit string as the low-to-high bits below a
terminal `1`.  Unlike nested pairing, this adds exactly one bit. -/
def packBinaryString : List Bool → Nat
  | [] => 1
  | bit :: bits => Nat.bit bit (packBinaryString bits)

theorem packBinaryString_ne_zero (bits : List Bool) :
    packBinaryString bits ≠ 0 := by
  induction bits with
  | nil => simp [packBinaryString]
  | cons bit bits ih =>
      cases bit <;> simp [packBinaryString, ih]

@[simp] theorem bits_packBinaryString (bits : List Bool) :
    (packBinaryString bits).bits = bits ++ [true] := by
  induction bits with
  | nil => simp [packBinaryString]
  | cons bit bits ih =>
      rw [packBinaryString,
        Nat.bits_append_bit _ bit
          (fun hzero ↦ (packBinaryString_ne_zero bits hzero).elim)]
      simp [ih]

theorem packBinaryString_injective :
    Function.Injective packBinaryString := by
  intro left right hcode
  have hbits := congrArg Nat.bits hcode
  simpa using List.append_left_injective [true]
    (show left ++ [true] = right ++ [true] by simpa using hbits)

@[simp] theorem size_packBinaryString (bits : List Bool) :
    Nat.size (packBinaryString bits) = bits.length + 1 := by
  rw [← Nat.size_eq_bits_len]
  simp

/-- Prefix serialization of an arithmetic term. -/
def binaryTermCode {n : Nat} :
    LO.FirstOrder.ArithmeticSemiterm Nat n → List Bool
  | #i => binaryNatCode 0 ++ binaryNatCode i.val
  | &x => binaryNatCode 1 ++ binaryNatCode x
  | Semiterm.func (arity := k) f v =>
      binaryNatCode 2 ++ binaryNatCode k ++
        binaryNatCode (Encodable.encode f) ++
        (List.ofFn fun i ↦ binaryTermCode (v i)).flatten

/-- Prefix serialization of an arithmetic formula. -/
def binaryFormulaCode :
    {n : Nat} →
      LO.FirstOrder.ArithmeticSemiformula Nat n → List Bool
  | _, Semiformula.rel (arity := k) R v =>
      binaryNatCode 0 ++ binaryNatCode k ++
        binaryNatCode (Encodable.encode R) ++
        (List.ofFn fun i ↦ binaryTermCode (v i)).flatten
  | _, Semiformula.nrel (arity := k) R v =>
      binaryNatCode 1 ++ binaryNatCode k ++
        binaryNatCode (Encodable.encode R) ++
        (List.ofFn fun i ↦ binaryTermCode (v i)).flatten
  | _, ⊤ => binaryNatCode 2
  | _, ⊥ => binaryNatCode 3
  | _, phi ⋏ psi =>
      binaryNatCode 4 ++ binaryFormulaCode phi ++ binaryFormulaCode psi
  | _, phi ⋎ psi =>
      binaryNatCode 5 ++ binaryFormulaCode phi ++ binaryFormulaCode psi
  | _, ∀⁰ phi => binaryNatCode 6 ++ binaryFormulaCode phi
  | _, ∃⁰ phi => binaryNatCode 7 ++ binaryFormulaCode phi

def binarySequentCode
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition) : List Bool :=
  binaryNatCode Gamma.card ++
    Gamma.toList.flatMap binaryFormulaCode

/-- A concrete binary string for every real PA `Derivation2`.  Proof fields
are erased, while rule tags, displayed sequents, principal syntax, witnesses,
and recursive premises are retained. -/
def binaryDerivationCode :
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition} →
      LO.FirstOrder.Derivation2 PA Gamma → List Bool
  | _, .closed Gamma phi _ _ =>
      binaryNatCode 0 ++ binarySequentCode Gamma ++
        binaryFormulaCode phi
  | Gamma, .axm phi _ _ =>
      binaryNatCode 1 ++ binarySequentCode Gamma ++
        binaryFormulaCode
          (Rewriting.emb phi : LO.FirstOrder.ArithmeticProposition)
  | Gamma, .verum _ =>
      binaryNatCode 2 ++ binarySequentCode Gamma
  | Gamma, .and (φ := phi) (ψ := psi) _ dp dq =>
      binaryNatCode 3 ++ binarySequentCode Gamma ++
        binaryFormulaCode phi ++ binaryFormulaCode psi ++
        binaryDerivationCode dp ++ binaryDerivationCode dq
  | Gamma, .or (φ := phi) (ψ := psi) _ dp =>
      binaryNatCode 4 ++ binarySequentCode Gamma ++
        binaryFormulaCode phi ++ binaryFormulaCode psi ++
        binaryDerivationCode dp
  | Gamma, .all (φ := phi) _ dp =>
      binaryNatCode 5 ++ binarySequentCode Gamma ++
        binaryFormulaCode phi ++ binaryDerivationCode dp
  | Gamma, .exs (φ := phi) _ t dp =>
      binaryNatCode 6 ++ binarySequentCode Gamma ++
        binaryFormulaCode phi ++ binaryTermCode t ++
        binaryDerivationCode dp
  | Gamma, .wk dp _ =>
      binaryNatCode 7 ++ binarySequentCode Gamma ++
        binaryDerivationCode dp
  | _, .shift (Γ := Delta) dp =>
      binaryNatCode 8 ++
        binarySequentCode (Delta.image Rewriting.shift) ++
        binaryDerivationCode dp
  | Gamma, .cut (φ := phi) dp dn =>
      binaryNatCode 9 ++ binarySequentCode Gamma ++
      binaryFormulaCode phi ++
        binaryDerivationCode dp ++ binaryDerivationCode dn

/-! ## Executable parser into Foundation's checked raw codes -/

/-- Parse exactly `count` consecutive values with a prefix parser. -/
def decodeMany {alpha : Type*}
    (decode : List Bool → Option (alpha × List Bool)) :
    Nat → List Bool → Option (List alpha × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (head, bits) ← decode bits
      let (tail, bits) ← decodeMany decode count bits
      pure (head :: tail, bits)

/-- Foundation's vector code, written as a computable list fold. -/
def rawVectorCode : List Nat → Nat
  | [] => 0
  | head :: tail => Nat.pair head (rawVectorCode tail) + 1

theorem decodeMany_flatMap_append
    {alpha : Type*}
    (decode : List Bool → Option (alpha × List Bool))
    (encode : alpha → List Bool)
    (items : List alpha) (suffix : List Bool)
    (hdecode : ∀ item ∈ items, ∀ rest,
      decode (encode item ++ rest) = some (item, rest)) :
    decodeMany decode items.length
        (items.flatMap encode ++ suffix) =
      some (items, suffix) := by
  induction items with
  | nil => simp [decodeMany]
  | cons head tail ih =>
      simp only [List.length_cons, List.flatMap_cons]
      rw [decodeMany]
      rw [List.append_assoc]
      rw [hdecode head (by simp)
        (tail.flatMap encode ++ suffix)]
      simp [ih (fun item hitem rest ↦
        hdecode item (by simp [hitem]) rest)]

theorem decodeMany_map_flatMap_append
    {alpha beta : Type*}
    (decode : List Bool → Option (beta × List Bool))
    (encode : alpha → List Bool) (value : alpha → beta)
    (items : List alpha) (suffix : List Bool)
    (hdecode : ∀ item ∈ items, ∀ rest,
      decode (encode item ++ rest) = some (value item, rest)) :
    decodeMany decode items.length
        (items.flatMap encode ++ suffix) =
      some (items.map value, suffix) := by
  induction items with
  | nil => simp [decodeMany]
  | cons head tail ih =>
      simp only [List.length_cons, List.flatMap_cons, List.map_cons]
      rw [decodeMany, List.append_assoc]
      rw [hdecode head (by simp)
        (tail.flatMap encode ++ suffix)]
      simp [ih (fun item hitem rest ↦
        hdecode item (by simp [hitem]) rest)]

theorem rawVectorCode_ofFn {arity : Nat}
    (v : Fin arity → Nat) :
    rawVectorCode (List.ofFn v) = Matrix.vecToNat v := by
  induction arity with
  | zero => simp [rawVectorCode, Matrix.vecToNat, Matrix.empty_eq]
  | succ arity ih =>
      rw [List.ofFn_succ, Matrix.vecToNat, Matrix.foldr_succ]
      simp [rawVectorCode, ih, Matrix.vecHead, Matrix.vecTail,
        Matrix.vecToNat, Function.comp_def]

/-- Parse a structurally serialized term and return its Foundation Goedel
code.  Fuel controls only recursive syntax depth; malformed strings return
`none`. -/
def decodeBinaryTermRaw :
    Nat → List Bool → Option (Nat × List Bool)
  | 0, _ => none
  | fuel + 1, bits => do
      let (tag, bits) ← decodeBinaryNat bits
      match tag with
      | 0 => do
          let (index, bits) ← decodeBinaryNat bits
          pure (Nat.pair 0 index + 1, bits)
      | 1 => do
          let (freeIndex, bits) ← decodeBinaryNat bits
          pure (Nat.pair 1 freeIndex + 1, bits)
      | 2 => do
          let (arity, bits) ← decodeBinaryNat bits
          let (functionCode, bits) ← decodeBinaryNat bits
          let (arguments, bits) ←
            decodeMany (decodeBinaryTermRaw fuel) arity bits
          pure
            (Nat.pair 2
                (Nat.pair arity
                  (Nat.pair functionCode (rawVectorCode arguments))) + 1,
              bits)
      | _ => none

theorem decodeBinaryTermRaw_binaryTermCode_append
    {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (fuel : Nat) (hfuel : termSymbolCount term < fuel)
    (suffix : List Bool) :
    decodeBinaryTermRaw fuel (binaryTermCode term ++ suffix) =
      some (Encodable.encode term, suffix) := by
  induction term generalizing fuel suffix with
  | bvar index =>
      cases fuel with
      | zero => simp [termSymbolCount] at hfuel
      | succ fuel =>
          simp [binaryTermCode, decodeBinaryTermRaw,
            LO.FirstOrder.Semiterm.encode_eq_toNat,
            LO.FirstOrder.Semiterm.toNat]
  | fvar freeIndex =>
      cases fuel with
      | zero => simp [termSymbolCount] at hfuel
      | succ fuel =>
          simp [binaryTermCode, decodeBinaryTermRaw,
            LO.FirstOrder.Semiterm.encode_eq_toNat,
            LO.FirstOrder.Semiterm.toNat]
  | func functionSymbol arguments ih =>
      cases fuel with
      | zero => simp [termSymbolCount] at hfuel
      | succ fuel =>
          have hchild (i) :
              termSymbolCount (arguments i) < fuel := by
            have hle :
                termSymbolCount (arguments i) ≤
                  Finset.univ.sum
                    (fun j ↦ termSymbolCount (arguments j)) :=
              Finset.single_le_sum
                (f := fun j ↦ termSymbolCount (arguments j))
                (s := Finset.univ)
                (fun j _ ↦ Nat.zero_le
                  (termSymbolCount (arguments j)))
                (Finset.mem_univ i)
            simp [termSymbolCount] at hfuel
            omega
          have hmany :=
            decodeMany_map_flatMap_append
              (decodeBinaryTermRaw fuel)
              binaryTermCode Encodable.encode
              (List.ofFn arguments) suffix
              (by
                intro child hchildMem rest
                rcases
                    (List.mem_ofFn' arguments child).mp hchildMem with
                  ⟨i, rfl⟩
                exact ih i fuel (hchild i) rest)
          have hmany' :
              decodeMany (decodeBinaryTermRaw fuel)
                  (List.ofFn arguments).length
                  ((List.ofFn fun i ↦
                    binaryTermCode (arguments i)).flatten ++ suffix) =
                some
                  (List.ofFn (fun i ↦ Encodable.encode (arguments i)),
                    suffix) := by
            simpa [List.flatMap, List.map_ofFn,
              Function.comp_def] using hmany
          simp only [List.length_ofFn] at hmany'
          simp [binaryTermCode, decodeBinaryTermRaw, hmany',
            LO.FirstOrder.Semiterm.encode_eq_toNat,
            LO.FirstOrder.Semiterm.toNat, rawVectorCode_ofFn]

/-- Parse a structurally serialized formula and return its Foundation Goedel
code. -/
def decodeBinaryFormulaRaw :
    Nat → List Bool → Option (Nat × List Bool)
  | 0, _ => none
  | fuel + 1, bits => do
      let (tag, bits) ← decodeBinaryNat bits
      match tag with
      | 0 => do
          let (arity, bits) ← decodeBinaryNat bits
          let (relationCode, bits) ← decodeBinaryNat bits
          let (arguments, bits) ←
            decodeMany (decodeBinaryTermRaw fuel) arity bits
          pure
            (Nat.pair 0
                (Nat.pair arity
                  (Nat.pair relationCode (rawVectorCode arguments))) + 1,
              bits)
      | 1 => do
          let (arity, bits) ← decodeBinaryNat bits
          let (relationCode, bits) ← decodeBinaryNat bits
          let (arguments, bits) ←
            decodeMany (decodeBinaryTermRaw fuel) arity bits
          pure
            (Nat.pair 1
                (Nat.pair arity
                  (Nat.pair relationCode (rawVectorCode arguments))) + 1,
              bits)
      | 2 => pure (Nat.pair 2 0 + 1, bits)
      | 3 => pure (Nat.pair 3 0 + 1, bits)
      | 4 => do
          let (left, bits) ← decodeBinaryFormulaRaw fuel bits
          let (right, bits) ← decodeBinaryFormulaRaw fuel bits
          pure (Nat.pair 4 (Nat.pair left right) + 1, bits)
      | 5 => do
          let (left, bits) ← decodeBinaryFormulaRaw fuel bits
          let (right, bits) ← decodeBinaryFormulaRaw fuel bits
          pure (Nat.pair 5 (Nat.pair left right) + 1, bits)
      | 6 => do
          let (body, bits) ← decodeBinaryFormulaRaw fuel bits
          pure (Nat.pair 6 body + 1, bits)
      | 7 => do
          let (body, bits) ← decodeBinaryFormulaRaw fuel bits
          pure (Nat.pair 7 body + 1, bits)
      | _ => none

theorem decodeBinaryFormulaRaw_binaryFormulaCode_append
    {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity)
    (fuel : Nat) (hfuel : formulaSymbolCount formula < fuel)
    (suffix : List Bool) :
    decodeBinaryFormulaRaw fuel
        (binaryFormulaCode formula ++ suffix) =
      some (Encodable.encode formula, suffix) := by
  induction formula generalizing fuel suffix with
  | rel relationSymbol arguments =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          have hchild (i) :
              termSymbolCount (arguments i) < fuel := by
            have hle :
                termSymbolCount (arguments i) ≤
                  Finset.univ.sum
                    (fun j ↦ termSymbolCount (arguments j)) :=
              Finset.single_le_sum
                (f := fun j ↦ termSymbolCount (arguments j))
                (s := Finset.univ)
                (fun j _ ↦ Nat.zero_le
                  (termSymbolCount (arguments j)))
                (Finset.mem_univ i)
            simp [formulaSymbolCount] at hfuel
            omega
          have hmany :=
            decodeMany_map_flatMap_append
              (decodeBinaryTermRaw fuel)
              binaryTermCode Encodable.encode
              (List.ofFn arguments) suffix
              (by
                intro child hchildMem rest
                rcases
                    (List.mem_ofFn' arguments child).mp hchildMem with
                  ⟨i, rfl⟩
                exact
                  decodeBinaryTermRaw_binaryTermCode_append
                    (arguments i) fuel (hchild i) rest)
          have hmany' :
              decodeMany (decodeBinaryTermRaw fuel)
                  (List.ofFn arguments).length
                  ((List.ofFn fun i ↦
                    binaryTermCode (arguments i)).flatten ++ suffix) =
                some
                  (List.ofFn (fun i ↦ Encodable.encode (arguments i)),
                    suffix) := by
            simpa [List.flatMap, List.map_ofFn,
              Function.comp_def] using hmany
          simp only [List.length_ofFn] at hmany'
          simp [binaryFormulaCode, decodeBinaryFormulaRaw, hmany',
            LO.FirstOrder.Semiformula.encode_eq_toNat,
            LO.FirstOrder.Semiformula.toNat,
            LO.FirstOrder.Semiterm.encode_eq_toNat,
            rawVectorCode_ofFn]
  | nrel relationSymbol arguments =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          have hchild (i) :
              termSymbolCount (arguments i) < fuel := by
            have hle :
                termSymbolCount (arguments i) ≤
                  Finset.univ.sum
                    (fun j ↦ termSymbolCount (arguments j)) :=
              Finset.single_le_sum
                (f := fun j ↦ termSymbolCount (arguments j))
                (s := Finset.univ)
                (fun j _ ↦ Nat.zero_le
                  (termSymbolCount (arguments j)))
                (Finset.mem_univ i)
            simp [formulaSymbolCount] at hfuel
            omega
          have hmany :=
            decodeMany_map_flatMap_append
              (decodeBinaryTermRaw fuel)
              binaryTermCode Encodable.encode
              (List.ofFn arguments) suffix
              (by
                intro child hchildMem rest
                rcases
                    (List.mem_ofFn' arguments child).mp hchildMem with
                  ⟨i, rfl⟩
                exact
                  decodeBinaryTermRaw_binaryTermCode_append
                    (arguments i) fuel (hchild i) rest)
          have hmany' :
              decodeMany (decodeBinaryTermRaw fuel)
                  (List.ofFn arguments).length
                  ((List.ofFn fun i ↦
                    binaryTermCode (arguments i)).flatten ++ suffix) =
                some
                  (List.ofFn (fun i ↦ Encodable.encode (arguments i)),
                    suffix) := by
            simpa [List.flatMap, List.map_ofFn,
              Function.comp_def] using hmany
          simp only [List.length_ofFn] at hmany'
          simp [binaryFormulaCode, decodeBinaryFormulaRaw, hmany',
            LO.FirstOrder.Semiformula.encode_eq_toNat,
            LO.FirstOrder.Semiformula.toNat,
            LO.FirstOrder.Semiterm.encode_eq_toNat,
            rawVectorCode_ofFn]
  | verum =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          simp [binaryFormulaCode, decodeBinaryFormulaRaw,
            LO.FirstOrder.Semiformula.encode_eq_toNat,
            LO.FirstOrder.Semiformula.toNat]
  | falsum =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          simp [binaryFormulaCode, decodeBinaryFormulaRaw,
            LO.FirstOrder.Semiformula.encode_eq_toNat,
            LO.FirstOrder.Semiformula.toNat]
  | and left right ihLeft ihRight =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          have hLeft : formulaSymbolCount left < fuel := by
            simp [formulaSymbolCount] at hfuel
            omega
          have hRight : formulaSymbolCount right < fuel := by
            simp [formulaSymbolCount] at hfuel
            omega
          simp [binaryFormulaCode, decodeBinaryFormulaRaw,
            ihLeft fuel hLeft, ihRight fuel hRight,
            LO.FirstOrder.Semiformula.encode_eq_toNat,
            LO.FirstOrder.Semiformula.toNat]
  | or left right ihLeft ihRight =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          have hLeft : formulaSymbolCount left < fuel := by
            simp [formulaSymbolCount] at hfuel
            omega
          have hRight : formulaSymbolCount right < fuel := by
            simp [formulaSymbolCount] at hfuel
            omega
          simp [binaryFormulaCode, decodeBinaryFormulaRaw,
            ihLeft fuel hLeft, ihRight fuel hRight,
            LO.FirstOrder.Semiformula.encode_eq_toNat,
            LO.FirstOrder.Semiformula.toNat]
  | all body ih =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          have hBody : formulaSymbolCount body < fuel := by
            simp [formulaSymbolCount] at hfuel
            omega
          simp [binaryFormulaCode, decodeBinaryFormulaRaw,
            ih fuel hBody,
            LO.FirstOrder.Semiformula.encode_eq_toNat,
            LO.FirstOrder.Semiformula.toNat]
  | exs body ih =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          have hBody : formulaSymbolCount body < fuel := by
            simp [formulaSymbolCount] at hfuel
            omega
          simp [binaryFormulaCode, decodeBinaryFormulaRaw,
            ih fuel hBody,
            LO.FirstOrder.Semiformula.encode_eq_toNat,
            LO.FirstOrder.Semiformula.toNat]

/-- Bitset code of a displayed sequent from its distinct formula codes. -/
def rawSequentCode (formulas : List Nat) : Nat :=
  formulas.foldl (fun code formulaCode ↦ code + 2 ^ formulaCode) 0

theorem rawSequentCode_eq_sum (formulas : List Nat) :
    rawSequentCode formulas =
      (formulas.map (fun formulaCode ↦ 2 ^ formulaCode)).sum := by
  suffices ∀ initial : Nat,
      formulas.foldl
          (fun code formulaCode ↦ code + 2 ^ formulaCode) initial =
        initial +
          (formulas.map (fun formulaCode ↦ 2 ^ formulaCode)).sum by
    simpa [rawSequentCode] using this 0
  intro initial
  induction formulas generalizing initial with
  | nil => simp
  | cons head tail ih =>
      simp [ih, Nat.add_assoc]

theorem rawSequentCode_encode_toList
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition) :
    rawSequentCode (Gamma.toList.map Encodable.encode) =
      (⌜Gamma⌝ : Nat) := by
  rw [rawSequentCode_eq_sum]
  simp [LO.FirstOrder.Derivation2.Sequent.quote_def,
    LO.FirstOrder.Semiformula.quote_eq_encode]
  rfl

def decodeBinarySequentRaw :
    Nat → List Bool → Option (Nat × List Bool)
  | 0, _ => none
  | fuel + 1, bits => do
      let (cardinality, bits) ← decodeBinaryNat bits
      let (formulas, bits) ←
        decodeMany (decodeBinaryFormulaRaw fuel) cardinality bits
      pure (rawSequentCode formulas, bits)

theorem formulaSymbolCount_le_sequentSymbolCount
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hformula : formula ∈ Gamma) :
    formulaSymbolCount formula ≤ sequentSymbolCount Gamma := by
  exact Finset.single_le_sum
    (f := fun phi ↦ formulaSymbolCount phi)
    (s := Gamma)
    (fun phi _ ↦ Nat.zero_le (formulaSymbolCount phi))
    hformula

theorem decodeBinarySequentRaw_binarySequentCode_append
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (fuel : Nat)
    (hfuel : sequentSymbolCount Gamma + 1 < fuel)
    (suffix : List Bool) :
    decodeBinarySequentRaw fuel
        (binarySequentCode Gamma ++ suffix) =
      some ((⌜Gamma⌝ : Nat), suffix) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      have hformula
          (formula : LO.FirstOrder.ArithmeticProposition)
          (hmem : formula ∈ Gamma) :
          formulaSymbolCount formula < fuel := by
        have hle :=
          formulaSymbolCount_le_sequentSymbolCount hmem
        omega
      have hmany :=
        decodeMany_map_flatMap_append
          (decodeBinaryFormulaRaw fuel)
          binaryFormulaCode Encodable.encode
          Gamma.toList suffix
          (by
            intro formula hmem rest
            exact
              decodeBinaryFormulaRaw_binaryFormulaCode_append
                formula fuel
                (hformula formula (by simpa using hmem)) rest)
      have hmany' :
          decodeMany (decodeBinaryFormulaRaw fuel) Gamma.card
              (Gamma.toList.flatMap binaryFormulaCode ++ suffix) =
            some (Gamma.toList.map Encodable.encode, suffix) := by
        simpa using hmany
      simp [binarySequentCode, decodeBinarySequentRaw, hmany',
        rawSequentCode_encode_toList]

def rawProofAxL (sequent formula : Nat) : Nat :=
  Nat.pair sequent (Nat.pair 0 formula) + 1

def rawProofAxm (sequent formula : Nat) : Nat :=
  Nat.pair sequent (Nat.pair 9 formula) + 1

def rawProofVerum (sequent : Nat) : Nat :=
  Nat.pair sequent (Nat.pair 1 0) + 1

def rawProofAnd
    (sequent leftFormula rightFormula left right : Nat) : Nat :=
  Nat.pair sequent
      (Nat.pair 2
        (Nat.pair leftFormula
          (Nat.pair rightFormula (Nat.pair left right)))) + 1

def rawProofOr
    (sequent leftFormula rightFormula premise : Nat) : Nat :=
  Nat.pair sequent
      (Nat.pair 3
        (Nat.pair leftFormula (Nat.pair rightFormula premise))) + 1

def rawProofAll (sequent formula premise : Nat) : Nat :=
  Nat.pair sequent (Nat.pair 4 (Nat.pair formula premise)) + 1

def rawProofExs
    (sequent formula witness premise : Nat) : Nat :=
  Nat.pair sequent
      (Nat.pair 5 (Nat.pair formula (Nat.pair witness premise))) + 1

def rawProofWk (sequent premise : Nat) : Nat :=
  Nat.pair sequent (Nat.pair 6 premise) + 1

def rawProofShift (sequent premise : Nat) : Nat :=
  Nat.pair sequent (Nat.pair 7 premise) + 1

def rawProofCut (sequent formula left right : Nat) : Nat :=
  Nat.pair sequent
      (Nat.pair 8 (Nat.pair formula (Nat.pair left right))) + 1

@[simp] theorem rawProofAxL_eq_foundation
    (sequent formula : Nat) :
    rawProofAxL sequent formula =
      LO.FirstOrder.Arithmetic.Bootstrapping.axL sequent formula := by
  simp [rawProofAxL,
    LO.FirstOrder.Arithmetic.Bootstrapping.axL,
    LO.FirstOrder.Arithmetic.nat_pair_eq]

@[simp] theorem rawProofAxm_eq_foundation
    (sequent formula : Nat) :
    rawProofAxm sequent formula =
      LO.FirstOrder.Arithmetic.Bootstrapping.axm sequent formula := by
  simp [rawProofAxm,
    LO.FirstOrder.Arithmetic.Bootstrapping.axm,
    LO.FirstOrder.Arithmetic.nat_pair_eq]

@[simp] theorem rawProofVerum_eq_foundation (sequent : Nat) :
    rawProofVerum sequent =
      LO.FirstOrder.Arithmetic.Bootstrapping.verumIntro sequent := by
  simp [rawProofVerum,
    LO.FirstOrder.Arithmetic.Bootstrapping.verumIntro,
    LO.FirstOrder.Arithmetic.nat_pair_eq]

@[simp] theorem rawProofAnd_eq_foundation
    (sequent leftFormula rightFormula left right : Nat) :
    rawProofAnd sequent leftFormula rightFormula left right =
      LO.FirstOrder.Arithmetic.Bootstrapping.andIntro
        sequent leftFormula rightFormula left right := by
  simp [rawProofAnd,
    LO.FirstOrder.Arithmetic.Bootstrapping.andIntro,
    LO.FirstOrder.Arithmetic.nat_pair_eq]

@[simp] theorem rawProofOr_eq_foundation
    (sequent leftFormula rightFormula premise : Nat) :
    rawProofOr sequent leftFormula rightFormula premise =
      LO.FirstOrder.Arithmetic.Bootstrapping.orIntro
        sequent leftFormula rightFormula premise := by
  simp [rawProofOr,
    LO.FirstOrder.Arithmetic.Bootstrapping.orIntro,
    LO.FirstOrder.Arithmetic.nat_pair_eq]

@[simp] theorem rawProofAll_eq_foundation
    (sequent formula premise : Nat) :
    rawProofAll sequent formula premise =
      LO.FirstOrder.Arithmetic.Bootstrapping.allIntro
        sequent formula premise := by
  simp [rawProofAll,
    LO.FirstOrder.Arithmetic.Bootstrapping.allIntro,
    LO.FirstOrder.Arithmetic.nat_pair_eq]

@[simp] theorem rawProofExs_eq_foundation
    (sequent formula witness premise : Nat) :
    rawProofExs sequent formula witness premise =
      LO.FirstOrder.Arithmetic.Bootstrapping.exsIntro
        sequent formula witness premise := by
  simp [rawProofExs,
    LO.FirstOrder.Arithmetic.Bootstrapping.exsIntro,
    LO.FirstOrder.Arithmetic.nat_pair_eq]

@[simp] theorem rawProofWk_eq_foundation
    (sequent premise : Nat) :
    rawProofWk sequent premise =
      LO.FirstOrder.Arithmetic.Bootstrapping.wkRule
        sequent premise := by
  simp [rawProofWk,
    LO.FirstOrder.Arithmetic.Bootstrapping.wkRule,
    LO.FirstOrder.Arithmetic.nat_pair_eq]

@[simp] theorem rawProofShift_eq_foundation
    (sequent premise : Nat) :
    rawProofShift sequent premise =
      LO.FirstOrder.Arithmetic.Bootstrapping.shiftRule
        sequent premise := by
  simp [rawProofShift,
    LO.FirstOrder.Arithmetic.Bootstrapping.shiftRule,
    LO.FirstOrder.Arithmetic.nat_pair_eq]

@[simp] theorem rawProofCut_eq_foundation
    (sequent formula left right : Nat) :
    rawProofCut sequent formula left right =
      LO.FirstOrder.Arithmetic.Bootstrapping.cutRule
        sequent formula left right := by
  simp [rawProofCut,
    LO.FirstOrder.Arithmetic.Bootstrapping.cutRule,
    LO.FirstOrder.Arithmetic.nat_pair_eq]

/-- Parse one complete proof prefix.  The first output is the Foundation raw
proof code and the second is its displayed conclusion-sequent code. -/
def decodeBinaryProofRaw :
    Nat → List Bool → Option ((Nat × Nat) × List Bool)
  | 0, _ => none
  | fuel + 1, bits => do
      let (tag, bits) ← decodeBinaryNat bits
      let (sequent, bits) ← decodeBinarySequentRaw fuel bits
      match tag with
      | 0 => do
          let (formula, bits) ← decodeBinaryFormulaRaw fuel bits
          pure ((rawProofAxL sequent formula, sequent), bits)
      | 1 => do
          let (formula, bits) ← decodeBinaryFormulaRaw fuel bits
          pure ((rawProofAxm sequent formula, sequent), bits)
      | 2 => pure ((rawProofVerum sequent, sequent), bits)
      | 3 => do
          let (leftFormula, bits) ← decodeBinaryFormulaRaw fuel bits
          let (rightFormula, bits) ← decodeBinaryFormulaRaw fuel bits
          let (left, bits) ← decodeBinaryProofRaw fuel bits
          let (right, bits) ← decodeBinaryProofRaw fuel bits
          pure
            ((rawProofAnd sequent leftFormula rightFormula
                left.1 right.1,
              sequent),
            bits)
      | 4 => do
          let (leftFormula, bits) ← decodeBinaryFormulaRaw fuel bits
          let (rightFormula, bits) ← decodeBinaryFormulaRaw fuel bits
          let (premise, bits) ← decodeBinaryProofRaw fuel bits
          pure
            ((rawProofOr sequent leftFormula rightFormula premise.1,
              sequent),
            bits)
      | 5 => do
          let (formula, bits) ← decodeBinaryFormulaRaw fuel bits
          let (premise, bits) ← decodeBinaryProofRaw fuel bits
          pure ((rawProofAll sequent formula premise.1, sequent), bits)
      | 6 => do
          let (formula, bits) ← decodeBinaryFormulaRaw fuel bits
          let (witness, bits) ← decodeBinaryTermRaw fuel bits
          let (premise, bits) ← decodeBinaryProofRaw fuel bits
          pure
            ((rawProofExs sequent formula witness premise.1, sequent),
              bits)
      | 7 => do
          let (premise, bits) ← decodeBinaryProofRaw fuel bits
          pure ((rawProofWk sequent premise.1, sequent), bits)
      | 8 => do
          let (premise, bits) ← decodeBinaryProofRaw fuel bits
          pure ((rawProofShift sequent premise.1, sequent), bits)
      | 9 => do
          let (formula, bits) ← decodeBinaryFormulaRaw fuel bits
          let (left, bits) ← decodeBinaryProofRaw fuel bits
          let (right, bits) ← decodeBinaryProofRaw fuel bits
          pure
            ((rawProofCut sequent formula left.1 right.1, sequent), bits)
      | _ => none

theorem decodeBinaryProofRaw_cut_components
    (fuel sequent formula leftCode leftConclusion
      rightCode rightConclusion : Nat)
    (sequentBits formulaBits leftBits rightBits suffix : List Bool)
    (hsequent :
      decodeBinarySequentRaw fuel
          (sequentBits ++ formulaBits ++ leftBits ++ rightBits ++ suffix) =
        some
          (sequent,
            formulaBits ++ leftBits ++ rightBits ++ suffix))
    (hformula :
      decodeBinaryFormulaRaw fuel
          (formulaBits ++ leftBits ++ rightBits ++ suffix) =
        some (formula, leftBits ++ rightBits ++ suffix))
    (hleft :
      decodeBinaryProofRaw fuel
          (leftBits ++ rightBits ++ suffix) =
        some ((leftCode, leftConclusion), rightBits ++ suffix))
    (hright :
      decodeBinaryProofRaw fuel (rightBits ++ suffix) =
        some ((rightCode, rightConclusion), suffix)) :
    decodeBinaryProofRaw (fuel + 1)
        (binaryNatCode 9 ++ sequentBits ++ formulaBits ++
          leftBits ++ rightBits ++ suffix) =
      some
        ((rawProofCut sequent formula leftCode rightCode, sequent),
          suffix) := by
  have hsequent' :
      decodeBinarySequentRaw fuel
          (sequentBits ++
            (formulaBits ++ (leftBits ++ (rightBits ++ suffix)))) =
        some
          (sequent,
            formulaBits ++ (leftBits ++ (rightBits ++ suffix))) := by
    simpa only [List.append_assoc] using hsequent
  have hformula' :
      decodeBinaryFormulaRaw fuel
          (formulaBits ++ (leftBits ++ (rightBits ++ suffix))) =
        some (formula, leftBits ++ (rightBits ++ suffix)) := by
    simpa only [List.append_assoc] using hformula
  have hleft' :
      decodeBinaryProofRaw fuel
          (leftBits ++ (rightBits ++ suffix)) =
        some ((leftCode, leftConclusion), rightBits ++ suffix) := by
    simpa only [List.append_assoc] using hleft
  simp only [List.append_assoc, decodeBinaryProofRaw,
    decodeBinaryNat_binaryNatCode_append]
  dsimp
  rw [hsequent']
  dsimp
  rw [hformula']
  dsimp
  rw [hleft']
  dsimp
  rw [hright]
  dsimp
  rfl

theorem decodeBinaryProofRaw_cut_chain
    (fuel sequent formula leftCode leftConclusion
      rightCode rightConclusion : Nat)
    (suffix : List Bool)
    {sequentInput formulaInput leftInput rightInput : List Bool}
    (hsequent :
      decodeBinarySequentRaw fuel sequentInput =
        some (sequent, formulaInput))
    (hformula :
      decodeBinaryFormulaRaw fuel formulaInput =
        some (formula, leftInput))
    (hleft :
      decodeBinaryProofRaw fuel leftInput =
        some ((leftCode, leftConclusion), rightInput))
    (hright :
      decodeBinaryProofRaw fuel rightInput =
        some ((rightCode, rightConclusion), suffix)) :
    decodeBinaryProofRaw (fuel + 1)
        (binaryNatCode 9 ++ sequentInput) =
      some
        ((rawProofCut sequent formula leftCode rightCode, sequent),
          suffix) := by
  simp only [decodeBinaryProofRaw,
    decodeBinaryNat_binaryNatCode_append]
  dsimp
  rw [hsequent]
  dsimp
  rw [hformula]
  dsimp
  rw [hleft]
  dsimp
  rw [hright]
  dsimp
  rfl

def decodePackedCheckedPAProof (code : Nat) : Option (Nat × Nat) := do
  let bits := code.bits
  guard (bits.getLast? = some true)
  let payload := bits.dropLast
  let (proof, suffix) ←
    decodeBinaryProofRaw (payload.length + 1) payload
  guard suffix.isEmpty
  pure proof

def binaryProofLength
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (b : LO.FirstOrder.Derivation2 PA Gamma) : Nat :=
  (binaryDerivationCode b).length

/-! ## Proof-field-free checked PA certificates -/

/-- A proof-field-free syntax tree for the same PA/Hilbert-sequent calculus
checked by Foundation.  Every node stores the displayed conclusion sequent;
validity below is determined by Foundation's real checker, not by this
datatype. -/
inductive CheckedPAProofTree where
  | closed
      (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
      (phi : LO.FirstOrder.ArithmeticProposition)
  | axm
      (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
      (sigma : LO.FirstOrder.ArithmeticSentence)
  | verum
      (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
  | and
      (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
      (phi psi : LO.FirstOrder.ArithmeticProposition)
      (left right : CheckedPAProofTree)
  | or
      (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
      (phi psi : LO.FirstOrder.ArithmeticProposition)
      (premise : CheckedPAProofTree)
  | all
      (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
      (phi : LO.FirstOrder.ArithmeticSemiformula Nat 1)
      (premise : CheckedPAProofTree)
  | exs
      (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
      (phi : LO.FirstOrder.ArithmeticSemiformula Nat 1)
      (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      (premise : CheckedPAProofTree)
  | wk
      (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
      (premise : CheckedPAProofTree)
  | shift
      (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
      (premise : CheckedPAProofTree)
  | cut
      (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
      (phi : LO.FirstOrder.ArithmeticProposition)
      (left right : CheckedPAProofTree)

def CheckedPAProofTree.conclusion :
    CheckedPAProofTree →
      Finset LO.FirstOrder.ArithmeticProposition
  | .closed Gamma _ => Gamma
  | .axm Gamma _ => Gamma
  | .verum Gamma => Gamma
  | .and Gamma _ _ _ _ => Gamma
  | .or Gamma _ _ _ => Gamma
  | .all Gamma _ _ => Gamma
  | .exs Gamma _ _ _ => Gamma
  | .wk Gamma _ => Gamma
  | .shift Gamma _ => Gamma
  | .cut Gamma _ _ _ => Gamma

/-- The exact Foundation raw code represented by a certificate tree.  This
is used only by the existing checker; it is not used as the proof length. -/
noncomputable def CheckedPAProofTree.rawCode :
    CheckedPAProofTree → Nat
  | .closed Gamma phi =>
      LO.FirstOrder.Arithmetic.Bootstrapping.axL
        (⌜Gamma⌝ : Nat) (⌜phi⌝ : Nat)
  | .axm Gamma sigma =>
      LO.FirstOrder.Arithmetic.Bootstrapping.axm
        (⌜Gamma⌝ : Nat) (⌜sigma⌝ : Nat)
  | .verum Gamma =>
      LO.FirstOrder.Arithmetic.Bootstrapping.verumIntro
        (⌜Gamma⌝ : Nat)
  | .and Gamma phi psi left right =>
      LO.FirstOrder.Arithmetic.Bootstrapping.andIntro
        (⌜Gamma⌝ : Nat) (⌜phi⌝ : Nat) (⌜psi⌝ : Nat)
        left.rawCode right.rawCode
  | .or Gamma phi psi premise =>
      LO.FirstOrder.Arithmetic.Bootstrapping.orIntro
        (⌜Gamma⌝ : Nat) (⌜phi⌝ : Nat) (⌜psi⌝ : Nat)
        premise.rawCode
  | .all Gamma phi premise =>
      LO.FirstOrder.Arithmetic.Bootstrapping.allIntro
        (⌜Gamma⌝ : Nat) (⌜phi⌝ : Nat) premise.rawCode
  | .exs Gamma phi witness premise =>
      LO.FirstOrder.Arithmetic.Bootstrapping.exsIntro
        (⌜Gamma⌝ : Nat) (⌜phi⌝ : Nat) (⌜witness⌝ : Nat)
        premise.rawCode
  | .wk Gamma premise =>
      LO.FirstOrder.Arithmetic.Bootstrapping.wkRule
        (⌜Gamma⌝ : Nat) premise.rawCode
  | .shift Gamma premise =>
      LO.FirstOrder.Arithmetic.Bootstrapping.shiftRule
        (⌜Gamma⌝ : Nat) premise.rawCode
  | .cut Gamma phi left right =>
      LO.FirstOrder.Arithmetic.Bootstrapping.cutRule
        (⌜Gamma⌝ : Nat) (⌜phi⌝ : Nat)
        left.rawCode right.rawCode

/-- A certificate is valid exactly when its represented raw code is accepted
by Foundation's PA derivation checker. -/
def CheckedPAProofTree.Valid (b : CheckedPAProofTree) : Prop :=
  LO.FirstOrder.Arithmetic.Bootstrapping.Derivation PA b.rawCode

/-- Honest binary serialization of the proof-field-free certificate. -/
def CheckedPAProofTree.binaryCode :
    CheckedPAProofTree → List Bool
  | .closed Gamma phi =>
      binaryNatCode 0 ++ binarySequentCode Gamma ++
        binaryFormulaCode phi
  | .axm Gamma sigma =>
      binaryNatCode 1 ++ binarySequentCode Gamma ++
        binaryFormulaCode
          (Rewriting.emb sigma : LO.FirstOrder.ArithmeticProposition)
  | .verum Gamma =>
      binaryNatCode 2 ++ binarySequentCode Gamma
  | .and Gamma phi psi left right =>
      binaryNatCode 3 ++ binarySequentCode Gamma ++
        binaryFormulaCode phi ++ binaryFormulaCode psi ++
        left.binaryCode ++ right.binaryCode
  | .or Gamma phi psi premise =>
      binaryNatCode 4 ++ binarySequentCode Gamma ++
        binaryFormulaCode phi ++ binaryFormulaCode psi ++
        premise.binaryCode
  | .all Gamma phi premise =>
      binaryNatCode 5 ++ binarySequentCode Gamma ++
        binaryFormulaCode phi ++ premise.binaryCode
  | .exs Gamma phi witness premise =>
      binaryNatCode 6 ++ binarySequentCode Gamma ++
        binaryFormulaCode phi ++ binaryTermCode witness ++
        premise.binaryCode
  | .wk Gamma premise =>
      binaryNatCode 7 ++ binarySequentCode Gamma ++
        premise.binaryCode
  | .shift Gamma premise =>
      binaryNatCode 8 ++ binarySequentCode Gamma ++
        premise.binaryCode
  | .cut Gamma phi left right =>
      binaryNatCode 9 ++ binarySequentCode Gamma ++
        binaryFormulaCode phi ++ left.binaryCode ++ right.binaryCode

def CheckedPAProofTree.binaryLength (b : CheckedPAProofTree) : Nat :=
  b.binaryCode.length

/-- Structural fuel sufficient for every recursive parser call.  The two
leading units pay for the rule tag and the sequent-parser layer. -/
def CheckedPAProofTree.parseWeight : CheckedPAProofTree → Nat
  | .closed Gamma phi =>
      2 + sequentSymbolCount Gamma + formulaSymbolCount phi
  | .axm Gamma sigma =>
      2 + sequentSymbolCount Gamma +
        formulaSymbolCount
          (Rewriting.emb sigma : LO.FirstOrder.ArithmeticProposition)
  | .verum Gamma => 2 + sequentSymbolCount Gamma
  | .and Gamma phi psi left right =>
      2 + sequentSymbolCount Gamma + formulaSymbolCount phi +
        formulaSymbolCount psi + left.parseWeight + right.parseWeight
  | .or Gamma phi psi premise =>
      2 + sequentSymbolCount Gamma + formulaSymbolCount phi +
        formulaSymbolCount psi + premise.parseWeight
  | .all Gamma phi premise =>
      2 + sequentSymbolCount Gamma + formulaSymbolCount phi +
        premise.parseWeight
  | .exs Gamma phi witness premise =>
      2 + sequentSymbolCount Gamma + formulaSymbolCount phi +
        termSymbolCount witness + premise.parseWeight
  | .wk Gamma premise =>
      2 + sequentSymbolCount Gamma + premise.parseWeight
  | .shift Gamma premise =>
      2 + sequentSymbolCount Gamma + premise.parseWeight
  | .cut Gamma phi left right =>
      2 + sequentSymbolCount Gamma + formulaSymbolCount phi +
        left.parseWeight + right.parseWeight

/-- Full parser round trip: every proof-field-free certificate is decoded to
the exact Foundation raw proof code and exact displayed conclusion code. -/
theorem CheckedPAProofTree.decodeBinaryProofRaw_binaryCode_append
    (b : CheckedPAProofTree) (fuel : Nat)
    (hfuel : b.parseWeight < fuel) (suffix : List Bool) :
    decodeBinaryProofRaw fuel (b.binaryCode ++ suffix) =
      some ((b.rawCode, (⌜b.conclusion⌝ : Nat)), suffix) := by
  induction b generalizing fuel suffix with
  | closed Gamma phi =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma + 1 < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hphi : formulaSymbolCount phi < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [CheckedPAProofTree.binaryCode, decodeBinaryProofRaw,
            decodeBinarySequentRaw_binarySequentCode_append
              Gamma fuel hseq,
            decodeBinaryFormulaRaw_binaryFormulaCode_append
              phi fuel hphi,
            CheckedPAProofTree.rawCode,
            CheckedPAProofTree.conclusion,
            LO.FirstOrder.Semiformula.quote_eq_encode]
  | axm Gamma sigma =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma + 1 < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hphi :
              formulaSymbolCount
                  (Rewriting.emb sigma :
                    LO.FirstOrder.ArithmeticProposition) < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [CheckedPAProofTree.binaryCode, decodeBinaryProofRaw,
            decodeBinarySequentRaw_binarySequentCode_append
              Gamma fuel hseq,
            decodeBinaryFormulaRaw_binaryFormulaCode_append
              (Rewriting.emb sigma :
                LO.FirstOrder.ArithmeticProposition) fuel hphi,
            CheckedPAProofTree.rawCode,
            CheckedPAProofTree.conclusion,
            LO.FirstOrder.Sentence.quote_def,
            LO.FirstOrder.Semiformula.quote_eq_encode]
  | verum Gamma =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma + 1 < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [CheckedPAProofTree.binaryCode, decodeBinaryProofRaw,
            decodeBinarySequentRaw_binarySequentCode_append
              Gamma fuel hseq,
            CheckedPAProofTree.rawCode,
            CheckedPAProofTree.conclusion]
  | and Gamma phi psi left right ihLeft ihRight =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma + 1 < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hphi : formulaSymbolCount phi < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hpsi : formulaSymbolCount psi < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hleft : left.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hright : right.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [CheckedPAProofTree.binaryCode, decodeBinaryProofRaw,
            decodeBinarySequentRaw_binarySequentCode_append
              Gamma fuel hseq,
            decodeBinaryFormulaRaw_binaryFormulaCode_append
              phi fuel hphi,
            decodeBinaryFormulaRaw_binaryFormulaCode_append
              psi fuel hpsi,
            ihLeft fuel hleft, ihRight fuel hright,
            CheckedPAProofTree.rawCode,
            CheckedPAProofTree.conclusion,
            LO.FirstOrder.Semiformula.quote_eq_encode]
  | or Gamma phi psi premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma + 1 < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hphi : formulaSymbolCount phi < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hpsi : formulaSymbolCount psi < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hpremise : premise.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [CheckedPAProofTree.binaryCode, decodeBinaryProofRaw,
            decodeBinarySequentRaw_binarySequentCode_append
              Gamma fuel hseq,
            decodeBinaryFormulaRaw_binaryFormulaCode_append
              phi fuel hphi,
            decodeBinaryFormulaRaw_binaryFormulaCode_append
              psi fuel hpsi,
            ih fuel hpremise,
            CheckedPAProofTree.rawCode,
            CheckedPAProofTree.conclusion,
            LO.FirstOrder.Semiformula.quote_eq_encode]
  | all Gamma phi premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma + 1 < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hphi : formulaSymbolCount phi < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hpremise : premise.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [CheckedPAProofTree.binaryCode, decodeBinaryProofRaw,
            decodeBinarySequentRaw_binarySequentCode_append
              Gamma fuel hseq,
            decodeBinaryFormulaRaw_binaryFormulaCode_append
              phi fuel hphi,
            ih fuel hpremise,
            CheckedPAProofTree.rawCode,
            CheckedPAProofTree.conclusion,
            LO.FirstOrder.Semiformula.quote_eq_encode]
  | exs Gamma phi witness premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma + 1 < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hphi : formulaSymbolCount phi < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hwitness : termSymbolCount witness < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hpremise : premise.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [CheckedPAProofTree.binaryCode, decodeBinaryProofRaw,
            decodeBinarySequentRaw_binarySequentCode_append
              Gamma fuel hseq,
            decodeBinaryFormulaRaw_binaryFormulaCode_append
              phi fuel hphi,
            decodeBinaryTermRaw_binaryTermCode_append
              witness fuel hwitness,
            ih fuel hpremise,
            CheckedPAProofTree.rawCode,
            CheckedPAProofTree.conclusion,
            LO.FirstOrder.Semiformula.quote_eq_encode,
            LO.FirstOrder.Semiterm.quote_eq_encode]
  | wk Gamma premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma + 1 < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hpremise : premise.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [CheckedPAProofTree.binaryCode, decodeBinaryProofRaw,
            decodeBinarySequentRaw_binarySequentCode_append
              Gamma fuel hseq,
            ih fuel hpremise,
            CheckedPAProofTree.rawCode,
            CheckedPAProofTree.conclusion]
  | shift Gamma premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma + 1 < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hpremise : premise.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [CheckedPAProofTree.binaryCode, decodeBinaryProofRaw,
            decodeBinarySequentRaw_binarySequentCode_append
              Gamma fuel hseq,
            ih fuel hpremise,
            CheckedPAProofTree.rawCode,
            CheckedPAProofTree.conclusion]
  | cut Gamma phi left right ihLeft ihRight =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma + 1 < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hphi : formulaSymbolCount phi < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hleft : left.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hright : right.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          let rightInput := right.binaryCode ++ suffix
          let leftInput := left.binaryCode ++ rightInput
          let formulaInput := binaryFormulaCode phi ++ leftInput
          let sequentInput := binarySequentCode Gamma ++ formulaInput
          have hseqParse :
              decodeBinarySequentRaw fuel sequentInput =
                some ((⌜Gamma⌝ : Nat), formulaInput) := by
            exact decodeBinarySequentRaw_binarySequentCode_append
              Gamma fuel hseq formulaInput
          have hformulaParse :
              decodeBinaryFormulaRaw fuel formulaInput =
                some (Encodable.encode phi, leftInput) := by
            exact decodeBinaryFormulaRaw_binaryFormulaCode_append
              phi fuel hphi leftInput
          have hleftParse :
              decodeBinaryProofRaw fuel leftInput =
                some
                  ((left.rawCode, (⌜left.conclusion⌝ : Nat)),
                    rightInput) := by
            exact ihLeft fuel hleft rightInput
          have hrightParse :
              decodeBinaryProofRaw fuel rightInput =
                some
                  ((right.rawCode, (⌜right.conclusion⌝ : Nat)),
                    suffix) := by
            exact ihRight fuel hright suffix
          have hparse :=
            decodeBinaryProofRaw_cut_chain
              fuel (⌜Gamma⌝ : Nat) (Encodable.encode phi)
              left.rawCode (⌜left.conclusion⌝ : Nat)
              right.rawCode (⌜right.conclusion⌝ : Nat)
              suffix
              (sequentInput := sequentInput)
              (formulaInput := formulaInput)
              (leftInput := leftInput)
              (rightInput := rightInput)
              hseqParse hformulaParse hleftParse hrightParse
          simpa [CheckedPAProofTree.binaryCode,
            CheckedPAProofTree.rawCode,
            CheckedPAProofTree.conclusion,
            LO.FirstOrder.Semiformula.quote_eq_encode,
            sequentInput, formulaInput, leftInput, rightInput,
            List.append_assoc] using hparse

theorem two_le_binaryNatCode_length (n : Nat) :
    2 ≤ (binaryNatCode n).length := by
  simp [binaryNatCode]

theorem list_sum_ofFn_eq_finset_sum {arity : Nat}
    (f : Fin arity → Nat) :
    (List.ofFn f).sum = ∑ i, f i := by
  induction arity with
  | zero => simp
  | succ arity ih =>
      rw [List.ofFn_succ, List.sum_cons, Fin.sum_univ_succ]
      rw [ih]

theorem length_flatten_ofFn {alpha : Type*} {arity : Nat}
    (code : Fin arity → List alpha) :
    (List.ofFn code).flatten.length =
      ∑ i, (code i).length := by
  rw [List.length_flatten, List.map_ofFn]
  simpa [Function.comp_def] using
    list_sum_ofFn_eq_finset_sum (fun i ↦ (code i).length)

theorem termSymbolCount_le_binaryTermCode_length
    {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    termSymbolCount term ≤ (binaryTermCode term).length := by
  induction term with
  | bvar index =>
      have htag := two_le_binaryNatCode_length 0
      have hindex := two_le_binaryNatCode_length index.val
      simp [termSymbolCount, binaryTermCode]
      omega
  | fvar freeIndex =>
      have htag := two_le_binaryNatCode_length 1
      have hindex := two_le_binaryNatCode_length freeIndex
      simp [termSymbolCount, binaryTermCode]
      omega
  | func functionSymbol arguments ih =>
      have hchildren :
          Finset.univ.sum
              (fun i ↦ termSymbolCount (arguments i)) ≤
            Finset.univ.sum
              (fun i ↦ (binaryTermCode (arguments i)).length) :=
        Finset.sum_le_sum (fun i _ ↦ ih i)
      have hflatten :=
        length_flatten_ofFn
          (fun i ↦ binaryTermCode (arguments i))
      have htag := two_le_binaryNatCode_length 2
      simp only [termSymbolCount, binaryTermCode,
        List.length_append]
      rw [hflatten]
      omega

theorem formulaSymbolCount_le_binaryFormulaCode_length
    {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    formulaSymbolCount formula ≤ (binaryFormulaCode formula).length := by
  induction formula with
  | rel relationSymbol arguments =>
      have hchildren :
          Finset.univ.sum
              (fun i ↦ termSymbolCount (arguments i)) ≤
            Finset.univ.sum
              (fun i ↦ (binaryTermCode (arguments i)).length) :=
        Finset.sum_le_sum
          (fun i _ ↦ termSymbolCount_le_binaryTermCode_length
            (arguments i))
      have hflatten :=
        length_flatten_ofFn
          (fun i ↦ binaryTermCode (arguments i))
      have htag := two_le_binaryNatCode_length 0
      simp only [formulaSymbolCount, binaryFormulaCode,
        List.length_append]
      rw [hflatten]
      omega
  | nrel relationSymbol arguments =>
      have hchildren :
          Finset.univ.sum
              (fun i ↦ termSymbolCount (arguments i)) ≤
            Finset.univ.sum
              (fun i ↦ (binaryTermCode (arguments i)).length) :=
        Finset.sum_le_sum
          (fun i _ ↦ termSymbolCount_le_binaryTermCode_length
            (arguments i))
      have hflatten :=
        length_flatten_ofFn
          (fun i ↦ binaryTermCode (arguments i))
      have htag := two_le_binaryNatCode_length 1
      simp only [formulaSymbolCount, binaryFormulaCode,
        List.length_append]
      rw [hflatten]
      omega
  | verum =>
      exact le_trans (by simp [formulaSymbolCount])
        (two_le_binaryNatCode_length 2)
  | falsum =>
      exact le_trans (by simp [formulaSymbolCount])
        (two_le_binaryNatCode_length 3)
  | and left right ihLeft ihRight =>
      have htag := two_le_binaryNatCode_length 4
      simp only [formulaSymbolCount, binaryFormulaCode,
        List.length_append]
      omega
  | or left right ihLeft ihRight =>
      have htag := two_le_binaryNatCode_length 5
      simp only [formulaSymbolCount, binaryFormulaCode,
        List.length_append]
      omega
  | all body ih =>
      have htag := two_le_binaryNatCode_length 6
      simp only [formulaSymbolCount, binaryFormulaCode,
        List.length_append]
      omega
  | exs body ih =>
      have htag := two_le_binaryNatCode_length 7
      simp only [formulaSymbolCount, binaryFormulaCode,
        List.length_append]
      omega

theorem sequentSymbolCount_le_binarySequentCode_length
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition) :
    sequentSymbolCount Gamma ≤ (binarySequentCode Gamma).length := by
  have hsum :
      Gamma.sum formulaSymbolCount ≤
        Gamma.sum (fun phi ↦ (binaryFormulaCode phi).length) :=
    Finset.sum_le_sum
      (fun phi _ ↦ formulaSymbolCount_le_binaryFormulaCode_length phi)
  have hflat :
      (Gamma.toList.flatMap binaryFormulaCode).length =
        Gamma.sum (fun phi ↦ (binaryFormulaCode phi).length) := by
    rw [List.length_flatMap]
    simp
  have hheader := two_le_binaryNatCode_length Gamma.card
  have hsum' :
      sequentSymbolCount Gamma ≤
        (Gamma.toList.flatMap binaryFormulaCode).length := by
    rw [hflat]
    exact hsum
  simp only [binarySequentCode, List.length_append]
  omega

theorem CheckedPAProofTree.parseWeight_le_binaryLength
    (b : CheckedPAProofTree) :
    b.parseWeight ≤ b.binaryLength := by
  induction b with
  | closed Gamma phi =>
      have htag := two_le_binaryNatCode_length 0
      have hseq := sequentSymbolCount_le_binarySequentCode_length Gamma
      have hphi := formulaSymbolCount_le_binaryFormulaCode_length phi
      simp only [CheckedPAProofTree.parseWeight,
        CheckedPAProofTree.binaryLength,
        CheckedPAProofTree.binaryCode, List.length_append]
      omega
  | axm Gamma sigma =>
      have htag := two_le_binaryNatCode_length 1
      have hseq := sequentSymbolCount_le_binarySequentCode_length Gamma
      have hphi := formulaSymbolCount_le_binaryFormulaCode_length
        (Rewriting.emb sigma : LO.FirstOrder.ArithmeticProposition)
      simp only [CheckedPAProofTree.parseWeight,
        CheckedPAProofTree.binaryLength,
        CheckedPAProofTree.binaryCode, List.length_append]
      omega
  | verum Gamma =>
      have htag := two_le_binaryNatCode_length 2
      have hseq := sequentSymbolCount_le_binarySequentCode_length Gamma
      simp only [CheckedPAProofTree.parseWeight,
        CheckedPAProofTree.binaryLength,
        CheckedPAProofTree.binaryCode, List.length_append]
      omega
  | and Gamma phi psi left right ihLeft ihRight =>
      simp only [CheckedPAProofTree.binaryLength] at ihLeft ihRight
      have htag := two_le_binaryNatCode_length 3
      have hseq := sequentSymbolCount_le_binarySequentCode_length Gamma
      have hphi := formulaSymbolCount_le_binaryFormulaCode_length phi
      have hpsi := formulaSymbolCount_le_binaryFormulaCode_length psi
      simp only [CheckedPAProofTree.parseWeight,
        CheckedPAProofTree.binaryLength,
        CheckedPAProofTree.binaryCode, List.length_append]
      omega
  | or Gamma phi psi premise ih =>
      simp only [CheckedPAProofTree.binaryLength] at ih
      have htag := two_le_binaryNatCode_length 4
      have hseq := sequentSymbolCount_le_binarySequentCode_length Gamma
      have hphi := formulaSymbolCount_le_binaryFormulaCode_length phi
      have hpsi := formulaSymbolCount_le_binaryFormulaCode_length psi
      simp only [CheckedPAProofTree.parseWeight,
        CheckedPAProofTree.binaryLength,
        CheckedPAProofTree.binaryCode, List.length_append]
      omega
  | all Gamma phi premise ih =>
      simp only [CheckedPAProofTree.binaryLength] at ih
      have htag := two_le_binaryNatCode_length 5
      have hseq := sequentSymbolCount_le_binarySequentCode_length Gamma
      have hphi := formulaSymbolCount_le_binaryFormulaCode_length phi
      simp only [CheckedPAProofTree.parseWeight,
        CheckedPAProofTree.binaryLength,
        CheckedPAProofTree.binaryCode, List.length_append]
      omega
  | exs Gamma phi witness premise ih =>
      simp only [CheckedPAProofTree.binaryLength] at ih
      have htag := two_le_binaryNatCode_length 6
      have hseq := sequentSymbolCount_le_binarySequentCode_length Gamma
      have hphi := formulaSymbolCount_le_binaryFormulaCode_length phi
      have hwitness := termSymbolCount_le_binaryTermCode_length witness
      simp only [CheckedPAProofTree.parseWeight,
        CheckedPAProofTree.binaryLength,
        CheckedPAProofTree.binaryCode, List.length_append]
      omega
  | wk Gamma premise ih =>
      simp only [CheckedPAProofTree.binaryLength] at ih
      have htag := two_le_binaryNatCode_length 7
      have hseq := sequentSymbolCount_le_binarySequentCode_length Gamma
      simp only [CheckedPAProofTree.parseWeight,
        CheckedPAProofTree.binaryLength,
        CheckedPAProofTree.binaryCode, List.length_append]
      omega
  | shift Gamma premise ih =>
      simp only [CheckedPAProofTree.binaryLength] at ih
      have htag := two_le_binaryNatCode_length 8
      have hseq := sequentSymbolCount_le_binarySequentCode_length Gamma
      simp only [CheckedPAProofTree.parseWeight,
        CheckedPAProofTree.binaryLength,
        CheckedPAProofTree.binaryCode, List.length_append]
      omega
  | cut Gamma phi left right ihLeft ihRight =>
      simp only [CheckedPAProofTree.binaryLength] at ihLeft ihRight
      have htag := two_le_binaryNatCode_length 9
      have hseq := sequentSymbolCount_le_binarySequentCode_length Gamma
      have hphi := formulaSymbolCount_le_binaryFormulaCode_length phi
      simp only [CheckedPAProofTree.parseWeight,
        CheckedPAProofTree.binaryLength,
        CheckedPAProofTree.binaryCode, List.length_append]
      omega

theorem CheckedPAProofTree.decodeBinaryProofRaw_binaryCode
    (b : CheckedPAProofTree) :
    decodeBinaryProofRaw (b.binaryCode.length + 1) b.binaryCode =
      some ((b.rawCode, (⌜b.conclusion⌝ : Nat)), []) := by
  have hfuel : b.parseWeight < b.binaryCode.length + 1 := by
    have h := b.parseWeight_le_binaryLength
    simp only [CheckedPAProofTree.binaryLength] at h
    omega
  simpa using
    b.decodeBinaryProofRaw_binaryCode_append
      (b.binaryCode.length + 1) hfuel []

def CheckedPAProofTree.packedCode (b : CheckedPAProofTree) : Nat :=
  packBinaryString b.binaryCode

@[simp] theorem CheckedPAProofTree.size_packedCode
    (b : CheckedPAProofTree) :
    Nat.size b.packedCode = b.binaryLength + 1 := by
  simp [CheckedPAProofTree.packedCode,
    CheckedPAProofTree.binaryLength]

@[simp] theorem CheckedPAProofTree.decodePacked_packedCode
    (b : CheckedPAProofTree) :
    decodePackedCheckedPAProof b.packedCode =
      some (b.rawCode, (⌜b.conclusion⌝ : Nat)) := by
  simp [decodePackedCheckedPAProof,
    CheckedPAProofTree.packedCode,
    CheckedPAProofTree.decodeBinaryProofRaw_binaryCode]

/-- Erase only proof-irrelevant fields from a real Foundation derivation.
The displayed syntax and recursive rule tree are retained verbatim. -/
def CheckedPAProofTree.ofDerivation :
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition} →
      LO.FirstOrder.Derivation2 PA Gamma → CheckedPAProofTree
  | _, .closed Gamma phi _ _ => .closed Gamma phi
  | Gamma, .axm sigma _ _ => .axm Gamma sigma
  | Gamma, .verum _ => .verum Gamma
  | Gamma, .and (φ := phi) (ψ := psi) _ left right =>
      .and Gamma phi psi (ofDerivation left) (ofDerivation right)
  | Gamma, .or (φ := phi) (ψ := psi) _ premise =>
      .or Gamma phi psi (ofDerivation premise)
  | Gamma, .all (φ := phi) _ premise =>
      .all Gamma phi (ofDerivation premise)
  | Gamma, .exs (φ := phi) _ witness premise =>
      .exs Gamma phi witness (ofDerivation premise)
  | Gamma, .wk premise _ => .wk Gamma (ofDerivation premise)
  | _, .shift (Γ := Delta) premise =>
      .shift (Delta.image Rewriting.shift) (ofDerivation premise)
  | Gamma, .cut (φ := phi) left right =>
      .cut Gamma phi (ofDerivation left) (ofDerivation right)

@[simp] theorem CheckedPAProofTree.conclusion_ofDerivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (b : LO.FirstOrder.Derivation2 PA Gamma) :
    (CheckedPAProofTree.ofDerivation b).conclusion = Gamma := by
  cases b <;> rfl

@[simp] theorem CheckedPAProofTree.binaryCode_ofDerivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (b : LO.FirstOrder.Derivation2 PA Gamma) :
    (CheckedPAProofTree.ofDerivation b).binaryCode =
      binaryDerivationCode b := by
  induction b <;>
    simp [CheckedPAProofTree.ofDerivation,
      CheckedPAProofTree.binaryCode, binaryDerivationCode, *]

@[simp] theorem CheckedPAProofTree.binaryLength_ofDerivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (b : LO.FirstOrder.Derivation2 PA Gamma) :
    (CheckedPAProofTree.ofDerivation b).binaryLength =
      binaryProofLength b := by
  simp [CheckedPAProofTree.binaryLength, binaryProofLength]

@[simp] theorem CheckedPAProofTree.fstIdx_rawCode
    (b : CheckedPAProofTree) :
    LO.FirstOrder.Arithmetic.fstIdx b.rawCode =
      (⌜b.conclusion⌝ : Nat) := by
  cases b <;>
    simp [CheckedPAProofTree.rawCode,
      CheckedPAProofTree.conclusion]

theorem CheckedPAProofTree.valid_iff_derivationOf
    (b : CheckedPAProofTree) :
    b.Valid ↔
      LO.FirstOrder.Arithmetic.Bootstrapping.DerivationOf
        PA b.rawCode (⌜b.conclusion⌝ : Nat) := by
  simp [CheckedPAProofTree.Valid,
    LO.FirstOrder.Arithmetic.Bootstrapping.DerivationOf]

/-- Checker soundness for the efficient certificate coordinate: acceptance
produces a real PA derivation of exactly the displayed conclusion. -/
theorem CheckedPAProofTree.Valid.toDerivation
    {b : CheckedPAProofTree} (hb : b.Valid) :
    Nonempty (LO.FirstOrder.Derivation2 PA b.conclusion) := by
  rcases
      LO.FirstOrder.Arithmetic.Bootstrapping.Derivation.sound hb with
    ⟨Gamma, hGamma, hderivation⟩
  have hEq : Gamma = b.conclusion :=
    LO.FirstOrder.Derivation2.Sequent.quote_inj (V := Nat) (by
      simpa using hGamma)
  rcases hderivation with ⟨d⟩
  exact ⟨LO.FirstOrder.Derivation2.cast d hEq⟩

@[simp] theorem CheckedPAProofTree.rawCode_ofDerivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (b : LO.FirstOrder.Derivation2 PA Gamma) :
    (CheckedPAProofTree.ofDerivation b).rawCode =
      (LO.FirstOrder.Derivation2.typedQuote Nat b).val := by
  induction b <;>
    simp [CheckedPAProofTree.ofDerivation,
      CheckedPAProofTree.rawCode,
      LO.FirstOrder.Derivation2.typedQuote,
      LO.FirstOrder.Semiformula.quote_def,
      LO.FirstOrder.Semiterm.quote_def,
      LO.FirstOrder.Sentence.quote_def,
      LO.FirstOrder.Sentence.typed_quote_def,
      ← LO.FirstOrder.Derivation2.setShift_typed_quote, *]

/-- Erasing proof-irrelevant fields from a real derivation cannot create a
new assumption: the resulting certificate is accepted by Foundation's same
PA checker. -/
theorem CheckedPAProofTree.valid_ofDerivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (b : LO.FirstOrder.Derivation2 PA Gamma) :
    (CheckedPAProofTree.ofDerivation b).Valid := by
  let q := LO.FirstOrder.Derivation2.typedQuote Nat b
  have hq :
      LO.FirstOrder.Arithmetic.Bootstrapping.Derivation PA q.val :=
    q.derivationOf.2
  simpa [CheckedPAProofTree.Valid, q] using hq

/-! ## Same-coordinate bounded proof predicate -/

def packedPayloadLength (code : Nat) : Nat :=
  Nat.size code - 1

@[simp] theorem CheckedPAProofTree.packedPayloadLength_packedCode
    (b : CheckedPAProofTree) :
    packedPayloadLength b.packedCode = b.binaryLength := by
  simp [packedPayloadLength]

/-- The concrete proof predicate before arithmetization.  The decoded raw code
must prove exactly the requested singleton conclusion in Foundation's PA
checker. -/
def PackedPAProofChecks (code formulaCode : Nat) : Prop :=
  ∃ rawCode : Nat,
    decodePackedCheckedPAProof code =
      some (rawCode, 2 ^ formulaCode) ∧
    LO.FirstOrder.Arithmetic.Bootstrapping.Proof
      PA rawCode formulaCode

/-- Pudlak's bounded predicate `P(x,y)` on the honest binary coordinate. -/
def EfficientPAProofPredicate (bound formulaCode : Nat) : Prop :=
  ∃ code : Nat,
    packedPayloadLength code ≤ bound ∧
      PackedPAProofChecks code formulaCode

def CheckedPAProofTree.Proves
    (b : CheckedPAProofTree)
    (formula : LO.FirstOrder.ArithmeticProposition) : Prop :=
  b.Valid ∧ b.conclusion = {formula}

theorem CheckedPAProofTree.Proves.rawProof
    {b : CheckedPAProofTree}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (h : b.Proves formula) :
    LO.FirstOrder.Arithmetic.Bootstrapping.Proof
      PA b.rawCode (Encodable.encode formula) := by
  have hd := b.valid_iff_derivationOf.mp h.1
  rw [h.2] at hd
  simpa [LO.FirstOrder.Arithmetic.Bootstrapping.Proof,
    LO.FirstOrder.Semiformula.quote_eq_encode] using hd

theorem CheckedPAProofTree.Proves.packedChecks
    {b : CheckedPAProofTree}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (h : b.Proves formula) :
    PackedPAProofChecks b.packedCode (Encodable.encode formula) := by
  refine ⟨b.rawCode, ?_, h.rawProof⟩
  rw [b.decodePacked_packedCode, h.2]
  simp [LO.FirstOrder.Derivation2.Sequent.quote_def,
    LO.FirstOrder.Semiformula.quote_eq_encode]

theorem CheckedPAProofTree.Proves.efficientPredicate
    {b : CheckedPAProofTree}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (h : b.Proves formula) :
    EfficientPAProofPredicate b.binaryLength
      (Encodable.encode formula) := by
  exact ⟨b.packedCode, by simp, h.packedChecks⟩

theorem derivation_to_efficientPredicate
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (b : LO.FirstOrder.Derivation2 PA Gamma)
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hGamma : Gamma = {formula}) :
    EfficientPAProofPredicate (binaryProofLength b)
      (Encodable.encode formula) := by
  let tree := CheckedPAProofTree.ofDerivation b
  have hproves : tree.Proves formula := by
    constructor
    · exact CheckedPAProofTree.valid_ofDerivation b
    · simpa [tree] using hGamma
  simpa [tree] using hproves.efficientPredicate

theorem packedPAProofChecks_sound
    {code : Nat}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hcheck : PackedPAProofChecks code (Encodable.encode formula)) :
    Nonempty (LO.FirstOrder.Derivation2 PA {formula}) := by
  rcases hcheck with ⟨rawCode, _, hraw⟩
  exact ⟨
    LO.FirstOrder.Arithmetic.Bootstrapping.Provable.sound2
      (T := PA) (by
        refine ⟨rawCode, ?_⟩
        simpa [LO.FirstOrder.Semiformula.quote_eq_encode] using hraw)⟩

theorem binaryProofLength_exists (amplification n : Nat) :
    ∃ k : Nat,
      ∃ b :
        PA ⊢!₂!
          (succinctFiniteConsistencySentence amplification n :
            LO.FirstOrder.ArithmeticProposition),
        binaryProofLength b = k := by
  have hproof :
      Nonempty
        (PA ⊢!₂!
          (succinctFiniteConsistencySentence amplification n :
            LO.FirstOrder.ArithmeticProposition)) :=
    (LO.FirstOrder.provable_iff_derivable2 (T := PA)).mp
      (provable_succinctFiniteConsistencySentence amplification n)
  rcases hproof with ⟨b⟩
  exact ⟨binaryProofLength b, b, rfl⟩

noncomputable def minBinaryProofLength
    (amplification n : Nat) : Nat := by
  classical
  exact Nat.find (binaryProofLength_exists amplification n)

theorem minBinaryProofLength_spec (amplification n : Nat) :
    ∃ b :
      PA ⊢!₂!
        (succinctFiniteConsistencySentence amplification n :
          LO.FirstOrder.ArithmeticProposition),
      binaryProofLength b = minBinaryProofLength amplification n := by
  classical
  exact Nat.find_spec (binaryProofLength_exists amplification n)

theorem minBinaryProofLength_le
    (amplification n : Nat)
    (b :
      PA ⊢!₂!
        (succinctFiniteConsistencySentence amplification n :
          LO.FirstOrder.ArithmeticProposition)) :
    minBinaryProofLength amplification n ≤ binaryProofLength b := by
  classical
  exact Nat.find_min'
    (binaryProofLength_exists amplification n)
    ⟨b, rfl⟩

#check val_powTwoTerm
#print axioms val_powTwoTerm

#check powTwoTerm_complexity_le
#print axioms powTwoTerm_complexity_le

#check powTwoTerm_symbolCount
#print axioms powTwoTerm_symbolCount

#check models_succinctFiniteConsistencySentence_iff
#print axioms models_succinctFiniteConsistencySentence_iff

#check checks_complete
#print axioms checks_complete

#check checks_to_real_derivation
#print axioms checks_to_real_derivation

#check minStructuralProofLength_spec
#print axioms minStructuralProofLength_spec

#check minBinaryProofLength_spec
#print axioms minBinaryProofLength_spec

#check CheckedPAProofTree.decodePacked_packedCode
#print axioms CheckedPAProofTree.decodePacked_packedCode

#check derivation_to_efficientPredicate
#print axioms derivation_to_efficientPredicate

#check packedPAProofChecks_sound
#print axioms packedPAProofChecks_sound

end FoundationSuccinctFiniteConsistencyTarget
