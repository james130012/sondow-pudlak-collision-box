import integration.FoundationCompactSyntaxTransformationBounds
import integration.FoundationCompactCanonicalDecodeLength
import integration.FoundationCompactVerifierFormulaListChecks

/-!
# Binary-code bounds for checker syntax transformations

The local certificate checker compares canonical binary codes after applying
`shift`, `free`, negation, and one-variable substitution.  Symbol-count bounds
alone do not control large variable indices, so this file works directly with
the emitted binary-code lengths.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactSyntaxTransformationCodeBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCanonicalDecodeLength
open FoundationCompactSyntaxTransformationBounds

theorem natSize_add_one_le (value : Nat) :
    Nat.size (value + 1) <= Nat.size value + 1 := by
  rw [Nat.size_le]
  have hvalue : value + 1 <= 2 ^ Nat.size value :=
    Nat.succ_le_iff.mpr (Nat.lt_size_self value)
  exact hvalue.trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat))
      (Nat.lt_succ_self (Nat.size value)))

theorem binaryTermCode_shift_length_le
    {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermCode (Rew.shift term)).length <=
      2 * (binaryTermCode term).length := by
  induction term with
  | bvar index =>
      simp [binaryTermCode]
      omega
  | fvar index =>
      have hsize := natSize_add_one_le index
      simp [binaryTermCode, binaryNatCode_length]
      omega
  | func functionSymbol arguments ih =>
      simp only [Rew.func, binaryTermCode, List.length_append]
      rw [length_flatten_ofFn, length_flatten_ofFn]
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode (Rew.shift (arguments index))).length) <=
            Finset.univ.sum
              (fun index => 2 * (binaryTermCode (arguments index)).length) :=
        Finset.sum_le_sum (fun index _ => ih index)
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode
                  ((Rew.shift ∘ arguments) index)).length) <=
            2 * Finset.univ.sum
              (fun index => (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
                (fun index =>
                  2 * (binaryTermCode (arguments index)).length) := by
            simpa [Function.comp_def] using hchildren
          _ = _ := by rw [Finset.mul_sum]
      have hchildrenBound :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode (Rew.shift (arguments index))).length) <=
            2 * Finset.univ.sum
              (fun index => (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
                (fun index =>
                  2 * (binaryTermCode (arguments index)).length) := hchildren
          _ = _ := by rw [Finset.mul_sum]
      omega

theorem binaryFormulaCode_shift_length_le
    {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    (binaryFormulaCode (Rewriting.shift formula)).length <=
      2 * (binaryFormulaCode formula).length := by
  induction formula using Semiformula.rec' with
  | hverum =>
      simp [binaryFormulaCode]
      omega
  | hfalsum =>
      simp [binaryFormulaCode]
      omega
  | hrel relationSymbol arguments =>
      simp only [Semiformula.rew_rel, binaryFormulaCode,
        List.length_append]
      rw [length_flatten_ofFn, length_flatten_ofFn]
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode (Rew.shift (arguments index))).length) <=
            Finset.univ.sum
              (fun index =>
                2 * (binaryTermCode (arguments index)).length) :=
        Finset.sum_le_sum
          (fun index _ => binaryTermCode_shift_length_le (arguments index))
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode
                  ((Rew.shift ∘ arguments) index)).length) <=
            2 * Finset.univ.sum
              (fun index => (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
                (fun index =>
                  2 * (binaryTermCode (arguments index)).length) := by
            simpa [Function.comp_def] using hchildren
          _ = _ := by rw [Finset.mul_sum]
      have hchildrenBound :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode (Rew.shift (arguments index))).length) <=
            2 * Finset.univ.sum
              (fun index => (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
                (fun index =>
                  2 * (binaryTermCode (arguments index)).length) := hchildren
          _ = _ := by rw [Finset.mul_sum]
      omega
  | hnrel relationSymbol arguments =>
      simp only [Semiformula.rew_nrel, binaryFormulaCode,
        List.length_append]
      rw [length_flatten_ofFn, length_flatten_ofFn]
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode (Rew.shift (arguments index))).length) <=
            Finset.univ.sum
              (fun index =>
                2 * (binaryTermCode (arguments index)).length) :=
        Finset.sum_le_sum
          (fun index _ => binaryTermCode_shift_length_le (arguments index))
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode
                  ((Rew.shift ∘ arguments) index)).length) <=
            2 * Finset.univ.sum
              (fun index => (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
                (fun index =>
                  2 * (binaryTermCode (arguments index)).length) := by
            simpa [Function.comp_def] using hchildren
          _ = _ := by rw [Finset.mul_sum]
      have hchildrenBound :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode (Rew.shift (arguments index))).length) <=
            2 * Finset.univ.sum
              (fun index => (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
                (fun index =>
                  2 * (binaryTermCode (arguments index)).length) := hchildren
          _ = _ := by rw [Finset.mul_sum]
      omega
  | hand left right ihLeft ihRight =>
      simp only [LogicalConnective.HomClass.map_and, binaryFormulaCode,
        List.length_append]
      omega
  | hor left right ihLeft ihRight =>
      simp only [LogicalConnective.HomClass.map_or, binaryFormulaCode,
        List.length_append]
      omega
  | hall body ih =>
      simp only [Rewriting.app_all, Rew.q_shift, binaryFormulaCode,
        List.length_append]
      have ih' :
          (binaryFormulaCode ((Rewriting.app Rew.shift) body)).length <=
            2 * (binaryFormulaCode body).length := by
        simpa using ih
      omega
  | hexs body ih =>
      simp only [Rewriting.app_exs, Rew.q_shift, binaryFormulaCode,
        List.length_append]
      have ih' :
          (binaryFormulaCode ((Rewriting.app Rew.shift) body)).length <=
            2 * (binaryFormulaCode body).length := by
        simpa using ih
      omega

theorem binaryTermCode_free_length_le
    {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat (arity + 1)) :
    (binaryTermCode (Rew.free term)).length <=
      2 * (binaryTermCode term).length := by
  induction term with
  | bvar index =>
      cases index using Fin.lastCases
      all_goals simp [binaryTermCode, binaryNatCode_length] <;> omega
  | fvar index =>
      have hsize := natSize_add_one_le index
      simp [binaryTermCode, binaryNatCode_length]
      omega
  | func functionSymbol arguments ih =>
      simp only [Rew.func, binaryTermCode, List.length_append]
      rw [length_flatten_ofFn, length_flatten_ofFn]
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode (Rew.free (arguments index))).length) <=
            Finset.univ.sum
              (fun index => 2 * (binaryTermCode (arguments index)).length) :=
        Finset.sum_le_sum (fun index _ => ih index)
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode
                  ((Rew.free ∘ arguments) index)).length) <=
            2 * Finset.univ.sum
              (fun index => (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
                (fun index =>
                  2 * (binaryTermCode (arguments index)).length) := by
            simpa [Function.comp_def] using hchildren
          _ = _ := by rw [Finset.mul_sum]
      omega

def freeFormulaAlong
    {sourceArity targetArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat sourceArity)
    (harity : sourceArity = targetArity + 1) :
    LO.FirstOrder.ArithmeticSemiformula Nat targetArity := by
  subst sourceArity
  exact Rewriting.free formula

theorem binaryFormulaCode_freeAlong_length_le
    {sourceArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat sourceArity) :
    forall {targetArity : Nat}
      (harity : sourceArity = targetArity + 1),
      (binaryFormulaCode (freeFormulaAlong formula harity)).length <=
        2 * (binaryFormulaCode formula).length := by
  induction formula using Semiformula.rec' with
  | hverum =>
      intro targetArity harity
      cases harity
      simp [freeFormulaAlong, binaryFormulaCode]
      omega
  | hfalsum =>
      intro targetArity harity
      cases harity
      simp [freeFormulaAlong, binaryFormulaCode]
      omega
  | hrel relationSymbol arguments =>
      intro targetArity harity
      cases harity
      simp only [freeFormulaAlong, Semiformula.rew_rel,
        binaryFormulaCode, List.length_append]
      rw [length_flatten_ofFn, length_flatten_ofFn]
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode (Rew.free (arguments index))).length) <=
            Finset.univ.sum
              (fun index =>
                2 * (binaryTermCode (arguments index)).length) :=
        Finset.sum_le_sum
          (fun index _ => binaryTermCode_free_length_le (arguments index))
      have hchildrenBound :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode (Rew.free (arguments index))).length) <=
            2 * Finset.univ.sum
              (fun index => (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
                (fun index =>
                  2 * (binaryTermCode (arguments index)).length) := hchildren
          _ = _ := by rw [Finset.mul_sum]
      omega
  | hnrel relationSymbol arguments =>
      intro targetArity harity
      cases harity
      simp only [freeFormulaAlong, Semiformula.rew_nrel,
        binaryFormulaCode, List.length_append]
      rw [length_flatten_ofFn, length_flatten_ofFn]
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode (Rew.free (arguments index))).length) <=
            Finset.univ.sum
              (fun index =>
                2 * (binaryTermCode (arguments index)).length) :=
        Finset.sum_le_sum
          (fun index _ => binaryTermCode_free_length_le (arguments index))
      have hchildrenBound :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode (Rew.free (arguments index))).length) <=
            2 * Finset.univ.sum
              (fun index => (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
                (fun index =>
                  2 * (binaryTermCode (arguments index)).length) := hchildren
          _ = _ := by rw [Finset.mul_sum]
      omega
  | hand left right ihLeft ihRight =>
      intro targetArity harity
      cases harity
      have hleft := ihLeft (targetArity := targetArity) rfl
      have hright := ihRight (targetArity := targetArity) rfl
      simp only [freeFormulaAlong,
        LogicalConnective.HomClass.map_and, binaryFormulaCode,
        List.length_append] at hleft hright ⊢
      omega
  | hor left right ihLeft ihRight =>
      intro targetArity harity
      cases harity
      have hleft := ihLeft (targetArity := targetArity) rfl
      have hright := ihRight (targetArity := targetArity) rfl
      simp only [freeFormulaAlong,
        LogicalConnective.HomClass.map_or, binaryFormulaCode,
        List.length_append] at hleft hright ⊢
      omega
  | hall body ih =>
      intro targetArity harity
      cases harity
      have hbody := ih (targetArity := targetArity + 1) rfl
      simp only [freeFormulaAlong, Rewriting.app_all, Rew.q_free,
        binaryFormulaCode, List.length_append] at hbody ⊢
      have hbody' :
          (binaryFormulaCode ((Rewriting.app Rew.free) body)).length <=
            2 * (binaryFormulaCode body).length := by
        simpa using hbody
      omega
  | hexs body ih =>
      intro targetArity harity
      cases harity
      have hbody := ih (targetArity := targetArity + 1) rfl
      simp only [freeFormulaAlong, Rewriting.app_exs, Rew.q_free,
        binaryFormulaCode, List.length_append] at hbody ⊢
      have hbody' :
          (binaryFormulaCode ((Rewriting.app Rew.free) body)).length <=
            2 * (binaryFormulaCode body).length := by
        simpa using hbody
      omega

theorem binaryFormulaCode_free_length_le
    {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat (arity + 1)) :
    (binaryFormulaCode (Rewriting.free formula)).length <=
      2 * (binaryFormulaCode formula).length := by
  simpa [freeFormulaAlong] using
    (binaryFormulaCode_freeAlong_length_le formula
      (targetArity := arity) rfl)

theorem binaryFormulaCode_neg_length_le
    {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    (binaryFormulaCode (∼formula)).length <=
      2 * (binaryFormulaCode formula).length := by
  have htag23 : Nat.size 2 = Nat.size 3 := by decide
  have htag45 : Nat.size 4 = Nat.size 5 := by decide
  have htag67 : Nat.size 6 = Nat.size 7 := by decide
  induction formula using Semiformula.rec' <;>
    simp [binaryFormulaCode, binaryNatCode_length, *] <;> omega

theorem four_le_binaryTermCode_length
    {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    4 <= (binaryTermCode term).length := by
  cases term with
  | bvar index =>
      have htag := two_le_binaryNatCode_length 0
      have hindex := two_le_binaryNatCode_length index.val
      simp only [binaryTermCode, List.length_append]
      omega
  | fvar index =>
      have htag := two_le_binaryNatCode_length 1
      have hindex := two_le_binaryNatCode_length index
      simp only [binaryTermCode, List.length_append]
      omega
  | func functionSymbol arguments =>
      have htag := two_le_binaryNatCode_length 2
      have hfunction :=
        two_le_binaryNatCode_length (Encodable.encode functionSymbol)
      simp only [binaryTermCode, List.length_append]
      omega

theorem binaryTermCode_bShift_length_le_add_symbols
    {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermCode (Rew.bShift term)).length <=
      (binaryTermCode term).length + 2 * termSymbolCount term := by
  induction term with
  | bvar index =>
      have hsize := natSize_add_one_le index.val
      simp [binaryTermCode, binaryNatCode_length, termSymbolCount]
      omega

  | fvar index =>
      simp [binaryTermCode, termSymbolCount]
  | func functionSymbol arguments ih =>
      simp only [Rew.func, binaryTermCode, termSymbolCount,
        List.length_append]
      rw [length_flatten_ofFn, length_flatten_ofFn]
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode (Rew.bShift (arguments index))).length) <=
            Finset.univ.sum
              (fun index =>
                (binaryTermCode (arguments index)).length +
                  2 * termSymbolCount (arguments index)) :=
        Finset.sum_le_sum (fun index _ => ih index)
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode
                  ((Rew.bShift ∘ arguments) index)).length) <=
            Finset.univ.sum
                (fun index => (binaryTermCode (arguments index)).length) +
              2 * Finset.univ.sum
                (fun index => termSymbolCount (arguments index)) := by
        calc
          _ <= Finset.univ.sum
                (fun index =>
                  (binaryTermCode (arguments index)).length +
                    2 * termSymbolCount (arguments index)) := by
            simpa [Function.comp_def] using hchildren
          _ = _ := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
      omega

def substitutionCodeFactor
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat -> Nat
  | 0 => (binaryTermCode witness).length
  | depth + 1 =>
      substitutionCodeFactor witness depth +
        2 * termSymbolCount witness

theorem four_le_substitutionCodeFactor
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat) :
    4 <= substitutionCodeFactor witness depth := by
  induction depth with
  | zero =>
      simpa [substitutionCodeFactor] using
        four_le_binaryTermCode_length witness
  | succ depth ih =>
      simp only [substitutionCodeFactor]
      omega

theorem substitutionOne_qpow_termImageBound
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat) :
    RewritingTermImageBound
      ((Rew.subst ![witness]).qpow depth)
      (termSymbolCount witness) := by
  induction depth with
  | zero =>
      simpa using substitutionOne_termImageBound witness
  | succ depth ih =>
      simpa [Rew.qpow] using
        ih.q (one_le_termSymbolCount witness)

theorem qpow_substitutionOne_bvar_code_length_le
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    forall (depth : Nat) (index : Fin (1 + depth)),
      (binaryTermCode
          (((Rew.subst ![witness]).qpow depth)
            (#index : LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth)))).length <=
        substitutionCodeFactor witness depth := by
  intro depth
  induction depth with
  | zero =>
      intro index
      have hindex : index = 0 := Fin.eq_zero index
      subst index
      simp [Rew.qpow, substitutionCodeFactor]
  | succ depth ih =>
      intro index
      cases index using Fin.cases with
      | zero =>
          have hfactor := four_le_substitutionCodeFactor witness (depth + 1)
          simpa [Rew.qpow, binaryTermCode, binaryNatCode_length] using hfactor
      | succ index =>
          have hprevious := ih index
          have hsymbols :=
            (substitutionOne_qpow_termImageBound witness depth).1 index
          have hshift :=
            binaryTermCode_bShift_length_le_add_symbols
              (((Rew.subst ![witness]).qpow depth)
                (#index : LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth)))
          simp only [Rew.qpow, Rew.q_bvar_succ]
          simp only [substitutionCodeFactor]
          omega

theorem qpow_substitutionOne_fvar_eq
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    forall (depth freeIndex : Nat),
      ((Rew.subst ![witness]).qpow depth)
          (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth)) =
        (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat (0 + depth)) := by
  intro depth
  induction depth with
  | zero =>
      intro freeIndex
      simp [Rew.qpow]
  | succ depth ih =>
      intro freeIndex
      simp [Rew.qpow, ih]

theorem binaryTermCode_substitutionOne_qpow_length_le
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth)) :
    (binaryTermCode (((Rew.subst ![witness]).qpow depth) term)).length <=
      substitutionCodeFactor witness depth *
        (binaryTermCode term).length := by
  induction term with
  | bvar index =>
      have himage :=
        qpow_substitutionOne_bvar_code_length_le witness depth index
      have hinput := four_le_binaryTermCode_length
        (#index : LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth))
      have hfactor := four_le_substitutionCodeFactor witness depth
      have hmul := Nat.mul_le_mul_left
        (substitutionCodeFactor witness depth)
        (show 1 <= (binaryTermCode
            (#index : LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth))).length by
          omega)
      exact himage.trans (by simpa using hmul)
  | fvar freeIndex =>
      have heq := qpow_substitutionOne_fvar_eq witness depth freeIndex
      have hfactor := four_le_substitutionCodeFactor witness depth
      have hfactorOne : 1 <= substitutionCodeFactor witness depth := by
        omega
      rw [heq]
      have hmul := Nat.mul_le_mul_left
        (binaryTermCode
          (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat (0 + depth))).length
        hfactorOne
      simpa [binaryTermCode, Nat.mul_comm] using hmul
  | func functionSymbol arguments ih =>
      rename_i functionArity
      simp only [Rew.func, binaryTermCode, List.length_append]
      rw [length_flatten_ofFn, length_flatten_ofFn]
      let factor := substitutionCodeFactor witness depth
      let header :=
        (binaryNatCode 2).length +
          (binaryNatCode functionArity).length +
          (binaryNatCode (Encodable.encode functionSymbol)).length
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode
                  (((Rew.subst ![witness]).qpow depth)
                    (arguments index))).length) <=
            Finset.univ.sum
              (fun index =>
                factor * (binaryTermCode (arguments index)).length) :=
        Finset.sum_le_sum (fun index _ => ih index)
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode
                  ((((Rew.subst ![witness]).qpow depth) ∘
                    arguments) index)).length) <=
            factor * Finset.univ.sum
              (fun index => (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
                (fun index =>
                  factor * (binaryTermCode (arguments index)).length) := by
            simpa [Function.comp_def] using hchildren
          _ = _ := by rw [Finset.mul_sum]
      have hfactor : 1 <= factor := by
        dsimp [factor]
        have := four_le_substitutionCodeFactor witness depth
        omega
      have hheader : header <= factor * header := by
        have hmul := Nat.mul_le_mul_left header hfactor
        simpa [Nat.mul_comm] using hmul
      change header +
          Finset.univ.sum
            (fun index =>
              (binaryTermCode
                ((((Rew.subst ![witness]).qpow depth) ∘
                  arguments) index)).length) <=
        factor *
          (header + Finset.univ.sum
            (fun index => (binaryTermCode (arguments index)).length))
      calc
        _ <= header + factor * Finset.univ.sum
              (fun index => (binaryTermCode (arguments index)).length) :=
          Nat.add_le_add_left hchildren' header
        _ <= factor * header + factor * Finset.univ.sum
              (fun index => (binaryTermCode (arguments index)).length) :=
          Nat.add_le_add_right hheader _
        _ = _ := by simp [header, Nat.mul_add, Nat.add_assoc]

theorem substitutionCodeFactor_monotone
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    Monotone (substitutionCodeFactor witness) := by
  apply monotone_nat_of_le_succ
  intro depth
  simp only [substitutionCodeFactor]
  omega

theorem payload_le_factor_mul_payload
    {factor payload : Nat} (hfactor : 1 <= factor) :
    payload <= factor * payload := by
  have hmul := Nat.mul_le_mul_left payload hfactor
  simpa [Nat.mul_comm] using hmul

theorem header_payload_le_factor_mul
    {factor header inputPayload outputPayload : Nat}
    (hfactor : 1 <= factor)
    (hpayload : outputPayload <= factor * inputPayload) :
    header + outputPayload <= factor * (header + inputPayload) := by
  have hheader := payload_le_factor_mul_payload
    (payload := header) hfactor
  calc
    header + outputPayload <=
        factor * header + factor * inputPayload :=
      Nat.add_le_add hheader hpayload
    _ = factor * (header + inputPayload) := by rw [Nat.mul_add]

theorem header_two_payloads_le_factor_mul
    {factor header inputLeft inputRight outputLeft outputRight : Nat}
    (hfactor : 1 <= factor)
    (hleft : outputLeft <= factor * inputLeft)
    (hright : outputRight <= factor * inputRight) :
    header + outputLeft + outputRight <=
      factor * (header + inputLeft + inputRight) := by
  have hheader := payload_le_factor_mul_payload
    (payload := header) hfactor
  calc
    header + outputLeft + outputRight <=
        factor * header + factor * inputLeft + factor * inputRight :=
      Nat.add_le_add (Nat.add_le_add hheader hleft) hright
    _ = factor * (header + inputLeft + inputRight) := by
      simp [Nat.mul_add, Nat.add_assoc]

def substituteFormulaAlong
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat)
    {sourceArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat sourceArity)
    (harity : sourceArity = 1 + depth) :
    LO.FirstOrder.ArithmeticSemiformula Nat (0 + depth) := by
  subst sourceArity
  exact Rewriting.app ((Rew.subst ![witness]).qpow depth) formula

theorem binaryFormulaCode_substitutionAlong_length_le
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    {sourceArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat sourceArity) :
    forall (depth budget : Nat)
      (harity : sourceArity = 1 + depth),
      depth + formulaSymbolCount formula <= budget ->
      (binaryFormulaCode
          (substituteFormulaAlong witness depth formula harity)).length <=
        substitutionCodeFactor witness budget *
          (binaryFormulaCode formula).length := by
  induction formula using Semiformula.rec' with
  | hverum =>
      intro depth budget harity hbudget
      cases harity
      have hfactor := four_le_substitutionCodeFactor witness budget
      have hfactorOne : 1 <= substitutionCodeFactor witness budget := by omega
      simpa [substituteFormulaAlong, binaryFormulaCode] using
        (payload_le_factor_mul_payload
          (payload := (binaryNatCode 2).length) hfactorOne)
  | hfalsum =>
      intro depth budget harity hbudget
      cases harity
      have hfactor := four_le_substitutionCodeFactor witness budget
      have hfactorOne : 1 <= substitutionCodeFactor witness budget := by omega
      simpa [substituteFormulaAlong, binaryFormulaCode] using
        (payload_le_factor_mul_payload
          (payload := (binaryNatCode 3).length) hfactorOne)
  | hrel relationSymbol arguments =>
      intro depth budget harity hbudget
      cases harity
      simp only [substituteFormulaAlong, Semiformula.rew_rel,
        binaryFormulaCode, List.length_append]
      rw [length_flatten_ofFn, length_flatten_ofFn]
      let factor := substitutionCodeFactor witness budget
      let header :=
        (binaryNatCode 0).length +
          (binaryNatCode (List.ofFn arguments).length).length +
          (binaryNatCode (Encodable.encode relationSymbol)).length
      have hdepth : depth <= budget := by
        have hone := one_le_formulaSymbolCount
          (Semiformula.rel relationSymbol arguments)
        omega
      have hmono := substitutionCodeFactor_monotone witness hdepth
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode
                  (((Rew.subst ![witness]).qpow depth)
                    (arguments index))).length) <=
            Finset.univ.sum
              (fun index =>
                factor * (binaryTermCode (arguments index)).length) := by
        apply Finset.sum_le_sum
        intro index hindex
        have hterm := binaryTermCode_substitutionOne_qpow_length_le
          witness depth (arguments index)
        exact hterm.trans
          (Nat.mul_le_mul_right
            (binaryTermCode (arguments index)).length hmono)
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode
                  ((((Rew.subst ![witness]).qpow depth) ∘
                    arguments) index)).length) <=
            factor * Finset.univ.sum
              (fun index => (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
                (fun index =>
                  factor * (binaryTermCode (arguments index)).length) := by
            simpa [Function.comp_def] using hchildren
          _ = _ := by rw [Finset.mul_sum]
      have hfactor := four_le_substitutionCodeFactor witness budget
      have hfactorOne : 1 <= factor := by
        dsimp [factor]
        omega
      simpa [header] using
        (header_payload_le_factor_mul
          (factor := factor) (header := header)
          hfactorOne hchildren')
  | hnrel relationSymbol arguments =>
      intro depth budget harity hbudget
      cases harity
      simp only [substituteFormulaAlong, Semiformula.rew_nrel,
        binaryFormulaCode, List.length_append]
      rw [length_flatten_ofFn, length_flatten_ofFn]
      let factor := substitutionCodeFactor witness budget
      let header :=
        (binaryNatCode 1).length +
          (binaryNatCode (List.ofFn arguments).length).length +
          (binaryNatCode (Encodable.encode relationSymbol)).length
      have hdepth : depth <= budget := by
        have hone := one_le_formulaSymbolCount
          (Semiformula.nrel relationSymbol arguments)
        omega
      have hmono := substitutionCodeFactor_monotone witness hdepth
      have hchildren :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode
                  (((Rew.subst ![witness]).qpow depth)
                    (arguments index))).length) <=
            Finset.univ.sum
              (fun index =>
                factor * (binaryTermCode (arguments index)).length) := by
        apply Finset.sum_le_sum
        intro index hindex
        have hterm := binaryTermCode_substitutionOne_qpow_length_le
          witness depth (arguments index)
        exact hterm.trans
          (Nat.mul_le_mul_right
            (binaryTermCode (arguments index)).length hmono)
      have hchildren' :
          Finset.univ.sum
              (fun index =>
                (binaryTermCode
                  ((((Rew.subst ![witness]).qpow depth) ∘
                    arguments) index)).length) <=
            factor * Finset.univ.sum
              (fun index => (binaryTermCode (arguments index)).length) := by
        calc
          _ <= Finset.univ.sum
                (fun index =>
                  factor * (binaryTermCode (arguments index)).length) := by
            simpa [Function.comp_def] using hchildren
          _ = _ := by rw [Finset.mul_sum]
      have hfactor := four_le_substitutionCodeFactor witness budget
      have hfactorOne : 1 <= factor := by
        dsimp [factor]
        omega
      simpa [header] using
        (header_payload_le_factor_mul
          (factor := factor) (header := header)
          hfactorOne hchildren')
  | hand left right ihLeft ihRight =>
      intro depth budget harity hbudget
      cases harity
      have hleftBudget :
          depth + formulaSymbolCount left <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hrightBudget :
          depth + formulaSymbolCount right <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hleft := ihLeft depth budget rfl hleftBudget
      have hright := ihRight depth budget rfl hrightBudget
      have hfactor := four_le_substitutionCodeFactor witness budget
      have hfactorOne : 1 <= substitutionCodeFactor witness budget := by omega
      simpa [substituteFormulaAlong, binaryFormulaCode, Nat.add_assoc] using
        (header_two_payloads_le_factor_mul
          (factor := substitutionCodeFactor witness budget)
          (header := (binaryNatCode 4).length)
          hfactorOne hleft hright)
  | hor left right ihLeft ihRight =>
      intro depth budget harity hbudget
      cases harity
      have hleftBudget :
          depth + formulaSymbolCount left <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hrightBudget :
          depth + formulaSymbolCount right <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hleft := ihLeft depth budget rfl hleftBudget
      have hright := ihRight depth budget rfl hrightBudget
      have hfactor := four_le_substitutionCodeFactor witness budget
      have hfactorOne : 1 <= substitutionCodeFactor witness budget := by omega
      simpa [substituteFormulaAlong, binaryFormulaCode, Nat.add_assoc] using
        (header_two_payloads_le_factor_mul
          (factor := substitutionCodeFactor witness budget)
          (header := (binaryNatCode 5).length)
          hfactorOne hleft hright)
  | hall body ih =>
      intro depth budget harity hbudget
      cases harity
      have hbodyBudget :
          (depth + 1) + formulaSymbolCount body <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hbody := ih (depth + 1) budget rfl hbodyBudget
      have hfactor := four_le_substitutionCodeFactor witness budget
      have hfactorOne : 1 <= substitutionCodeFactor witness budget := by omega
      simpa [substituteFormulaAlong, Rew.qpow, binaryFormulaCode] using
        (header_payload_le_factor_mul
          (factor := substitutionCodeFactor witness budget)
          (header := (binaryNatCode 6).length)
          hfactorOne hbody)
  | hexs body ih =>
      intro depth budget harity hbudget
      cases harity
      have hbodyBudget :
          (depth + 1) + formulaSymbolCount body <= budget := by
        simp only [formulaSymbolCount] at hbudget
        omega
      have hbody := ih (depth + 1) budget rfl hbodyBudget
      have hfactor := four_le_substitutionCodeFactor witness budget
      have hfactorOne : 1 <= substitutionCodeFactor witness budget := by omega
      simpa [substituteFormulaAlong, Rew.qpow, binaryFormulaCode] using
        (header_payload_le_factor_mul
          (factor := substitutionCodeFactor witness budget)
          (header := (binaryNatCode 7).length)
          hfactorOne hbody)

theorem substitutionCodeFactor_eq
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat) :
    substitutionCodeFactor witness depth =
      (binaryTermCode witness).length +
        2 * depth * termSymbolCount witness := by
  induction depth with
  | zero =>
      simp [substitutionCodeFactor]
  | succ depth ih =>
      simp only [substitutionCodeFactor, ih]
      simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]

theorem substitutionCodeFactor_le_codePolynomial
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    substitutionCodeFactor witness (formulaSymbolCount formula) <=
      3 * ((binaryFormulaCode formula).length + 1) *
        ((binaryTermCode witness).length + 1) := by
  let formulaLength := (binaryFormulaCode formula).length
  let witnessLength := (binaryTermCode witness).length
  let product := (formulaLength + 1) * (witnessLength + 1)
  have hformula : formulaSymbolCount formula <= formulaLength := by
    simpa [formulaLength] using
      formulaSymbolCount_le_binaryFormulaCode_length formula
  have hwitness : termSymbolCount witness <= witnessLength := by
    simpa [witnessLength] using
      termSymbolCount_le_binaryTermCode_length witness
  have hproduct :
      formulaSymbolCount formula * termSymbolCount witness <= product := by
    dsimp [product]
    exact Nat.mul_le_mul
      (hformula.trans (Nat.le_succ formulaLength))
      (hwitness.trans (Nat.le_succ witnessLength))
  have hwitnessProduct : witnessLength <= product := by
    calc
      witnessLength <= witnessLength + 1 := Nat.le_succ _
      _ = 1 * (witnessLength + 1) := by simp
      _ <= (formulaLength + 1) * (witnessLength + 1) :=
        Nat.mul_le_mul_right _ (Nat.succ_pos formulaLength)
  have hproductTwice :
      2 * formulaSymbolCount formula * termSymbolCount witness <=
        2 * product := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hproduct
  rw [substitutionCodeFactor_eq]
  calc
    (binaryTermCode witness).length +
          2 * formulaSymbolCount formula * termSymbolCount witness <=
        product + 2 * product :=
      Nat.add_le_add hwitnessProduct hproductTwice
    _ = 3 * product := by omega
    _ = 3 * ((binaryFormulaCode formula).length + 1) *
        ((binaryTermCode witness).length + 1) := by
      simp [product, formulaLength, witnessLength, Nat.mul_assoc]

theorem binaryFormulaCode_substitution_one_length_le
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryFormulaCode (formula/[witness])).length <=
      3 * ((binaryFormulaCode formula).length + 1) *
        ((binaryTermCode witness).length + 1) *
        (binaryFormulaCode formula).length := by
  have hbudget :
      0 + formulaSymbolCount formula <= formulaSymbolCount formula := by
    simp
  have hsubstitution :=
    binaryFormulaCode_substitutionAlong_length_le witness formula
      0 (formulaSymbolCount formula) rfl hbudget
  have hfactor :=
    substitutionCodeFactor_le_codePolynomial formula witness
  have hscaled := Nat.mul_le_mul_right
    (binaryFormulaCode formula).length hfactor
  exact hsubstitution.trans (by
    simpa [substituteFormulaAlong, Rew.qpow, Nat.mul_assoc] using hscaled)

theorem formulaListCodeWeight_map_shift_le
    (formulas : List LO.FirstOrder.ArithmeticProposition) :
    FoundationCompactVerifierFormulaListChecks.formulaListCodeWeight
        (formulas.map Rewriting.shift) <=
      2 * FoundationCompactVerifierFormulaListChecks.formulaListCodeWeight
        formulas := by
  induction formulas with
  | nil => simp [FoundationCompactVerifierFormulaListChecks.formulaListCodeWeight]
  | cons formula formulas ih =>
      have hformula := binaryFormulaCode_shift_length_le formula
      simp only [List.map_cons,
        FoundationCompactVerifierFormulaListChecks.formulaListCodeWeight_cons]
      omega

#print axioms binaryTermCode_shift_length_le
#print axioms binaryFormulaCode_shift_length_le
#print axioms binaryTermCode_free_length_le
#print axioms binaryFormulaCode_free_length_le
#print axioms binaryFormulaCode_neg_length_le
#print axioms binaryTermCode_bShift_length_le_add_symbols
#print axioms qpow_substitutionOne_bvar_code_length_le
#print axioms binaryTermCode_substitutionOne_qpow_length_le
#print axioms binaryFormulaCode_substitutionAlong_length_le
#print axioms binaryFormulaCode_substitution_one_length_le
#print axioms formulaListCodeWeight_map_shift_le

end FoundationCompactSyntaxTransformationCodeBounds
